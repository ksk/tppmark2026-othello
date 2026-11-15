#!/usr/bin/env python3
"""Kernel-check independent conditional links, then apply them without axioms."""
import argparse
from concurrent.futures import ThreadPoolExecutor,as_completed
import fcntl
import hashlib
import json
import os
from pathlib import Path
import signal
import shutil
import subprocess
import threading
import time
from build_blocks import foundation_context
from manifest_paths import resolve_path


def digest(path):
    with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()


def main(directory,jobs,rocq,through=0,only_group=None,conditional_only=False,interface_jobs=None):
    interface_jobs=interface_jobs or jobs
    directory=directory.resolve();root=directory.parent
    lock=(directory/'build.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX)
    manifest=json.loads((directory/'manifest.json').read_text());source=resolve_path(directory, manifest['source'])
    groups=[g for i,g in enumerate(manifest['groups']) if (not through or max(g['blocks'])<through) and (only_group is None or i==only_group)]
    if not groups:raise ValueError('no matching link groups')
    context=json.loads((source/'build-state.json').read_text())['context']
    if foundation_context(root,rocq.expanduser().resolve())[1]!=context:
        raise ValueError('shared foundations changed; rebuild source blocks first')
    statefile=directory/'build-state.json';state=json.loads(statefile.read_text()) if statefile.exists() else {}
    if state.get('context')!=context:state=dict(context=context,modules={})
    state['complete']=False;mutex=threading.RLock();children=set();stop=threading.Event();started=time.monotonic()
    dependency_hashes={}
    environment=os.environ.copy();environment['OCAMLPATH']=str(root/'native')+(':'+environment['OCAMLPATH'] if environment.get('OCAMLPATH') else '')
    def save():
        p=statefile.with_suffix('.tmp');p.write_text(json.dumps(state,indent=2)+'\n');p.replace(statefile)
    def interrupt(sig,frame):
        stop.set()
        with mutex:
            for p in children:
                if p.poll() is None:p.terminate()
    signal.signal(signal.SIGINT,interrupt);signal.signal(signal.SIGTERM,interrupt)
    def compile(name,dependencies):
        path=directory/(name+'.v');obj=path.with_suffix('.vo')
        sha=digest(path);deps={str(p):dependency_hashes[str(p)] if str(p) in dependency_hashes else digest(p) for p in dependencies}
        old=state['modules'].get(name,{})
        if old.get('exit_code')==0 and old.get('source')==sha and old.get('dependencies')==deps and obj.exists() and old.get('object')==digest(obj):return True
        if stop.is_set():return False
        t=time.monotonic()
        with (directory/(name+'.log')).open('w') as out:
            p=subprocess.Popen([str(rocq.expanduser()),'compile','-q','-noglob','-Q',str(root),'TPP2026.Six',str(path)],env=environment,stdout=out,stderr=subprocess.STDOUT)
            with mutex:children.add(p)
            code=p.wait()
            with mutex:children.discard(p)
        record=dict(source=sha,dependencies=deps,exit_code=code,seconds=time.monotonic()-t)
        if code==0:record['object']=digest(obj)
        with mutex:state['modules'][name]=record;save()
        print(f'{name}: exit={code}; seconds={record["seconds"]:.1f}',flush=True)
        if code:stop.set()
        return code==0
    shared=[source/'Goal.vo',root/'ExportExp/ExportDag.vo',root/'ExportExp/ImportCheck.vo',root/'NativeData.vo',root/'native/tpp_data/tpp_data_plugin.cmxs']
    if manifest.get('compressed'):shared += [root/'LinkExp/CompressedLink.vo',root/'LinkExp/CompressedData.vo',root/'native/tpp_compressed/tpp_compressed_plugin.cmxs']
    elif manifest.get('lazy'):shared += [root/'LinkExp/LazyLink.vo',root/'LinkExp/LazyData.vo',root/'native/tpp_lazy/tpp_lazy_plugin.cmxs']
    if manifest.get('direct'):shared += [root/'LinkExp/FastLink.vo',root/'native/tpp_links/tpp_links_plugin.cmxs']
    # These jobs are run after their blocks have finished; no partially
    # written or stale block interface is accepted as a dependency.
    block_state=json.loads((source/'build-state.json').read_text())
    required={d for g in groups for d in g['dependencies']}
    for d in required:
        name=f'B{d:05d}';record=block_state['modules'][name]
        obj=source/(name+'.vo');sha=digest(obj)
        assert record['exit_code']==0 and record['source']==digest(source/(name+'.v')) and record['object']==sha
        dependency_hashes[str(obj)]=sha
    dependency_hashes.update({str(p):digest(p) for p in shared})
    if manifest.get('split_data'):
        with ThreadPoolExecutor(max_workers=interface_jobs) as pool:
            pending=[pool.submit(compile,f'D{d:05d}',shared) for d in sorted(required)]
            results=[f.result() for f in as_completed(pending)]
            if not all(results) or stop.is_set():return 2
        dependency_hashes.update({str(directory/f'D{d:05d}.vo'):digest(directory/f'D{d:05d}.vo') for d in required})
    if manifest.get('lazy') and not conditional_only:
        def bridge_deps(d):
            deps=shared+[source/f'B{d:05d}.vo']
            if manifest.get('split_data'):deps += [directory/f'D{d:05d}.vo']
            old=manifest.get('reuse_bridges',{}).get(str(d))
            if old:deps.append(resolve_path(directory, old))
            return deps
        with ThreadPoolExecutor(max_workers=interface_jobs) as pool:
            pending=[pool.submit(compile,f'E{d:05d}',bridge_deps(d)) for d in sorted(required)]
            results=[f.result() for f in as_completed(pending)]
            if not all(results) or stop.is_set():return 2
        dependency_hashes.update({str(directory/f'E{d:05d}.vo'):digest(directory/f'E{d:05d}.vo') for d in required})
    def group_deps(g):
        ds=g['blocks'] if manifest.get('split_data') else g['dependencies']
        deps=shared+[source/f'B{d:05d}.vo' for d in ds]
        if manifest.get('lazy'):
            prefix='D' if manifest.get('split_data') else 'E'
            deps += [directory/f'{prefix}{d:05d}.vo' for d in g['dependencies']]
        return deps
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        pending=[pool.submit(compile,g['name'],group_deps(g)) for g in groups]
        results=[f.result() for f in as_completed(pending)];ok=all(results)
    if not ok or stop.is_set():return 2
    if conditional_only or len(groups)<len(manifest['groups']):
        save();print(f'Checked {len(groups)} conditional link batches; assembly pending',flush=True);return 0
    if not compile('Links',shared+[directory/(g['name']+'.vo') for g in manifest['groups']]+([directory/f'E{d:05d}.vo' for d in sorted(required)] if manifest.get('split_data') else [])):return 2
    state['complete']=True;state['seconds_this_run']=time.monotonic()-started;save()
    print(f'Closed assembly: {manifest["namespace"]}.Links',flush=True)
    return 0


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('directory',type=Path);p.add_argument('--jobs',type=int,default=8)
    p.add_argument('--rocq',type=Path,default=Path(shutil.which('rocq') or 'rocq'))
    p.add_argument('--through-block',type=int,default=0)
    p.add_argument('--only-group',type=int)
    p.add_argument('--interface-jobs',type=int,help='separate concurrency for small data and bridge modules')
    p.add_argument('--conditional-only',action='store_true')
    a=p.parse_args()
    if a.conditional_only and not json.loads((a.directory/'manifest.json').read_text()).get('split_data'):p.error('--conditional-only requires split data')
    raise SystemExit(main(a.directory,a.jobs,a.rocq,a.through_block,a.only_group,a.conditional_only,a.interface_jobs))
