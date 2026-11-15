#!/usr/bin/env python3
"""Compile independent Rocq certificate blocks in parallel, with safe resume."""
from __future__ import annotations
import argparse
import concurrent.futures
import fcntl
import hashlib
import json
import os
from pathlib import Path
import signal
import shutil
import subprocess
import sys
import threading
import time
from manifest_paths import resolve_path


def digest(path):
    with path.open('rb') as source:
        return hashlib.file_digest(source,'sha256').hexdigest()


def foundation_context(root,rocq):
    """Fingerprint the actual compiler and the shared checked objects."""
    version=subprocess.check_output([str(rocq),'--version'],text=True)
    conclusions={'CertificateResult.vo','OptimalPlay.vo'}
    foundation={p.name:digest(p) for p in root.glob('*.vo') if p.name not in conclusions}
    plugin=root/'native/tpp_data/tpp_data_plugin.cmxs'
    if plugin.exists():foundation['native/tpp_data/tpp_data_plugin.cmxs']=digest(plugin)
    context=hashlib.sha256(json.dumps([version,foundation],sort_keys=True).encode()).hexdigest()
    return version,context


def main(args):
    directory=args.directory.resolve()
    root=directory.parent
    manifest=json.loads((directory/'manifest.json').read_text())
    rocq=args.rocq.expanduser().resolve()
    lock=(directory/'build.lock').open('a')
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    version,context=foundation_context(root,rocq)
    environment=os.environ.copy()
    if manifest.get('encoding')=='native' or manifest.get('links_encoding') in ('grouped_imports','reflected_imports'):
        environment['OCAMLPATH']=str(root/'native')+(':'+environment['OCAMLPATH'] if environment.get('OCAMLPATH') else '')
    grid_dependencies={p.name:digest(p) for p in (root/'GridExp').glob('*.vo')}
    grid_context=hashlib.sha256(json.dumps(grid_dependencies,sort_keys=True).encode()).hexdigest()
    export_dependencies={n:digest(root/'ExportExp'/n) for n in ('ExportDag.vo','ImportCheck.vo') if (root/'ExportExp'/n).exists()}
    export_context=hashlib.sha256(json.dumps(export_dependencies,sort_keys=True).encode()).hexdigest()
    grid_end=root/'GridEndExp/GridEndgame.vo'
    grid_end_context=digest(grid_end) if grid_end.exists() else ''
    state_path=directory/'build-state.json'
    state=json.loads(state_path.read_text()) if state_path.exists() else {}
    if state.get('context')!=context:
        state={'context':context,'version':version,'modules':{}}
    state['complete']=False
    state['blocks_complete']=False
    state.pop('check',None)
    mutex=threading.RLock()
    children=set()
    stop=threading.Event()
    start=time.monotonic()

    def save():
        temp=state_path.with_suffix('.tmp')
        temp.write_text(json.dumps(state,indent=2)+'\n')
        temp.replace(state_path)

    def interrupt(signum,frame):
        stop.set()
        with mutex:
            for p in children:
                if p.poll() is None:p.terminate()
    signal.signal(signal.SIGINT,interrupt)
    signal.signal(signal.SIGTERM,interrupt)

    def auxiliary_for(source):
        with source.open() as f:prefix=f.read(2048)
        uses_grid='TPP2026.Six.GridExp' in prefix
        auxiliary=grid_context if uses_grid else None
        if 'TPP2026.Six.ExportExp' in prefix:auxiliary=(auxiliary or '')+':'+export_context
        if 'TPP2026.Six.GridEndExp' in prefix:auxiliary=(auxiliary or '')+':'+grid_context+':'+grid_end_context
        return auxiliary

    def compile_module(name):
        source=directory/(name+'.v');obj=source.with_suffix('.vo')
        source_hash=digest(source)
        auxiliary=auxiliary_for(source)
        with mutex:
            old=state['modules'].get(name,{})
            if old.get('source')==source_hash and old.get('auxiliary')==auxiliary and old.get('exit_code')==0 and obj.exists() and old.get('object')==digest(obj):
                return True
        if stop.is_set() or (args.seconds and time.monotonic()-start>=args.seconds):
            stop.set();return False
        command=[str(rocq),'compile','-q','-noglob','-Q',str(root),'TPP2026.Six',str(source)]
        t=time.monotonic()
        with (directory/(name+'.log')).open('w') as output:
            p=subprocess.Popen(command,cwd=root,env=environment,stdout=output,stderr=subprocess.STDOUT)
            with mutex:children.add(p)
            try:
                status=p.wait(timeout=args.module_timeout or None)
            except subprocess.TimeoutExpired:
                p.terminate()
                try:p.wait(timeout=10)
                except subprocess.TimeoutExpired:p.kill();p.wait()
                status=124
            finally:
                with mutex:children.discard(p)
        record={'source':source_hash,'exit_code':status,'seconds':time.monotonic()-t}
        if auxiliary is not None:record['auxiliary']=auxiliary
        if status==0:record['object']=digest(obj)
        with mutex:
            state['modules'][name]=record
            save()
        if status:
            print(f'{name}: failed ({status}); see {name}.log',flush=True)
            stop.set()
        return status==0

    if not compile_module('Goal'):return 2
    # A changed Goal object makes all block proofs stale, even if source text
    # is unchanged. It is small, and its hash is kept explicitly.
    goal_hash=digest(directory/'Goal.vo')
    if state.get('goal')!=goal_hash:
        state['modules']={k:v for k,v in state['modules'].items() if k=='Goal'}
        state['goal']=goal_hash
        save()
    blocks=['B%05d'%b['index'] for b in manifest['blocks']]
    success=True;done=0;last=time.monotonic()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures={pool.submit(compile_module,name):name for name in blocks}
        for future in concurrent.futures.as_completed(futures):
            success=future.result() and success;done+=1
            now=time.monotonic()
            if now-last>=30 or done==len(blocks):
                passed=sum(1 for n,r in state['modules'].items() if n.startswith('B') and r['exit_code']==0)
                print(f'blocks checked: {passed}/{len(blocks)}; seconds={now-start:.1f}',flush=True)
                last=now
    if not success or stop.is_set():return 2
    state['blocks_complete']=True;save()
    if args.blocks_only:
        print(f'Checked {len(blocks)} independent blocks; composition pending',flush=True)
        return 0
    # The composition must be rebuilt if any block object changed. Rechecking
    # these two small sources also detects a stale transitive import directly.
    if manifest.get('parallel_links'):
        command=[sys.executable,str(root/'build_parallel_links.py'),str(resolve_path(directory, manifest['parallel_links'])),
                 '--jobs',str(args.link_jobs),'--rocq',str(rocq)]
        if args.link_interface_jobs:command+=['--interface-jobs',str(args.link_interface_jobs)]
        p=subprocess.Popen(command,cwd=root.parent)
        with mutex:children.add(p)
        status=p.wait()
        with mutex:children.discard(p)
        if status:return status
    elif manifest.get('links_prefix'):
        name='LinksPrefix'
        state['modules'].pop(name,None)
        dependencies={f'B{b["index"]:05d}.vo':digest(directory/f'B{b["index"]:05d}.vo')
                      for b in manifest['blocks'][:manifest['links_prefix']]}
        receipt_path=directory/'links-prefix-receipt.json'
        if receipt_path.exists():
            receipt=json.loads(receipt_path.read_text())
            if (receipt.get('context')==context and receipt.get('exit_code')==0 and
                receipt['source']==digest(directory/(name+'.v')) and
                receipt.get('object')==digest(directory/(name+'.vo')) and
                receipt['dependencies']==dependencies):
                # Reuse the prefix only when the receipt matches its inputs.
                record={k:v for k,v in receipt.items() if k in ('source','object','seconds','exit_code')}
                auxiliary=auxiliary_for(directory/(name+'.v'))
                if auxiliary is not None:record['auxiliary']=auxiliary
                state['modules'][name]=record
        if not compile_module(name):return 2
        receipt=dict(state['modules'][name],context=context,dependencies=dependencies)
        receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
    for name in ('Links','Result'):
        state['modules'].pop(name,None)
        if not compile_module(name):return 2
    if args.check!='none':
        command=[str(rocq),'check','-silent','-Q',str(root),'TPP2026.Six']
        if args.check=='vm':command+=['-bytecode-compiler','yes']
        command+=[manifest['namespace']+'.Result']
        t=time.monotonic()
        with (directory/'Check.log').open('w') as f:
            p=subprocess.Popen(command,cwd=root,env=environment,stdout=f,stderr=subprocess.STDOUT)
            with mutex:children.add(p)
            status=p.wait()
            with mutex:children.discard(p)
        state['check']={'command':command,'exit_code':status,'seconds':time.monotonic()-t}
        save()
        if status:return 1
    state['complete']=True
    state['seconds_this_run']=time.monotonic()-start
    save()
    print(f"Compiled {manifest['namespace']}.Result ({manifest['nodes']} nodes)",flush=True)
    return 0


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory',type=Path)
    parser.add_argument('--rocq',type=Path,default=Path(shutil.which('rocq') or 'rocq'))
    parser.add_argument('--jobs',type=int,default=4)
    parser.add_argument('--link-jobs',type=int,default=2,help='separate memory-conscious concurrency for link batches')
    parser.add_argument('--link-interface-jobs',type=int,default=0,help='separate concurrency for data and bridge modules; 0 follows --link-jobs')
    parser.add_argument('--seconds',type=float,default=0)
    parser.add_argument('--module-timeout',type=float,default=1800)
    parser.add_argument('--blocks-only',action='store_true',help='stop after all independent blocks, before closed assembly')
    parser.add_argument('--check',choices=('none','kernel','vm'),default='none')
    args=parser.parse_args()
    if args.jobs<1 or args.link_jobs<1 or args.link_interface_jobs<0 or args.seconds<0 or args.module_timeout<0:parser.error('invalid resource limit')
    raise SystemExit(main(args))
