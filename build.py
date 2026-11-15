#!/usr/bin/env python3
"""Build the Othello proofs from the distributed sources in an isolated directory."""
from pathlib import Path
import argparse
import csv
from datetime import datetime, timezone
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
MAPS = [
    ('4x4', 'TPP2026.Four'), ('6x6', 'TPP2026.Six'),
    ('common', 'TPP2026.Common'), ('common/proofs', 'TPP2026.Common.Proofs'),
    ('boards', 'TPP2026.Boards'), ('proofs', 'TPP2026.Proofs'),
    ('proofs/equivalence', 'TPP2026.Proofs.Equivalence'),
    ('proofs/certificates', 'TPP2026.Proofs.Certificates'),
    ('solutions', 'TPP2026.Solutions'),
]
COMMON = ['common/Rules', 'common/Specification', 'common/proofs/RuleFacts',
          'common/proofs/SpecificationFacts', 'common/Game', 'common/proofs/GameFacts']
FOUR = ['4x4/Rules', '4x4/Bounds', '4x4/Certificate', '4x4/CertificateResult', '4x4/RulesExamples']
SIX_BASE = ['Rules', 'Bounds', 'Dag', 'FastDag', 'FastDecode', 'NatBits', 'BitRules',
            'BitDag', 'BlockDag', 'ProjectDag', 'BinaryDag', 'BinaryBytes', 'Endgame',
            'CutDag', 'StringDag', 'Symmetry', 'InitialSymmetry', 'ImportDag', 'TacticData',
            'RulesExamples']
SIX_NATIVE = ['NativeData', 'Replay', 'GridExp/GridRules', 'GridExp/GridDag',
              'ExportExp/ExportDag', 'ExportExp/ImportCheck',
              'LinkExp/CompressedLink', 'LinkExp/CompressedData',
              'LinkExp/BoundedAudit']
PLUGINS = ['tpp_data', 'tpp_compressed', 'tpp_audit']
COMPILED = {'.vo', '.vos', '.vok', '.glob', '.aux', '.cmxs', '.cmx', '.cmi', '.cmo', '.o', '.pyc'}


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def write_json(path, data):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(data, indent=2) + '\n')
    temporary.replace(path)


def capacity(build, six):
    existing = build
    while not existing.exists():
        existing = existing.parent
    objects = sum(p.stat().st_size for p in build.rglob('*.vo')) if build.exists() else 0
    budget = 50_000_000_000 if six else 100_000_000
    reserve = 20_000_000_000 if six else 1_000_000_000
    additional = max(budget - objects, 0)
    free = shutil.disk_usage(existing).free
    return {'free_bytes': free, 'existing_object_bytes': objects,
            'estimated_full_object_bytes': 33_000_000_000 if six else 10_000_000,
            'additional_build_budget_bytes': additional, 'reserve_bytes': reserve,
            'required_free_bytes': additional + reserve,
            'enough_space': free >= additional + reserve,
            'certificate_source_bytes_copied': 0}


class Build:
    def __init__(self, args):
        self.args = args
        self.path = args.build_dir.resolve()
        self.rocq = Path(shutil.which(str(args.rocq)) or str(args.rocq)).expanduser().resolve()
        if not self.rocq.is_file():
            raise ValueError('Rocq not found; set ROCQ=/absolute/path/to/rocq')
        self.version = subprocess.check_output([str(self.rocq), '--version'], text=True)
        self.environment = os.environ.copy()
        for key in ('COQPATH', 'ROCQPATH', 'OCAMLPATH'):
            self.environment.pop(key, None)
        self.environment['OCAMLPATH'] = str(self.path / '6x6/native')
        self.environment['PATH'] = str(self.rocq.parent) + os.pathsep + self.environment.get('PATH', '')
        self.environment.setdefault('OCAMLRUNPARAM', 'o=30')
        self.mapping = [x for directory, logical in MAPS for x in ('-Q', str(self.path / directory), logical)]
        self.record_path = self.path / 'build.json'
        self.record = json.loads(self.record_path.read_text()) if self.record_path.exists() else {
            'started': datetime.now(timezone.utc).isoformat(),
            'initial_project_object_count': 0,
            'source_only': True, 'steps': {}, 'requests': []}
        if (self.record.get('source_only') is not True or
                self.record.get('initial_project_object_count') != 0 or
                not isinstance(self.record.get('steps'), dict) or
                not isinstance(self.record.get('requests'), list)):
            raise ValueError('The output directory does not have a source-build record')
        self.record['toolchain'] = self.version
        self.record['complete'] = False

    def prepare(self):
        certificate_source = self.args.certificate_source.resolve()
        names = (ROOT / 'distribution/git-files.txt').read_text().splitlines()
        if any(Path(n).suffix in COMPILED for n in names):
            raise ValueError('Compiled files are not allowed in the source inventory')
        initial = list(self.path.rglob('*.vo')) if self.path.exists() else []
        if not self.record_path.exists() and initial:
            raise ValueError('Unrecorded compiled files found in the build directory')
        if (not self.record_path.exists() and self.path.exists() and
                any(self.path.iterdir())):
            raise ValueError('Unrecorded files found; use a new or empty build directory')
        self.path.mkdir(parents=True, exist_ok=True)
        # Record ownership before preparing inputs, so an interrupted preparation
        # can resume without accepting an unrelated directory as build output.
        write_json(self.record_path, self.record)
        (self.path / 'logs').mkdir(exist_ok=True)
        for directory, _ in MAPS:
            (self.path / directory).mkdir(parents=True, exist_ok=True)
        source_hashes = {}
        for relative in names:
            source, target = ROOT / relative, self.path / relative
            if source.is_symlink() or not source.resolve().is_relative_to(ROOT):
                raise ValueError(f'Invalid source path: {relative}')
            if source.stat().st_size > 5_000_000:
                raise ValueError(f'Large file in the small source package: {relative}')
            sha = digest(source)
            source_hashes[relative] = sha
            target.parent.mkdir(parents=True, exist_ok=True)
            if not target.exists() or digest(target) != sha:
                shutil.copy2(source, target)
        count = 0
        if self.args.target != '4x4':
            with (ROOT / 'distribution/certificates.tsv').open() as stream:
                rows = list(csv.DictReader(stream, delimiter='\t'))
            for row in rows:
                relative = Path(row['path'])
                if relative.is_absolute() or '..' in relative.parts or relative.suffix not in ('.v', '.json'):
                    raise ValueError(f'Invalid certificate path: {relative}')
                source, target = certificate_source / relative, self.path / relative
                if source.is_symlink() or not source.resolve().is_relative_to(certificate_source):
                    raise ValueError(f'Invalid certificate source: {relative}')
                if source.stat().st_size != int(row['bytes']) or digest(source) != row['sha256']:
                    raise ValueError(f'Certificate size or hash mismatch: {relative}')
                target.parent.mkdir(parents=True, exist_ok=True)
                if target.exists():
                    if not os.path.samefile(source, target):
                        raise ValueError(f'Unexpected certificate copy in build directory: {relative}')
                else:
                    # The compiler writes new objects beside this name. It never edits the source.
                    # Do not fall back to copying several GB if hard links are unavailable.
                    os.link(source, target)
                count += 1
            print(f'Checked and hard-linked {count} certificate source files; copied no certificate data.', flush=True)
        write_json(self.path / 'inputs.json', {'small_sources': source_hashes,
                   'certificate_inventory_sha256': digest(ROOT / 'distribution/certificates.tsv'),
                   'certificate_files': count, 'certificate_data_copied': False,
                   'project_load_paths': {logical: directory for directory, logical in MAPS}})
        self.record['requests'].append({'target': self.args.target, 'started': datetime.now(timezone.utc).isoformat()})
        write_json(self.record_path, self.record)

    def run(self, name, command, *, cwd=None, live=False, timeout=None):
        log = self.path / 'logs' / (name.replace('/', '_') + '.log')
        print(f'Starting {name}', flush=True)
        started = time.monotonic()
        with log.open('w') as output:
            if live:
                process = subprocess.Popen(command, cwd=cwd or self.path, env=self.environment,
                                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                try:
                    for line in process.stdout:
                        output.write(line)
                        output.flush()
                        print(line, end='', flush=True)
                    code = process.wait()
                except BaseException:
                    process.terminate()
                    process.wait()
                    raise
            else:
                try:
                    code = subprocess.run(command, cwd=cwd or self.path, env=self.environment,
                                          stdout=output, stderr=subprocess.STDOUT, timeout=timeout).returncode
                except subprocess.TimeoutExpired:
                    code = 124
        entry = {'exit_code': code, 'seconds': time.monotonic() - started,
                 'command': [str(x) for x in command], 'log': str(log.relative_to(self.path))}
        self.record['steps'][name] = entry
        write_json(self.record_path, self.record)
        if code:
            print(log.read_text()[-6000:])
            raise RuntimeError(f'{name} failed ({code}); see {log}')
        return entry

    def compile(self, name):
        source = self.path / (name + '.v')
        obj = source.with_suffix('.vo')
        inputs = {'source': digest(source), 'toolchain': self.version}
        for namespace, modules in re.findall(r'^From\s+(\S+)\s+Require\s+(?:Import|Export)\s+(.+?)\.(?=\s|$)', source.read_text(), re.M | re.S):
            for directory, logical in sorted(MAPS, key=lambda pair: -len(pair[1])):
                if namespace == logical or namespace.startswith(logical + '.'):
                    suffix = namespace[len(logical):].strip('.').replace('.', '/')
                    for module in modules.split():
                        dependency = self.path / directory / suffix / (module.replace('.', '/') + '.vo')
                        inputs[str(dependency.relative_to(self.path))] = digest(dependency)
                    break
        for plugin in re.findall(r'Declare ML Module "([^"]+)"', source.read_text()):
            inputs[plugin] = digest(self.path / '6x6/native' / plugin / (plugin + '_plugin.cmxs'))
        old = self.record['steps'].get(name, {})
        if old.get('inputs') == inputs and old.get('exit_code') == 0 and obj.exists() and old.get('object_sha256') == digest(obj):
            return
        entry = self.run(name, [str(self.rocq), 'compile', '-q', '-noglob', *self.mapping, str(source)],
                         timeout=None if name == 'proofs/Audit6' else self.args.module_timeout or None)
        entry.update(inputs=inputs, object_sha256=digest(obj))
        write_json(self.record_path, self.record)

    def native(self):
        find = self.args.ocamlfind or self.rocq.parent / 'ocamlfind'
        if not Path(find).is_file():
            raise ValueError('Set OCAMLFIND to ocamlfind from the Rocq toolchain')
        for plugin in PLUGINS:
            directory = self.path / '6x6/native' / plugin
            source = directory / (plugin + '_plugin.ml')
            obj = source.with_suffix('.cmxs')
            inputs = {'source': digest(source), 'META': digest(directory / 'META'), 'toolchain': self.version}
            old = self.record['steps'].get('native/' + plugin, {})
            if old.get('inputs') == inputs and old.get('exit_code') == 0 and obj.exists() and old.get('object_sha256') == digest(obj):
                continue
            entry = self.run('native/' + plugin, [str(find), 'ocamlopt', '-rectypes',
                             '-package', 'rocq-runtime.plugins.ltac2', '-shared', '-linkall',
                             '-o', obj.name, source.name], cwd=directory)
            entry.update(inputs=inputs, object_sha256=digest(obj))
            write_json(self.record_path, self.record)

    def board(self, size):
        for name in COMMON + ['boards/' + size]:
            self.compile(name)

    def common(self, size):
        self.board(size)
        solution = {'Four': 'Othello4x4', 'Six': 'Othello6x6'}[size]
        for name in ['proofs/equivalence/' + size,
                     'proofs/certificates/' + size, 'solutions/' + solution]:
            self.compile(name)

    def four(self):
        for name in FOUR:
            self.compile(name)
        self.common('Four')
        self.run('kernel-4x4', [str(self.rocq), 'check', '-silent', *self.mapping,
                               'TPP2026.Solutions.Othello4x4', 'TPP2026.Four.RulesExamples'],
                 timeout=self.args.module_timeout or None)

    def six(self):
        for name in SIX_BASE:
            self.compile('6x6/' + name)
        self.native()
        for name in SIX_NATIVE:
            self.compile('6x6/' + name)
        self.board('Six')
        self.compile('proofs/equivalence/Six')
        self.compile('6x6/Semantics/Optimal')
        self.compile('6x6/Semantics/OptimalReplay')
        for directory in ('InitialLower', 'InitialUpper'):
            self.run('certificate/' + directory,
                     [sys.executable, str(self.path / '6x6/build_blocks.py'),
                      str(self.path / '6x6' / directory), '--rocq', str(self.rocq),
                      '--jobs', str(self.args.jobs), '--link-jobs', str(self.args.link_jobs),
                      '--link-interface-jobs', str(self.args.interface_jobs),
                      '--module-timeout', str(self.args.module_timeout)], live=True)
        self.compile('6x6/CertificateResult')
        self.compile('6x6/OptimalPlay')
        self.common('Six')

    def finish(self):
        self.record['complete'] = True
        self.record['finished'] = datetime.now(timezone.utc).isoformat()
        self.record['object_bytes'] = sum(p.stat().st_size for p in self.path.rglob('*.vo'))
        self.record['free_bytes_after'] = shutil.disk_usage(self.path).free
        write_json(self.record_path, self.record)
        print(f'Build passed. Record: {self.record_path}', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('target', choices=['4x4', '6x6', 'all', 'disk', 'audit-6x6', 'kernel-6x6'])
    parser.add_argument('--rocq', default='rocq')
    parser.add_argument('--ocamlfind', type=Path)
    parser.add_argument('--build-dir', type=Path, default=ROOT / '_build')
    parser.add_argument('--certificate-source', type=Path, default=ROOT)
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--link-jobs', type=int, default=1)
    parser.add_argument('--interface-jobs', type=int, default=4)
    parser.add_argument('--module-timeout', type=float, default=1800)
    parser.add_argument('--fresh', action='store_true', help='require a new, empty build directory')
    args = parser.parse_args()
    if min(args.jobs, args.link_jobs, args.interface_jobs) < 1 or args.module_timeout < 0:
        parser.error('Invalid resource limit')
    build = args.build_dir.resolve()
    if build == ROOT or ROOT.is_relative_to(build):
        parser.error('Use a separate build directory')
    space = capacity(build, args.target != '4x4')
    print(json.dumps(space, indent=2), flush=True)
    if args.target == 'disk':
        return 0 if space['enough_space'] else 1
    if not space['enough_space']:
        parser.error('Not enough free space for the build budget and reserve')
    if args.fresh and build.exists() and any(build.iterdir()):
        parser.error('--fresh requires a new or empty build directory')
    job = Build(args)
    job.record.setdefault('initial_capacity', job.record.get('capacity_before', space))
    job.record['capacity_before'] = space
    job.prepare()
    if args.target in ('4x4', 'all'):
        job.four()
    if args.target in ('6x6', 'all', 'audit-6x6', 'kernel-6x6'):
        job.six()
    if args.target == 'audit-6x6':
        job.compile('proofs/Audit6')
    if args.target == 'kernel-6x6':
        job.run('kernel-6x6', [str(job.rocq), 'check', '-silent', *job.mapping, 'TPP2026.Solutions.Othello6x6'])
    job.finish()
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
