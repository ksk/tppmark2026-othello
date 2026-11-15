"""Check the source inventories without copying any certificate data."""
from pathlib import Path, PurePosixPath
import argparse
import csv
import hashlib
import subprocess

ROOT = Path(__file__).resolve().parent.parent
COMPILED = {'.vo', '.vos', '.vok', '.glob', '.aux', '.cmxs', '.cmx', '.cmi', '.cmo', '.o', '.pyc'}


def checked_path(relative, root=ROOT):
    path = PurePosixPath(relative)
    if path.is_absolute() or '..' in path.parts or str(path) != relative:
        raise ValueError(f'Invalid inventory path: {relative}')
    result = root / relative
    if result.is_symlink() or not result.is_file() or not result.resolve().is_relative_to(root):
        raise ValueError(f'Missing file or external link: {relative}')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificates', action='store_true', help='also read and hash the separate certificate sources')
    parser.add_argument('--certificate-root', type=Path, default=ROOT, help='directory containing the separate certificate sources')
    parser.add_argument('--staged', action='store_true', help='also check that the Git index matches the file inventory and working tree')
    args = parser.parse_args()
    files = (ROOT / 'distribution/git-files.txt').read_text().splitlines()
    if any(Path(p).suffix in COMPILED for p in files):
        raise ValueError('Compiled files must not be included in the source package')
    if len(files) != len(set(files)):
        raise ValueError('Duplicate Git inventory entry')
    paths = [checked_path(p) for p in files]
    total = sum(p.stat().st_size for p in paths)
    if any(p.stat().st_size > 5_000_000 for p in paths):
        raise ValueError('A repository source file exceeds the 5 MB inventory limit')
    print(f'Repository source files: {len(files)} files, {total:,} bytes')
    with (ROOT / 'distribution/certificates.tsv').open() as f:
        rows = list(csv.DictReader(f, delimiter='\t'))
    names = [row['path'] for row in rows]
    if any(Path(p).suffix not in ('.v', '.json') for p in names):
        raise ValueError('The certificate archive must contain only source and manifest files')
    if len(names) != len(set(names)) or set(names) & set(files):
        raise ValueError('Duplicate or overlapping certificate inventory entry')
    print(f'Separate certificates: {len(rows)} files, {sum(int(r["bytes"]) for r in rows):,} bytes')
    if args.certificates:
        for i, row in enumerate(rows):
            path = checked_path(row['path'], args.certificate_root.resolve())
            if path.stat().st_size != int(row['bytes']):
                raise ValueError(f'Size mismatch: {row["path"]}')
            with path.open('rb') as f:
                actual = hashlib.file_digest(f, 'sha256').hexdigest()
            if actual != row['sha256']:
                raise ValueError(f'Hash mismatch: {row["path"]}')
            if i % 1000 == 0:
                print(f'Certificates checked: {i}/{len(rows)}', flush=True)
        print('All certificate sizes and SHA-256 hashes match.')
    if args.staged:
        raw = subprocess.check_output(['git', 'ls-files', '--stage', '-z'], cwd=ROOT)
        entries = {}
        for item in raw.decode().split('\0'):
            if not item:
                continue
            metadata, name = item.split('\t', 1)
            mode, oid, stage = metadata.split()
            if mode not in ('100644', '100755') or stage != '0':
                raise ValueError(f'Unexpected index mode or merge stage: {name}')
            entries[name] = oid
        if set(entries) != set(files):
            raise ValueError(f'Index mismatch: extra={sorted(set(entries)-set(files))}; missing={sorted(set(files)-set(entries))}')
        for name, oid in entries.items():
            actual = subprocess.check_output(['git', 'hash-object', '--', name], cwd=ROOT, text=True).strip()
            if actual != oid:
                raise ValueError(f'Unstaged change: {name}')
        print('Git index matches the file inventory and working tree.')


if __name__ == '__main__':
    main()
