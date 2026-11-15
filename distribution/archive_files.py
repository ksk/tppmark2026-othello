"""Check or unpack the separate 6x6 certificate source archives."""

import argparse
import csv
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import tarfile
import tempfile


ROOT = Path(__file__).resolve().parent.parent
DIRECTORIES = {
    'InitialLower', 'InitialLowerCompact',
    'InitialUpper', 'InitialUpperLocalCompact',
}


def file_hash(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def load_inventory():
    report = json.loads((ROOT / 'distribution/archives.json').read_text())
    inventory = ROOT / 'distribution/certificates.tsv'
    if file_hash(inventory) != report['inventory']['sha256']:
        raise ValueError('The archive record and certificate inventory differ')
    with inventory.open() as stream:
        rows = list(csv.DictReader(stream, delimiter='\t'))
    entries = {}
    for row in rows:
        name = row['path']
        path = PurePosixPath(name)
        if (len(path.parts) != 3 or path.parts[0] != '6x6'
                or path.parts[1] not in DIRECTORIES
                or path.suffix not in ('.v', '.json')
                or str(path) != name or name in entries):
            raise ValueError(f'Invalid inventory entry: {name}')
        entries[name] = row
    return report, entries


def check_archives(directory, report):
    paths = []
    for item in report['archives']:
        name = item['file']
        if Path(name).name != name:
            raise ValueError(f'Invalid archive name: {name}')
        path = directory / name
        if (not path.is_file() or path.stat().st_size != item['bytes']
                or file_hash(path) != item['sha256']):
            raise ValueError(f'Missing or changed archive: {path}')
        print(f'{name}: size and SHA-256 match', flush=True)
        paths.append(path)
    return paths


def unpack_archives(paths, entries, destination):
    board = destination / '6x6'
    if board.is_symlink():
        raise ValueError(f'The destination must not be a symlink: {board}')
    for name in sorted(DIRECTORIES):
        target = board / name
        if target.exists() or target.is_symlink():
            raise ValueError(f'Certificate directory already exists: {target}')
    board.mkdir(parents=True, exist_ok=True)
    required = sum(int(row['bytes']) for row in entries.values())
    if shutil.disk_usage(board).free < required + 1_000_000_000:
        raise ValueError('Unpacking needs the source size plus 1 GB free')
    seen = set()
    # Write each source once, then move its directory on the same filesystem.
    with tempfile.TemporaryDirectory(prefix='.unpack-', dir=board) as work:
        temporary = Path(work)
        for path in paths:
            print(f'Unpacking {path.name}', flush=True)
            with gzip.open(path, 'rb') as compressed:
                with tarfile.open(fileobj=compressed, mode='r|') as archive:
                    for member in archive:
                        name = member.name
                        if (name not in entries or name in seen
                                or not member.isfile()
                                or member.size != int(entries[name]['bytes'])):
                            raise ValueError(
                                f'Unexpected archive member: {name}')
                        target = temporary / name
                        target.parent.mkdir(parents=True, exist_ok=True)
                        checksum = hashlib.sha256()
                        with archive.extractfile(member) as source:
                            with target.open('xb') as output:
                                while data := source.read(1024 * 1024):
                                    output.write(data)
                                    checksum.update(data)
                        if checksum.hexdigest() != entries[name]['sha256']:
                            raise ValueError(
                                f'Certificate hash mismatch: {name}')
                        seen.add(name)
                # Finish the gzip stream to check its CRC and length trailer.
                while compressed.read(1024 * 1024):
                    pass
        if seen != set(entries):
            raise ValueError('Some certificate files are missing')
        for name in sorted(DIRECTORIES):
            target = board / name
            if target.exists() or target.is_symlink():
                raise ValueError(
                    f'Destination appeared during unpacking: {target}')
        for name in sorted(DIRECTORIES):
            (temporary / '6x6' / name).rename(board / name)
    print(f'Unpacked and checked {len(seen)} sources in {destination}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('check', 'unpack'))
    parser.add_argument('--archive-dir', required=True)
    parser.add_argument('--source-root', type=Path, default=ROOT)
    args = parser.parse_args()
    if not args.archive_dir:
        parser.error('Set ARCHIVE_DIR=/path/to/archives')
    report, entries = load_inventory()
    paths = check_archives(Path(args.archive_dir).resolve(), report)
    if args.action == 'unpack':
        unpack_archives(paths, entries, args.source_root.resolve())


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, tarfile.TarError) as error:
        raise SystemExit(str(error))
