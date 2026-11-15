"""Check README pairs and detect edits since their last translation review.

These checks catch common mistakes, not differences in meaning. Use
--record-review only after reading both versions and checking their claims.
"""
from pathlib import Path
from urllib.parse import unquote, urlsplit
import argparse
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / 'distribution/docs-pairs.json'
FENCES = re.compile(r'^```([^\n]*)\n(.*?)^```[ \t]*$', re.M | re.S)
LINKS = re.compile(r'\]\(([^)]+)\)')
NUMBERS = re.compile(r'(?<![A-Za-z0-9])[-−]?\d+(?:[.,]\d+)*(?!\d|[.,]\d)')
JAPANESE = re.compile(r'[\u3040-\u30ff\u3400-\u9fff]')


def canonical(text):
    return text.replace('README-ja.md', 'README.md').replace('−', '-')


def technical_content(text):
    commands, examples = [], []
    for language, body in FENCES.findall(text):
        if language.strip() in ('coq', 'rocq'):
            examples.append(body.strip())
        commands.extend(line.strip() for line in body.splitlines()
                        if line.strip().startswith(('make ', 'python3 ', 'rocq ', 'git ')))
    prose = FENCES.sub('', text)
    return {
        'commands': commands,
        'Rocq examples': examples,
        'numbers': sorted({canonical(n).replace(',', '') for n in NUMBERS.findall(text)}),
        'code identifiers': sorted({canonical(n) for n in re.findall(r'`([^`\n]+)`', prose)}),
        'link targets': sorted({canonical(n) for n in LINKS.findall(text)}),
        'heading levels': re.findall(r'^(#+) ', text, re.M),
    }


def inspect_pair(english, japanese, files):
    errors = []
    texts = []
    for name in (english, japanese):
        path = ROOT / name
        if name not in files or not path.is_file():
            return [f'Missing README from the file list: {name}'], None
        text = path.read_text()
        texts.append(text)
        for link in LINKS.findall(text):
            parsed = urlsplit(link)
            if parsed.scheme or parsed.netloc:
                continue
            target = (path.parent / unquote(parsed.path)).resolve() if parsed.path else path
            if not target.is_relative_to(ROOT):
                errors.append(f'{name}: link leaves the repository: {link}')
                continue
            relative = str(target.relative_to(ROOT))
            if relative not in files and not any(n.startswith(relative.rstrip('/') + '/') for n in files):
                errors.append(f'{name}: link target is not in the source package: {link}')
            elif parsed.fragment:
                if not target.is_file() or f'id="{unquote(parsed.fragment)}"' not in target.read_text():
                    errors.append(f'{name}: missing explicit anchor: {link}')
    if JAPANESE.search(texts[0].replace('[日本語](README-ja.md)', '')):
        errors.append(f'{english}: Japanese text outside the language link')
    left, right = map(technical_content, texts)
    for key in left:
        if left[key] != right[key]:
            errors.append(f'{english}: different {key}\n  English: {left[key]}\n  Japanese: {right[key]}')
    hashes = {name: hashlib.sha256(text.encode()).hexdigest()
              for name, text in zip((english, japanese), texts)}
    return errors, {'english': english, 'japanese': japanese, 'sha256': hashes}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record-review', action='store_true',
                        help='record hashes after manually comparing both versions')
    args = parser.parse_args()
    files = set((ROOT / 'distribution/git-files.txt').read_text().splitlines())
    english = sorted(n for n in files if Path(n).name == 'README.md')
    japanese = {str(Path(n).with_name('README-ja.md')) for n in english}
    if japanese != {n for n in files if Path(n).name == 'README-ja.md'}:
        print('The file list must contain one Japanese README for each English README.', file=sys.stderr)
        return 1
    errors, pairs = [], []
    for name in english:
        problems, pair = inspect_pair(name, str(Path(name).with_name('README-ja.md')), files)
        errors.extend(problems)
        pairs.append(pair)
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    record = {'version': 1,
              'review_method': 'Both versions were read together. The automated checks do not establish semantic equivalence.',
              'pairs': pairs}
    if args.record_review:
        RECORD.write_text(json.dumps(record, indent=2) + '\n')
        print(f'Recorded the translation review for {len(pairs)} README pairs.')
    elif not RECORD.exists() or json.loads(RECORD.read_text()) != record:
        print('README files have changed since the last translation review. Read both versions, then run check_docs.py --record-review.', file=sys.stderr)
        return 1
    else:
        print(f'{len(pairs)} README pairs match the technical checks and recorded review hashes.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
