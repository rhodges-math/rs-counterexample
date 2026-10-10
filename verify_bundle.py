"""Check the integrity and import completeness of this source bundle.

* every file listed in SHA256SUMS.json is present with the recorded hash;
* every `RSCounterexample.*` and `Complexitylib.*` import of a local or vendored module is present;
* the Lake requirements in lakefile.toml match the revisions pinned in lake-manifest.json;
* every vendored complexitylib file matches its recorded upstream hash; for an edited file,
  reversing the recorded diff gives back the upstream file with the recorded upstream hash.
"""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent
hashes = json.loads((root / 'SHA256SUMS.json').read_text(encoding='utf-8'))
bad = [name for name, digest in hashes.items()
       if not (root / name).is_file()
       or hashlib.sha256((root / name).read_bytes()).hexdigest() != digest]
if bad:
    raise SystemExit('Missing or changed files: ' + ', '.join(bad))

IMPORT = re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+([^\r\n]+)', re.M)
records = json.loads((root / 'provenance/LOCAL_MODULES.json').read_text(encoding='utf-8'))
modules = {r['module']: r['path'] for r in records}
vendor = root / 'vendor/complexitylib'
upstream = json.loads((vendor / 'UPSTREAM_SOURCES.json').read_text(encoding='utf-8'))
vendored = {p.removesuffix('.lean').replace('/', '.'): 'vendor/complexitylib/' + p
            for p in upstream['files']}
known = set(modules) | set(vendored)
absent = [path for path in list(modules.values()) + list(vendored.values()) if not (root / path).is_file()]
if absent:
    raise SystemExit('Missing module sources: ' + ', '.join(absent))
for name, path in list(modules.items()) + list(vendored.items()):
    text = (root / path).read_text(encoding='utf-8-sig')
    for match in IMPORT.finditer(text):
        for dep in match.group(1).split():
            if dep.startswith('--'):
                break
            if dep.startswith(('RSCounterexample.', 'Complexitylib.')) and dep not in known:
                raise SystemExit(f'Missing dependency of {name}: {dep}')

# Lake requirements and the manifest
lakefile = (root / 'lakefile.toml').read_text(encoding='utf-8')
manifest = json.loads((root / 'lake-manifest.json').read_text(encoding='utf-8'))
pinned = {p['name']: p for p in manifest['packages'] if not p.get('inherited')}
requires = lakefile.split('[[require]]')[1:]
for block in requires:
    block = block.split('[[')[0]
    field = {k: v for k, v in re.findall(r'^(\w+)\s*=\s*"([^"]*)"', block, re.M)}
    p = pinned.get(field.get('name'))
    if p is None or p['url'] != field.get('git') or p['rev'] != field.get('rev'):
        raise SystemExit(f'lakefile.toml requirement {field.get("name")} does not match lake-manifest.json')
if len(requires) != len(pinned):
    raise SystemExit('lake-manifest.json pins packages that lakefile.toml does not require')


def reverse_diff(text, diff):
    """The text before a unified diff (a -> b), given the text after it."""
    nl = '\r\n' if '\r\n' in text else '\n'
    new = text.split(nl)
    lines = diff.split('\n')
    hunks, i = [], 0
    while i < len(lines) and not lines[i].startswith('@@'):
        i += 1
    while i < len(lines):
        m = re.match(r'^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@', lines[i])
        if not m:
            raise SystemExit('Malformed recorded diff')
        old_n, new_n = int(m.group(2) or 1), int(m.group(4) or 1)
        start = int(m.group(3)) - (1 if new_n else 0)
        old_side, new_side = [], []
        i += 1
        while old_n > 0 or new_n > 0:
            line = lines[i]
            tag, body = (line[:1], line[1:]) if line else (' ', '')
            if tag in ' -':
                old_side.append(body)
                old_n -= 1
            if tag in ' +':
                new_side.append(body)
                new_n -= 1
            i += 1
        hunks.append((start, old_side, new_side))
    for start, old_side, new_side in reversed(hunks):
        if new[start:start + len(new_side)] != new_side:
            raise SystemExit('Recorded diff does not apply')
        new[start:start + len(new_side)] = old_side
    return nl.join(new)


for path, meta in upstream['files'].items():
    data = (vendor / path).read_bytes()
    if meta.get('origin_kind') == 'edited':
        if hashlib.sha256(data).hexdigest() != meta['release_sha256']:
            raise SystemExit('Edited vendored source differs from its recorded hash: ' + path)
        data = reverse_diff(data.decode('utf-8'), meta['diff']).encode('utf-8')
    if hashlib.sha256(data).hexdigest() != meta['sha256']:
        raise SystemExit('Vendored source differs from its recorded upstream hash: ' + path)
license_meta = upstream.get('license_file')
if license_meta and hashlib.sha256((vendor / 'LICENSE').read_bytes()).hexdigest() != license_meta['sha256']:
    raise SystemExit('vendor/complexitylib/LICENSE differs from the upstream license file')
edited = sum(1 for m in upstream['files'].values() if m.get('origin_kind') == 'edited')
print(f'Verified {len(hashes)} distributed files, {len(modules)} local modules and '
      f'{len(vendored)} vendored complexitylib modules ({edited} edited, checked against upstream).')
