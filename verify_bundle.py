"""Check the integrity and local import completeness of this source bundle."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent
hashes = json.loads((root / 'SHA256SUMS.json').read_text(encoding='utf-8'))
bad = [name for name, digest in hashes.items()
       if not (root/name).is_file()
       or hashlib.sha256((root/name).read_bytes()).hexdigest() != digest]
if bad:
    raise SystemExit('Missing or changed files: ' + ', '.join(bad))
records = json.loads((root/'provenance/LOCAL_MODULES.json').read_text(encoding='utf-8'))
modules = {r['module'] for r in records}
for r in records:
    text = (root/r['path']).read_text(encoding='utf-8-sig')
    for match in re.finditer(r'^\s*import\s+([^\r\n]+)', text, re.M):
        for dep in match.group(1).split():
            if dep.startswith('Schubert.') and dep not in modules:
                raise SystemExit('Missing local dependency: ' + dep)
print(f'Verified {len(hashes)} distributed files and {len(modules)} local modules.')
