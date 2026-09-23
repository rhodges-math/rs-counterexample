"""Compile every local source in dependency order with bounded concurrency.

Requires Lean/Lake 4.33.0 and the pinned public Mathlib dependencies. Run
`lake exe cache get` first on a fresh machine to obtain public build caches.
The default recompiles all local sources. --resume reuses only successful
compilations recorded by this standalone builder with matching source hashes.
"""
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--jobs', type=int, default=3)
parser.add_argument('--resume', action='store_true')
args = parser.parse_args()
if args.jobs < 1:
    raise SystemExit('--jobs must be positive')
records = json.loads((ROOT / 'provenance/LOCAL_MODULES.json').read_text(encoding='utf-8'))
modules = {r['module']: r for r in records}
deps = {}
for name, r in modules.items():
    text = (ROOT / r['path']).read_text(encoding='utf-8-sig')
    imports = [d for m in re.finditer(r'^\s*import\s+([^\r\n]+)', text, re.M)
               for d in m.group(1).split() if d.startswith('Schubert.')]
    if any(d not in modules for d in imports):
        raise SystemExit('Local dependency missing from bundle: ' + name)
    deps[name] = set(imports)
logs = ROOT / '.lake/verification'
logs.mkdir(parents=True, exist_ok=True)
env = dict(os.environ)
env.pop('LEAN_PATH', None)
env.pop('LEAN_SRC_PATH', None)
env['LEAN_NUM_THREADS'] = '2'
started = time.monotonic()
results = {}
fingerprints = {}
pin = (ROOT/'lake-manifest.json').read_bytes() + (ROOT/'lean-toolchain').read_bytes()


def fingerprint(name):
    if name not in fingerprints:
        content = (ROOT/modules[name]['path']).read_bytes() + b'\0' + pin
        for dep in sorted(deps[name]):
            content += b'\0' + fingerprint(dep).encode()
        fingerprints[name] = hashlib.sha256(content).hexdigest()
    return fingerprints[name]


if args.resume and (logs/'results.json').is_file():
    for r in json.loads((logs/'results.json').read_text())['compiled']:
        name = r['module']
        if name not in modules:
            continue
        obj = ROOT/'.lake/build/lib/lean'/Path(modules[name]['path']).with_suffix('.olean')
        if (r['exit_code'] == 0 and r.get('source_key') == fingerprint(name)
                and obj.is_file() and obj.stat().st_size > 0):
            results[name] = r


def compile_module(name):
    before = time.monotonic()
    relative = modules[name]['path']
    output = Path('.lake/build/lib/lean') / Path(relative).with_suffix('.olean')
    (ROOT / output).parent.mkdir(parents=True, exist_ok=True)
    result = subprocess.run(['lake', 'env', 'lean', relative, '-o', str(output)], cwd=ROOT, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (logs / (name + '.log')).write_bytes(result.stdout)
    return dict(module=name, exit_code=result.returncode,
                source_key=fingerprint(name),
                seconds=round(time.monotonic()-before, 2))


remaining = set(modules) - set(results)
done = set(results)
if done:
    print(f'Resuming with {len(done)} already compiled and source-matched modules.', flush=True)
failed = False
with ThreadPoolExecutor(max_workers=args.jobs) as pool:
    active = {}
    while remaining or active:
        if not failed:
            ready = sorted((name for name in remaining if deps[name] <= done),
                           key=lambda name: (0 if '.Support.' in name or '.TypeA.' in name else 1, name))
            for name in ready[:args.jobs-len(active)]:
                remaining.remove(name)
                active[pool.submit(compile_module, name)] = name
        if not active:
            if failed:
                break
            raise RuntimeError('Cyclic local import graph')
        finished, _ = wait(active, return_when=FIRST_COMPLETED)
        for future in finished:
            name = active.pop(future)
            result = future.result()
            results[name] = result
            if result['exit_code']:
                failed = True
                print('FAILED: ' + name, flush=True)
                print((logs / (name+'.log')).read_text(encoding='utf-8', errors='replace')[-18000:], flush=True)
            else:
                done.add(name)
                if len(done) % 10 == 0 or len(done) == len(modules):
                    print(f'Built {len(done)}/{len(modules)} local modules ({name})', flush=True)
        (logs / 'results.json').write_text(json.dumps(dict(
            success=False, compiled=sorted(results.values(), key=lambda r:r['module'])), indent=2)+'\n')
        if failed and not active:
            break
(logs / 'results.json').write_text(json.dumps(dict(
    success=not failed and len(done)==len(modules),
    seconds=round(time.monotonic()-started, 2),
    compiled=sorted(results.values(), key=lambda r:r['module'])), indent=2)+'\n')
if failed:
    raise SystemExit(1)
print(f'All {len(done)} local modules built successfully.', flush=True)
