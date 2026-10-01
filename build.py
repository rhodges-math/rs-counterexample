"""Build the pinned Tau Ceti modules and the vendored complexitylib files with Lake, then compile
every local source in dependency order.

Requires the Lean toolchain of `lean-toolchain` (installed by elan) and the pinned public Lake
dependencies of `lake-manifest.json`. Run `lake exe cache get` first on a fresh machine to obtain
the public Mathlib build cache.

Phase 1 runs `lake build` on the Tau Ceti modules that the local sources import, and on the
`Complexitylib` library of this package (the vendored files in `vendor/complexitylib/`); Lake
compiles them from the pinned and vendored sources, reusing Mathlib objects from the cache.
Phase 2 compiles every local module with `lake env lean`.

The default recompiles all local sources. --resume reuses only successful compilations recorded
by this standalone builder with matching source fingerprints. --check only reports whether every
local module was compiled from the current sources and whether the Lake targets of phase 1 are up
to date.
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
parser.add_argument('--check', action='store_true',
                    help='only check that every module was compiled from the current sources')
args = parser.parse_args()
if args.jobs < 1:
    raise SystemExit('--jobs must be positive')

IMPORT = re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+([^\r\n]+)', re.M)


def header_imports(text):
    """The modules imported by a source header."""
    result = []
    for m in IMPORT.finditer(text):
        for dep in m.group(1).split():
            if dep.startswith('--'):
                break
            result.append(dep)
    return result


records = json.loads((ROOT / 'provenance/LOCAL_MODULES.json').read_text(encoding='utf-8'))
modules = {r['module']: r for r in records}
vendored = json.loads((ROOT / 'vendor/complexitylib/UPSTREAM_SOURCES.json').read_text(encoding='utf-8'))
vendored_modules = {p.removesuffix('.lean').replace('/', '.') for p in vendored['files']}
deps = {}
tauceti = set()
for name, r in modules.items():
    imports = header_imports((ROOT / r['path']).read_text(encoding='utf-8-sig'))
    tauceti.update(d for d in imports if d.startswith('TauCeti.'))
    local = [d for d in imports if d.startswith('Schubert.')]
    missing = [d for d in local if d not in modules]
    missing += [d for d in imports if d.startswith('Complexitylib.') and d not in vendored_modules]
    if missing:
        raise SystemExit('Dependency missing from bundle: ' + name + ' imports ' + ', '.join(missing))
    deps[name] = set(local)
lake_targets = sorted(tauceti) + ['Complexitylib']

logs = ROOT / '.lake/verification'
logs.mkdir(parents=True, exist_ok=True)
env = dict(os.environ)
env.pop('LEAN_PATH', None)
env.pop('LEAN_SRC_PATH', None)
env['LEAN_NUM_THREADS'] = '2'
started = time.monotonic()
results = {}
fingerprints = {}
pin = ((ROOT / 'lake-manifest.json').read_bytes() + (ROOT / 'lean-toolchain').read_bytes()
       + (ROOT / 'lakefile.toml').read_bytes()
       + (ROOT / 'vendor/complexitylib/UPSTREAM_SOURCES.json').read_bytes())


def output_of(name):
    return Path('.lake/build/lib/lean') / Path(modules[name]['path']).with_suffix('.olean')


def fingerprint(name):
    if name not in fingerprints:
        content = (ROOT / modules[name]['path']).read_bytes() + b'\0' + pin
        for dep in sorted(deps[name]):
            content += b'\0' + fingerprint(dep).encode()
        fingerprints[name] = hashlib.sha256(content).hexdigest()
    return fingerprints[name]


def lake_build(no_build=False):
    """`lake build` (or `lake build --no-build`) of the phase-1 targets."""
    before = time.monotonic()
    cmd = ['lake', 'build'] + (['--no-build'] if no_build else []) + lake_targets
    result = subprocess.run(cmd, cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (logs / ('_lake_check.log' if no_build else '_lake_build.log')).write_bytes(result.stdout)
    return dict(targets=lake_targets, tauceti_modules=len(tauceti),
                vendored_modules=len(vendored_modules), exit_code=result.returncode,
                seconds=round(time.monotonic() - before, 2))


if args.check:
    recorded = {}
    if (logs / 'results.json').is_file():
        recorded = {r['module']: r for r in json.loads((logs / 'results.json').read_text())['compiled']}
    stale = [n for n in modules
             if n not in recorded or recorded[n]['exit_code'] != 0
             or recorded[n].get('source_key') != fingerprint(n)
             or not (ROOT / output_of(n)).is_file()]
    print(f'{len(modules) - len(stale)}/{len(modules)} local modules compiled from the current sources.')
    lk = lake_build(no_build=True)
    print(f'Lake: {len(tauceti)} Tau Ceti modules and {len(vendored_modules)} vendored complexitylib '
          'modules ' + ('up to date.' if lk['exit_code'] == 0
                        else 'NOT up to date (see .lake/verification/_lake_check.log).'))
    raise SystemExit(1 if stale or lk['exit_code'] else 0)

mathlib = ROOT / '.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean'
if not mathlib.is_file():
    raise SystemExit('Mathlib build objects not found; run `lake exe cache get` first.')

if args.resume and (logs / 'results.json').is_file():
    for r in json.loads((logs / 'results.json').read_text())['compiled']:
        name = r['module']
        if name not in modules:
            continue
        obj = ROOT / output_of(name)
        if (r['exit_code'] == 0 and r.get('source_key') == fingerprint(name)
                and obj.is_file() and obj.stat().st_size > 0):
            results[name] = r

lake_result = None


def compile_module(name):
    before = time.monotonic()
    output = output_of(name)
    (ROOT / output).parent.mkdir(parents=True, exist_ok=True)
    cmd = ['lake', 'env', 'lean', modules[name]['path'], '-o', str(output)]
    result = subprocess.run(cmd, cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (logs / (name + '.log')).write_bytes(result.stdout)
    return dict(module=name, exit_code=result.returncode, source_key=fingerprint(name),
                seconds=round(time.monotonic() - before, 2))


def save(success=False, final=False):
    data = dict(success=success)
    if final:
        data['seconds'] = round(time.monotonic() - started, 2)
    data['lake'] = lake_result
    data['compiled'] = sorted(results.values(), key=lambda r: r['module'])
    (logs / 'results.json').write_text(json.dumps(data, indent=2) + '\n')


def run_local():
    remaining = set(modules) - set(results)
    done = set(results)
    if done:
        print(f'Resuming with {len(done)} already compiled and source-matched modules.', flush=True)
    failed = False
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        active = {}
        while remaining or active:
            if not failed:
                ready = sorted(name for name in remaining if deps[name] <= done)
                for name in ready[:args.jobs - len(active)]:
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
                    print((logs / (name + '.log')).read_text(encoding='utf-8', errors='replace')[-18000:],
                          flush=True)
                else:
                    done.add(name)
                    if len(done) % 25 == 0 or len(done) == len(modules):
                        print(f'Built {len(done)}/{len(modules)} local modules ({name})', flush=True)
            save()
            if failed and not active:
                break
    return not failed


print(f'Lake: building {len(tauceti)} Tau Ceti modules and the {len(vendored_modules)} vendored '
      'complexitylib modules...', flush=True)
lake_result = lake_build()
ok = lake_result['exit_code'] == 0
if not ok:
    print('FAILED: lake build; see .lake/verification/_lake_build.log', flush=True)
    print((logs / '_lake_build.log').read_text(encoding='utf-8', errors='replace')[-18000:], flush=True)
else:
    print(f'Lake: done ({lake_result["seconds"]} s).', flush=True)
    ok = run_local()
save(success=ok and len(results) == len(modules), final=True)
if not ok:
    raise SystemExit(1)
print(f'Tau Ceti ({len(tauceti)} imported modules), {len(vendored_modules)} vendored complexitylib '
      f'modules and {len(results)} local modules built successfully.', flush=True)
