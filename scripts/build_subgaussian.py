#!/usr/bin/env python3
"""Build the extension serially, retaining independent progress after errors."""
from pathlib import Path
import argparse, re, subprocess, sys, tomllib
root=Path(__file__).resolve().parents[1]
config=tomllib.loads((root/'lakefile.toml').read_text())
roots={lib['name']:root/lib.get('srcDir','') for lib in config['lean_lib']}
roots['Ginibre']=root/'.lake/packages/GinibreCorrelationIdentities'
p=argparse.ArgumentParser()
p.add_argument('--target', action='append', default=[])
p.add_argument('--start-at')
p.add_argument('--module', action='append', default=[],
    help='Warm-cache serial entry point; Lake still checks its imports and the final targets.')
p.add_argument('--dry-run', action='store_true')
a=p.parse_args()
targets=a.target or ['SubgaussianSection8']
r=subprocess.run([sys.executable,str(root/'scripts/check_subgaussian_scope.py'),*targets],cwd=root,text=True,capture_output=True,check=True)
modules=r.stdout.splitlines()[:-1]
if a.start_at and a.start_at not in modules: raise SystemExit('Start module not in import closure.')
if a.module and a.start_at: raise SystemExit('Use either --module or --start-at.')
if set(a.module) - set(modules): raise SystemExit('Requested module not in import closure.')
start=modules.index(a.start_at) if a.start_at else 0
# A restored baseline is traversed by Lake itself. Do not invoke Lake once
# per unchanged baseline module. Cold builds still use the full serial list.
selected=[m for m in modules[start:] if not a.start_at or m.startswith('SubgaussianSection8')]
if a.module: selected=[m for m in modules if m in set(a.module)]
failed=set();blocked=set()
for i,mod in enumerate(selected,1):
    source=roots[mod.split('.')[0]]/(mod.replace('.','/')+'.lean')
    deps=set(re.findall(r'^import\s+([\w.]+)',source.read_text(),re.M)) if source.is_file() else set()
    if deps & (failed|blocked):
        blocked.add(mod);print(f'[{i}/{len(selected)}] Deferred {mod}: failed dependency',flush=True);continue
    print(f'[{i}/{len(selected)}] lake build +{mod}',flush=True)
    # Keep errors visible without replaying all cached linter warnings for every import.
    if not a.dry_run and subprocess.run(['lake','--log-level','error','build','+'+mod],cwd=root).returncode:
        failed.add(mod)
if failed:
    print('Failed modules: '+', '.join(sorted(failed)),flush=True)
    raise SystemExit(1)
print('Final scoped target: lake build '+ ' '.join(targets),flush=True)
if not a.dry_run: subprocess.run(['lake','build',*targets],cwd=root,check=True)
