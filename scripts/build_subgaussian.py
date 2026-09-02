#!/usr/bin/env python3
"""Build only the selected extension and its exact imported project dependencies."""
from pathlib import Path
import argparse, subprocess, sys
root=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser()
p.add_argument('--target', action='append', default=[])
p.add_argument('--start-at')
p.add_argument('--dry-run', action='store_true')
a=p.parse_args()
targets=a.target or ['SubgaussianSection8']
r=subprocess.run([sys.executable,str(root/'scripts/check_subgaussian_scope.py'),*targets],cwd=root,text=True,capture_output=True,check=True)
modules=r.stdout.splitlines()[:-1]
if a.start_at and a.start_at not in modules: raise SystemExit('Start module not in import closure.')
start=modules.index(a.start_at) if a.start_at else 0
for i,mod in enumerate(modules[start:],start+1):
    print(f'[{i}/{len(modules)}] lake build +{mod}',flush=True)
    if not a.dry_run: subprocess.run(['lake','build','+'+mod],cwd=root,check=True)
print('Final scoped target: lake build '+ ' '.join(targets),flush=True)
if not a.dry_run: subprocess.run(['lake','build',*targets],cwd=root,check=True)
