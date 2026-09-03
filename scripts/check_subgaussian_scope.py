#!/usr/bin/env python3
"""Read the selected new-project import closure; never build the dependency defaults."""
from pathlib import Path
import argparse, re, tomllib
root = Path(__file__).resolve().parents[1]
config = tomllib.loads((root / 'lakefile.toml').read_text())
roots = {lib['name']: root / lib.get('srcDir', '') for lib in config['lean_lib']}
p = argparse.ArgumentParser()
p.add_argument('targets', nargs='*', default=['SubgaussianSection8'])
a = p.parse_args()
seen = set()
visiting = set()
ordered = []
def visit(mod):
    if mod in seen or mod.split('.')[0] not in roots: return
    if mod in visiting: raise SystemExit('Import cycle: ' + mod)
    if mod.startswith('CircularLawSection4'):
        raise SystemExit('Forbidden Section4 dependency: ' + mod)
    path = roots[mod.split('.')[0]] / (mod.replace('.', '/') + '.lean')
    if not path.is_file(): raise SystemExit('Missing source: ' + str(path))
    visiting.add(mod)
    # All project import headers use ordinary top-level import lines.
    for dep in re.findall(r'^import\s+([\w.]+)', path.read_text(), re.M): visit(dep)
    visiting.remove(mod)
    seen.add(mod)
    ordered.append(mod)
for t in a.targets: visit(t)
for mod in ordered: print(mod)
print(f'{len(seen)} project modules; Section4: 0')
