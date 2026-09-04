#!/usr/bin/env python3
"""Source regression guard; compiled public signatures and kernel audits remain required."""
from pathlib import Path
import re
from check_placeholders import code_only

root = Path(__file__).resolve().parents[1]
bridge = root / 'Section8/BernoulliSection8/Section3Integration.lean'
code = code_only(bridge.read_text())
match = re.search(r'^structure UpstreamInputs .*? where\n(.*?)(?=^\S)', code, re.M | re.S)
if not match:
    raise SystemExit('Missing explicit Section 8 upstream structure.')
fields = re.findall(r'^  (\w+)\s*:', match[1], re.M)
expected = ['comparisonConstant', 'proposition32', 'cook112', 'bbvRing', 'bbvGinibre']
if fields != expected:
    raise SystemExit(f'Unexpected upstream fields: {fields!r}')
for forbidden in ['BC12GinibreNegativeMomentTightness', 'GinibreProjectionIntegralFormula',
                  'GinibreCorrelationFormulas', 'known.negativeMoment',
                  'known.projection', 'known.correlation']:
    if forbidden in code:
        raise SystemExit(f'BC12 premise reintroduced: {forbidden}')
if 'Proposition38.proposition38_withoutBC12' not in code:
    raise SystemExit('The adapter must call the BC12-free Section 3 endpoint.')
if 'normalizedDense_hasGinibreLaw A' not in code:
    raise SystemExit('The Gaussian model law must be constructed internally.')
for name in ['Section3Integration', 'Section3GaussianLaw']:
    source = code_only((root / f'Section8/BernoulliSection8/{name}.lean').read_text())
    if re.search(r'\b(sorry|admit|unsafe|axiom|native_decide)\b', source):
        raise SystemExit(f'Forbidden proof escape in {name}.')
    if re.search(r'\bset_option\s+', source):
        raise SystemExit(f'Checking options must not be overridden in {name}.')
print('Section 8 public upstream boundary: Proposition 3.2, Cook 1.12, two BBV comparisons; no BC12 fields.')
