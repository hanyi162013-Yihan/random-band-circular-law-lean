# Section 6 continuation checkpoint — 2026-09-02

## Verified fourteen-module checkpoint

Commit: `0dce34d3de176151db96ee1da21bb18b57a7dfb6`.
[Dedicated GitHub run 33667008094](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33667008094),
job `100371135774`: **success** on 2026-09-02.

- All 14 Section 6 modules and the combined entry point compiled in the actual
  publication layout. Lean reported 3244 build jobs, including dependencies.
- New Section 6 modules treat warnings as errors.
- The transitive audit passed: 215 declarations, 173 theorem declarations
  (including generated declarations). Only `propext`, `Classical.choice`,
  and `Quot.sound` are allowed.
- All 20 strict regression examples passed, including even-size offset ties,
  the one-dimensional core, empty tails, Gaussian normalization, actual matrix
  independence, and zero-length quadrature.
- The repository placeholder-proof scanner passed.

This checkpoint now includes the literal Gaussian/profile model, finite
normalization and energy identities, product independence, tail rotations,
centered mesh identification, and actual BV quadrature estimates. It does not
yet prove the compact-core analytic inputs or the noncompact circular law.

The next eight modules and their added regressions are pending a separate
integrated check. They are not covered by the successful run above.
These extend the mass-limit/comparability work with literal limiting mass
identities and the expected Gaussian tail Jensen inequality. The latter
reuses Section 5 / replacement's a.e.-parameter nonvanishing and local L²
estimates instead of postulating logarithmic integrability. The generic
`InvariantPhaseAverage` module has independently passed a strict local check.

No large local dependency download was performed; the cloud job uses its own
runner and cache. Local checks reused existing pinned dependencies.

## Earlier verified checkpoint

This record concerns the five new modules in `CircularLawSection6`, not all of
the manuscript's Section 6. See `README.md` for the remaining mathematical inputs.

Local checks against the existing pinned Lean 4.33.0/mathlib installation:

- All five modules elaborated successfully with `warningAsError=true`.
- Their combined `CircularLawSection6.lean` entry point passed the same check.
- The transitive axiom audit passed: 21 declarations, 19 theorems (including
  generated declarations). Only `propext`, `Classical.choice`, and `Quot.sound`
  are allowed. `verification/axioms.txt` now records the newer checkpoint.
- All seven regression examples passed with warnings treated as errors.
- The repository source-token scanner passed on all 538 current Lean files.
- The child manifest uses relative paths and reuses `../.lake/packages`.

These were targeted checks reusing local dependencies and compiled inputs, not
a fresh local rebuild of the whole Section 5 dependency tree. No large local
download was performed. The separate **Section 6 verification** GitHub workflow
builds this publication layout and repeats the axiom/regression checks; its
actual run conclusion must be consulted before claiming remote CI success.

The new lemmas use honest ordinary hypotheses for their external finite-size
and limiting inputs. Passing an axiom audit does not prove those hypotheses or
complete the Gaussian-profile circular-law theorem.
