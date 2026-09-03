# From radius five to each fixed compact interval

This note concerns the combined manuscript's Lemma 3.5, not the numbering
of arXiv:2410.16457v3 (where Corollary 3.5 is the counting result).

## The shortcut

Do not extrapolate an interval count on `[-5,5]` to `[-R,R]`. Return to the
v3 pointwise resolvent estimate (3.11), which is valid for every `Im eta > 0`
and imposes no bound on `Re eta`. All constants in the quantitative
comparison are independent of `Re eta`.

Choose `0 < c < epsilon/8` and set `v = B^(-1/8) N^c`. Then
`B v^8 = N^(8c)`. The explicit rate ledger in
`ExplicitStieltjesRate.lean`, with parameter `8c`, gives the common rate
`N^(-c/4)` for every point at that height, once `N` exceeds one threshold.
The threshold is chosen before the real spectral coordinate.

For the arbitrary fixed interval `[-R-2,R+2]`, take a one-dimensional mesh
with spacing `N^(-2)`. Since `1 <= B <= N`, the height is at least
`N^(-1/8)`, and hence the Stieltjes Lipschitz constant `v^(-2)` is at most
`N^(1/4) <= N`. Mesh interpolation therefore costs at most `2/N` when
comparing two empirical transforms. This is smaller than the chosen
comparison rate. There are at most `(2R+6)N²` points. Applying the existing
pointwise failure bound to both ensembles and taking a finite union costs
at most `2(2R+6)N^(-8)`.

Comparing both empirical transforms to the same free transform at the grid
points, and then interpolating the two empirical transforms directly,
avoids needing a separate continuity assumption on the free transform.

## What the argument does not say

- It does not obtain a rate from a different existentially chosen exponent
  at each grid point. The common exponent is exposed in Lean explicitly.
- It does not use only the old BBV instances at the old grid points.
  It invokes the same BBV Theorem 2.8 schema at the new points; those
  comparisons remain explicit parameters, not hidden axioms.
- It does not infer polynomially small spectral tails outside radius 5
  from a second-moment bound. That inference would not be valid.
- It is a fixed-`R` statement. The final logarithmic truncation argument
  first sends `N` to infinity and then `R` to infinity. Arbitrarily growing
  `R_N` is not claimed.

## The smoothing step

The finite-spectrum smoothing proof is now in `PoissonSmoothingKernel`,
`PoissonSmoothingFinite`, `LocalPoissonSmoothing`, `PoissonSmoothingCDF`,
and `PoissonSmoothingProbability`. It uses `Delta=sqrt(v)` and proves
the exact symmetric-spectrum/squared-CDF identity, including zero values.
Endpoint-window mass is itself bounded by a slightly enlarged Poisson
integral, directly controlled by the empirical imaginary Stieltjes bound.
The kernel tail costs `2v/(pi Delta)`. No free-law density or spectral-tail
interface is needed. The final bound is

```text
local squared-CDF distance <= ((2R+10)E + (8C+8)sqrt(v))/pi.
```

Here `E` is the compact comparison error and `C` bounds the reference
imaginary part. The precise small-height premise is `3sqrt(v)<=1`.

## Actual-matrix integration

`matrix_stieltjesTrace_eq_symmetric_singularValues` identifies the actual
Hermitization resolvent trace with the symmetric singular-value transform.
Its proof uses the right singular-vector basis and the resolvent block
equations, including when the original matrix is singular.

The model-level constructor `lemma35LocalBulkComparisonInput_of_v3_models`
uses the simpler common height `v=N^(-e/16)`, where `e=min(epsilon,1)` and
both bandwidths are eventually at least `N^epsilon`. Then `Bv^8 >= N^(e/2)`
and the common comparison exponent is `zeta=e/64`. The smoothing error
`sqrt(v)` is at most `N^(-zeta)`.

On the grid for `[-R-1,R+1]`, both actual matrix transforms are close to
the canonical free transform. The latter has norm below one, as proved
in the vendored v3 development. The same event therefore gives comparison
error `4N^(-zeta)` and reference imaginary part at most `3`, without a
separate density or free-transform continuity input. The final CDF error
is at most `((8R+72)/pi)N^(-zeta)` eventually, and the event fails with
probability at most `2(2R+4)N^(-8)`.

The reusable generic assembly retains its comparison parameter. The more
concrete `proposition36_cyclicShortRing_of_atom_copies_and_bbv` now fills it
internally: `CyclicV3Model` and `DenseV3Model` construct the actual models
from the supplied independent atom arrays, including off-band zeros.
`ConcreteBulkScales` proves that `W >= M^beta` gives bandwidth eventually
at least `M^(beta/2)`, absorbing the fixed profile constant. Thus
`lemma35LocalBulkComparisonInput_cyclic_dense` uses the common exponent
`beta/128` for every fixed radius. No already-assumed CDF, concentration,
or model-validity conclusion occurs in this adapter; the named BBV
comparison instances remain explicit.
