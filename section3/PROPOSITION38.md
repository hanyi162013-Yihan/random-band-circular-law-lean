# Proposition 3.8 — subgaussian full-block high-band anchor

Target: arXiv:2609.01295v1, **Proposition 3.8 (High-band log potential for
subgaussian full-block rings)**, equations (3.18)–(3.25), PDF pp. 16–17.
The checked `main.tex` SHA-256 is
`eb737f3e1541e7949cf71354fa7cd18a49f2d779d2c71108dda262339e8d98fe`.
The manuscript is read-only and is not copied into this project.

The source-facing endpoint is
`ShortRingAnchor.Proposition38.proposition38` in
[`Assembly.lean`](ShortRingAnchor/Proposition38/Assembly.lean).
Successful build/audit records, not the presence of theorem source text,
determine verification status; see the verification section below.

## Statement and realization

The fixed atom is **real**, centered, variance one, and subgaussian; it may
be discrete. Write `m=s+3`, with `s>0`, block width `W>0`, and `N=mW`.
All scalar entries in the three cyclic block diagonals are independent,
with coefficient `1/sqrt(3W)`. For `0<omega<1/9`,
`W ≥ N^(8/9+omega)` eventually, and `N,W → infinity`, the conclusion is
`(1/N) log |det(X-zI)| → U_circ(z)` in probability.

The shift `z` is any fixed complex number; constants may depend on it.
There is no radius-five restriction and no density assumption on the ring
atom. The `Atom` structure uses a finite subgaussian MGF parameter.

`AtomArray` uses the conventional masked-IID realization: an independent
`N×N` array, with unused entries outside the mask. These unused variables
do not occur in `fullBlockMatrix`. The finite-size atom model includes no
tail estimate, norm bound, connectivity certificate, or invertibility
assertion. Cross-size independence and independence from the dense
comparison ensemble are not required.

The dense reference is the same explicit normalized independent-atom
array used by section3. Its moment data and finite Ginibre formulas remain
visible, rather than asserting that an arbitrary reference is Ginibre.

## Exact external boundary

The two **newly authorized** literature inputs are centralized in
[`ExternalInputs.lean`](ShortRingAnchor/Proposition38/ExternalInputs.lean):

- `Proposition32Input`: repaired full-block LSV estimate from Proposition
  3.2, for `m ≥ m_*` and `W ≥ m`, with floor `(3W)^(-25m)` and
  failure at most `C/sqrt(3W)`.
- `Cook112Input`: Cook (2018), Theorem 1.12 / (1.21), specialized to
  zero-one masks and real atoms. The threshold parameter is `sigma_0=1/2`.
  Its event retains **both**
  `s_min(M) ≤ t/sqrt(N)` and `||M|| ≤ K sqrt(N)`.
  The spread parameter and `0<delta,nu<1` are explicit.

These are predicates supplied as theorem arguments. They are not axioms,
proved literature results, or assumed norm-free LSV bounds.

The **pre-existing section3 boundary is retained**:

- BBV canonical comparison for the actual ring and dense v3 models;
- the named BC12 negative-moment tightness input
  `BC12GinibreNegativeMomentTightness`, for some `p>0`;
- the finite Ginibre correlation and projection formulas in
  `ShortRingAnchor/BC12/KnownFormulas.lean`.

The full Ginibre logdet limit and its nonsingularity are derived from those
finite formulas; neither is an additional assumption of the endpoint.
This remains a conditional formalization, not a claim to have proved
Cook, Proposition 3.2, BBV, or all Ginibre integral formulas from scratch.

There is no Theorem 3.1 or geometric Brascamp–Lieb premise on this discrete
branch. The Section 8 `Section3SubgaussianHighBandInput`, which assumes
Proposition 3.8, is not imported or used.

## Internal proof

1. Verify the literal three-neighbour mask, all three distinct block
   positions, row/column variance sums, and exact v3 bandwidth `3W`.
2. Obtain all finite atom moments. Prove Cook spread by convergence of
   truncated first and second moments.
3. Prove broad connectivity with `delta=1/(2m²)`, `nu=1/(2m)`.
   Light blocks carry at most `nu |J|` selected columns. A nonempty
   proper heavy-block set gains at least one cyclic neighbour. This
   yields the required scalar-row expansion for every column set.
4. For bounded `m`, write the actual masked matrix as a sum of block
   compressions. Its norm is at most `m²` times the complete IID matrix
   norm. The copied, proved IID subgaussian tail gives exceptional
   probability `exp(-N)`. The rescaled shift costs at most
   `sqrt(3)|z|sqrt(N)`; a fixed Cook norm constant therefore suffices.
5. Apply Cook with `t=N^(-1/4)`, obtaining a normalized floor at least
   `N^(-2)`. For large `m`, use Proposition 3.2; the high-band
   inequality itself implies `m≤W`. A single vanishing budget covers
   both regimes, even when the block count oscillates between them.
6. Absorb `25 log(3W)` into a small power and reuse the existing scale
   `L=N^(1+3kappa)/W+2 log N`. Choose the slightly larger capped cutoff
   `a=min(1,N^(tau-beta/8))`, with `beta=8/9+omega`.
   It dominates the v3 counting threshold and satisfies `aL→0`.
7. Instantiate actual Hermitization counting, compact Stieltjes-to-CDF
   smoothing, logarithmic truncation, and exact row second moments.
   The existing high-probability assembly gives (3.19). Singular ring
   matrices are excluded only on an event whose probability tends to
   zero, never by an unjustified per-dimension a.s. invertibility premise.

The older direct-sum block norm proof is also retained and audited; the
final endpoint uses the shorter literal-matrix compression route.

## New source files

All files below are under `ShortRingAnchor/Proposition38/`:

- `Source.lean`, `AtomMoments.lean`, `Scales.lean`;
- `Profile.lean`, `Model.lean`, `V3Moments.lean`;
- `HeavyBlocks.lean`, `BroadConnectivity.lean`, `Spread.lean`;
- `BlockEmbedding.lean`, `BlockNorm.lean`;
- `MaskNorm.lean`, `MatrixNormTail.lean`, `SingularScaling.lean`;
- `ExternalInputs.lean`, `LeastValue.lean`, `Assembly.lean`, `Audit.lean`.

The copied norm proof consists of
`Vendor/SubgaussianNorm/Data.lean`,
`Vendor/SubgaussianNorm/OperatorNorm.lean`, and its provenance `README.md`.
No dependency caches or manuscript files are copied.

Every new theorem has a source-step comment. The audit enumerates all
new theorems and 22 reused norm-proof declarations, including the final
conditional endpoint.

## Verification

The complete local verification passed on **2026-09-03 at 03:44 UTC**:
250 Lean source files, the ordinary build, and 351 exact axiom reports
covering 340 distinct declarations. The Proposition 3.8 audit contributes
80 reports, including the final endpoint. No non-foundational axiom or
forbidden source construct was found. GitHub verification is a separate
run and is not implied by this local record.

Run using the already installed Lean 4.33.0 / pinned mathlib dependencies:

```sh
node scripts/serial-upstream-build.mjs ShortRingAnchor.Proposition38.Audit
node scripts/verify-project.mjs
```

The verifier runs the **ordinary `lake --no-cache build`**, a source hygiene
scan, and all three exact kernel audit lists. It rejects missing,
duplicate, unexpected, or non-foundational axiom reports. The allowed
axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

The complete verification records are
[`audit/verification/summary.json`](audit/verification/summary.json) and
[`audit/verification/Proposition38Audit.log`](audit/verification/Proposition38Audit.log).
A current certificate must explicitly contain
`ShortRingAnchor.Proposition38.proposition38`.
Historical section3 or earlier component-only logs do not certify it.

The optional `--proposition38-only` mode still runs the ordinary project
build, but audits only the new endpoint/components and writes to
`audit/proposition38-verification/`. It does not rerun the historical
Proposition 3.6 audit lists.

No new large files, cache downloads, cache deletion, or other-project
mutations are part of these commands. Local compilation is serialized.

## Remaining external work

Relative to the displayed input boundary, the target is the full
Proposition 3.8 deduction, not merely a norm or LSV component. Proving the
two newly authorized literature estimates themselves is out of scope.

A further reduction of the retained baseline would connect the already
proved nonoptimal Ginibre LSV/counting route directly to the concrete
reference array and discharge `hBC12Negative`. Deriving the finite
Ginibre eigenvalue correlation formulas from Gaussian entries is a
separate, substantially larger task.
