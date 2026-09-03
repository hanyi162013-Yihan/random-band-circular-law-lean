# Reuse audit: planar-complex Section 10

Baseline repository commit: `42c26b6` (Lean 4.33.0).
The stable real Section 10 files are not edited.

The requested final integration also applies to the real-density endpoint.
It is deferred until the complex front-end is verified; the source-connected
integration is to be compiled and audited in cloud CI only.

The user explicitly confirmed that BBV and BC12 remain dependencies of the
final result. This is a conditional literature-based formalization, not a
from-first-principles proof of those upstream results. The final source
connection must expose this boundary in theorem signatures and reports.
The user also explicitly accepted the geometric Brascamp--Lieb inequality
as a classical external input for the real-density branch only.

## Imported proved facts

| Source | Reused result | Mathematical role |
|---|---|---|
| `Section4/CircularLawSection4/ProductSmallBall.lean` | `complexBallBound_of_le_smul_volume` | The joint complex atom law has disk mass at most `π L r²`. This is a planar result, not a result about independent real/imaginary components. |
| `Section10/BernoulliSection10/AffineLog.lean` | `lintegral_sq_le_of_exponential_tail`, `lintegral_sq_add_const_le`, `lintegral_lintegral_sq_sub_le` | Scalar-independent tail integration and independent-copy bounds; reused without duplicating their proofs. |
| `Section10/BernoulliSection10/ProductMarginal.lean` | `measurePreserving_pi_restrict_embedding` | Finite IID coordinate restriction; already generic in the atom space. |
| `Section10/BernoulliSection10/PhysicalRows.lean` | Physical block types and complex determinant/exterior row affinity | Already a genuinely complex deterministic theorem. |
| `Section9/BernoulliLinearAlgebra/` | Cleared transfer and exterior algebra | Common deterministic foundation. |

Further exact reuse identified during integration: the squarefree
Rademacher coefficient bound already has an arbitrary complex polynomial as
its input, and the variance-profile geometry theorems only concern real
deterministic variance weights, not real atom laws. Those statements do not
need complex-specific replacements. The positive-size matrix reindexing and
the final spectral replacement library are likewise independent of atom type.

## Relevant results found in other projects

- The Section 4 project (`2026-08-31/nu/outputs/CircularLawSection4`)
  contains complex operator-affine logarithmic second moments and complex
  multiaffine small-ball estimates. These proofs are already published under
  `Section4/` in the baseline repository. They are not copied into a second
  independently maintained vendor tree.
- The finite-moment short-ring project
  (`2026-09-01/finite-moment-short-ring-anchor`) has
  `Proposition36Planar.lean` and `Theorem31CyclicPlanar.lean`, now published
  in the independent `section3/` project. Their signatures still state the
  appropriate BBV/BC12 inputs. Integration must respect the separate Lake
  project and the overlapping `ShortRingAnchor` namespaces.
  This was rechecked against GitHub main at `42c26b6`:
  `proposition36_cyclicShortRing_planar_from_published_theorem31` explicitly
  takes `bbvA`, `bbvG`, `hBC12Negative`, and `hBC12Full`.
  The real endpoint additionally retains `RealFiniteGeometricBrascampLieb`.
  These are genuine upstream theorem hypotheses, not failures of the kernel
  axiom audit and not automatically discharged by importing the file.
- The high-band LSV project (`2026-09-01/high-band-lsv-2609-01295`)
  contains planar tensorization, small-ball, and model theorems. These are
  also present in the Section 3 vendor graph.
- The Sections 5–6 project has complex atom logarithmic and transfer
  controls. Its taper/cell statements are not automatically the full-block
  Section 10 coefficient-scale estimate.

No complete planar-complex Section 10 endpoint was found in these inspected
projects. In particular, a highest-monomial estimate is not substituted for
the full coefficient-tensor estimate of Corollary 10.3.

## New proof obligations

The complex sibling library uses the original joint law on `ℂ`, complex
affine interpolation, and norm-square second moments. It derives a linear
small-ball envelope from the imported planar disk theorem and the probability
bound. Its internal condition `1 ≤ L` is constructed from any original bound
by replacing it with `max 1 L`; public planar analytic statements have no such
extra condition. The physical packet and asymptotic integration remain subject
to fresh builds and audits listed in `COMPLEX_FORMALIZATION_MAP.md`.
