# BernoulliSection10 — local bounded-density estimates

Lean 4 source for the real i.i.d. atom specialization of items **10.2--10.10**
in Section 10 of Yi Han's
[*The circular law for non-Hermitian random band matrices: optimal bandwidth,
periodic profile and discrete law*, arXiv:2609.01295v1](https://arxiv.org/abs/2609.01295v1).
The corresponding preprint pages are 69--74, with deferred proofs on pages
78--82. The formalization has explicit constants and constructs its coefficient,
nonvanishing, multiaffinity, integrability, and random-endpoint-invertibility
proofs internally. See [the item-by-item map](FORMALIZATION_MAP.md) for exact
statements and retained hypotheses.

This chapter is a separate Lean library in the repository's shared Lake
project. It imports `BernoulliLinearAlgebra` from `Section9/`; it does not
vendor mathlib or require any machine-specific path.

## Scope of this upload

- The nine proof chains use the arXiv numbering. The namespace, imports,
  theorem names, numbered helper constants, comments, and documentation use
  `BernoulliSection10` and items 10.2--10.10.
- The probability model is `IsBoundedDensityAtom μ L` with `μ : Measure ℝ`:
  independent copies of one centered, variance-one real bounded-density law.
  The target spaces and matrix coefficients may be complex; this does **not**
  make the random atom law complex.
- The broader planar-complex and directional conditional-density alternatives
  in arXiv v1 are **not formalized by this library**. Nor does its single-law
  API claim the independent, non-identically-distributed generality of 10.2
  and 10.3. The deterministic row-affinity result 10.4 has no atom-law restriction.
- Proposition 10.1, the high-band input at the start of this section,
  and the asymptotic arguments in Sections 10.4--10.6 are outside
  this upload. This is not a full formalization of the entire new Section 10.
- Proposition 10.7 uses fixed conditioned outside data `c ≠ 0` and invertible
  `R`; Proposition 10.10 uses unitary-frame coordinates for its decomposable
  wedges. These representations and their exact signatures are documented
  in the map, rather than concealed behind a completeness percentage.

## Toolchain

- Lean `v4.33.0`
- mathlib `v4.33.0`, pinned in the repository-root manifest

## Layout

- `BoundedDensity.lean`: the scalar atom law and one-dimensional density
  estimates;
- `AffineLog.lean`: Lemma 10.2;
- `MultiAffine.lean`: Corollary 10.3;
- `MultiAffineSecondMoment.lean`: recursive `L²` control used to close 10.5;
- `PhysicalRows.lean`: Lemma 10.4;
- `PhysicalModel.lean`, `PhysicalAffinity.lean`, `EfronStein.lean`,
  `HodgeIntegrability.lean`, and `RowConcentration.lean`: the concrete row
  model and completed caller-facing Lemma 10.5;
- `IntegratedHodge.lean`: deterministic Hodge identities for Lemma 10.6;
- `EndpointDeterminant.lean`: concrete normalized endpoint determinant
  deviation, almost-sure invertibility, and explicit negative-log estimate;
- `EndpointExteriorGrowth.lean`, `EndpointConditioningGrowth.lean`, and
  `EndpointConditioningScale.lean`: the simultaneous forward exterior family
  of the two actual endpoint blocks, its measure-preserving row-law model,
  Hodge--Jacobi inverse control, and the explicit certificate-free
  `C_L W log(eW)` exact-conditioning estimate;
- `HodgeEnvelope.lean`: concrete forward coefficient tensors, one-site
  interface determinant estimates, simultaneous forward/inverse Hodge
  envelope, its explicit first-moment bound, and finite second moment;
- `HodgeFamily.lean`: all exterior degrees packaged into one dependent
  finite product, so Corollary 10.3 controls their maximum with a single row
  cost; includes the improved one-site Hodge envelope, first moment, finite
  second moment, and almost-sure control;
- `TensorCornerBound.lean`, `HodgeFamilyGrowth.lean`: zero/one-hot corner
  bounds for canonical multiaffine tensors, concrete complementary-minor and
  Frobenius estimates, an explicit `C_z W log(eW)` tensor estimate, and the
  completed certificate-free `C_{L,z} s W log(eW)` one-site/interval
  first-moment bounds for Lemma 10.6;
- `ProductMarginal.lean`: measure-preserving restriction of finite i.i.d.
  products to an injectively selected coordinate family;
- `IntervalHodge.lean`: the concrete interval envelope, lossless site
  marginals, both the original sum-over-degrees and improved
  maximum-over-degrees envelopes, linear-in-length first-moment bounds,
  finite second moments, and almost-sure forward/inverse product control for
  Lemma 10.6;
- `HodgeIntegrability.lean`: recursive/flat row equivalence, internal nonzero
  witness, and concrete interval-log `L²` theorem;
- `PacketBoundary.lean`, `PacketComparisonGrowth.lean`,
  `PacketMultiaffine.lean`, and `PacketProbability.lean`: deterministic
  packet comparison, completed endpoint integration for Proposition 10.8,
  physical-row grouping, and completed Proposition 10.9;
- `MultiAffineGrowth.lean`, `RademacherTensor.lean`, and
  `SquarefreeRademacher.lean`: deterministic tensor evaluation bounds and
  the exact Rademacher lower bound for a complete squarefree coefficient
  vector;
- `PacketTensorScaling.lean`, `PacketTensorReverse.lean`: both directions of
  comparison between raw squarefree coefficients and the canonical tensor
  of normalized `3W` physical rows, with explicit `O(W log(eW))` logarithmic
  loss;
- `SeamComparison.lean`, `SeamProbability.lean`: deterministic
  Gram-volume/exterior-pressure comparison and the complete nine-block
  conditional expectation theorem of Proposition 10.7;
- `PacketFrame.lean`: checked frame, coefficient-limit, exact Gram-energy,
  and scalar-polynomial nonvanishing layer for Proposition 10.10;
- `PacketFrameProbability.lean`: physical-row affinity through the frame
  limit, concrete Corollary 10.3 evaluation, and the positive inverse-log
  reduction for the scalar 10.10 polynomial;
- `PacketReset.lean`: endpoint integration and the complete iterated packet
  expectation theorem of Proposition 10.10;
- `FORMALIZATION_MAP.md`: precise source-to-Lean map;
- `AUDIT.md`: reproducible build, placeholder, and axiom audit.

## Build

From the **repository root**, run:

```sh
lake build BernoulliSection10
lake env lean Section10/BernoulliSection10/AxiomAudit.lean
# All released chapters:
lake build
```

On a fresh machine, first follow the root README's dependency/cache setup.
The audit commands and their recorded status are in [AUDIT.md](AUDIT.md).
The public umbrella import is `import BernoulliSection10`.
