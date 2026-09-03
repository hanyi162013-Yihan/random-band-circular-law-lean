# Hermitization counting and the published Theorem 3.1

## Verification status

The planar Proposition 3.6 endpoint, including counting and the copied
Theorem 3.1, has passed `lake --no-cache build`. This includes the cyclic
law adapter, numerical reindexing, and HS cutoff removal. The real-density
endpoint is still being checked. Full-build and final axiom-audit results
will be recorded here only after those commands succeed.

## Mathematical reconstruction

The counting proof uses the exact cutoff

```text
a_M = B_M^(-1/8) M^tau,     B_M a_M^8 = M^(8 tau).
```

The v3 pointwise comparison and McDiarmid estimate are applied on a finite
vertical grid with spacing `M^-2`. Its complement has probability at most
`4 M^-8` in all sufficiently large dimensions. The canonical free Stieltjes
transform has norm below one; grid interpolation gives norm at most three.
The Poisson kernel then gives, on one common event, for every `r >= a_M`,

```text
# {Hermitization eigenvalues in [-r,r]} <= 6 M (2r).
```

For `r > 1` the dimension bound suffices. This is the actual shifted matrix,
not a separately assumed spectral family. BBV remains the named external
comparison. The resulting Proposition 3.6 endpoint has no `hCount`, no
externally supplied counting event, and no externally chosen counting constant.

The Theorem 3.1 proof is copied from the user's high-band project at commit
`d20607307ee57f31d77397b34bdb2910bef30936`, not introduced as a hypothesis.
The new adapters establish:

1. The cyclic profile satisfies the source lower/upper variance bounds with
   constants `c0/3` and `C0`, and has row normalization one.
2. Independence and matching entry laws identify the full matrix law with
   the source product model, including deterministic off-band zeros.
3. For the real branch, an essentially bounded density has an everywhere
   bounded measurable representative with the same law. An almost surely
   real atom has the law of its real-part embedding.
4. The numerical certificates hold along arbitrary `M k -> infinity`,
   without requiring the dimensions to be injective or strictly increasing.
5. The two definitions of the least singular value agree. With `t=M^-2`,
   the source threshold is exactly `exp(-sourceHardEdgeScale)`.
6. The strict lower-tail event with HS cutoff is Borel and transports under
   equality of matrix laws. The source's non-strict estimate bounds it.
7. `HS(X)^2/M` equals the empirical singular-value second moment. Its
   expectation is one. Markov and the proved two-limit argument remove
   the HS cutoff without adding a concentration premise.

All shifts `z : Complex` are allowed; bounds may depend on the fixed shift.
Neither a radius-five condition nor a bound `|z| <= 2.5` is introduced.

## Endpoint boundary

The intended most concrete planar endpoint is
`proposition36_cyclicShortRing_planar_from_published_theorem31`.
The real/complex-alternative endpoint is
`proposition36_cyclicShortRing_from_published_theorem31`.
Both construct the former `hCount` and `hLSV` inputs internally.

The remaining literature premises are explicit theorem parameters:

- BBV's canonical Gaussian-to-free comparison. For the ring it is supplied
  on the upper half-plane, covering both the vertical counting grid and
  horizontal smoothing lines; for the dense process only the latter are needed.
- The BC12 shifted negative-moment tightness input. The previously proved
  polynomial-least-value/mesoscopic-count reduction remains available.
- The BC12 full logdet convergence input. The previously proved finite-formula
  theorem can supply it; Gaussian moment/correlation formulas are not inferred
  merely from normalized independent entries.
- Only for the real branch: `RealFiniteGeometricBrascampLieb`, exactly the
  premise present in the copied upstream proof. The planar endpoint does
  not require it.

There are no new least-value, joint-law, singular-vector-measurability,
HS-concentration, local CDF, or Hermitization-count hypotheses.

## Remaining work after this integration

The next short route for the BC12 negative-moment boundary is to identify
the actual normalized shifted Gaussian law with the already available
polynomial least-value estimate, and combine it with the dense specialization
of the counting constructor above. The deterministic summation and
high-probability-to-tightness steps are already proved in
`BC12/NegativeMomentCounting.lean`; no new Stieltjes smoothing is required.
The finite-formula logdet route is separate and remains explicitly conditional
on its exact Ginibre formulas. Neither BBV nor the real geometric BL theorem
is claimed to be proved by this integration.

## New source files

All paths in this table are under `ShortRingAnchor/`.

| File | Role |
| --- | --- |
| `VerticalStieltjesCounting.lean` | Vertical grid, resolvent interpolation, finite counting and probability bound |
| `HermitizationCountingFromV3.lean` | Exact cutoff arithmetic and actual-model all-cutoff event |
| `Proposition36Counting.lean` | Proposition 3.6 with counting input discharged |
| `CyclicHighBandProfile.lean` | Cyclic support and source variance-profile bounds |
| `UniformSequenceSelection.lean` | Uniformization over all admissible width sequences |
| `HighBandUniformNumerics.lean` | Reindex the copied numerical certificates |
| `CyclicPlanarHighBandModel.lean` | Planar product model and equality of matrix laws |
| `HighBandLSVBridge.lean` | Exact scalar, measurable-event, and second-moment identities |
| `HighBandLSVProbability.lean` | Apply the copied planar theorem and remove the HS cutoff |
| `Theorem31CyclicPlanar.lean` | Actual cyclic least-value conclusion, planar branch |
| `BoundedDensityRepresentative.lean` | Everywhere bounded measurable density representative |
| `CyclicRealHighBandModel.lean` | Real product model and equality of matrix laws |
| `HighBandRealLSVProbability.lean` | Apply the copied real theorem, retaining its BL premise |
| `Theorem31CyclicReal.lean` | Actual cyclic least-value conclusion, real/alternative branches |
| `Proposition36Planar.lean` | Planar Proposition 3.6 with counting and Theorem 3.1 connected |
| `Proposition36PublishedTheorem31.lean` | Real/complex-alternative Proposition 3.6 endpoint |
| `HighBandIntegrationAudit.lean` | Audit all new declarations and eight upstream endpoints |

Three additional copied files are `Vendor/ModelLawTransport.lean`,
`Vendor/ModelStatements.lean`, and `Vendor/PaperModelTheorem.lean`.
Their provenance and all compatibility edits are listed in [UPSTREAM.md](UPSTREAM.md).
The new helpers are `scripts/serial-upstream-build.mjs` and
`scripts/audit-lean-sources.mjs`. The latter scans all project/vendored Lean
sources outside hidden dependency directories, excluding comments and strings;
it is a hygiene check, not a substitute for kernel verification.

No manuscript or original proof project is changed. No Lake directory is
copied or removed; all dependencies are built from existing local sources.
Failed development logs are retained for diagnostics, not counted as
verification certificates.
