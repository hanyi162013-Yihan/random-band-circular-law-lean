# Complex Section 10: verification status (work in progress)

This is not a completion certificate. The final real/complex Section 3
source connections are still pending. BBV, BC12, and (for the real branch
only) geometric Brascamp--Lieb are explicitly accepted literature inputs.

An upstream density-record definition error was confirmed by cloud-printed
types in run `33715585984`: its finiteness field accidentally quantified over
every bound instead of using infinity. The minimal correction and the new
construction regression require a fresh dependency rebuild. See
[DENSITY_SCHEMA_CORRECTION.md](DENSITY_SCHEMA_CORRECTION.md).

## Reproducible front-end checks

Use the repository's pinned Lean 4.33.0 and mathlib revision:

```sh
lake exe cache get
lake build BernoulliSection10Complex.Front
python3 scripts/check_placeholders.py --path Section10/BernoulliSection10Complex
python3 scripts/check_axioms.py \
  --audit-file Section10/BernoulliSection10Complex/AnalyticAxiomAudit.lean \
  --audit-file Section10/BernoulliSection10Complex/FrontAxiomAudit.lean
lake env lean Section10/BernoulliSection10Complex/FrontSignatureAudit.lean
```

The user requested that the final source integration be compiled in the
cloud. No local build of that final integration has been run.

## Recorded checks

- At commit `56c2022`, the **complete Front target passed** in
  [run 33710177008](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33710177008),
  with the final `lake build BernoulliSection10Complex.Front` check successful.
  Its separate analytic/front axiom audits passed (23 reports, only
  `propext`, `Classical.choice`, `Quot.sound`), and the public complex
  signature regression checks passed. The overall run failed in three
  conditional-closure modules due to namespace/name resolution; corrections
  were committed in `1915df2` and await a subsequent cloud check.
- The latest root configuration now selects the published `section3/`
  source. Actual IID model, planar LSV, density representative and real LSV
  adapters are written; their first cloud integration check is running.
  No local integration compilation has been performed.
- In [run 33713026658](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33713026658)
  at `0e8a721`, the front-end passed again with the published `section3/`
  dependency, and `BernoulliSection10.HighBandClosure` compiled. The new
  Gaussian moment helper and density representative reported elaboration
  errors; the complex circular-law assembly reported ambiguous real/complex
  names. Fixes are on the working branch, pending cloud verification.
  This does not yet verify either source-connected final endpoint.
- At `b505051`, the cloud run
  [33714301600](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33714301600)
  compiled `GaussianReferenceFacts` in 1.8 seconds. Explicit real-to-complex
  intermediate types removed the previous elaboration timeout. This verifies
  the Gaussian moments and density domination, not yet the full source model.
- `ee286a8` adds source-connected real and planar circular-law endpoints,
  with separately named BBV/BC12 inputs and real-only geometric
  Brascamp--Lieb. These new proofs are **written, not yet build-verified**.
  The cloud workflow now builds and audits them after their prerequisites.

- The planar affine-log core and its eight kernel-axiom reports passed
  locally; only `propext`, `Classical.choice`, and `Quot.sound` occurred.
- The first cloud front-end build ran at commit
  `ede9654632350f6cc6323ee1929b96e0f5b084a9`:
  [run 33708332599](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33708332599).
  It failed in three modules, not in three mathematical propositions:
  `MultiAffineGrowth`, `EndpointExteriorGrowth`, and
  `PhysicalMatrixEntries`. Dependent modules were explicitly skipped.
- That run did compile the actual complex packet evaluation,
  nonvanishing, packet-law transports, interval concatenation, the
  Hodge envelopes and bounds, resampling/concentration, reset-sandwich
  integrability, and the norm-square atom law-of-large-numbers module.
- The three identified source issues were corrected in `48b7f07`.
  All three corrections passed in
  [run 33709210633](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33709210633).
  That run also checked endpoint exterior/conditioning growth and scale,
  packet comparison growth, and the actual complex matrix energy limit.
  Its remaining failed module was `PacketTensorScaling`, which lacked an
  explicit import of the complex packet/frame definitions and therefore
  resolved some names to the old real branch. The import is now corrected;
  the next cloud run must check it and the 17 skipped dependent modules.
- The source-token scan passed on all 77 then-present complex Lean files;
  this scan is not a substitute for compilation.
- [Run 33709639103](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33709639103)
  checked the corrected tensor scaling, packet reset, physical reset,
  conditional reset, mean stitching, stitched pressure and remainder L1.
  The remaining failure was a real absolute-value expression on a complex
  coordinate in the deterministic reverse tensor comparison; it is now
  expressed with the complex norm. Ten dependent modules were skipped.
- Both density branches now have an internal `HighBandClosure` composition
  lemma. Its explicit high-band premise is pending construction from
  Section 3; it is not being counted as the final source connection.

## Outstanding delivery work

1. Recheck the verified complete front-end against the updated Section 3
   dependency tree as part of the final complete build.
2. Check the complex high-band and circular-law assembly. Its historical
   `Section3Inputs` parameter is only an internal staging interface.
3. Cloud-verify the written connections to published Section 3 proofs for both density branches,
   leaving only the explicitly accepted literature boundary and model
   hypotheses; perform this integration build in cloud CI.
4. Refresh full source scans, actual public theorem signatures and
   kernel-axiom reports, update the detailed map, then publish the verified
   result in the repository's `Section10/` main-branch location.

The WIP branch is `codex/section10-complex-density`; no completion merge
into main has been made.
