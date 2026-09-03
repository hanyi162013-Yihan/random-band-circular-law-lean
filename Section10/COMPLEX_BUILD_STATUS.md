# Complex Section 10: verification status (work in progress)

This is not a completion certificate. The final real/complex Section 3
source connections are still pending. BBV, BC12, and (for the real branch
only) geometric Brascamp--Lieb are explicitly accepted literature inputs.

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

1. Finish the complete complex front-end build, axiom audit, and signature
   checks. A partial CI run is not counted as complete.
2. Check the complex high-band and circular-law assembly. Its current
   `Section3Inputs` parameter is only an internal staging interface.
3. Connect actual published Section 3 proofs for both density branches,
   leaving only the explicitly accepted literature boundary and model
   hypotheses; perform this integration build in cloud CI.
4. Refresh full source scans, actual public theorem signatures and
   kernel-axiom reports, update the detailed map, then publish the verified
   result in the repository's `Section10/` main-branch location.

The WIP branch is `codex/section10-complex-density`; no completion merge
into main has been made.
