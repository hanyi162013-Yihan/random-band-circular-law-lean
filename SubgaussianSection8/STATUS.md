# General subgaussian extension and Section 3 integration

The baseline logarithmic-bandwidth proof is verified at source commit `d29fd6f0cefcaa4ec3afe09f14c54df3e16842d4` by [GitHub Actions run 33688229894](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33688229894/job/100440674643).

The extension belongs to the root Lake project of `random-band-circular-law-lean`. [PR #1](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/pull/1) integrates it and the verified Rademacher baseline `24a1e37550a7e471bec4bb668ce4bde92fae3cbb` into `main`. The development branch is `codex/section8-subgaussian`, in a separate local checkout.

## Current integration

The public final theorems now take `Section3UpstreamInputs`, and `section3_input` constructs the former high-band interface using `ShortRingAnchor.Proposition38.proposition38`. The concrete Gaussian reference moments, IID coordinates and matrix/probability transports are proved in the new bridge modules. [Integration proof map and cloud gate](../Section8/SECTION3_INTEGRATION.md). The current integration is not certified by the earlier baseline run.

## Scope

The fixed real atom law is a probability measure with mean zero, second moment one, and a finite subgaussian MGF parameter. No bounded-support, symmetry, or density hypothesis is imposed. Cook and Nguyen remain explicit inputs with their quantitative ranges covering the atom parameter. The concrete Section 3.8 proof retains its named Proposition 3.2, Cook 1.12, canonical BBV and BC12/finite Ginibre formula inputs.

The conclusion uses the exact cyclic-band dimension `N=(s+3)W`, physical normalization `1/sqrt(3W)`, `W → ∞`, and `W/log N → ∞`. It covers every bounded continuous real test function on the complex plane.

## Proof stages

| Stage | Modules |
|---|---|
| Law and probability foundation | Atom, Inputs, SourceInputs, IID, Energy |
| Measurable interface and deterministic transfer control | Interface, BoundedBlockGrowth, BlockEntryControl, TransferGrowth, TransferBounds |
| Cook boundary and fixed-frame estimates | BoundarySmallBall, EndpointInterface, BoundaryGrowth, FrameSmallBall, TerminalRates |
| Averaged reset and complete-cell pressure | ConditionalCappedReset through CompleteCellPressureLimit |
| Incomplete cells, seam and Section 3 calibration | Remainder, RemainderLimit, Seam, SeamLimit, HighBandTransport, PressureCalibration, LogPotential |
| Weak circular-law conclusion | CircularReduction, HighBand, Results |

The directly measurable interface event replaces the finite-support event of the Rademacher specialization. The proof bounds normalized block entries by their operator norms. The coordinate-exposure estimate absorbs the fixed atom parameter into a width threshold and uses a `W²` bound; this preserves the needed `O(W log(eW))` terminal loss.

## Historical baseline validation

All 32 new library modules and the normal `lake build SubgaussianSection8` target passed. The import audit selects 282 project modules in total, of which 32 belong to the new library, plus its root module. Section 4 contributes zero modules; existing imported dependencies use verified cached artifacts. Only new modules are explicitly checked by the serial warm-cache runner, followed by the normal scoped root build.

The source placeholder scan passed for all 34 files in `SubgaussianSection8`, including its two audit files. Thirteen strict axiom reports passed with only `propext`, `Classical.choice` and `Quot.sound`. The compiled public signatures confirm that the final statements require only the atom, Cook and Nguyen inputs covering its parameter, the permitted Section 3 input, and the ordinary positive-dimension and logarithmic-bandwidth assumptions.

The successful run restored the extension's own cache. Its new Lean compilations were exactly CellResetRates, CompleteCellPressureLimit, LogPotential, Results and the root import module. The earlier 28 new modules were reused from cache. No baseline source files were changed.

The Section 3 integration changes the source and library resolution and therefore receives the separate cloud validation above.
