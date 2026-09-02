# General subgaussian extension — validation in progress

The full logarithmic-bandwidth proof now has a first source draft. It is not yet a verified result.

The extension is in `codex/section8-subgaussian` of the existing `random-band-circular-law-lean` repository, based on verified Rademacher commit `24a1e37550a7e471bec4bb668ce4bde92fae3cbb`. It is developed in a separate local checkout.

## Scope

The fixed real atom law is a probability measure with mean zero, second moment one, and a finite subgaussian MGF parameter. No bounded-support, symmetry, or density hypothesis is imposed. Cook, Nguyen, and Section 3 Proposition 3.8 remain explicit external inputs, with the two quantitative input ranges covering the atom's parameter.

The draft conclusion uses the exact cyclic-band dimension `N=(s+3)W`, physical normalization `1/sqrt(3W)`, `W → ∞`, and `W/log N → ∞`. It covers every bounded continuous real test function on the complex plane.

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

## Validation

GitHub has compiled 28 of the 32 new modules, including all measurable interface, Cook terminal, deterministic transfer, seam and remainder estimates. The four remaining modules are the reset-rate and final pressure/potential/result assembly; a missing atom argument in the reset-rate proof has been corrected for the next CI run. The import audit currently selects 32 new library modules plus their existing dependencies, with zero Section 4 imports. Only new modules are explicitly built when a baseline cache is restored; Lake checks their actual dependency artifacts. Independent modules continue after a failure, while descendants of a failed module are deferred.

Acceptance requires the normal `lake build SubgaussianSection8` target to succeed, followed by strict axiom and public-signature audits. A source placeholder scan alone does not establish completion.
