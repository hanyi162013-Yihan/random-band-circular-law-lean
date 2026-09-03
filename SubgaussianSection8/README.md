# General subgaussian Section 8

Verified extension of the Rademacher specialization to every fixed real IID law with mean zero, second moment one and a finite subgaussian MGF parameter. No bounded-support, symmetry or density hypothesis is imposed. Cook and Nguyen remain explicit external inputs. Proposition 3.8 is now constructed from the concrete Section 3 proof under its existing named literature inputs; see [the integration record](../Section8/SECTION3_INTEGRATION.md).

The final results are `SubgaussianSection8.section8_subgaussian_log_potential` and `SubgaussianSection8.section8_subgaussian_circular_law` in [Results.lean](Results.lean). For the exact cyclic-band dimension `N=(s+3)W`, they assume positive widths and core-site counts, `W → ∞` and `W/log N → ∞`. The circular-law result covers every bounded continuous real test function on the complex plane. The quantitative Cook and Nguyen ranges must cover the fixed atom parameter.

This library belongs to the root Lake project of `random-band-circular-law-lean`. [PR #1](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/pull/1) integrates both the verified Rademacher specialization and this general extension into `main`. Development uses a separate local checkout on `codex/section8-subgaussian`. It extends verified Rademacher commit `24a1e37550a7e471bec4bb668ce4bde92fae3cbb`; existing Section 4/8/9/10 and vendor source files are unchanged by the extension.

## Verification

The Section 3 integration passed its [separate cloud gate](../Section8/SECTION3_INTEGRATION.md) at `b6c379836fcc6cf166881768d1a0ad6782c5c552`: both Section 8 targets, 56 combined axiom reports, and both compiled public signatures. The new bridge uses default proof-checking limits. The following records the earlier baseline.

Proof-source commit: `d29fd6f0cefcaa4ec3afe09f14c54df3e16842d4`.

[Successful GitHub Actions run](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33688229894/job/100440674643) completed on 2026-09-02:

- All 32 new modules and the normal `lake build SubgaussianSection8` target passed.
- The selected import closure contains zero Section 4 modules.
- All 34 extension files, including both audit files, passed the placeholder scan.
- All 13 strict axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
- Compiled public signatures expose only the ordinary distribution and bandwidth conditions and the approved external inputs. No pressure, reset, seam, energy or reference-ensemble certificate is required.

CI restores available integration and Section 3 artifacts, then builds only the two explicit Section 8 targets and their actual imports. See [STATUS.md](STATUS.md) for the proof map.
