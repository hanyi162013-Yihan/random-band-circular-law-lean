# General subgaussian extension: scope and effort

The target is the Section 8 circular law and fixed-z log-potential limit for a fixed real IID atom with mean zero, second moment one, and an arbitrary finite subgaussian MGF parameter. No density, finite-support, symmetry, or deterministic atom bound will be imposed. The scale remains W → ∞ and W / log N → ∞. Cook, Nguyen, and Section 3 Proposition 3.8 are the only external mathematical inputs.

The original verified repository is pinned at 24a1e37550a7e471bec4bb668ce4bde92fae3cbb. This is a separate local checkout of the existing repository, on branch `codex/section8-subgaussian`, with its own Lean library. No source, build script, branch, or deliverable in the original project is edited.

A source-level estimate is 20–30 new/adapted modules and roughly 30–60% of the effort of the completed Rademacher specialization. These figures estimate engineering effort, not a verified mathematical completion percentage or promised wall-clock time.

1. General atom, product/IID coordinates, and second-moment energy facts. Existing Section 9 family interfaces and the Section 10 second-moment law of large numbers can be reused.
2. General interface and transfer controls. Replace finite-support measurability with directly measurable norm/determinant/inverse events, preserving restriction to actual subinterval coordinates. Bound normalized entries from the existing general subgaussian operator-norm event. Constants may depend on the fixed subgaussian parameter, never on the sequence index or ring length.
3. General Cook packet, capped reset averaging, pressure concentration/calibration, seam and remainder, and high-band transport. Parameterize the existing assembly. Check that Cook's slow error is averaged and only exponentially small interface errors are union-bounded. Adapt the fresh-coordinate exposure threshold to the arbitrary fixed atom parameter.
4. Final public theorem, source map, and audits. A normal scoped Lake build must succeed. The import closure must exclude Section 4. Audit all new main declarations and inspect the public signature for unauthorized proof inputs. Scan for placeholders.

Current status: the independent package and pinned dependency are prepared; foundation source and the general interface source are being checked. The general theorem is not yet complete or verified.
