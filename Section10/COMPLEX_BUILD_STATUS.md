# Complex Section 10: verified

Both real and planar-complex source-connected endpoints passed
[cloud run 33719162307](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33719162307)
at proof-source commit `362c47fe69c5330b18e1818497dcbbe4433df1be`.
The run took 4 minutes 13 seconds and reused the preceding checked cache.

- Normal builds of all three Section 10 targets and their actual imports passed.
- The chapter source-token scan passed for 207 Lean files.
- All 492 fresh axiom reports from 9 audit files passed, with only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Printed final signatures retain only the original model assumptions,
  BBV/BC12, and real-only geometric Brascamp–Lieb; no Section 3/model/LSV/
  counting/high-band certificate is a caller argument.
- The canonical finite-density field and its concrete Gaussian/RN
  construction checks passed.

The user explicitly requested scoped verification instead of a whole-root
recheck. The earlier whole-root run was cancelled for that reason; it is
not reported as either a completed full build or a proof failure. No local
compilation of the source integration was performed.

See [SOURCE_CONNECTION_AUDIT.md](SOURCE_CONNECTION_AUDIT.md) for the exact
commands, durable logs, input boundary and unclaimed extensions;
[COMPLEX_FORMALIZATION_MAP.md](COMPLEX_FORMALIZATION_MAP.md) for the complete
item-by-item map; and [DENSITY_SCHEMA_CORRECTION.md](DENSITY_SCHEMA_CORRECTION.md)
for the upstream definition error and single shared correction `5c7be7b`.

This is the requested real/planar IID bounded-density finite-third-moment
scope, not a claim for heterogeneous or directional-density alternatives.
