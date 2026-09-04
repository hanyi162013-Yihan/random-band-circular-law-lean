# Section 10: real and planar source-connection audit

## Current migration status

The BC12-free signatures, all three Section 10 targets and all 502 exact
Section 10 axiom reports passed at
`c4e807877fefef8339a6ff01ec4ed75bc08ded81`, in
[run 33815655602](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33815655602/job/100847217601).
That root job subsequently failed on a missing Section 9 audit-only import;
this is a Section 10 checkpoint, not an overall green run. The import issue
is fixed. The expanded root check passed at `d7d732c`, including all nine
public targets, 1379 reports, all 502 Section 10 reports, the density schema
and seven selected module replays. See the
[completed certificate](../GAUSSIAN_MIGRATION_VERIFICATION.md).
`VerifiedGinibreSources` supplies the old BC12 compatibility proposition
internally from BBV. The certificates and tables below describe the
**historical pre-migration commit** and are not certificates for current
source changes. See [the migration audit](../GAUSSIAN_INPUT_MIGRATION.md).

## Historical verification boundary

**PASS.** Proof-source commit: `362c47fe69c5330b18e1818497dcbbe4433df1be`.
[Cloud run 33719162307](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33719162307)
completed successfully on 2026-09-03, 05:31:03–05:35:16 UTC (4 minutes
13 seconds). The actual models, both high-band anchors, all four final
caller-facing theorems, and the separate signature/axiom audits passed.

| Check | Verified result |
|---|---|
| Normal Lake build | All three Section 10 targets and their actual dependencies passed |
| Chapter placeholder scan | 207 Lean files passed |
| Fresh exact axiom audit | 492 reports from 9 audit files; only the three standard axioms below |
| Final printed signatures | Only BBV, BC12, real-only geometric Brascamp–Lieb and original model assumptions |
| Concrete density regression | Actual ENNReal infinity; finite-bound and Gaussian/RN constructions passed |
| Independent downloaded-log check | All 492 reports matched their exact source declarations and multiplicities |

The durable [verification record](verification/verification.json),
[final printed signatures](verification/connected-axioms-signatures.log),
and [density-schema print](verification/density-schema.log) are included.
The complete GitHub artifact has SHA-256
`77d24d02d7cdecb9cf7309a0176ec0dc71d7110541a1a82988f1b08fe846250a`.

The earlier `e7ca00c` run compiled the final theorems, then its whole-root
stage was stopped when the user narrowed verification. The successful run
above replaces it as the final scoped verification record; no completed
whole-repository build is claimed for this release.

Subsequent merge `a562be3` incorporates the canonical shared density
correction `5c7be7b`, with explicit ENNReal infinity and a record-local
implicit-parameter guard. Its independent Section 3 check already passed in
[run 33718453418](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33718453418).
The successful scoped Section 10 check above verifies its downstream connection.

The integration has not been compiled locally. Local checks were restricted
to source inspection, placeholder scanning, audit-parser tests, dependency
graph inspection and Git operations.

## Public entry points

Import `BernoulliSection10Source`. All names below are in that namespace;
the implementations are in `BernoulliSection10Source/DensityCircularLaw.lean`.

| Theorem | Atom space | Conclusion | Literature parameters |
|---|---|---|---|
| `planar_density_circular_law` | `ℂ` | Weak circular law in probability against every bounded continuous real test function | BBV, BC12 |
| `real_density_circular_law` | `ℝ` | The same circular law | BBV, BC12, real geometric Brascamp–Lieb |
| `planar_density_ring_log_limit` | `ℂ` | Normalized shifted log determinant converges in probability to the circular logarithmic potential | BBV, BC12 |
| `real_density_ring_log_limit` | `ℝ` | The same logarithmic-potential limit | BBV, BC12, real geometric Brascamp–Lieb |

The retained model hypotheses are an IID probability law with bounded
Lebesgue density, mean zero, unit second moment, finite third absolute
moment, and positive integer widths `W n` tending to infinity. The dimension
is `N n = (s n + 3) * W n`. No growth restriction is imposed on `s`.
Complex density means density of the joint law with respect to planar
Lebesgue measure; independence of real and imaginary parts, circular
symmetry, and vanishing complex second moment are not assumed.

The finite-row statements construct their probability-measure instances
from the atom hypothesis. They do not require an extra finite-measure
assumption. The circular laws use literal physical matrices sampled from
one infinite IID sequence; auxiliary Gaussian randomness is eliminated.

## What is constructed, rather than assumed

| Module | Mathematical role |
|---|---|
| `IIDModels` | Actual independent atom copies, coefficient profile, source random-matrix model, exact bandwidth `3W` |
| `DensityRepresentative` | Bounded Radon–Nikodym representative from the original measure-domination hypothesis |
| `PlanarHighBand`, `RealHighBand` | Concrete band models and whole-matrix law transport; source LSV application and cutoff removal |
| `GaussianReferenceModel` | Literal normalized circular Ginibre matrix, atom moments/density, independence, nonsingularity and row moments |
| `LiteratureInputs` | Explicit BBV and literal-Ginibre BC12 hypotheses, and proved transport to the product sample space |
| `FullBlockLogLimit` | Source counting, local bulk comparison, cutoff/rate choices, and Proposition 10.1 assembly |
| `ConnectedHighBand` | Both high-band anchors with all internal model, counting and LSV inputs discharged |
| `DensityCircularLaw` | Existing pressure/reset/seam/remainder and proved Tao–Vu closure applied to those anchors |

`BBVComparisonInput` includes the source's canonical Gaussian/free-transform
comparison. `BC12GinibreInput` concerns only the explicitly defined circular
Gaussian ensemble, not an arbitrary comparison model or the target matrix.
The real endpoint additionally retains `RealFiniteGeometricBrascampLieb`.
These are ordinary, explicitly accepted theorem hypotheses, not custom Lean
axioms or internally proved literature results.

The final signatures must contain no `Section3Inputs`, `HighBandLogLimit`,
LSV, counting, reset, pressure, reference-limit or model-validity certificate.
Internal composition lemmas with such parameters remain available, but are
not the final entry points listed above.

## Independent checks

The user requested continued verification limited to Section 10 and its
actual dependencies, not an automatic whole-repository recheck. The cloud
workflow therefore runs normal `lake build` for exactly
`BernoulliSection10`, `BernoulliSection10Complex`, and
`BernoulliSection10Source`. Lake checks their imported dependencies without
rewriting traces or trusting omitted modules. Separate audit gates cover:

- the raw planar atom and physical-coordinate signatures;
- actual construction of the corrected finite density bound;
- concrete real/complex source models and Gaussian reference;
- the final theorem parameters, including the explicit literature boundary;
- exact `#print axioms` report counts and the allowlist `propext`,
  `Classical.choice`, `Quot.sound`;
- a Section 10 source-token scan forbidding proof placeholders and custom
  axioms.

Kernel-axiom reports alone do not establish either the absence of theorem
parameters or the inhabitability of a hypothesis. In particular, the
[density-definition correction](DENSITY_SCHEMA_CORRECTION.md) is part of
this verification and must not be omitted when citing the source connection.

## Selected source and concurrent work

The checked Section 3 baseline is `42c26b6`, plus the documented finite-density
field correction. The later Proposition 3.8 update is outside this task by
the user's instruction. The final endpoint's import closure has 447 project
modules and does not import the `ShortRingAnchor` umbrella or that update.
Other tasks' repository changes must be preserved during publication.
Both tasks now share correction commit `5c7be7b`, whose explicit
`(⊤ : ENNReal)` annotation denotes the same infinity as the earlier inferred
`⊤`. The exact canonical file and hash are recorded in
`DENSITY_SCHEMA_CORRECTION.md`; unrelated chapter changes are not imported.

## Reproduction

Publication merges the verified branch with main at `4707c05` without
conflicts. All 207 chapter Lean files, the 463 modules in their combined
import closure, and eight dependency/configuration/verification files are
byte-identical to `362c47f`. Unrelated main files are preserved; its newer
Proposition 3.8 is not in that import closure and is not claimed as rechecked.
The existing 286-entry Section 3 source manifest remains hash-consistent.
This read-only identity check does not rerun Lean or widen verification.
See [publication.json](verification/publication.json).

From the repository root with the committed Lean/mathlib pins and Python
3.11 or newer:

```sh
lake exe cache get
lake build BernoulliSection10 BernoulliSection10Complex BernoulliSection10Source
python3 scripts/check_placeholders.py --path Section10
python3 scripts/check_axioms.py \
  --audit-file Section10/BernoulliSection10/AxiomAudit.lean \
  --audit-file Section10/BernoulliSection10/AsymptoticAxiomAudit.lean \
  --audit-file Section10/BernoulliSection10/CompletionAxiomAudit.lean \
  --audit-file Section10/BernoulliSection10Complex/AnalyticAxiomAudit.lean \
  --audit-file Section10/BernoulliSection10Complex/FrontAxiomAudit.lean \
  --audit-file Section10/BernoulliSection10Complex/ClosureAxiomAudit.lean \
  --audit-file Section10/BernoulliSection10Complex/GaussianReferenceAxiomAudit.lean \
  --audit-file Section10/BernoulliSection10Source/ModelAxiomAudit.lean \
  --audit-file Section10/BernoulliSection10Source/AxiomAudit.lean
lake env lean Section10/BernoulliSection10Source/DensitySchemaAudit.lean
lake env lean Section10/BernoulliSection10Complex/FrontSignatureAudit.lean
```

For the final theorem alone, use `lake build BernoulliSection10Source`.
Its final parameter and axiom audit is
`Section10/BernoulliSection10Source/AxiomAudit.lean`.

Do not replace these scoped commands with the root-wide serial builder or
unrelated chapter audits unless a new request explicitly calls for them.

## Exact unclaimed extensions

This release targets real and planar-complex IID bounded-density atoms with
finite third moment. It does not claim heterogeneous-law versions of
10.2–10.3, directional conditional-density hypotheses, or a general
finite-`(2+α)`-moment replacement of the third moment. It permits three
block sites as well as the paper's at-least-four-site case; this is a
stronger dimension range, not a proof gap.
