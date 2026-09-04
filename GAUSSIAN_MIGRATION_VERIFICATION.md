# Gaussian-source migration: exact verification checkpoint

Status: **all three projects passed**, with source-identical root/Section 5
checks and a focused corrected Section 6 check, as identified below.

## Commits and cloud evidence

| Project | Proof commit | Run / job | Verified checks |
|---|---|---|---|
| Root | `d7d732c43b498eea721df3299fc4faf520d15262` | [33822184759 / 100867044160](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33822184759/job/100867044160) | Nine normal public targets; 1379 axiom reports; three public-signature/schema regressions; seven module kernel replays |
| Section 5 | `d7d732c43b498eea721df3299fc4faf520d15262` | [33822184759 / 100867044155](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33822184759/job/100867044155) | Normal public target; 1109 axiom reports, including all 865 named public source theorems; six module kernel replays |
| Section 6 | `55b3dfe331eda01cae41ce7b40c28dc8b4d67c60` | [33823364955 / 100870664069](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33823364955/job/100870664069) | Both normal public targets; 839 axiom reports, including all 808 named public source theorems; both original regression files; sixteen module kernel replays |

Between these commits the only Lean source change is the missing namespace
import for `circularRadialPotential` in
`section6/CircularLawSection6/GinibreSourceConsequences.lean`.
The other two changes add focused project selection to the workflows.
No root or Section 5 mathematical source, dependency pin, build driver or
audit command changed. Their passed checks therefore apply unchanged to
the proof sources at `55b3dfe`; the Section 6 retry does not claim to have
rerun root or Section 5. The earlier combined run's overall conclusion is
failure because its old Section 6 job failed.

The earlier, smaller base migration really did pass all three projects
together at `d603e530a375908fd4d0a997045a7bb359eadd35`, in
[run 33816611348](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33816611348).
The later general Section 5 and legacy Section 6 source-record reductions
are additions beyond that checkpoint, not invalidations of its green result.

## Scope

Passed coverage is 3327 axiom reports over 2951 distinct declarations
and 29 selected proof-module replays. Repeated audit reports are not counted
as different theorems. The named public source-theorem audits cover Section 5
and Section 6; the root audit is a selected transitive audit, not an exhaustive
listing of every declaration in all root libraries.

Every axiom report is checked against exactly `propext`, `Classical.choice`
and `Quot.sound`. Ordinary mathematical hypotheses remain hypotheses.
Kernel replay uses the pinned Lean 4.33.0 checker, with exact module coverage
and one worker; it is not an external independent proof checker and does not
replay all of mathlib. All builds run in GitHub Actions. No local Lean build
or large local cache download was used. No proof-checking limits were raised.

The public BC12/Gaussian reference sources in Sections 3, 5, 6, 8 and 10 are
constructed by proofs. BBV, the accepted Proposition 3.2/Cook inputs, separate
Cook/Nguyen inputs, real geometric Brascamp–Lieb and finite Section 4 pressure
interfaces remain explicit where applicable. Historical optional squared-law
and Han routes are not inputs of the preferred Section 6 BBV-core endpoint.
See [the input map](GAUSSIAN_INPUT_MIGRATION.md).

The further complex-density and Gaussian-core pressure constructions are a
separate development and are not certified by this checkpoint.

## Retained cloud reports

Artifacts are retained by GitHub for 30 days. The metadata below identifies
the report archives exactly; these hashes are not hashes of Lean proofs.

| Project | Artifact ID | Bytes | SHA-256 |
|---|---|---|---|
| Root | `9918758895` | 70526 | `0c265a8bcbf63c0bff48fa069968de1fbcd2b208085f3dbe858546116be0df48` |
| Section 5 | `9918876425` | 27797 | `907907e860468451e9508287952e7200a8ddac0f346a839c0528dbaa61720961` |
| Section 6 | `9919233632` | 21812 | `c97cff62cb663822b69ac7eb7be37d4ef4cc405f9f6b8fcfb0ea30eea937b459` |
