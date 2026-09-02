# Section 5 verification record

Date: 2026-09-02. Lean and mathlib: v4.33.0.

## Original mathematical snapshot — passed

| Check | Result | Evidence |
|---|---|---|
| Integrated project build, followed by a final rebuild | 4079 jobs; exit 0 | Local final build log recorded in the coverage table |
| Strict re-elaboration of the extension | 65 modules; warnings treated as errors | `verification/strict-modules.txt` |
| Selected-entry transitive axiom audit | 224 different declarations | `verification/critical-axioms.txt` |
| Exhaustive public Section 5 namespace audit | 1561 declarations, including 1215 theorems | `verification/exhaustive-axioms.txt` |
| Boundary regression proofs | All 15 examples passed with warnings treated as errors | `Section5Regression.lean`, `verification/final-audit-result.txt` |
| Additional Lean kernel replay | 117 source modules plus the Section 5 umbrella; exact 118-module coverage and exit 0 | `verification/kernel-replay.txt`, `verification/kernel-result.txt` |

The continuous mathematical work started at 06:21:05 UTC. The final original
checks were confirmed complete by 13:43:29 UTC, exceeding the requested six-hour
minimum. No mathematical source was changed during the final strict/audit/kernel
checks. Existing warnings in upstream projects are not a claim that the complete
dependency tree is warning-free.

The axiom audits allow only `propext`, `Classical.choice`, and `Quot.sound`.
Ordinary theorem hypotheses are not axioms: these checks do not discharge the
explicit Section 3/4 or model assumptions. See `SECTION5_COVERAGE.md`.
The extra replay uses Lean's installed checker, not an independent logical
system. It does not use `--fresh` or replay all of mathlib.

## Repository publication layout

All 142 original source/validation files other than the two Lake configuration
files are byte-identical to the checked local snapshot. The five additional
short-ring support files are byte-identical to the original local dependency
closure. Only dependency paths and library registration are adapted for this
repository. `SOURCE_SHA256SUMS` covers all 149 published source/configuration/
validation files and has passed its integrity check.

The extra repository-relative local build was interrupted at the user's request
on 2026-09-02 at approximately 15:56 UTC (exit 130), before completion and without
a reported proof error. Existing caches were retained. No successful local
publication-layout build or second publication-layout audit is claimed.

The user requested publication followed by compilation on GitHub. The dedicated
[Section 5 verification workflow](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/workflows/section5.yml)
checks source integrity, compiles `CircularLawSections56` from `section5/`, and
runs the selected/exhaustive axiom audits and all 15 boundary regressions. Build
and audit logs are retained as workflow artifacts. This record does not assume
that a queued or running CI job has passed; consult the actual run conclusion.

The original verification records above are retained as evidence for the
unchanged mathematical sources, rather than being presented as results of a
second kernel replay in the publication layout.
