# Reproducibility and trust audit

Scope: the real IID bounded-density finite-third-moment branch of
[arXiv:2609.01295v1](https://arxiv.org/abs/2609.01295v1), Section 10,
through its circular-law conclusion. Exact mathematical inputs and
uncovered atom-law extensions are listed in
[ASSUMPTIONS.md](ASSUMPTIONS.md) and [FORMALIZATION_MAP.md](FORMALIZATION_MAP.md).

## Completion verification checkpoint — 2026-09-02

| Check | Status and scope |
|---|---|
| Complete new proof chain through `density_circular_law` | **PASS**, development build, including `CompletionAxiomAudit` |
| Completion audit | **PASS**, all **343** actual `#print axioms` reports matched their declarations and used only the allowlist below |
| Source placeholder scan | **PASS**, all **381** released Lean source files, including tracked and newly added files |
| Release dependency graph | **PASS**, **373** library modules, no missing local import or cycle |
| Full release-root serial build and final `lake build` | **In progress**; not yet reported as a new full-release pass |
| Fresh repository-wide axiom audit | **Pending full release verification**; expected **857** reports across **11** audit files |

The development completion build finished at approximately 10:12 UTC.
The 343-report allowlist check used the actual Lean compiler messages
preserved in Lake's nonsynthetic completion-audit trace; only their
source-location/severity formatting was normalized for the audit parser.
No build metadata, proof artifact, or axiom report was rewritten.
The full release checks below execute the audit files afresh.

Subsequent Lean edits at this checkpoint correct application comments in
`ProbabilityLimits.lean` and trailing whitespace in `RemainderProbability.lean`;
no proof term or statement changes. The vendored Tao–Vu files retain the
documented extra final blank line; their exact release hashes are recorded.

## Reproducible full verification

Run from the repository root with Lean `v4.33.0`, the committed
mathlib manifest (`db584cd6d46c92f209a44c0f1c829460d327499d`), and
Python 3.11 or newer:

```sh
lake exe cache get
python3 scripts/check_axioms.py --self-test
python3 scripts/check_placeholders.py
python3 scripts/build_serial.py
python3 scripts/check_axioms.py
```

The serial builder checks every library module in dependency order and
then runs the complete default `lake build`. Serializing project modules
limits peak memory; it does not omit modules or replace kernel checking.

The source scan masks comments and strings, checks both tracked and
untracked source, and also supports source-only archives without Git metadata.
Generated `.lake/` dependency/build trees are excluded.

The axiom checker discovers all `*AxiomAudit.lean` files, runs Lean on
each, verifies exact declaration/report multiplicities, and rejects a
missing report, malformed report, Lean error, or non-allowlisted dependency.
Its allowlist is exactly:

```text
propext
Classical.choice
Quot.sound
```

Neither `sorryAx` nor any project-defined axiom is permitted.
These three logical foundations are not manuscript assumptions.

## Chapter audit inventory

| File | Reports | Purpose |
|---|---:|---|
| `BernoulliSection10/AxiomAudit.lean` | 64 | Established local estimates 10.2–10.10 and their concrete analytical/algebraic dependencies |
| `BernoulliSection10/AsymptoticAxiomAudit.lean` | 39 | Ceiling scales, finite maxima, integer division, and vanishing explicit errors |
| `BernoulliSection10/CompletionAxiomAudit.lean` | 343 | Concrete coordinate laws, singular frames, conditional reset, stitching, seam, remainder, Section 3 adapters, high-band and target limits, energy, replacement, and the final circular law |

The chapter total is 446 reports. The repository-wide total is 857,
including the unchanged Section 4 and Section 9 audits. Repeated reports
across audit files are intentional and are not described as distinct theorems.

The completion audit also prints `SourceInputs.Section3Inputs` and checks
the full explicit signatures of the seven principal endpoints. This
statement inspection matters: an allowed axiom list alone cannot show
that an informal theorem was translated faithfully or that unwanted
hypotheses were not inserted as parameters.

## Previously published baseline

The [integrated GitHub Actions run](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33590358281)
passed for source commit `48a1556090a0944a8f06b85bd220116ada66129b`
on 2026-09-02. That clean Ubuntu run checked 257 library modules, the
complete default build, and 475 reports across nine audit files, in
25 minutes 35 seconds. It verifies the older local-results baseline,
not the later continuation recorded above.

The stable Section 4/9 sources and the earlier local 10.2–10.10 proofs were
not modified by this continuation. New modules import them through the
repository's library boundaries. Dependency provenance and source hashes
are recorded in `PROVENANCE.md` and the two vendored proof directories.
