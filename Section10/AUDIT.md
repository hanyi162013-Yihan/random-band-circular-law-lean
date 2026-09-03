# Reproducibility and trust audit

The verification records below belong to the earlier real conditional
release at their stated commits. They are not verification certificates
for the new planar/source-connected work on this branch. Its current
evidence and outstanding checks are in
[SOURCE_CONNECTION_AUDIT.md](SOURCE_CONNECTION_AUDIT.md), which records
the successful scoped real/planar verification and 492 reports at `362c47f`.

Scope: the real IID bounded-density finite-third-moment branch of
[arXiv:2609.01295v1](https://arxiv.org/abs/2609.01295v1), Section 10,
through its circular-law conclusion. Exact mathematical inputs and
uncovered atom-law extensions are listed in
[ASSUMPTIONS.md](ASSUMPTIONS.md) and [FORMALIZATION_MAP.md](FORMALIZATION_MAP.md).

## Verified completion — 2026-09-02

### Integration into `main`

The completed chapter and its required vendored dependencies are now
integrated into `main`. The integration fast-forwards the previously
verified completion history; no Lean source, dependency pin, build
configuration, verification script, or other chapter source was changed
relative to completion snapshot
`f3b485775ad2eed0ba3eefe1daa1fc85180dcbb1`. The follow-up integration commit
only updates this audit record and the root README's branch instructions.

That exact completion snapshot also passed a
[second clean full-repository run](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33624155590)
on 2026-09-02, from 11:21:23 to 11:54:38 UTC. Its full downloaded log was
independently checked for all 373 library targets, the final default
`lake build`, the 381-file placeholder scan, and all 857 fresh axiom reports.
This is verification evidence for the unchanged proof source, not a claim
that a later automatic `main`-branch run has already completed.

### Original proof-source verification

The [clean GitHub Actions run](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33620303116)
passed for source commit **`1cb4a34cd6867cda79b26a9c8e4bded4cdabb515`**.
Its Ubuntu 24.04 job ran from 10:36:11 to 11:11:24 UTC, **35 minutes 13 seconds**.
It installed the pinned toolchain and dependency cache, built the released
libraries from source, and then executed every audit file afresh.

| Check | Status and scope |
|---|---|
| Complete proof chain through `density_circular_law` | **PASS**, clean release build and independent development compilation |
| Full release-root serial build and final `lake build` | **PASS**, all **373** distinct library modules, followed by the complete default build |
| Fresh repository-wide axiom audit | **PASS**, **857** actual reports across **11** audit files; exact declaration/report multiplicities and the allowlist below |
| Section 10 audits within that run | **PASS**, **446** reports: 64 local, 39 asymptotic, and 343 completion reports |
| Source placeholder scan | **PASS**, all **381** released Lean source files |
| Release dependency graph | **PASS**, **373** library modules, no missing local import or cycle |
| Public statement inspection | **PASS**, the four Section 3 fields and seven principal endpoint signatures were printed by Lean |
| Source-only archive checks | **PASS**, archive-mode source scan, dependency discovery, parser tests, vendor hashes, and exact committed-file comparison |

The downloaded clean-run log was independently parsed again: all 373
module targets and the final default-build success were present, and all
857 fresh compiler axiom reports matched the released audit declarations.
Only GitHub's job/step/timestamp prefix was removed; report text was unchanged.

The earlier development completion check finished at approximately 10:12 UTC
and validated 343 actual compiler reports. The later clean release run also
checks the intervening comment and whitespace corrections. The full-release
pass reported here is the clean Ubuntu run, not the memory-constrained Mac's
separate all-library rebuild. Subsequent completion-record edits are
documentation only; no Lean source, dependency pin, build configuration,
verification script, or workflow was changed after this verified source commit.

The vendored Tao–Vu files retain the documented extra final blank line;
their exact release hashes are recorded. Section 4/9 source and the original
external proof projects were not edited by this continuation.

### Final public signature

The clean compiler printed the following complete type. In particular, no
pressure, reset, seam, remainder, reference-law, energy, or replacement
certificate is an argument:

```text
@BernoulliSection10.density_circular_law : ∀ {μ : MeasureTheory.Measure ℝ} {L : ℝ},
  BernoulliSection10.IsBoundedDensityAtom μ L →
    MeasureTheory.Integrable (fun x => |x| ^ 3) μ →
      BernoulliSection10.SourceInputs.Section3Inputs μ L →
        ∀ (W s : ℕ → ℕ),
          (∀ (n : ℕ), 0 < W n) →
            Filter.Tendsto W Filter.atTop Filter.atTop →
              ∀ (f : BoundedContinuousFunction ℂ ℝ),
                MeasureTheory.TendstoInMeasure (MeasureTheory.Measure.infinitePi fun x => μ)
                  (fun n ω =>
                    TaoVuReplacement.realEsdTest
                      (BernoulliSection10.densityCyclicMatrix (W n) (s n)
                        (BernoulliSection10.physicalRowsFromSequence (W n) (s n) ω))
                      ⇑f)
                  Filter.atTop fun x => ∫ (z : ℂ), f z ∂BernoulliSection10.DiskReference.circularMeasure
```

Statement review also checked the literal variance normalization, algebraic
eigenvalue multiplicities, normalized planar disk law, arbitrary diverging
dimension sequences, second-moment-only energy conclusion, and the separate
qualitative anchor error. These checks supplement, not replace, the detailed
source mapping and explicit scope qualifications.

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
