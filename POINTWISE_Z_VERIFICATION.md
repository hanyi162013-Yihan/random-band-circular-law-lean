# Fixed-shift logarithmic-potential verification

This certificate records the 2026-09-04 strengthening of the caller-facing
logarithmic-potential chain from a planar-almost-everywhere endpoint to a
theorem at every prescribed finite shift `z : ℂ`.

## Meaning of the statement

The Lean declarations quantify over an arbitrary caller-chosen `z : ℂ` and
then prove convergence in probability at that shift. Thus there is no
exceptional planar null set in these logarithmic-potential conclusions.
This is not a claim that one probability-one event works simultaneously for
all uncountably many complex shifts. The reusable Tao--Vu replacement theorem
still accepts an almost-everywhere family; concrete circular-law proofs obtain
that family by applying `ae_of_all` to the pointwise theorem.

Historical generic interfaces with almost-everywhere hypotheses remain
available. They are not the preferred concrete endpoints.

## New checked route

- Section 5 exposes
  `PublishedSection3Concrete.indicator_complex_logPotential_at_of_bbv` for an
  arbitrary fixed shift on the actual complex-density sample law.
- Section 6 proves the compact-core comparison and normalization at a fixed
  shift, transports the Section 5 theorem through the finite-prefix core,
  reconstructs the sparse mean, combines sparse and dense subsequences, and
  exposes `NoncompactProfile.gaussian_profile_logPotential_of_bbv`.
- `NoncompactProfile.gaussian_profile_circular_law_of_pointwise_bbv` applies
  `ae_of_all` only at the general replacement boundary.
- The already pointwise caller-facing endpoints
  `BernoulliSection8.section8_bernoulli_log_potential`,
  `SubgaussianSection8.section8_subgaussian_log_potential`,
  `BernoulliSection10Source.planar_density_ring_log_limit`, and
  `BernoulliSection10Source.real_density_ring_log_limit` were retained and
  rechecked in the root project.

For the new Section 6 endpoint, the only literature premise is the explicit
`BBVComparisonInput` argument, in addition to the stated deterministic profile
and bandwidth assumptions. It is a hypothesis of the theorem, not a Lean
axiom. No BC12 result, caller-supplied pressure estimate, Ginibre log-potential
limit, or exceptional-set certificate is an input to this preferred route.

## Cloud evidence

The verified source commit is
[`043514b`](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/commit/043514bb14be1d3bc14be9e9564cb3dd1f62a4b1).

| Check | Result |
| --- | --- |
| Complete Section 5 repository-layout build and audit | [run 33916638215](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33916638215), success |
| Focused pointwise Section 6 build, BBV/pointwise audits and regressions | [run 33921454440](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33921454440), success |
| Full historical Section 6 umbrella, axiom audit and regression | [run 33921891278](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33921891278), success |
| Root + Section 5 + Section 6 migration build, exact public audit and kernel replay | [run 33922165206](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33922165206), success |

The final cross-project run checked:

- 857 root-project modules, including the Section 8 and Section 10 public
  targets; 25 audit files with 1379 axiom reports; three signature/schema
  regressions; and seven kernel-replayed modules;
- 578 Section 5 modules; three audit files with 1122 reports; the pressure
  regression; and eight kernel-replayed modules;
- 706 Section 6 modules; three audit files with 899 reports, including all 25
  focused pointwise reports; four regression files; and 26 kernel-replayed
  modules.

All 3400 axiom reports contained only Lean's standard foundational axioms
`propext`, `Classical.choice`, and `Quot.sound`. All 41 selected changed modules
were replayed by Lean's `leanchecker` with exact coverage and exit status zero.
No checking limit or soundness option was changed.

The verification used GitHub Actions and restored project build caches. No
local Lean/mathlib download or local `lake build` was used for this change.
