# Reproducibility and trust audit

This records the real i.i.d. specialization of items 10.2--10.10 in
[arXiv:2609.01295v1](https://arxiv.org/abs/2609.01295v1). Exact source alignment,
retained hypotheses, and uncovered extensions are in `FORMALIZATION_MAP.md`.
Commands below run from the repository root, using Lean/mathlib `v4.33.0`
and the committed dependency manifest. The deterministic dependency is the
repository's `BernoulliLinearAlgebra` library in `Section9/`.

## Full default build

```sh
lake build BernoulliSection10
lake build
```

Publication status: **PASS**, on 2026-09-02. The
[integrated GitHub Actions run](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33590358281)
checked source commit `48a1556090a0944a8f06b85bd220116ada66129b` using a clean
standard Ubuntu runner. All 257 repository library modules, including all
38 Section 10 Lean files, compiled, followed by the full default `lake build`.
The complete run, including setup and audits, took 25 minutes 35 seconds.

The chapter includes the
continuous-density, probability, Hodge-integrability, packet-probability,
concrete simultaneous one-site and interval Hodge-envelope, the improved
single-cost maximum-over-exterior-degrees Hodge family, its concrete
zero/one-hot corner and complementary-minor coefficient-tensor bounds, the
fully explicit `C_z W log(eW)` simultaneous tensor/forward first-moment bound,
the common `C_{L,z}` one-site and interval conclusion completing Lemma 10.6,
measure-preserving product-marginal, endpoint-determinant, deterministic
packet-frame, raw/normalized tensor comparison, complete nine-block seam,
and fixed-degree packet-reset modules.

## Placeholder scan

The scan covers all Lean sources in this chapter and excludes generated
`.lake` contents.

```sh
rg -n --glob '*.lean' \
  '\bsorry\b|\badmit\b|^[[:space:]]*(axiom|opaque)[[:space:]]' Section10
```

Publication status: **PASS**, checked for the publication sources on
2026-09-02. The scan returned no matches (ripgrep exit status `1`).
It covers all 38 Lean files: 37 modules and the umbrella import.
The public API follows items 10.2--10.10 of the cited arXiv source.

## Axiom audit

```sh
lake env lean Section10/BernoulliSection10/AxiomAudit.lean
```

Publication status: **PASS**, in the integrated run above. All 64 reports
from this chapter matched their audit commands and used only the three
foundational axioms listed below. The repository-wide total was 475 reports
across nine audit files. This checks the public results for 10.2,
10.3, 10.5, 10.7--10.10, the endpoint determinant estimates, the concrete one-site
and interval Hodge envelopes (including the improved maximum-over-degrees
versions), their first/second moments, the concrete tensor corner bound and
the explicit `C_z W log(eW)` forward estimate and common
`C_{L,z} s W log(eW)` Hodge bound, the finite-product
marginal theorem, the deterministic 10.10 frame/nonvanishing layer, both
raw/normalized packet-tensor comparisons, and the final iterated expectation
theorems. Every audited declaration must depend only on the
standard foundational principles already used by mathlib:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` or project-defined axiom is permitted in the audited declarations.
The nine proof chains are complete for the documented real i.i.d. scope;
this is not a claim that all of the extended arXiv v1 Section 10 is covered.
An axiom audit verifies dependencies, not the faithfulness of an informal
statement's translation; the source map and theorem signatures remain essential.
