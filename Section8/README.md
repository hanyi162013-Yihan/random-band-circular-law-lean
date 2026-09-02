# Section 8 — discrete Bernoulli branch

This directory formalizes the symmetric Rademacher specialization of Section 8 of the fixed arXiv v1 source. The actual matrix is `BernoulliSection8.rademacherMatrix W s`: its block count is `m = s + 3`, its scalar dimension is `(s + 3) * W`, and the factor `1 / sqrt (3W)` is part of the matrix definition. The source range `m ≥ 4` is expressed by `0 < s`.

**Current status: the full proof chain is written, and Lean verification is in progress. This is not yet a completed or validated Section 8 release.**

The intended public results are `section8_bernoulli_log_potential` and `section8_bernoulli_circular_law` in `BernoulliSection8/Section8Results.lean`. Their displayed inputs are Cook, Nguyen, the Section 3 high-band proposition, positivity of the dimensions, and the source bandwidth conditions. There is no caller-supplied pressure, reset, seam, energy, or log-potential certificate in the circular-law statement.

The permitted analytic inputs are:

- `NguyenBottomSingularInput`, at a subgaussian bound at least one;
- `CookDeformedSquareInput`, specialized internally to the actual Rademacher family;
- `Section3SubgaussianHighBandInput rademacherLaw 1`, matching Proposition 3.8 and the associated Section 3 source estimates.

Section 4 is not an analytic input. Existing proved deterministic algebra and probability lemmas are reused from the repository; their directory names do not introduce new assumptions.

The reset argument integrates each capped loss before summing. Cook's slower error is therefore averaged, whereas Nguyen's exponentially small interface failures are union-bounded using `log N / W → 0`. The exact independent anchor contains `ceil(W^(1/200))` complete cells and a terminal packet. It is not the one-cell construction used elsewhere in the repository. Zero determinants are explicitly present in terminal bad events.

See `SOURCE_MAP.md` for the source-equation correspondence, `SECTION9_DEPENDENCY_AUDIT.md` for local terminal and interface reuse, and `SECTION10_REUSE_AUDIT.md` for the deterministic and circular-law reduction reuse.

Verification gates for a completed release are a full `lake build`, the repository's strict `scripts/check_axioms.py` audit, a placeholder scan that masks comments and strings, and inspection of `PublicSignatureAudit.lean`. Until these gates pass, the public theorem source is a work in progress.
