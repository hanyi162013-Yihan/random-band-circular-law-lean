# Section 8 — discrete Bernoulli branch

This directory formalizes the Rademacher specialization of Section 8 of the fixed arXiv v1 source, with independent entries taking values ±1 with equal probabilities. The actual matrix is `BernoulliSection8.rademacherMatrix W s`: its block count is `m = s + 3`, its scalar dimension is `(s + 3) * W`, and the factor `1 / sqrt (3W)` is part of the matrix definition. The source range `m ≥ 4` is expressed by `0 < s`.

**BC12-free integration:** the public endpoints now call the new Section 3.8 endpoint and construct the explicit Gaussian reference law internally. The BC12 negative-moment, projection and correlation fields are removed. See [the proof map and verification boundary](SECTION3_INTEGRATION.md); historical certificates do not certify a later source revision.

**Historical conditional integration:** both Section 8 targets and all 56 combined axiom reports passed at `b6c379836fcc6cf166881768d1a0ad6782c5c552`, with default proof-checking limits.

**Verified baseline:** source commit `15433d8765efd6c9767967140bb6969b6e31f643` passed the normal `lake build BernoulliSection8` target, all 28 strict axiom reports, the public signature check, and the 55-file Section 8 placeholder scan in [GitHub Actions run 33676900277](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33676900277). The dependency closure contains 271 project modules, including 53 Section 8 modules and no Section 4 modules. The only logical axioms reported are `propext`, `Classical.choice`, and `Quot.sound`.

The public results are `section8_bernoulli_log_potential` and `section8_bernoulli_circular_law` in `BernoulliSection8/Section8Results.lean`. Their compiled public signatures take Cook, Nguyen, `RademacherSection3UpstreamInputs`, positivity of the dimensions, and the source bandwidth conditions. The Section 3.8 conclusion is constructed by its concrete proof. The circular-law theorem applies to every bounded continuous real test function. There is no caller-supplied pressure, reset, seam, energy, or log-potential certificate in its statement.

The permitted analytic inputs are:

- `NguyenBottomSingularInput`, at a subgaussian bound at least one;
- `CookDeformedSquareInput`, specialized internally to the actual Rademacher family;
- `RademacherSection3UpstreamInputs`, containing precisely Proposition 3.2, Cook 1.12 and the two canonical BBV comparisons, with a common comparison constant. No BC12 estimate, finite Ginibre formula or Gaussian-law premise is a public field.

Section 4 is not an analytic input. Existing proved deterministic algebra and probability lemmas are reused from the repository; their directory names do not introduce new assumptions.

The reset argument integrates each capped loss before summing. Cook's slower error is therefore averaged, whereas Nguyen's exponentially small interface failures are union-bounded using `log N / W → 0`. The exact independent anchor contains `ceil(W^(1/200))` complete cells and a terminal packet. It is not the one-cell construction used elsewhere in the repository. Zero determinants are explicitly present in terminal bad events.

See `SOURCE_MAP.md` for the source-equation correspondence, `SECTION9_DEPENDENCY_AUDIT.md` for local terminal and interface reuse, and `SECTION10_REUSE_AUDIT.md` for the deterministic and circular-law reduction reuse.

Run these verification gates from the repository root. The build checks Section 8 and its necessary dependencies; the source scan, strict public axiom audit, and signature printout target Section 8.

```sh
python3 scripts/build_subgaussian.py --target BernoulliSection8
python3 scripts/check_axioms.py --audit-file Section8/AxiomAudit.lean
lake env lean Section8/PublicSignatureAudit.lean
python3 scripts/check_placeholders.py --path Section8
```

CI builds the two Section 8 targets in serial import order, preserving completed artifacts after failures. It audits the original endpoints and the Section 3 integration together. There is no whole-repository build.

The placeholder scan masks comments and strings. Its `--path` argument must name an existing repository directory containing Lean sources; an invalid path or empty scan fails. Without `--path`, the script retains its repository-wide scan. Section 8 verification uses the scoped commands above.
