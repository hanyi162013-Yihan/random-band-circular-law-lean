# Section 6 integration correction — 2026-09-03

The Section 6 development branch was initially an exact copy of main's
Section 3 source at `42c26b672faec82a8ea7999a9cd0778c31618495`.
Its source manifest preserves the imported snapshot entries except for the
corrected `AtomAssumption21.lean`, whose size and hash are updated explicitly.
The original file had SHA256
`4c2184cd8bb5a135f334d095d4ba3565d504c641f3f59e080a102fb252909b16`.

Actual Gaussian-model instantiation exposed a source-definition error in
`ShortRingAnchor/AtomAssumption21.lean`:

```lean
bound_lt_top : bound < top
```

Lean auto-implicitly generalized the unbound identifier `top`. Consequently
the field required `forall {top : ENNReal}, bound < top`, an impossible
condition, not the intended finite upper bound. Conditional theorems can
compile with that premise; this does not establish its satisfiability.

With the user's approval, this branch corrects the field to
`bound < (⊤ : ENNReal)` and disables auto-implicit variables for this
structure. No mathematical bound or literature premise is added. Main is
not modified by this integration branch.

The unique shared source is commit
`5c7be7bf2bd843ccdbfb45fdc0144e3dc7163278` on
`codex/shared-density-definition-fix`, based directly on `42c26b6`.
It changes only this definition file; Section 6 and Section 10 reuse it.
The file is byte-identical to this branch's already-corrected version:
7643 bytes, SHA256
`f96c9a78fb9c59b098e3207da87c6a7e0abbecb46cf934a5d652478163dfe7d5`.
No second edit to the field is necessary when incorporating that commit.

`section6/CircularLawSection6/PublishedGaussianDensity.lean` constructs the
record for the actual circular Gaussian law, with bound 2. Two regression
examples check the constructor and its precise finiteness field. The
corrected imported dependency, concrete constructor, and existing Section 5/6
entry points compiled in run `33717315989`; that run failed later in an
unrelated new Section 6 reindexing proof. The complete build, audit and new
regressions still require a green run. The earlier 122-module green run
predates this correction.
