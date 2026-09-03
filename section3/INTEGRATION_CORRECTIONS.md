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

`section6/CircularLawSection6/PublishedGaussianDensity.lean` constructs the
record for the actual circular Gaussian law, with bound 2. Two regression
examples check the constructor and its precise finiteness field. The
corrected imported dependency and its Section 5/6 consumers must be checked
again in cloud CI; the earlier 122-module green run predates this correction.
