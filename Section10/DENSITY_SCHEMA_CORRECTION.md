# Upstream density-record correction

This is a Lean definition error, not an error in the paper's density hypothesis.

## Observed issue

The active Section 3 source `section3/ShortRingAnchor/AtomAssumption21.lean`
used the undeclared identifier `top` in the field

```lean
bound_lt_top : bound < top
```

The independent cloud inspection at commit `24d5b29`,
[run 33715585984](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33715585984),
printed its actual type as

```lean
bound_lt_top : ∀ {top : ENNReal}, bound < top
```

This is not an implicit parameter of the record itself. It is a universally
quantified field. Taking `top = 0` contradicts nonnegativity of `bound`, so
the old record has no instances. Conditional theorems consuming that record,
including the corresponding density-alternative constructors, could pass
kernel checks without being applicable to any actual density. Their old
axiom audits alone do not establish the intended mathematical application.

## Minimal source correction

The active source now says `bound_lt_top : bound < (⊤ : ENNReal)`, and disables
`autoImplicit` locally for that structure. No mathematical assumption is added: this
restores the intended finite essential bound. Historical unused vendor
snapshots are left unchanged; root Lake selects the corrected `section3/`.

`BernoulliSection10Source.DensitySchemaAudit` now constructs the record from
an arbitrary density and the ordinary hypothesis `K < ∞`. The RN adapter
constructs a representative from literal measure domination. The concrete
Gaussian model must also construct its actual bounded-density instance.
These construction checks supplement printed signatures and kernel-axiom
audits; none can be replaced by an axiom allowlist alone.

## Single shared correction

The Section 6 and Section 10 tasks agreed to use exactly one independent
correction: [`5c7be7bf2bd843ccdbfb45fdc0144e3dc7163278`](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/commit/5c7be7bf2bd843ccdbfb45fdc0144e3dc7163278),
on `codex/shared-density-definition-fix`, based on `42c26b6`. It changes only
`section3/ShortRingAnchor/AtomAssumption21.lean`; it contains no Section 6,
Section 10 or Proposition 3.8 integration. Section 10 incorporates it in
merge commit `a562be3` and updates its own source manifest separately.

The canonical file has 7643 bytes and SHA-256
`f96c9a78fb9c59b098e3207da87c6a7e0abbecb46cf934a5d652478163dfe7d5`.
It is byte-identical to the corrected file already used by the Section 6
task. The earlier Section 10 spelling `bound < ⊤` inferred the same ENNReal
type; its file-wide implicit-parameter guard is now narrowed to the record.
The canonical normalization passed its independent Section 3 build and
audit in [run 33718453418](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33718453418)
at `a562be3`. Its Section 10 downstream check passed in run `33719162307`
at `362c47f`, including the construction regression and final signatures.
It does not introduce a new mathematical assumption.

## Verification status

In [run 33715880853](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33715880853)
at `18178ad`, the corrected `AtomAssumption21`, its dependent density and law
adapters, `DensityRepresentative`, and the literal `GaussianReferenceModel`
compiled. The actual Gaussian density record is therefore now constructed.
The preliminary schema-print step ran before rebuilding that dependency and
loaded its old cached artifact; CI now explicitly builds the schema target
before doing a fresh print. That failed preliminary print is not evidence
about the corrected definition. The remaining source-stage failures were
real/complex function transport and equivalent rational-exponent syntax.

The correction and affected dependencies, both Section 10 endpoints, and
the scoped final audits passed run `33719162307`. The user explicitly replaced
the earlier whole-root check with Section 10-only verification. No local compilation
of this integration has been run. Previously verified direct planar-LSV
estimates use measure domination rather than this record; the scoped build
also validated their affected imports.

In [run 33716279954](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33716279954)
at `09add1a`, the schema target was built before the independent fresh print.
The ordinary finite-bound construction regression passed, and the printed
field uses actual infinity with no extra `{top}` quantifier. The shared
`FullBlockLogLimit` source theorem also compiled. The subsequent successful
scoped run `33719162307` checked the complete real/complex endpoints and all
492 Section 10 axiom reports. No whole-repository verification is claimed.
