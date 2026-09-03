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

The active source now says `bound_lt_top : bound < ⊤`, and disables
`autoImplicit` in that module. No mathematical assumption is added: this
restores the intended finite essential bound. Historical unused vendor
snapshots are left unchanged; root Lake selects the corrected `section3/`.

`BernoulliSection10Source.DensitySchemaAudit` now constructs the record from
an arbitrary density and the ordinary hypothesis `K < ∞`. The RN adapter
constructs a representative from literal measure domination. The concrete
Gaussian model must also construct its actual bounded-density instance.
These construction checks supplement printed signatures and kernel-axiom
audits; none can be replaced by an axiom allowlist alone.

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

The correction is on the working branch and requires fresh cloud compilation
of its affected dependencies, both Section 10 endpoints, the complete root
build, and all final audits before publication to main. No local compilation
of this integration has been run. Previously verified direct planar-LSV
estimates use measure domination rather than this record; they will still be
rebuilt because their imports are affected.
