# Random band circular law — Lean formalization

Lean 4 formalization accompanying Yi Han's paper
[*The circular law for non-Hermitian random band matrices: optimal bandwidth,
periodic profile and discrete law*](https://arxiv.org/abs/2609.01295).

This is a paper-wide repository. Its first source release contains **Section 4,
“Exterior transfer and local density tools”**. Sections 5–6 and their interfaces
are planned additions; they are not included or claimed as proved in this release.

## Scope and status

The Section 4 library contains 104 modules, with proof chains corresponding to
the nine named results in Section 4: row-linearity, the periodic
determinant identity, singleton-domain words, isolated full monomials,
multiaffine small-ball bounds, fresh closure, projective observability,
operator-affine logarithmic estimates, and pressure concentration.

See the [coverage and assumption map](Section4/FORMALIZATION_MAP.md) for exact
Lean entry points, retained hypotheses, intermediate interfaces, and manuscript
corrections. The [detailed Section 4 overview](Section4/README.md) is in Chinese.

This release does **not** assert a full formalization of the paper.
Coverage is stated at the level of the named proof chains; exact formulations,
constants, and hypotheses are documented in the Lean statements and coverage map.

Formal theorem statements are authoritative. Probability-law assumptions
(including normalization, independence, density or directional conditional
density, second moments, positive weights, and required nondegeneracy) remain
explicit theorem parameters. Legacy conditional APIs are retained alongside
the final paper-specific theorems; the presence of an interface theorem alone
does not establish an unconditional result.

No `sorry`, `admit`, or custom axioms occur in the released Lean sources.
The audit files print the dependencies of selected public theorems. Standard
Lean foundational axioms such as `propext`, `Classical.choice`, and `Quot.sound`
are not manuscript assumptions.

## Repository layout

```text
lakefile.toml                   # one Lake project and one mathlib dependency
lake-manifest.json              # exact dependency revisions
lean-toolchain                 # Lean 4.33.0
Section4/
  CircularLawSection4.lean      # public umbrella import
  CircularLawSection4/          # 104 proof modules; existing imports preserved
  *AxiomAudit.lean              # six audit entry points
  README.md
  FORMALIZATION_MAP.md
```

Later chapters can be added as libraries with their own source directories in
the same Lake project. They can import Section 4 directly and use the same
dependency cache; there is no need for a separate mathlib checkout per chapter.

## Build

All commands below run from the repository root, with Lean managed by `elan`.
The toolchain is pinned to `leanprover/lean4:v4.33.0`; mathlib is pinned by the
manifest to `db584cd6d46c92f209a44c0f1c829460d327499d` (tag `v4.33.0`).

```sh
git clone https://github.com/hanyi162013-Yihan/random-band-circular-law-lean.git
cd random-band-circular-law-lean
# On a new machine, this downloads the mathlib compiled cache (potentially large).
# Skip it if the matching dependencies and compiled cache are already available.
lake exe cache get
lake build
```

Only source and documentation are committed. Lean, mathlib, `.lake/`, compiled
objects, scratch files, and local filesystem paths are not part of the release.
The cache download is not needed merely to read or download the source.
Do not run `lake update` for routine checking: the committed manifest records
the dependency versions used for this release.

## Audit

After building:

```sh
lake env lean Section4/AxiomAudit.lean
lake env lean Section4/AssumptionFreeAxiomAudit.lean
lake env lean Section4/CompanionAxiomAudit.lean
lake env lean Section4/FlatAxiomAudit.lean
lake env lean Section4/FourGapsAxiomAudit.lean
lake env lean Section4/Section4CompleteAxiomAudit.lean
```

These audits supplement kernel checking; they are not a proof that an informal
paper statement has been translated faithfully. Review the theorem statements
and the coverage map when citing a particular result.

## Paper and licensing

Please cite the [paper](https://arxiv.org/abs/2609.01295) when referring to its
mathematical results, and include this repository's commit when referring to a
specific formalization snapshot.

No repository license has been selected for this initial publication.
Lean and mathlib retain their own licenses and are not vendored here.
