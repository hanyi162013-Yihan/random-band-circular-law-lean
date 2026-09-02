# Random band circular law — Lean formalization

Lean 4 formalization accompanying Yi Han's paper
[*The circular law for non-Hermitian random band matrices: optimal bandwidth,
periodic profile and discrete law*](https://arxiv.org/abs/2609.01295).

This is a paper-wide repository. It contains **Section 4,
“Exterior transfer and local density tools”**, **Section 9 libraries for
deterministic linear algebra and local small-ball arguments**, and
**the Section 10 bounded-density circular-law proof for real i.i.d. atoms**.
References in the Section 9 and 10 libraries use
[arXiv:2609.01295v1](https://arxiv.org/abs/2609.01295v1).
Sections 5–6 are not included or claimed as proved here.

## Scope and status

The Section 4 library contains 104 modules, with proof chains corresponding to
the nine named results in Section 4: row-linearity, the periodic
determinant identity, singleton-domain words, isolated full monomials,
multiaffine small-ball bounds, fresh closure, projective observability,
operator-affine logarithmic estimates, and pressure concentration.

See the [coverage and assumption map](Section4/FORMALIZATION_MAP.md) for exact
Lean entry points, retained hypotheses, intermediate interfaces, and manuscript
corrections. The [detailed Section 4 overview](Section4/README.md) is in Chinese.

The Section 9 library covers the algebraic proof chains in §9.1.3 and
§9.3–9.5: the raw unit-entry-weight finite-constant core of Lemma 7.5,
the Block Floquet identity of Lemma 7.6, Proposition 9.3, Corollary 9.4,
Jacobi/Hodge identities, and the deterministic boundary comparison underlying
Lemma 7.7. It also proves the exterior-operator comparison in Lemma 7.8.
It does not claim the full weighted-profile or uniform asymptotic estimates of
Lemmas 7.5 and 7.7. See the [Section 9 overview](Section9/README.md),
[coverage map](Section9/FORMALIZATION_MAP.md), and
[paper reference map](Section9/PAPER_REFERENCES.md).
The Section 9 library introduces no Cook, Nguyen, or RRQR axiom.

The `BernoulliSection9` library contains 75 modules for interface control,
the terminal packet, and the arbitrary-frame deduction in §§9.1–9.2.
Cook and Nguyen estimates are explicit inputs with fixed subgaussian ranges;
Cook also fixes the profile bounds. The public signatures use those ranges
directly. RRQR and the two-square/CUR constructions are proved internally.
The RRQR exponent is 16 (Lemma 9.1 states 4), and small-ball losses and failure
bounds are supplied as explicit finite expressions. See the
[small-ball overview](Section9/SMALL_BALL_README.md),
[formula map](Section9/SMALL_BALL_FORMALIZATION_MAP.md), and
[verification audit](Section9/SMALL_BALL_AUDIT.md). The integrated build and
public-theorem axiom audits passed on 2026-09-02; this verifies the documented
formal scope, not a complete translation of every paper statement.

The Section 10 library contains 111 Lean source files: 107 mathematical
modules, three audit modules, and its umbrella import. It covers the real IID
specialization of Proposition 10.1 through Proposition 10.10, equations
10.30–10.57, and the final circular-law conclusion of Theorem 2.10. The public
endpoint is `BernoulliSection10.density_circular_law`.

The final theorem retains only the original real-IID bounded-density,
finite-third-moment model assumptions and the exact permitted Section 3
statements (3.1, 3.3, 3.4, 3.5). The full-block high-band limit, actual
pressure/reset/seam/remainder assembly, and reference ensemble are proved
internally. Tao–Vu is a proved source dependency, not an extra assumption.
The clean full-repository build and all 857 axiom reports have passed;
Section 10 contributes 446 reports, including its 343-report completion audit.
The exact verification record is in the chapter audit. Planar-complex/directional-density atoms and
the heterogeneous-law generality of 10.2–10.3 are not claimed. See the
[Section 10 overview](Section10/README.md),
[exact source and scope map](Section10/FORMALIZATION_MAP.md), and
[build and axiom audit](Section10/AUDIT.md).
The [explicit assumption list](Section10/ASSUMPTIONS.md) and
[proof provenance](Section10/PROVENANCE.md) document the final trust boundary.

This release does **not** assert a full formalization of the paper.
Coverage is stated at the level of the named proof chains; exact formulations,
constants, and hypotheses are documented in the Lean statements and coverage map.

Formal theorem statements are authoritative. Probability-law assumptions
(including normalization, independence, density or directional conditional
density, second moments, positive weights, and required nondegeneracy) remain
explicit theorem parameters. General conditional APIs are provided alongside
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
Section9/
  BernoulliLinearAlgebra.lean   # public umbrella import
  BernoulliLinearAlgebra/       # deterministic proof modules; imports preserved
  BernoulliSection9.lean        # small-ball public umbrella import
  BernoulliSection9/            # 75 interface/terminal/frame proof modules
  AxiomAudit.lean
  SmallBallAxiomAudit.lean
  README.md
  FORMALIZATION_MAP.md
  PAPER_REFERENCES.md
  SMALL_BALL_*.md
Section10/
  BernoulliSection10.lean      # arXiv v1 numbering; public umbrella import
  BernoulliSection10/          # 107 mathematical modules and three audits
  README.md
  FORMALIZATION_MAP.md
  AUDIT.md
  ASSUMPTIONS.md
  PROVENANCE.md
vendor/
  tao-vu-replacement/          # 13 proved modules, pinned provenance/license
  short-ring-analysis/        # 30 proved generic modules, SHA-256 manifest
```

All libraries use the same Lake project and dependency cache. Later chapters
can be added with their own source directories and can import these libraries;
there is no need for a separate mathlib checkout per chapter.

## Build

All commands below run from the repository root, with Lean managed by `elan`.
The toolchain is pinned to `leanprover/lean4:v4.33.0`; mathlib is pinned by the
manifest to `db584cd6d46c92f209a44c0f1c829460d327499d` (tag `v4.33.0`).

```sh
git clone --branch section10-asymptotic-completion https://github.com/hanyi162013-Yihan/random-band-circular-law-lean.git
cd random-band-circular-law-lean
# On a new machine, this downloads the mathlib compiled cache (potentially large).
# Skip it if the matching dependencies and compiled cache are already available.
lake exe cache get
lake build

# Optional: build only the deterministic Section 9 library.
lake build BernoulliLinearAlgebra
# Optional: build the local small-ball proof chains and their dependencies.
lake build BernoulliSection9

# Optional: build the complete real-IID Section 10 proof and its dependencies.
lake build BernoulliSection10
```

The completion is published on `section10-asymptotic-completion`; the clone
command selects that branch explicitly rather than the earlier `main`
snapshot. For an immutable verification snapshot, check out the full source
commit recorded in [Section10/AUDIT.md](Section10/AUDIT.md).

Only source and documentation are committed. Lean, mathlib, `.lake/`, compiled
objects, scratch files, and local filesystem paths are not part of the release.
The cache download is not needed merely to read or download the source.
Do not run `lake update` for routine checking: the committed manifest records
the dependency versions used for this release.

For a memory-constrained machine, serialize project modules and run all checks:

```sh
python3 scripts/check_axioms.py --self-test
python3 scripts/check_placeholders.py
python3 scripts/build_serial.py
python3 scripts/check_axioms.py
```

Python 3.11 or newer is required. The serial builder checks every declared
library module, then runs the complete default `lake build`. The source scan
also supports source-only archives without Git metadata.

### Automated verification

The [complete Section 10 verification run](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33620303116)
passed for source commit `1cb4a34cd6867cda79b26a9c8e4bded4cdabb515` on
2026-09-02: **373** library modules, the complete default `lake build`,
**381** Lean files in the placeholder scan, and **857** axiom reports across
**11** audit files. The clean job took **35 minutes 13 seconds**, including
toolchain/cache setup and audits. See [Section10/AUDIT.md](Section10/AUDIT.md)
for exact scope, the final printed signature, and the earlier baseline record.

The `Lean verification` GitHub Actions workflow runs on pushes and pull requests,
and can also be started manually. It installs the pinned Lean toolchain,
downloads the matching mathlib cache, builds every library, and checks all
`*AxiomAudit.lean` entry points. Axiom reports must match their audit declarations
and use only `propext`, `Classical.choice`, and `Quot.sound`; a Lean error or an
unexpected dependency fails the job. The workflow also scans for proof
placeholders and project axioms.

Verification uses a standard GitHub-hosted Ubuntu runner, with no paid larger
runner, GitHub build-cache storage, or uploaded build artifacts. Modules are
built in dependency order to bound peak memory, followed by a complete
`lake build`. A successful job verifies the checked commit, not later edits or
the completeness of the paper translation. Submit changes on a verification
branch and review the successful check before merging into `main`.

## Audit

After building:

```sh
lake env lean Section4/AxiomAudit.lean
lake env lean Section4/AssumptionFreeAxiomAudit.lean
lake env lean Section4/CompanionAxiomAudit.lean
lake env lean Section4/FlatAxiomAudit.lean
lake env lean Section4/FourGapsAxiomAudit.lean
lake env lean Section4/Section4CompleteAxiomAudit.lean
lake env lean Section9/AxiomAudit.lean
lake env lean Section9/SmallBallAxiomAudit.lean
lake env lean Section10/BernoulliSection10/AxiomAudit.lean
lake env lean Section10/BernoulliSection10/AsymptoticAxiomAudit.lean
lake env lean Section10/BernoulliSection10/CompletionAxiomAudit.lean
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
The proved Tao–Vu source dependency preserves its upstream Apache-2.0 license
under `vendor/tao-vu-replacement/`.
