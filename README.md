# Random band circular law — Lean formalization

Lean 4 formalization accompanying Yi Han's paper
[*The circular law for non-Hermitian random band matrices: optimal bandwidth,
periodic profile and discrete law*](https://arxiv.org/abs/2609.01295).

This is a paper-wide repository. It contains **Section 4,
“Exterior transfer and local density tools”**, **Section 5**, **Section 8 for
real IID subgaussian atoms**, **Section 9 libraries for deterministic linear
algebra and local small-ball arguments**, and **the Section 10 bounded-density
circular-law proofs for real and planar-complex IID atoms**.
References in the Section 9 and 10 libraries use
[arXiv:2609.01295v1](https://arxiv.org/abs/2609.01295v1).
Section 3 has an independent [Proposition 3.6 subproject](section3/README.md),
with actual Hermitization counting and the copied high-band Theorem 3.1.
Its [integration and verification record](section3/HIGH_BAND_INTEGRATION.md)
states the exact BBV/BC12 and real-branch geometric Brascamp–Lieb boundary.
Section 5 has its own [subproject and verification record](section5/README.md).
The included Section 6 helper modules do not claim completion of Section 6.

## Scope and status

Section 8 proves the logarithmic-potential limit and circular law for every
fixed real IID law with mean zero, second moment one, and a finite subgaussian
MGF parameter, under `W → ∞` and `W/log N → ∞`, where `N=(s+3)W`.
Cook, Nguyen, and Section 3 Proposition 3.8 remain explicit external inputs.
The general theorem is
`SubgaussianSection8.section8_subgaussian_circular_law`; its proof requires no
bounded-support, symmetry, or density hypothesis. The Rademacher proof remains
available in `Section8/BernoulliSection8`. See the
[general Section 8 overview](SubgaussianSection8/README.md),
[proof and verification map](SubgaussianSection8/STATUS.md), and
[Rademacher overview](Section8/README.md).

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

Section 10 covers the real and planar-complex IID bounded-density,
finite-third-moment branches of Proposition 10.1 through Proposition 10.10,
equations 10.30–10.57, and the circular-law conclusion of Theorem 2.10.
Use `BernoulliSection10Source.real_density_circular_law` or
`BernoulliSection10Source.planar_density_circular_law`.

Both endpoints connect the actual Section 3 proofs internally. Only BBV,
BC12, and (for real atoms only) geometric Brascamp–Lieb remain as explicit
literature inputs, alongside the original model assumptions. No caller
Section 3, high-band, LSV, counting or model certificate remains. Tao–Vu is
a proved source dependency. The shared density-definition correction
`5c7be7b` is included; it repairs a Lean-only implicit-variable error.

[Scoped cloud verification](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33719162307)
passed at `362c47f`: all three Section 10 targets with their actual imports,
207 chapter source files, 492 exact axiom reports and the final printed
signatures. This is not a new whole-repository verification claim.
Directional conditional-density and heterogeneous-law extensions of
10.2–10.3 are not claimed. See the
[Section 10 overview](Section10/README.md),
[exact source and scope map](Section10/FORMALIZATION_MAP.md), and
[source-connection build and axiom audit](Section10/SOURCE_CONNECTION_AUDIT.md).
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
section3/                      # standalone Proposition 3.6; own Lake project and CI
section5/                      # Section 5 subproject; see its own README
Section8/
  BernoulliSection8.lean      # Rademacher specialization
  BernoulliSection8/          # proof modules and shared Section 8 lemmas
  README.md
SubgaussianSection8.lean       # general real-IID subgaussian public import
SubgaussianSection8/
  Results.lean               # final log-potential and circular-law theorems
  README.md
  STATUS.md
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
  BernoulliSection10Complex/   # actual planar-complex density proof
  BernoulliSection10Source/    # concrete Section 3 connections and final endpoints
  README.md
  FORMALIZATION_MAP.md
  AUDIT.md
  ASSUMPTIONS.md
  PROVENANCE.md
  SOURCE_CONNECTION_AUDIT.md
  verification/               # durable scoped audit records and signatures
vendor/
  tao-vu-replacement/          # 13 proved modules, pinned provenance/license
  short-ring-analysis/        # 30 proved generic modules, SHA-256 manifest
```

The root libraries use the same Lake project and dependency cache. Section 5
is a subproject that depends on this root project and shares its mathlib
package directory; see [its build instructions](section5/README.md).
Section 3 is a separate, pinned Lake package: build it from `section3/`.
Its dedicated verification passed for all 230 Lean files, normal `lake build`,
and 271 axiom reports covering 260 declarations; see
[the verified Section 3 run](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33702782802).
The documented BBV/BC12 and real-branch geometric BL hypotheses remain explicit.

## Build

All commands below run from the repository root, with Lean managed by `elan`.
The toolchain is pinned to `leanprover/lean4:v4.33.0`; mathlib is pinned by the
manifest to `db584cd6d46c92f209a44c0f1c829460d327499d` (tag `v4.33.0`).

```sh
git clone --branch main https://github.com/hanyi162013-Yihan/random-band-circular-law-lean.git
cd random-band-circular-law-lean
# On a new machine, this downloads the mathlib compiled cache (potentially large).
# Skip it if the matching dependencies and compiled cache are already available.
lake exe cache get
# Build only Section 8 and its actual imports.
lake build SubgaussianSection8

# Optional: build the Rademacher specialization.
lake build BernoulliSection8

# Optional: build only the deterministic Section 9 library.
lake build BernoulliLinearAlgebra
# Optional: build the local small-ball proof chains and their dependencies.
lake build BernoulliSection9

# Optional: build the real/planar Section 10 proofs and their actual imports.
lake build BernoulliSection10 BernoulliSection10Complex BernoulliSection10Source
```

The completed Section 10 proof and its required dependencies are integrated
into `main`. The original `section10-asymptotic-completion` branch remains
available as the reviewed completion snapshot. For an immutable verification
snapshot, check out the full source commit recorded in
[Section10/SOURCE_CONNECTION_AUDIT.md](Section10/SOURCE_CONNECTION_AUDIT.md).

Only source and documentation are committed. Lean, mathlib, `.lake/`, compiled
objects, scratch files, and local filesystem paths are not part of the release.
The cache download is not needed merely to read or download the source.
Do not run `lake update` for routine checking: the committed manifest records
the dependency versions used for this release.

For a memory-constrained machine, serialize the Section 8 import closure:

```sh
python3 scripts/check_axioms.py --self-test
python3 scripts/check_placeholders.py --path SubgaussianSection8
python3 scripts/build_subgaussian.py --target SubgaussianSection8
python3 scripts/check_axioms.py --audit-file SubgaussianSection8/AxiomAudit.lean
lake env lean SubgaussianSection8/PublicSignatureAudit.lean
```

Python 3.11 or newer is required. This serial builder checks only the selected
import closure, then runs the normal `lake build SubgaussianSection8` target.
The closure contains zero Section 4 modules. Existing `.lake` artifacts are
reused by Lake. The source scan also supports archives without Git metadata.

### Automated verification

Section 10 verification is limited to its three explicit library targets
and their real import dependencies. Its workflow retains the chapter source
scan, density-construction regression, final parameter checks, and all 492
chapter axiom reports. It does not automatically rebuild unrelated chapters
or invoke a whole-root audit. The verified integration run is
[33719162307](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33719162307).

The [general Section 8 verification run](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33688229894/job/100440674643)
passed at proof-source commit `d29fd6f0cefcaa4ec3afe09f14c54df3e16842d4`:
32 new modules, the normal `lake build SubgaussianSection8`, 34 extension
files without placeholders, 13 strict axiom reports, and compiled public
signatures. All reported axioms were `propext`, `Classical.choice`, or
`Quot.sound`. The [Rademacher baseline run](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33677989986/job/100407373237)
also passed independently. These checks cover the documented Section 8
scope; they do not claim completion of the entire paper.

The `General subgaussian Section 8` workflow runs for pull requests or manual
dispatch. It restores compiled artifacts and builds only Section 8 and its
required imports. Section 5 retains its independent workflow. Routine
Section 8 verification does not require a complete repository build.

The [complete Section 10 verification run](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33620303116)
passed for source commit `1cb4a34cd6867cda79b26a9c8e4bded4cdabb515` on
2026-09-02: **373** library modules, the complete default `lake build`,
**381** Lean files in the placeholder scan, and **857** axiom reports across
**11** audit files. The clean job took **35 minutes 13 seconds**, including
toolchain/cache setup and audits. See [Section10/AUDIT.md](Section10/AUDIT.md)
for exact scope, the final printed signature, and the earlier baseline record.

The Section 10 run above is a historical full-build record, not a requirement
to repeat all chapters for Section 8 changes. A successful job verifies its
checked source, not arbitrary later edits or completeness of the paper
translation. Axiom reports must match their audit declarations and use only
the three standard Lean foundations listed above.

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
