# Terminal and arbitrary-frame small-ball formalization

This library formalizes the local small-ball proof constructions in
Sections 9.1–9.2 of [arXiv:2609.01295](https://arxiv.org/abs/2609.01295),
together with the interface-control argument for Lemma 7.1. The terminal
and arbitrary-frame statements are Proposition 7.3 and Theorem 7.10.

It shares the repository's Lean 4.33.0/mathlib toolchain and imports the
`BernoulliLinearAlgebra` library in this directory. No machine-specific
dependency path is needed.

```lean
import BernoulliSection9.Section9Results
```

## Public interfaces

All names below are in the `BernoulliSection9` namespace.

| Interface | Content |
| --- | --- |
| `paperStrongRRQRConclusion` | Complex coordinate pivot and skeleton construction, with proved polynomial exponent 16 |
| `section9TerminalSmallBall` | Terminal capped loss for every positive cap, zero probability, reverse estimate, and Parseval |
| `section9TerminalSmallBallConditional` | Terminal result for outside-measurable deformations independent of the fresh packet |
| `section9PhysicalTerminalSmallBall` | Transfer to the physical row normalization |
| `section9ArbitraryFrameSmallBall` | Arbitrary orthonormal frames with endpoint good data |
| `section9ArbitraryFrameSmallBallConditional` | Outside-measurable random frame/endpoint data |
| `section9InterfaceAndArbitraryFrameSmallBall` | Interface probability control and the frame conclusion on the interface good event |

The probability constants belong to explicit Cook and Nguyen input records.
Each record fixes its subgaussian parameter range; Cook additionally fixes
a positive profile interval. The estimate fields apply only within those
ranges. The terminal public interface uses the Cook record's bound directly,
and the two interface squares carry their Nguyen bounds explicitly.

RRQR selection, masks, complete iid-square restrictions, conditioning
sigma-fields, and CUR/Schur elimination are constructed internally. None is
a caller-provided certificate. The two approved probability estimates remain
explicit mathematical inputs, not custom axioms.

## Exact coverage

The terminal packet is the unit-entry-weight model. The source provides
explicit finite loss/failure expressions; it does not separately package
all conclusions into the paper's single-constant asymptotic displays.
The RRQR theorem proves exponent 16, whereas Lemma 9.1 states exponent 4.
The artificial-frame limits are established along `lambda_q = q + 1`.

See the [formula map](SMALL_BALL_FORMALIZATION_MAP.md),
[paper reference index](SMALL_BALL_REFERENCE_MAP.md), and
[trust-boundary and verification audit](SMALL_BALL_AUDIT.md) for precise
statements, implementation choices, and verification status.

## Verification

From the repository root:

```sh
lake build
lake env lean Section9/SmallBallAxiomAudit.lean
```

The audit file prints both external-input structures, the public signatures,
and the logical axioms of the principal constructions and conclusions.
