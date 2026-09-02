# Section 9 small-ball audit

Reference: Yi Han, *The circular law for non-Hermitian random band matrices:
optimal bandwidth, periodic profile and discrete law*,
[arXiv:2609.01295](https://arxiv.org/abs/2609.01295).
The local statements are in Section 7; their technical proofs are in Section 9.

## Verification status

Publication preparation is in progress, using Lean 4.33.0 and the
repository's pinned mathlib dependency.

| Check | Result |
| --- | --- |
| `ExternalInputs.lean` standalone Lean elaboration | Passed; unused-variable warnings only |
| `lake build BernoulliSection9.ExternalInputs` | Passed (3150 build jobs, including cached dependencies) |
| Subgaussian/profile bounds at all five direct literature-estimate calls | Source review passed |
| Caller-facing bounds and square-restriction propagation | Source review passed; compilation pending |
| Placeholder/custom-axiom scan of small-ball Lean sources | Passed |
| Current-paper numbering and machine-local-path scans | Passed |
| Full repository build | Pending |
| Public-theorem `#print axioms` audit for this source tree | Pending |

The module checks are not reported as a full library build. Neither source
review nor a placeholder scan replaces Lean checking of the complete call chain.

## Explicit mathematical inputs

`ExternalInputs.lean` contains the two literature-input structures. They
are theorem parameters, not project axioms.

- `CookDeformedSquareInput` fixes `subgaussianBound`, `lowerWeight`, and
  `upperWeight`. The profile interval is positive and contains `1`, the
  profile used in the terminal packet. Its constants `beta L`, `cookC L`,
  and `cookc L` may depend on these fixed parameters as well as `L`.
  Both estimate fields require the supplied square's subgaussian parameter
  to be at most `subgaussianBound`, and each profile weight to lie in the
  fixed interval. The conditional field also requires the deformation's
  measurability, the stated sigma-field independence, and its almost-everywhere
  norm bound, as in Lemma 9.2.
- `NguyenBottomSingularInput` fixes a `subgaussianBound`. Its fixed-index
  and overcrowding fields are required only for squares in this range.
  Thus their constants may depend on that bound. Each application supplies
  the square's bound explicitly.

Injective reindexing and square restriction preserve the subgaussian
parameter. The two Cook applications therefore use bounds derived from the
packet's input bound. Both interface squares separately satisfy the Nguyen
bound. No caller supplies a mask, elimination, or RRQR certificate.

Kernel axiom inspection checks logical dependencies; the parameter ranges
above are separately inspected for mathematical agreement with the paper.

## Deterministic RRQR scope

The finite maximum-Gram-volume construction and complex min-max,
compression, and multiplication singular-value inequalities are internal
proofs. The output includes the exact threshold count, equal-cardinality
coordinate sets, literal pivot, empty-pivot convention, exact skeleton/CUR
identities, and polynomial singular-value/norm comparisons.

The proved exponent is `strongRRQRExponent = 16` for `n >= 2`, `tau >= 1`.
Lemma 9.1 states exponent `4`. The formal theorem is a sufficient polynomial
variant, not the literal exponent-4 statement. Terminal width thresholds
use the proved exponent throughout.

## Terminal and arbitrary-frame scope

The source constructs the masks, two disjoint complete iid squares,
conditioning sigma-fields, truncations, CUR/Schur reduction, determinant
lower bounds, coefficient comparisons, and conditional final-output
measurability internally.

- `t = W` fixes the exposure/reverse-event failure parameter. The capped
  conclusion still quantifies over every cap `T > 0`.
- Losses and failure probabilities are explicit finite expressions. A
  separate theorem collecting them into the exact single-`C,c` asymptotic
  display (7.19) is not claimed.
- The public terminal packet has deterministic entry weights equal to one,
  as in the main model. The optional general weighted-packet variant is not
  a public theorem here.
- The standalone frame theorem retains `PaperEndpointGood`; the
  interface-combined theorem constructs it on the interface good event.
- Random-parameter conclusions require outside measurability and
  independence. Fixed-parameter conclusions do not authorize substitution
  of dependent random data without those hypotheses.
- The exterior-degree, coefficient, value, and graph-volume limits are
  proved along the cofinal sequence `lambda_q = q + 1`. Operator-norm
  convergence is explicit; the rates in (9.51)-(9.52) are not separately
  packaged as quantitative inequalities.
- Terminal reverse estimates and Parseval are present. Fiberwise Parseval
  needs no global random-parameter moment hypothesis; the optional
  conditional-expectation formulation requires integrability.

## Proof details represented explicitly

The norm-truncation and second-Schur arguments (9.29)-(9.34) are implemented
with a hard norm cutoff and a cutoff of the whole second deformation. These
give the required agreement on the good event and the global polynomial
norm bounds; they are not literal copies of the radial cutoff or the
separately truncated inverse in (9.29) and (9.31). The square-size comparison
uses `W <= 4 n_i`. Conditional lifting is based on the final-output
measurability/Fubini argument following (9.43), so it does not require a
measurable RRQR selector.

The width thresholds explicitly enforce large-width and Nguyen cutoff
conditions. The passage from entrywise exterior limits to operator-norm
limits is also proved.

## Publication checks

1. Compile all changed probability-input applications and caller-facing
   signatures.
2. Integrate the `BernoulliLinearAlgebra` library under `Section9` as a
   repository-local dependency.
3. Run the full repository build and
   `lake env lean Section9/SmallBallAxiomAudit.lean`.
4. Scan the publication files for placeholders, incorrect paper references,
   machine-local paths, secrets, build caches, and unintended changes to
   existing repository libraries.
5. Record the actual results before publishing.
