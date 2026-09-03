import ShortRingAnchor.Proposition38.BroadConnectivity
import ShortRingAnchor.Proposition38.Spread
import ShortRingAnchor.Proposition38.MatrixNormTail
import ShortRingAnchor.Proposition38.SingularScaling

/-!
# The two newly authorized external inputs for Proposition 3.8

These are predicates on supplied proofs, NOT asserted theorems and NOT
axioms. No inhabitant is defined in this project. The final theorem takes
them as explicit arguments. The previously declared BBV and BC12 boundary
is unchanged and remains visible in the final theorem as well.

* `Proposition32Input`: the repaired real-subgaussian full-block estimate,
  arXiv:2609.01295v1, Proposition 3.2. Constants may depend on the fixed atom
  and the fixed complex shift. For `m ≥ m_*`, `W ≥ m`, failure is bounded
  by `C / sqrt(3W)` at the floor `(3W)^(-25m)`.
* `Cook112Input`: Cook (2018), Theorem 1.12 / (1.21), specialized to real
  atoms and zero-one profiles, so the threshold parameter is `σ₀=1/2`.
  Arbitrary deterministic complex perturbations are retained. The norm
  guard is retained in the event. The spread and broad-connectivity
  certificates are required by this interface and proved internally.

There is deliberately no norm-free Cook input, no assumed invertibility,
no Section 8 high-band input, and no theorem named as though these two
literature conclusions had been proved here.
-/

noncomputable section
open MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace ShortRingAnchor.Proposition38

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [IsProbabilityMeasure μ] (A : Atom)

/-- **External hypothesis**: manuscript Proposition 3.2, for a fixed `z`.
The dimension-uniform constants are chosen before the block dimensions. -/
def Proposition32Input (z : ℂ) : Prop :=
  ∃ mStar : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (W s : ℕ) (hW : 0 < W), 4 ≤ s + 3 → mStar ≤ s + 3 → s + 3 ≤ W →
    ∀ S : AtomArray μ A (Fin ((s + 3) * W) × Fin ((s + 3) * W)),
      μ.real {sample | GinibreLSV.leastSingularValue (fullBlockMatrix S sample - z • 1) ≤
        (3 * (W : ℝ)) ^ (-(25 * ((s + 3 : ℕ) : ℝ)))} ≤ C / Real.sqrt (3 * (W : ℝ))

/-- **External hypothesis**: Cook 1.12 for zero-one profiles. The constant
depends only on the displayed fixed parameters, never on matrix size,
the particular mask, or the deterministic perturbation. -/
def Cook112Input : Prop :=
  ∀ κ δ ν K : ℝ, CookSpread A κ → 0 < δ → δ < 1 → 0 < ν → ν < 1 → 1 ≤ K →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (hn : 0 < n) (S : AtomArray μ A (Fin n × Fin n))
        (adj : Fin n → Fin n → Prop) [DecidableRel adj],
        BroadlyConnected adj δ ν →
        ∀ (B : Matrix (Fin n) (Fin n) ℂ) (t : ℝ), 0 ≤ t →
          μ.real {sample |
            GinibreLSV.leastSingularValue
              (maskedMatrix id adj (S.subgaussianSquare.rawMatrix sample) + B) ≤
                t / Real.sqrt n ∧
            ‖maskedMatrix id adj (S.subgaussianSquare.rawMatrix sample) + B‖ ≤
                K * Real.sqrt n} ≤ C * (t + 1 / Real.sqrt n)

end ShortRingAnchor.Proposition38
