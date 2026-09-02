import BernoulliLinearAlgebra.ThreeBlockMatchingSurjective
import BernoulliLinearAlgebra.ThreeBlockInvalidZero
import BernoulliLinearAlgebra.GramVolumeReindex
import Mathlib.Tactic

/-!
# The actual zero-shift three-block terminal comparison

The full squarefree coefficient norm is first reduced to valid matchings,
using the vanishing of invalid coefficients.  Valid matching coefficients
have exactly the norms of their complementary minors, and the matching-to-
minor map is onto.  A coarse fiber bound by the total number of valid
matchings then gives a completely concrete `TerminalCoefficientComparison`.
-/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix Set Set.powersetCard

section ValidEnergy

variable {w : Type*} [Fintype w] [DecidableEq w] [LinearOrder w]

local instance threeBlockZeroComparisonVariableDecidableEq :
    DecidableEq (ThreeBlockVariable w) := Classical.decEq _

local instance threeBlockZeroOuterLinearOrder :
    LinearOrder (ThreeBlockOuter w) :=
  LinearOrder.lift'
    (fun x : ThreeBlockOuter w => (toLex x : Bool ×ₗ w))
    toLex.injective

/-- Unit virtual weights on genuine valid matchings. -/
def threeBlockValidUnitWeight (_a : ValidThreeBlockMatching w) : ℂ := 1

/-- A concrete finite certificate for valid matchings.  The only loss is
the deliberately coarse bound by the total number of valid matchings. -/
def threeBlockValidMaskCertificate :
    MaskExpansionCertificate
      (threeBlockMatchingMinorIndex : ValidThreeBlockMatching w →
        SquareMinorIndex (ThreeBlockOuter w))
      threeBlockValidUnitWeight where
  lowerWeight := 1
  upperWeight := 1
  fiberBound := Fintype.card (ValidThreeBlockMatching w)
  lowerWeight_nonneg := by norm_num
  upperWeight_nonneg := by norm_num
  onto := threeBlockMatchingMinorIndex_surjective
  weight_lower := by intro a; simp [threeBlockValidUnitWeight]
  weight_upper := by intro a; simp [threeBlockValidUnitWeight]
  fiber_card_le := by
    intro b
    simpa using Finset.card_filter_le
      (Finset.univ : Finset (ValidThreeBlockMatching w))
      (fun a => threeBlockMatchingMinorIndex a = b)

omit [LinearOrder w] in
/-- The squared energy over all squarefree masks is exactly the energy over
the valid matching subtype. -/
theorem threeBlockFullCoefficientEnergy_eq_validEnergy
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ) :
    (∑ S : Finset (ThreeBlockVariable w),
        ‖threeBlockDetCoefficient Q 0 S‖ ^ 2) =
      ∑ a : ValidThreeBlockMatching w,
        ‖threeBlockValidCoefficient Q a‖ ^ 2 := by
  classical
  let g : Finset (ThreeBlockVariable w) → ℝ := fun S =>
    ‖threeBlockDetCoefficient Q 0 S‖ ^ 2
  have hfilter :
      (∑ S ∈ Finset.univ.filter IsValidThreeBlockMatching, g S) =
        ∑ S ∈ (Finset.univ : Finset (Finset (ThreeBlockVariable w))), g S := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hSuniv hSnot
    have hnotValid : ¬IsValidThreeBlockMatching S := by
      intro hvalid
      exact hSnot (Finset.mem_filter.mpr ⟨hSuniv, hvalid⟩)
    simp [g, threeBlockDetCoefficient_zero_of_not_valid Q S hnotValid]
  have hvalidSubtype :
      (∑ S ∈ Finset.univ.filter IsValidThreeBlockMatching, g S) =
        ∑ a : ValidThreeBlockMatching w, g a.1 := by
    apply Finset.sum_subtype
    intro S
    simp
  calc
    (∑ S : Finset (ThreeBlockVariable w),
        ‖threeBlockDetCoefficient Q 0 S‖ ^ 2) = ∑ S, g S := rfl
    _ = ∑ S ∈ (Finset.univ : Finset (Finset (ThreeBlockVariable w))),
        g S := rfl
    _ = ∑ S ∈ Finset.univ.filter IsValidThreeBlockMatching, g S :=
      hfilter.symm
    _ = ∑ a : ValidThreeBlockMatching w, g a.1 := hvalidSubtype
    _ = _ := by
      rfl

omit [LinearOrder w] in
/-- Consequently, the paper's actual complete squarefree coefficient norm
is the finite `ℓ²` norm of its restriction to valid matchings. -/
theorem threeBlockDetCoefficientNorm_zero_eq_validL2Norm
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ) :
    threeBlockDetCoefficientNorm Q 0 =
      finiteL2Norm (threeBlockValidCoefficient Q) := by
  rw [threeBlockDetCoefficientNorm]
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [← coeffEnergy_eq_norm_sq]
  change (∑ S : Finset (ThreeBlockVariable w),
      ‖threeBlockDetCoefficient Q 0 S‖ ^ 2) =
    √(finiteEnergy (threeBlockValidCoefficient Q)) ^ 2
  have henergy : 0 ≤ finiteEnergy (threeBlockValidCoefficient Q) := by
    unfold finiteEnergy
    positivity
  rw [threeBlockFullCoefficientEnergy_eq_validEnergy, Real.sq_sqrt henergy]
  rfl

/-- Replacing each valid actual coefficient by its selected minor does not
change its finite `ℓ²` norm. -/
theorem threeBlockValidL2Norm_eq_virtualMinorL2Norm
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ) :
    finiteL2Norm (threeBlockValidCoefficient Q) =
      finiteL2Norm
        (maskCoefficient threeBlockMatchingMinorIndex
          threeBlockValidUnitWeight (squareMinorValue Q)) := by
  unfold finiteL2Norm finiteEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [show ‖threeBlockValidCoefficient Q a‖ =
      ‖squareMinorValue Q (threeBlockMatchingMinorIndex a)‖ by
    exact norm_threeBlockDetCoefficient_zero_eq_squareMinorValue Q a]
  simp [maskCoefficient, threeBlockValidUnitWeight]

/-- All square-minor `ℓ²` norm is the Gram volume. -/
theorem threeBlockMinorL2Norm_eq_gramVolume
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ) :
    finiteL2Norm (squareMinorValue Q) = gramVolume Q := by
  simpa [finiteL2Norm, squareMinorEnergy] using
    sqrt_squareMinorEnergy_eq_gramVolume Q

/-- The raw lower comparison has no loss: every minor is hit by a valid
matching of unit norm. -/
theorem gramVolume_le_threeBlockDetCoefficientNorm_zero
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ) :
    gramVolume Q ≤ threeBlockDetCoefficientNorm Q 0 := by
  have h := (maskCoefficientL2Norm_bounds
    (threeBlockMatchingMinorIndex : ValidThreeBlockMatching w →
      SquareMinorIndex (ThreeBlockOuter w))
    threeBlockValidUnitWeight (squareMinorValue Q)
    threeBlockValidMaskCertificate).1
  calc
    gramVolume Q = finiteL2Norm (squareMinorValue Q) :=
      (threeBlockMinorL2Norm_eq_gramVolume Q).symm
    _ ≤ finiteL2Norm
        (maskCoefficient threeBlockMatchingMinorIndex
          threeBlockValidUnitWeight (squareMinorValue Q)) := by
      simpa [threeBlockValidMaskCertificate] using h
    _ = finiteL2Norm (threeBlockValidCoefficient Q) :=
      (threeBlockValidL2Norm_eq_virtualMinorL2Norm Q).symm
    _ = threeBlockDetCoefficientNorm Q 0 :=
      (threeBlockDetCoefficientNorm_zero_eq_validL2Norm Q).symm

/-- Raw upper comparison, with the coarse square-root fiber count. -/
theorem threeBlockDetCoefficientNorm_zero_le_sqrtCard_mul_gramVolume
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ) :
    threeBlockDetCoefficientNorm Q 0 ≤
      √(Fintype.card (ValidThreeBlockMatching w) : ℝ) * gramVolume Q := by
  have h := (maskCoefficientL2Norm_bounds
    (threeBlockMatchingMinorIndex : ValidThreeBlockMatching w →
      SquareMinorIndex (ThreeBlockOuter w))
    threeBlockValidUnitWeight (squareMinorValue Q)
    threeBlockValidMaskCertificate).2
  calc
    threeBlockDetCoefficientNorm Q 0 =
        finiteL2Norm (threeBlockValidCoefficient Q) :=
      threeBlockDetCoefficientNorm_zero_eq_validL2Norm Q
    _ = finiteL2Norm
        (maskCoefficient threeBlockMatchingMinorIndex
          threeBlockValidUnitWeight (squareMinorValue Q)) :=
      threeBlockValidL2Norm_eq_virtualMinorL2Norm Q
    _ ≤ √(Fintype.card (ValidThreeBlockMatching w) : ℝ) *
        finiteL2Norm (squareMinorValue Q) := by
      simpa [threeBlockValidMaskCertificate] using h
    _ = _ := by rw [threeBlockMinorL2Norm_eq_gramVolume]

/-- One explicit zero-shift comparison constant. -/
def threeBlockZeroComparisonConstant : ℝ :=
  max 1 √(Fintype.card (ValidThreeBlockMatching w) : ℝ)

omit [LinearOrder w] in
theorem threeBlockZeroComparisonConstant_one_le :
    1 ≤ threeBlockZeroComparisonConstant (w := w) :=
  le_max_left _ _

/-- Concrete terminal comparison on the Boolean-tagged outer coordinates. -/
theorem threeBlockDetCoefficientNorm_zero_comparison :
    TerminalCoefficientComparison
      (fun Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ =>
        threeBlockDetCoefficientNorm Q 0)
      (threeBlockZeroComparisonConstant (w := w)) where
  one_le := threeBlockZeroComparisonConstant_one_le
  lower := by
    intro Q
    calc
      (threeBlockZeroComparisonConstant (w := w))⁻¹ * gramVolume Q ≤
          1 * gramVolume Q := by
        exact mul_le_mul_of_nonneg_right
          (inv_le_one_of_one_le₀
            (threeBlockZeroComparisonConstant_one_le (w := w)))
          (gramVolume_nonneg Q)
      _ = gramVolume Q := one_mul _
      _ ≤ threeBlockDetCoefficientNorm Q 0 :=
        gramVolume_le_threeBlockDetCoefficientNorm_zero Q
  upper := by
    intro Q
    calc
      threeBlockDetCoefficientNorm Q 0 ≤
          √(Fintype.card (ValidThreeBlockMatching w) : ℝ) * gramVolume Q :=
        threeBlockDetCoefficientNorm_zero_le_sqrtCard_mul_gramVolume Q
      _ ≤ threeBlockZeroComparisonConstant (w := w) * gramVolume Q := by
        exact mul_le_mul_of_nonneg_right (le_max_right _ _)
          (gramVolume_nonneg Q)

end ValidEnergy

section PacketComparison

variable {w : Type*} [Fintype w] [DecidableEq w] [LinearOrder w]

local instance threeBlockPacketComparisonVariableDecidableEq :
    DecidableEq (ThreeBlockVariable w) := Classical.decEq _

local instance threeBlockPacketBoolOuterLinearOrder :
    LinearOrder (ThreeBlockOuter w) :=
  LinearOrder.lift'
    (fun x : ThreeBlockOuter w => (toLex x : Bool ×ₗ w))
    toLex.injective

local instance threeBlockPacketOuterLinearOrder : LinearOrder (w ⊕ w) :=
  LinearOrder.lift'
    (fun x : w ⊕ w => (toLex x : w ⊕ₗ w)) toLex.injective

omit [LinearOrder w] in
theorem gramVolume_threeBlockOuterOfPacket
    (Q : Matrix (w ⊕ w) (w ⊕ w) ℂ) :
    gramVolume (threeBlockOuterOfPacket Q) = gramVolume Q := by
  exact gramVolume_submatrix_equiv (threeBlockOuterEquiv w) Q

/-- Minimal fully concrete closure requested for the terminal local-mask
step: the actual zero-shift coefficient function on `W ⊕ W` satisfies the
paper's two-sided Gram-volume comparison. -/
theorem threeBlockTerminalCoefficientOnPacket_zero_comparison :
    TerminalCoefficientComparison
      (threeBlockTerminalCoefficientOnPacket (w := w) 0)
      (threeBlockZeroComparisonConstant (w := w)) where
  one_le := threeBlockZeroComparisonConstant_one_le
  lower := by
    intro Q
    have h := (threeBlockDetCoefficientNorm_zero_comparison
      (w := w)).lower (threeBlockOuterOfPacket Q)
    simpa [threeBlockTerminalCoefficientOnPacket,
      gramVolume_threeBlockOuterOfPacket] using h
  upper := by
    intro Q
    have h := (threeBlockDetCoefficientNorm_zero_comparison
      (w := w)).upper (threeBlockOuterOfPacket Q)
    simpa [threeBlockTerminalCoefficientOnPacket,
      gramVolume_threeBlockOuterOfPacket] using h

end PacketComparison

end BernoulliLinearAlgebra
