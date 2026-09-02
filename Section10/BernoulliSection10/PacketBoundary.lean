import BernoulliLinearAlgebra.ConcreteBoundaryFinal
import BernoulliLinearAlgebra.ExteriorOperatorVolume
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The concrete three-site packet and its pathwise endpoint loss

This module fixes the exact packet polynomial used in Propositions 10.7--10.10
and records the pointwise coefficient--plane-volume estimate that is proved
inside the paper's proof of Proposition 10.8, equation (10.72). This is the
pointwise result used by the corrected arXiv v1 proof of Proposition 10.10.
-/

open scoped Matrix

noncomputable section

namespace BernoulliSection10

open Matrix
open BernoulliLinearAlgebra

variable {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]

local instance packetBoundarySumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift'
    (fun x : W ⊕ W => (toLex x : W ⊕ₗ W)) toLex.injective

/-- The literal seven-block boundary determinant polynomial
`P_{Theta,E_partial}` from (10.20)--(10.22). Its variables are precisely the
seven fresh packet blocks encoded by `ThreeBlockVariable W`; the endpoint
blocks `CL` and `BR` and the outside boundary relation `Theta` are fixed. -/
abbrev packetBoundaryPolynomial
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :=
  globalBoundaryDetPolynomial z CL BR Theta

/-- Euclidean norm of the full squarefree coefficient tensor of the concrete
packet polynomial. -/
abbrev packetBoundaryCoefficientNorm
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) : ℝ :=
  globalBoundaryCoefficientNorm z CL BR Theta

/-- The fully explicit multiplicative loss in the deterministic endpoint
comparison.  It contains the literal packet matching/translation constant and
the exact finite exterior-conditioning constant of `diag(CL,BR)`. -/
def packetEndpointComparisonConstant
    (z : ℂ) (CL BR : Matrix W W ℂ) : ℝ :=
  threeBlockConcreteComparisonConstant (W := W) z *
    endpointExteriorConstant CL BR

theorem one_le_threeBlockConcreteComparisonConstant (z : ℂ) :
    1 ≤ threeBlockConcreteComparisonConstant (W := W) z := by
  unfold threeBlockConcreteComparisonConstant
  exact one_le_mul_of_one_le_of_one_le
    (threeBlockZeroComparisonConstant_one_le (w := W))
    (threeBlockTranslationFactor_one_le (w := W) z)

/-- The shift loss in the literal three-site packet has exactly one factor
`1 + ‖z‖` for each of its `3W` diagonal variables.  This closed form is the
deterministic `O_z(W)` part of the integrated endpoint estimate. -/
theorem threeBlockTranslationFactor_eq_pow (z : ℂ) :
    threeBlockTranslationFactor (w := W) z =
      (1 + ‖z‖) ^ Fintype.card (ThreeBlockIndex W) := by
  simp [threeBlockTranslationFactor, translationFactor,
    threeBlockDiagonalShifts]

theorem log_threeBlockTranslationFactor_eq (z : ℂ) :
    Real.log (threeBlockTranslationFactor (w := W) z) =
      (Fintype.card (ThreeBlockIndex W) : ℝ) * Real.log (1 + ‖z‖) := by
  rw [threeBlockTranslationFactor_eq_pow, Real.log_pow]

/-! ## A quantitative count of the literal packet matchings -/

/-- Encode a valid partial row--column matching by its partial function from
rows to columns.  This avoids the much larger bound obtained by viewing a
matching as an arbitrary subset of all `7W²` fresh entries. -/
def matchingPartialMap (a : ValidThreeBlockMatching W) :
    ThreeBlockIndex W → Option (ThreeBlockIndex W) := fun i =>
  if h : ∃ e ∈ a.1, e.1.1 = i then
    some (Classical.choose h).1.2
  else none

theorem matchingPartialMap_eq_some_iff
    (a : ValidThreeBlockMatching W) (i j : ThreeBlockIndex W) :
    matchingPartialMap a i = some j ↔
      ∃ e ∈ a.1, e.1.1 = i ∧ e.1.2 = j := by
  classical
  unfold matchingPartialMap
  split_ifs with h
  · let e : ThreeBlockVariable W := Classical.choose h
    have he : e ∈ a.1 := (Classical.choose_spec h).1
    have hei : e.1.1 = i := (Classical.choose_spec h).2
    constructor
    · intro hj
      have hecol : e.1.2 = j := Option.some.inj hj
      exact ⟨e, he, hei, hecol⟩
    · rintro ⟨f, hf, hfi, hfj⟩
      have hef : e = f := a.2.1 he hf (hei.trans hfi.symm)
      subst f
      exact congrArg some hfj
  · constructor
    · simp
    · rintro ⟨e, he, hei, _⟩
      exact (h ⟨e, he, hei⟩).elim

/-- The partial-function encoding is faithful because a valid matching uses
each scalar row at most once. -/
theorem matchingPartialMap_injective :
    Function.Injective (matchingPartialMap (W := W)) := by
  classical
  intro a b hab
  apply Subtype.ext
  ext e
  constructor
  · intro he
    have ha : matchingPartialMap a e.1.1 = some e.1.2 :=
      (matchingPartialMap_eq_some_iff a e.1.1 e.1.2).2
        ⟨e, he, rfl, rfl⟩
    have hb : matchingPartialMap b e.1.1 = some e.1.2 := by
      rw [← hab]
      exact ha
    obtain ⟨f, hf, hrow, hcol⟩ :=
      (matchingPartialMap_eq_some_iff b e.1.1 e.1.2).1 hb
    have hef : f = e := by
      apply Subtype.ext
      exact Prod.ext hrow hcol
    simpa [hef] using hf
  · intro he
    have hb : matchingPartialMap b e.1.1 = some e.1.2 :=
      (matchingPartialMap_eq_some_iff b e.1.1 e.1.2).2
        ⟨e, he, rfl, rfl⟩
    have ha : matchingPartialMap a e.1.1 = some e.1.2 := by
      rw [hab]
      exact hb
    obtain ⟨f, hf, hrow, hcol⟩ :=
      (matchingPartialMap_eq_some_iff a e.1.1 e.1.2).1 ha
    have hef : f = e := by
      apply Subtype.ext
      exact Prod.ext hrow hcol
    simpa [hef] using hf

/-- A packet matching is one of at most `(3W+1)^(3W)` partial functions.
This is the combinatorial `exp (O(W log(eW)))` bound used in 10.8--10.10. -/
theorem card_validThreeBlockMatching_le :
    Fintype.card (ValidThreeBlockMatching W) ≤
      (Fintype.card (Option (ThreeBlockIndex W))) ^
        Fintype.card (ThreeBlockIndex W) := by
  calc
    Fintype.card (ValidThreeBlockMatching W) ≤
        Fintype.card (ThreeBlockIndex W → Option (ThreeBlockIndex W)) :=
      Fintype.card_le_of_injective (matchingPartialMap (W := W))
        (matchingPartialMap_injective (W := W))
    _ = _ := by simp

/-- The literal zero-shift coefficient-comparison constant has the same
`exp (O(W log(eW)))` bound, stated without hiding a matching-count
certificate. -/
theorem threeBlockZeroComparisonConstant_le_partialFunctionCount :
    threeBlockZeroComparisonConstant (w := W) ≤
      1 + ((Fintype.card (Option (ThreeBlockIndex W)) ^
        Fintype.card (ThreeBlockIndex W) : ℕ) : ℝ) := by
  let n := Fintype.card (ValidThreeBlockMatching W)
  let M := Fintype.card (Option (ThreeBlockIndex W)) ^
    Fintype.card (ThreeBlockIndex W)
  have hnM : n ≤ M := card_validThreeBlockMatching_le (W := W)
  have hnM' : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hnM
  have hsqrt : Real.sqrt (n : ℝ) ≤ 1 + (n : ℝ) := by
    have hsquare := Real.sq_sqrt (Nat.cast_nonneg n)
    have hsnonneg := Real.sqrt_nonneg (n : ℝ)
    nlinarith [sq_nonneg (Real.sqrt (n : ℝ) - 1)]
  unfold threeBlockZeroComparisonConstant
  apply max_le
  · exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  · exact hsqrt.trans (by
      simpa [M, add_comm] using add_le_add_left hnM' 1)

/-- Width-indexed form of the preceding bound. -/
theorem threeBlockZeroComparisonConstant_fin_le (W : ℕ) :
    threeBlockZeroComparisonConstant (w := Fin W) ≤
      1 + (((3 * W + 1) ^ (3 * W) : ℕ) : ℝ) := by
  have hcard : Fintype.card (ThreeBlockIndex (Fin W)) = 3 * W := by
    simp [ThreeBlockIndex, ThreeBlockOuter]
    omega
  have hopt : Fintype.card (Option (ThreeBlockIndex (Fin W))) = 3 * W + 1 := by
    simp [hcard]
  simpa [hcard, hopt] using
    (threeBlockZeroComparisonConstant_le_partialFunctionCount (W := Fin W))

theorem log_threeBlockZeroComparisonConstant_fin_le (W : ℕ) :
    Real.log (threeBlockZeroComparisonConstant (w := Fin W)) ≤
      Real.log (1 + (((3 * W + 1) ^ (3 * W) : ℕ) : ℝ)) := by
  exact Real.log_le_log
    (zero_lt_one.trans_le
      (threeBlockZeroComparisonConstant_one_le (w := Fin W)))
    (threeBlockZeroComparisonConstant_fin_le W)

theorem one_le_packetEndpointComparisonConstant
    (z : ℂ) (CL BR : Matrix W W ℂ) :
    1 ≤ packetEndpointComparisonConstant z CL BR := by
  unfold packetEndpointComparisonConstant endpointExteriorConstant
  exact one_le_mul_of_one_le_of_one_le
    (one_le_threeBlockConcreteComparisonConstant (W := W) z)
    (one_le_exactExteriorConditioningConstant (endpointFactor CL BR))

theorem packetEndpointComparisonConstant_pos
    (z : ℂ) (CL BR : Matrix W W ℂ) :
    0 < packetEndpointComparisonConstant z CL BR :=
  zero_lt_one.trans_le
    (one_le_packetEndpointComparisonConstant (W := W) z CL BR)

/-- The real Gram-volume definition is exactly the square-root form of the
paper's `det (I + Theta* Theta)`. -/
theorem log_gramVolume_eq_half_log_gramEnergy
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    Real.log (gramVolume Theta) =
      (1 / 2 : ℝ) * Real.log (gramEnergy Theta) := by
  rw [gramVolume, Real.log_sqrt (gramEnergy_nonneg Theta)]
  ring

/-- A reusable logarithmic form of a two-sided multiplicative comparison.
All positivity assumptions are explicit, so it is safe in Lean where
`Real.log 0 = 0`. -/
theorem abs_log_sub_log_le_log_of_inv_mul_le_of_le_mul
    {K x y : ℝ} (hK : 1 ≤ K) (hx : 0 < x) (hy : 0 < y)
    (hlower : K⁻¹ * y ≤ x) (hupper : x ≤ K * y) :
    |Real.log x - Real.log y| ≤ Real.log K := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hKne : K ≠ 0 := hKpos.ne'
  have hInvPos : 0 < K⁻¹ := inv_pos.mpr hKpos
  have hLowerLog : Real.log (K⁻¹ * y) ≤ Real.log x :=
    Real.log_le_log (mul_pos hInvPos hy) hlower
  have hUpperLog : Real.log x ≤ Real.log (K * y) :=
    Real.log_le_log hx hupper
  rw [abs_le]
  constructor
  · rw [Real.log_mul (inv_ne_zero hKne) hy.ne', Real.log_inv] at hLowerLog
    linarith
  · rw [Real.log_mul hKne hy.ne'] at hUpperLog
    linarith

/-- The pathwise estimate actually established in the proof of Proposition
10.8.  Unlike the displayed proposition, this theorem has no probability
space: it holds for every concrete pair of invertible endpoint blocks and
every invertible outside boundary relation.  No mask, elimination, Jacobi, or
chart-density certificate is required from the caller. -/
theorem packetCoefficient_log_gramVolume_pathwise
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (hTheta : IsUnit Theta.det) :
    |Real.log (packetBoundaryCoefficientNorm z CL BR Theta) -
        Real.log (gramVolume Theta)| ≤
      Real.log (packetEndpointComparisonConstant z CL BR) := by
  have hBounds :=
    globalBoundaryCoefficientNorm_bounds_fullyInstantiated
      z CL BR hCL hBR Theta hTheta
  have hCoefficient : 0 < packetBoundaryCoefficientNorm z CL BR Theta :=
    globalBoundaryCoefficientNorm_pos_fullyInstantiated
      z CL BR hCL hBR Theta hTheta
  exact abs_log_sub_log_le_log_of_inv_mul_le_of_le_mul
    (one_le_packetEndpointComparisonConstant (W := W) z CL BR)
    hCoefficient (gramVolume_pos Theta) hBounds.1 hBounds.2

/-- Printed half-log-Gram form of Proposition 10.8's deterministic core. -/
theorem packetCoefficient_log_gramEnergy_pathwise
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (hTheta : IsUnit Theta.det) :
    |Real.log (packetBoundaryCoefficientNorm z CL BR Theta) -
        (1 / 2 : ℝ) * Real.log (gramEnergy Theta)| ≤
      Real.log (packetEndpointComparisonConstant z CL BR) := by
  rw [← log_gramVolume_eq_half_log_gramEnergy Theta]
  exact packetCoefficient_log_gramVolume_pathwise
    z CL BR hCL hBR Theta hTheta

/-- The concrete packet coefficient tensor is nonzero.  This is the
nonvanishing input needed by Proposition 10.9, derived from the literal packet
objects rather than accepted as a polynomial certificate. -/
theorem packetBoundaryPolynomial_ne_zero
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (hTheta : IsUnit Theta.det) :
    packetBoundaryPolynomial z CL BR Theta ≠ 0 := by
  intro hzero
  change globalBoundaryDetPolynomial z CL BR Theta = 0 at hzero
  have hpos : 0 < packetBoundaryCoefficientNorm z CL BR Theta :=
    globalBoundaryCoefficientNorm_pos_fullyInstantiated
      z CL BR hCL hBR Theta hTheta
  have hnormzero : packetBoundaryCoefficientNorm z CL BR Theta = 0 := by
    change ‖globalBoundaryCoeffVector z CL BR Theta‖ = 0
    rw [norm_eq_zero]
    ext S
    simp [globalBoundaryCoeffVector, hzero]
  exact (ne_of_gt hpos) hnormzero

end BernoulliSection10
