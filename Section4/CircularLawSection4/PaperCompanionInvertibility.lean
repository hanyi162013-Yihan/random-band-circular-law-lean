import CircularLawSection4.PaperIndicatorRandomMatrix
import CircularLawSection4.PaperIndicatorFreshSample
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Determinant and invertibility of the paper companion transfers

This module proves the computation immediately following the paper's
companion-transfer definition.  In arbitrary state dimension `m + 1` the
companion convention contributes the sign `(-1)^(m+1)`.  The manuscript's
state dimension is `2W`, so the sign is one and the displayed identity is
exactly `det T_i = alpha_i / beta_i`.
-/

open scoped BigOperators Matrix ENNReal MeasureTheory
open MeasureTheory

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

section Deterministic

variable {R : Type*} [Field R]

/-- The left-edge coefficient in the paper's `0, ..., m+1` indexing. -/
def paperLeftEdgeCoefficient
    (m : ℕ) (x : ZMod N → Fin (m + 2) → R) : ZMod N → R :=
  fun i ↦ x i 0

/-- Removing the last row and the first column from a companion transfer
leaves the identity matrix. -/
private theorem paperCyclicTransfer_last_first_minor
    (N m : ℕ) [NeZero N]
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R)
    (i : ZMod N) :
    (paperCyclicTransferMatrix N m βraw a i).submatrix
        (Fin.last m).succAbove (0 : Fin (m + 1)).succAbove = 1 := by
  classical
  ext r c
  simp [paperCyclicTransferMatrix, Matrix.one_apply, eq_comm]

/-- Every other last-row cofactor of a companion transfer vanishes: after
removing a non-first column, the retained first column is zero. -/
private theorem paperCyclicTransfer_last_other_minor_det
    (N m : ℕ) [NeZero N]
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R)
    (i : ZMod N) (j : Fin (m + 1)) (hj : j ≠ 0) :
    ((paperCyclicTransferMatrix N m βraw a i).submatrix
        (Fin.last m).succAbove j.succAbove).det = 0 := by
  classical
  have hjval : 0 < j.val := by
    have : j.val ≠ 0 := by
      intro h
      apply hj
      apply Fin.ext
      exact h
    omega
  let k₀ : Fin m := ⟨0, by omega⟩
  apply Matrix.det_eq_zero_of_column_eq_zero k₀
  intro r
  have hsucc : j.succAbove k₀ = 0 := by
    apply Fin.ext
    simp [Fin.succAbove, k₀, hj]
  have hzero : (0 : Fin (m + 1)) ≠ r.succ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  simp [paperCyclicTransferMatrix, hsucc, hzero]

/-- Exact determinant of the paper's companion transfer in an arbitrary
state dimension. -/
theorem paperCyclicTransferMatrix_det
    (N m : ℕ) [NeZero N]
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R)
    (i : ZMod N) :
    (paperCyclicTransferMatrix N m βraw a i).det =
      (-1 : R) ^ (m + 1) * (a i 0 / βraw i) := by
  classical
  rw [Matrix.det_succ_row _ (Fin.last m)]
  rw [Finset.sum_eq_single (0 : Fin (m + 1))]
  · rw [paperCyclicTransfer_last_first_minor]
    simp [paperCyclicTransferMatrix, div_eq_mul_inv]
    ring
  · intro j _ hj
    rw [paperCyclicTransfer_last_other_minor_det N m βraw a i j hj]
    simp
  · simp

/-- In the manuscript's even state dimension the companion sign is one,
giving the displayed formula `det T_i = alpha_i / beta_i`. -/
theorem paperCyclicTransferMatrix_det_of_even
    (N m : ℕ) [NeZero N]
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R)
    (i : ZMod N) (hm : Even (m + 1)) :
    (paperCyclicTransferMatrix N m βraw a i).det = a i 0 / βraw i := by
  rw [paperCyclicTransferMatrix_det, hm.neg_one_pow, one_mul]

/-- The determinant computation immediately supplies nondegeneracy when the
two edge coefficients are nonzero. -/
theorem paperCyclicTransferMatrix_det_ne_zero
    (N m : ℕ) [NeZero N]
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R)
    (i : ZMod N) (hβ : βraw i ≠ 0) (hα : a i 0 ≠ 0) :
    (paperCyclicTransferMatrix N m βraw a i).det ≠ 0 := by
  rw [paperCyclicTransferMatrix_det]
  exact mul_ne_zero (neg_one_pow_ne_zero (m + 1)) (div_ne_zero hα hβ)

/-- A paper companion transfer with nonzero left and right edge
coefficients is an invertible element of the matrix ring. -/
theorem paperCyclicTransferMatrix_isUnit
    (N m : ℕ) [NeZero N]
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R)
    (i : ZMod N) (hβ : βraw i ≠ 0) (hα : a i 0 ≠ 0) :
    IsUnit (paperCyclicTransferMatrix N m βraw a i) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact (isUnit_iff_ne_zero.mpr
    (paperCyclicTransferMatrix_det_ne_zero N m βraw a i hβ hα))

/-- Exterior powers preserve invertibility, stated in the concrete compound
coordinates used throughout this formalization. -/
theorem compound_isUnit_of_isUnit_det
    {iota : Type*} [Fintype iota] [DecidableEq iota] [LinearOrder iota]
    (k : ℕ) (A : Matrix iota iota R) (hA : IsUnit A.det) :
    IsUnit (compound k A) := by
  refine IsUnit.of_mul_eq_one (compound k A⁻¹) ?_
  rw [← compound_mul, A.mul_nonsing_inv hA]
  simp [compound]
  rw [← exteriorPower.coe_basis]
  exact ((Pi.basisFun R iota).exteriorPower k).toMatrix_self

/-- Every exterior degree of a nondegenerate paper transfer is invertible. -/
theorem paperCyclicTransferMatrix_compound_isUnit
    (N m : ℕ) [NeZero N]
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R)
    (i : ZMod N) (hβ : βraw i ≠ 0) (hα : a i 0 ≠ 0)
    (k : ℕ) :
    IsUnit (compound k (paperCyclicTransferMatrix N m βraw a i)) := by
  apply compound_isUnit_of_isUnit_det
  exact (isUnit_iff_ne_zero.mpr
    (paperCyclicTransferMatrix_det_ne_zero N m βraw a i hβ hα))

/-- Simultaneous form for all exterior degrees. -/
theorem paperCyclicTransferMatrix_all_compounds_isUnit
    (N m : ℕ) [NeZero N]
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R)
    (i : ZMod N) (hβ : βraw i ≠ 0) (hα : a i 0 ≠ 0) :
    ∀ k : ℕ,
      IsUnit (compound k (paperCyclicTransferMatrix N m βraw a i)) :=
  fun k ↦ paperCyclicTransferMatrix_compound_isUnit
    N m βraw a i hβ hα k

/-- The denominator-cleared exterior transfer used in the paper is itself
invertible in every degree. -/
theorem paperCyclicTransferMatrix_clearedCompound_isUnit
    (N m : ℕ) [NeZero N]
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R)
    (i : ZMod N) (hβ : βraw i ≠ 0) (hα : a i 0 ≠ 0)
    (k : ℕ) :
    IsUnit (βraw i •
      compound k (paperCyclicTransferMatrix N m βraw a i)) := by
  have hcomp := paperCyclicTransferMatrix_compound_isUnit
    N m βraw a i hβ hα k
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
  exact isUnit_iff_ne_zero.mpr <| mul_ne_zero (pow_ne_zero _ hβ) <|
    ((Matrix.isUnit_iff_isUnit_det _).mp hcomp).ne_zero

/-- The companion transfer attached directly to a shifted scalar band row. -/
def paperShiftedScalarTransfer
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (x : ZMod N → Fin (m + 2) → R) (z : R) (i : ZMod N) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  paperCyclicTransferMatrix N m
    (paperRightEdgeCoefficient m x)
    (paperShiftedInteriorCoefficient m center x z) i

/-- Determinant of the literal shifted-band transfer in even state
dimension, before using that the left edge is not the diagonal slot. -/
theorem paperShiftedScalarTransfer_det_of_even
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (x : ZMod N → Fin (m + 2) → R) (z : R) (i : ZMod N)
    (hm : Even (m + 1)) :
    (paperShiftedScalarTransfer N m center x z i).det =
      paperShiftedInteriorCoefficient m center x z i 0 /
        paperRightEdgeCoefficient m x i := by
  exact paperCyclicTransferMatrix_det_of_even N m
    (paperRightEdgeCoefficient m x)
    (paperShiftedInteriorCoefficient m center x z) i hm

/-- **Companion determinant (paper formula).**  When the state dimension is
even and the diagonal slot is not the left edge, `det T_i = alpha_i/beta_i`.
-/
theorem paperShiftedScalarTransfer_det_eq_leftEdge_div_rightEdge
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (x : ZMod N → Fin (m + 2) → R) (z : R) (i : ZMod N)
    (hm : Even (m + 1)) (hcenter : center ≠ 0) :
    (paperShiftedScalarTransfer N m center x z i).det =
      paperLeftEdgeCoefficient m x i /
        paperRightEdgeCoefficient m x i := by
  rw [paperShiftedScalarTransfer_det_of_even N m center x z i hm]
  have hzero : (0 : Fin (m + 1)) ≠ center := Ne.symm hcenter
  simp [paperShiftedInteriorCoefficient, paperLeftEdgeCoefficient, hzero]

/-- Pointwise package: a nonzero shifted left edge and right edge make the
transfer, every exterior power, and every denominator-cleared exterior
transfer invertible. -/
theorem paperShiftedScalarTransfer_all_isUnit
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (x : ZMod N → Fin (m + 2) → R) (z : R) (i : ZMod N)
    (hβ : paperRightEdgeCoefficient m x i ≠ 0)
    (hα : paperShiftedInteriorCoefficient m center x z i 0 ≠ 0) :
    IsUnit (paperShiftedScalarTransfer N m center x z i) ∧
      ∀ k : ℕ,
        IsUnit (compound k (paperShiftedScalarTransfer N m center x z i)) ∧
        IsUnit (paperRightEdgeCoefficient m x i •
          compound k (paperShiftedScalarTransfer N m center x z i)) := by
  refine ⟨paperCyclicTransferMatrix_isUnit N m
    (paperRightEdgeCoefficient m x)
    (paperShiftedInteriorCoefficient m center x z) i hβ hα, ?_⟩
  intro k
  exact ⟨paperCyclicTransferMatrix_compound_isUnit N m
      (paperRightEdgeCoefficient m x)
      (paperShiftedInteriorCoefficient m center x z) i hβ hα k,
    paperCyclicTransferMatrix_clearedCompound_isUnit N m
      (paperRightEdgeCoefficient m x)
      (paperShiftedInteriorCoefficient m center x z) i hβ hα k⟩

end Deterministic

section ConcreteRowCompanion

/-- Direct row-companion form of the determinant computation over `ℂ`.
This is definitionally the same transfer as the paper matrix, exposed for
users of the row-linearity API. -/
theorem rowCompanion_finLeftShift_det
    (m : ℕ) (β : ℂ) (c : Fin (m + 1) → ℂ) :
    (rowCompanion (finLeftShift m) (Fin.last m) β c).det =
      (-1 : ℂ) ^ (m + 1) * (c 0 / β) := by
  simpa only [paperCyclicTransferMatrix_eq_rowCompanion] using
    (paperCyclicTransferMatrix_det (R := ℂ) 1 m
      (fun _ ↦ β) (fun _ ↦ c) (0 : ZMod 1))

/-- The manuscript's exact `det T = alpha / beta` formula in the direct
row-companion notation. -/
theorem rowCompanion_finLeftShift_det_of_even
    (m : ℕ) (β : ℂ) (c : Fin (m + 1) → ℂ)
    (hm : Even (m + 1)) :
    (rowCompanion (finLeftShift m) (Fin.last m) β c).det = c 0 / β := by
  rw [rowCompanion_finLeftShift_det, hm.neg_one_pow, one_mul]

/-- A direct row companion with nonzero edge coefficients is a unit. -/
theorem rowCompanion_finLeftShift_isUnit
    (m : ℕ) (β : ℂ) (c : Fin (m + 1) → ℂ)
    (hβ : β ≠ 0) (hα : c 0 ≠ 0) :
    IsUnit (rowCompanion (finLeftShift m) (Fin.last m) β c) := by
  rw [Matrix.isUnit_iff_isUnit_det, rowCompanion_finLeftShift_det]
  exact isUnit_iff_ne_zero.mpr <|
    mul_ne_zero (neg_one_pow_ne_zero (m + 1)) (div_ne_zero hα hβ)

/-- Every compound/exterior degree of the direct row companion is a unit. -/
theorem rowCompanion_finLeftShift_compound_isUnit
    (m k : ℕ) (β : ℂ) (c : Fin (m + 1) → ℂ)
    (hβ : β ≠ 0) (hα : c 0 ≠ 0) :
    IsUnit (compound k
      (rowCompanion (finLeftShift m) (Fin.last m) β c)) := by
  apply compound_isUnit_of_isUnit_det
  rw [rowCompanion_finLeftShift_det]
  exact isUnit_iff_ne_zero.mpr <|
    mul_ne_zero (neg_one_pow_ne_zero (m + 1)) (div_ne_zero hα hβ)

end ConcreteRowCompanion

section FlatSamples

/-- The actual companion transfer read from a flat complex IID sample. -/
def paperIndicatorTransferMatrix
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (b : Fin (m + 2) → ℂ) (ω : Fin (N * (m + 2)) → ℂ)
    (z : ℂ) (i : ZMod N) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  paperShiftedScalarTransfer N m center
    (fun row k ↦ b k * paperIndicatorXi N m ω row k) z i

/-- The actual companion transfer read from a flat real IID sample and then
embedded into `ℂ`, as in `paperIndicatorXSubZIOfReal`. -/
def paperIndicatorTransferMatrixOfReal
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (b : Fin (m + 2) → ℂ) (ω : Fin (N * (m + 2)) → ℝ)
    (z : ℂ) (i : ZMod N) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  paperShiftedScalarTransfer N m center
    (fun row k ↦ b k * paperIndicatorXiOfReal N m ω row k) z i

/-- Under a bounded planar density, every actual sampled transfer, every
compound, and every denominator-cleared compound is invertible almost
surely.  The hypothesis `center ≠ 0` is precisely the manuscript fact
`-W ≠ 0`, ensuring that the spectral shift does not alter `alpha_i`. -/
theorem ae_paperIndicatorTransferMatrix_all_isUnit_complex_withDensity
    (N m : ℕ) [NeZero N] (center : Fin (m + 1)) (hcenter : center ≠ 0)
    (b : Fin (m + 2) → ℂ) (hleft : b 0 ≠ 0)
    (hright : b (Fin.last (m + 1)) ≠ 0) (z : ℂ)
    {f : ℂ → ℝ≥0∞} {L : ℝ≥0∞}
    [IsProbabilityMeasure ((volume : Measure ℂ).withDensity f)]
    (hf : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ L) :
    ∀ᵐ ω ∂iidMeasure ((volume : Measure ℂ).withDensity f) (N * (m + 2)),
      ∀ i : ZMod N,
        IsUnit (paperIndicatorTransferMatrix N m center b ω z i) ∧
          ∀ k : ℕ,
            IsUnit (compound k
              (paperIndicatorTransferMatrix N m center b ω z i)) ∧
            IsUnit ((b (Fin.last (m + 1)) *
                paperIndicatorXi N m ω i (Fin.last (m + 1))) •
              compound k
                (paperIndicatorTransferMatrix N m center b ω z i)) := by
  filter_upwards [iidMeasure_ae_all_ne_zero_complex_withDensity
    hf (N * (m + 2))] with ω hω
  intro i
  let x : ZMod N → Fin (m + 2) → ℂ :=
    fun row k ↦ b k * paperIndicatorXi N m ω row k
  have hβ : paperRightEdgeCoefficient m x i ≠ 0 :=
    mul_ne_zero hright
      (hω (paperIndicatorFlatIndex N m i (Fin.last (m + 1))))
  have hα : paperShiftedInteriorCoefficient m center x z i 0 ≠ 0 := by
    simp only [paperShiftedInteriorCoefficient]
    rw [if_neg]
    · simpa [x] using
        (mul_ne_zero hleft (hω (paperIndicatorFlatIndex N m i 0)))
    · exact fun h ↦ hcenter h.symm
  simpa only [paperIndicatorTransferMatrix, x,
    paperRightEdgeCoefficient] using
    (paperShiftedScalarTransfer_all_isUnit N m center x z i hβ hα)

/-- Real bounded-density counterpart of
`ae_paperIndicatorTransferMatrix_all_isUnit_complex_withDensity`. -/
theorem ae_paperIndicatorTransferMatrix_all_isUnit_real_withDensity
    (N m : ℕ) [NeZero N] (center : Fin (m + 1)) (hcenter : center ≠ 0)
    (b : Fin (m + 2) → ℂ) (hleft : b 0 ≠ 0)
    (hright : b (Fin.last (m + 1)) ≠ 0) (z : ℂ)
    {f : ℝ → ℝ≥0∞} {L : ℝ≥0∞}
    [IsProbabilityMeasure ((volume : Measure ℝ).withDensity f)]
    (hf : ∀ᵐ w ∂(volume : Measure ℝ), f w ≤ L) :
    ∀ᵐ ω ∂iidMeasure ((volume : Measure ℝ).withDensity f) (N * (m + 2)),
      ∀ i : ZMod N,
        IsUnit (paperIndicatorTransferMatrixOfReal N m center b ω z i) ∧
          ∀ k : ℕ,
            IsUnit (compound k
              (paperIndicatorTransferMatrixOfReal N m center b ω z i)) ∧
            IsUnit ((b (Fin.last (m + 1)) *
                paperIndicatorXiOfReal N m ω i (Fin.last (m + 1))) •
              compound k
                (paperIndicatorTransferMatrixOfReal N m center b ω z i)) := by
  filter_upwards [iidMeasure_ae_all_ne_zero_real_withDensity
    hf (N * (m + 2))] with ω hω
  intro i
  let x : ZMod N → Fin (m + 2) → ℂ :=
    fun row k ↦ b k * paperIndicatorXiOfReal N m ω row k
  have hβ : paperRightEdgeCoefficient m x i ≠ 0 :=
    mul_ne_zero hright <| Complex.ofReal_ne_zero.mpr
      (hω (paperIndicatorFlatIndex N m i (Fin.last (m + 1))))
  have hα : paperShiftedInteriorCoefficient m center x z i 0 ≠ 0 := by
    simp only [paperShiftedInteriorCoefficient]
    rw [if_neg]
    · simpa [x] using (mul_ne_zero hleft <| Complex.ofReal_ne_zero.mpr
        (hω (paperIndicatorFlatIndex N m i 0)))
    · exact fun h ↦ hcenter h.symm
  simpa only [paperIndicatorTransferMatrixOfReal, x,
    paperRightEdgeCoefficient] using
    (paperShiftedScalarTransfer_all_isUnit N m center x z i hβ hα)

end FlatSamples

end CircularLawSection4
