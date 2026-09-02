import BernoulliSection10.IntervalRestriction
import BernoulliLinearAlgebra.ConcreteClearedTransfer

/-!
# The actual normalized full-block cyclic matrix

The parameter `s` counts the sites outside the terminal three-site packet;
the total number of sites is `s + 3`, and the scalar dimension is
`(s + 3) * W`. This convention avoids a separate partial definition at
zero, one, or two sites and covers every ring in Section 10.
-/

open scoped Matrix BigOperators

noncomputable section

namespace BernoulliSection10

open BernoulliLinearAlgebra Matrix Set Set.powersetCard

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

local instance cyclicPhysicalSumOrder (W : ℕ) : LinearOrder (Fin W ⊕ Fin W) :=
  BernoulliLinearAlgebra.clearedStepCompoundSumLinearOrder

def physicalIntervalSteps (W s : ℕ) (z : ℂ) (x : IntervalRows W s) :
    List (CompanionStep (Fin W)) :=
  List.ofFn fun j =>
    ⟨(intervalSiteBlocks z x j).B, (intervalSiteBlocks z x j).D,
      (intervalSiteBlocks z x j).C⟩

theorem polynomialClearedCompoundProduct_eq_reverse
    {W : Type*} [Fintype W] [LinearOrder W] (k : ℕ)
    (xs : List (CompanionStep W)) :
    polynomialClearedCompoundProduct k xs =
      (xs.reverse.map fun X => clearedStepCompound k X.B X.D X.C).prod := by
  induction xs with
  | nil => simp [polynomialClearedCompoundProduct, compound_one]
  | cons x xs ih =>
    simp only [polynomialClearedCompoundProduct, ih, List.reverse_cons,
      List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, Matrix.mul_one]

theorem polynomialClearedCompoundProduct_physicalIntervalSteps
    (W s : ℕ) (z : ℂ) (x : IntervalRows W s) (r : Fin (2 * W + 1)) :
    polynomialClearedCompoundProduct r.1 (physicalIntervalSteps W s z x) =
      intervalClearedProduct W s z x r := by
  rw [polynomialClearedCompoundProduct_eq_reverse]
  simp only [physicalIntervalSteps, ← list_ofFn_fin_rev, List.map_ofFn,
    Function.comp_def, intervalClearedProduct, reverseMatrixProduct, intervalClearedStep]

def densityShiftedCyclicMatrix (W s : ℕ) (z : ℂ) (x : IntervalRows W (s + 3)) :
    Matrix (Fin ((s + 3) * W)) (Fin ((s + 3) * W)) ℂ :=
  (physicalCyclicMatrix (m := s + 2)
    (fun j => (intervalSiteBlocks z x j).B)
    (fun j => (intervalSiteBlocks z x j).D)
    (fun j => (intervalSiteBlocks z x j).C)).reindex finProdFinEquiv finProdFinEquiv

def densityCyclicMatrix (W s : ℕ) (x : IntervalRows W (s + 3)) :
    Matrix (Fin ((s + 3) * W)) (Fin ((s + 3) * W)) ℂ :=
  densityShiftedCyclicMatrix W s 0 x

def densityCyclicLogDet (W s : ℕ) (z : ℂ) (x : IntervalRows W (s + 3)) : ℝ :=
  Real.log ‖(densityShiftedCyclicMatrix W s z x).det‖

theorem densityShiftedCyclicMatrix_eq_sub_scalar
    (W s : ℕ) (z : ℂ) (x : IntervalRows W (s + 3)) :
    densityShiftedCyclicMatrix W s z x = densityCyclicMatrix W s x - z • 1 := by
  have hB : (fun j => (intervalSiteBlocks z x j).B) =
      (fun j => (intervalSiteBlocks 0 x j).B) := rfl
  have hC : (fun j => (intervalSiteBlocks z x j).C) =
      (fun j => (intervalSiteBlocks 0 x j).C) := rfl
  have hD : siteBlockDiagonal (m := s + 2) (fun j => (intervalSiteBlocks z x j).D) =
      siteBlockDiagonal (fun j => (intervalSiteBlocks 0 x j).D) - z • 1 := by
    ext i j
    rcases i with ⟨i, a⟩
    rcases j with ⟨j, b⟩
    simp only [siteBlockDiagonal, Matrix.comp_apply, Matrix.diagonal_apply,
      Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply, intervalSiteBlocks, intervalPhysicalRow,
      physicalRowGroupOfAtoms]
    by_cases hij : i = j
    · simp [hij, Prod.ext_iff]
    · simp [hij, Prod.ext_iff]
  unfold densityCyclicMatrix
  simp only [densityShiftedCyclicMatrix]
  rw [hB, hC]
  unfold physicalCyclicMatrix
  rw [hD]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  simp only [Equiv.symm_apply_eq, Equiv.apply_symm_apply]
  abel

theorem densityCyclicLogDet_eq_polynomial_trace
    (W s : ℕ) (z : ℂ) (x : IntervalRows W (s + 3)) :
    densityCyclicLogDet W s z x =
      Real.log ‖polynomialClearedSignedCompoundTrace
        (physicalIntervalSteps W (s + 3) z x)‖ := by
  have h := polynomialClearedSignedCompoundTrace_listOfFn_eq_physical
    (m := s + 2) (fun j => (intervalSiteBlocks z x j).B)
    (fun j => (intervalSiteBlocks z x j).D)
    (fun j => (intervalSiteBlocks z x j).C) (by omega)
  have hsign : ‖floquetSign (R := ℂ) (m := s + 2) (w := Fin W)‖ = 1 := by
    rcases floquetSign_spec (R := ℂ) (m := s + 2) (w := Fin W) with hs | hs <;> simp [hs]
  unfold densityCyclicLogDet densityShiftedCyclicMatrix
  rw [Matrix.det_reindex_self]
  unfold physicalIntervalSteps
  rw [h, norm_mul, hsign, one_mul]

end BernoulliSection10
