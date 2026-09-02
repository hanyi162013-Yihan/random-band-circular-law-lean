import BernoulliSection8.CellResetLoss
import BernoulliSection8.CellPressureLimit
import BernoulliSection8.RademacherTransferBounds

/-!
# The actual complete-cell pressure sandwich

The maximizing degree is selected from the clipped core law. Only its
reset losses occur on the lower side. The upper side is simultaneous in
all degrees and uses the deterministic three-site Hodge bound.
-/

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator BigOperators NNReal

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

def completeCellSiteEmbedding (c K : ℕ) (k : Fin K) : Fin c ↪ Fin (K * c) where
  toFun := completeCellSite k
  inj' := by
    intro i j hij
    exact (Prod.mk.inj (finProdFinEquiv.injective hij)).2

theorem intervalRestriction_flatten_cell (W c K : ℕ) (k : Fin K)
    (x : Fin K → IntervalRows W c) :
    intervalRestriction (completeCellSiteEmbedding c K k) (flattenCompleteCells W c K x) =
      x k := by
  funext i
  obtain ⟨⟨j, a⟩, rfl⟩ := finProdFinEquiv.surjective i
  change intervalRestriction (completeCellSiteEmbedding c K k)
      (flattenCompleteCells W c K x) (intervalRowIndex j a) =
    x k (intervalRowIndex j a)
  simp only [intervalRestriction, Function.comp_apply, intervalRowEmbedding_rowIndex]
  exact flattenCompleteCells_row W c K x k j a

theorem completeCell_good_of_flatten_good (I : NguyenBottomSingularInput.{0, 0})
    (W c K : ℕ) (x : Fin K → IntervalRows W c)
    (hx : flattenCompleteCells W c K x ∈ rademacherInterfaceGoodEvent I W (K * c))
    (k : Fin K) : x k ∈ rademacherInterfaceGoodEvent I W c := by
  have h := rademacherInterfaceGoodEvent_subset_subinterval I (completeCellSiteEmbedding c K k) hx
  change intervalRestriction (completeCellSiteEmbedding c K k)
    (flattenCompleteCells W c K x) ∈ rademacherInterfaceGoodEvent I W c at h
  rwa [intervalRestriction_flatten_cell] at h

def cellTransferBudget (I : NguyenBottomSingularInput.{0, 0}) (W s : ℕ) (z : ℂ) : ℝ :=
  rademacherTransferLogConstant I z * ((s * W : ℕ) : ℝ) *
    (1 + Real.posLog (W : ℝ))

theorem interval_hodgeLoss_le_cellTransferBudget
    (I : NguyenBottomSingularInput.{0, 0}) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W) (hs : 0 < s)
    (z : ℂ) (x : IntervalRows W s) (hx : x ∈ rademacherInterfaceGoodEvent I W s)
    (r : Fin (2 * W + 1)) :
    matrixHodgeLoss (intervalClearedProduct W s z x r) ≤ cellTransferBudget I W s z := by
  apply rademacherInterval_hodgeLoss_le_of_good I hI W s hW hs z x hx.2
  intro i a
  rcases hx.1 i a with hh | hh <;> rw [hh] <;> norm_num

theorem interval_product_det_isUnit_of_good
    (I : NguyenBottomSingularInput.{0, 0}) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (z : ℂ) (x : IntervalRows W s) (hx : x ∈ rademacherInterfaceGoodEvent I W s)
    (r : Fin (2 * W + 1)) : IsUnit (intervalClearedProduct W s z x r).det := by
  have hd := rademacherInterface_dets_isUnit_of_good I hI W s hW x hx.2 z
  exact intervalClearedProduct_det_isUnit W s z x (fun j => (hd j).1) (fun j => (hd j).2) r

theorem clippedCoreLog_eq_log_on_good
    (I : NguyenBottomSingularInput.{0, 0}) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (z : ℂ) (x : IntervalRows W s) (hx : x ∈ rademacherInterfaceGoodEvent I W s)
    (A : ℝ≥0) (hA : cellTransferBudget I W s z ≤ A) (r : Fin (2 * W + 1)) :
    clippedCoreLog A W s z r x = Real.log ‖intervalClearedProduct W s z x r‖ := by
  have hn := rademacherInterval_norm_pos_of_good I hI W s hW z x hx r
  have hb := (rademacherInterval_abs_logNorm_le_on_measurable_good I hI W s hW z x hx r).trans hA
  exact clippedLog_eq_log_of_log_bounds hn (abs_le.mp hb).1 (abs_le.mp hb).2

def optimizingCellResetLoss (μ : Measure ℝ) (A : ℝ≥0) (W s K : ℕ) (z : ℂ) (T : ℝ)
    (x : Fin K → IntervalRows W (3 + s)) : ℝ :=
  ∑ k, cellIntervalResetLoss W s K k z (clippedCoreOptimizingDegree μ A W s z) T x

/-- The sandwich is for the real cleared product on its concrete global
good event. The two numerical premises merely choose clipping and reset
caps above the proved local Hodge budgets. -/
theorem complete_cell_pressure_sandwich
    (I : NguyenBottomSingularInput.{0, 0}) (hI : 1 ≤ I.subgaussianBound)
    (μ : Measure ℝ) (W s K : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (hs : 0 < s) (z : ℂ) (x : Fin K → IntervalRows W (3 + s))
    (hx : flattenCompleteCells W (3 + s) K x ∈ rademacherInterfaceGoodEvent I W (K * (3 + s)))
    (A : ℝ≥0) (hA : cellTransferBudget I W s z ≤ A) (T : ℝ)
    (hT : 2 * cellTransferBudget I W s z + cellTransferBudget I W 3 z ≤ T) :
    (K : ℝ) * clippedMaxCorePressure μ A W s z - completeCellCoreFluctuation μ A W s K z x -
        optimizingCellResetLoss μ A W s K z T x ≤
      intervalMaxDegreeLog W (K * (3 + s)) z (flattenCompleteCells W (3 + s) K x) ∧
    intervalMaxDegreeLog W (K * (3 + s)) z (flattenCompleteCells W (3 + s) K x) ≤
      (K : ℝ) * clippedMaxCorePressure μ A W s z + completeCellCoreFluctuation μ A W s K z x +
        (K : ℝ) * cellTransferBudget I W 3 z := by
  have hcgood (k : Fin K) : completeCellCore W s (x k) ∈ rademacherInterfaceGoodEvent I W s :=
    rademacherInterfaceGoodEvent_subset_subinterval I (Fin.natAddEmb 3)
      (completeCell_good_of_flatten_good I W (3 + s) K x hx k)
  have hrgood (k : Fin K) : completeCellReset W s (x k) ∈ rademacherInterfaceGoodEvent I W 3 :=
    rademacherInterfaceGoodEvent_subset_subinterval I (Fin.castAddEmb s)
      (completeCell_good_of_flatten_good I W (3 + s) K x hx k)
  have hclip (r : Fin (2 * W + 1)) (k : Fin K) :=
    clippedCoreLog_eq_log_on_good I hI W s hW z _ (hcgood k) A hA r
  have hunitc (r : Fin (2 * W + 1)) (j : ℕ) (hj : j < K) :
      IsUnit (cellCoreProducts W s K z r x j).det := by
    simpa only [cellCoreProducts, dif_pos hj] using
      interval_product_det_isUnit_of_good I hI W s hW z _ (hcgood ⟨j, hj⟩) r
  have hunitr (r : Fin (2 * W + 1)) (j : ℕ) (hj : j < K) :
      IsUnit (cellResetProducts W s K z r x j).det := by
    simpa only [cellResetProducts, dif_pos hj] using
      interval_product_det_isUnit_of_good I hI W 3 hW z _ (hrgood ⟨j, hj⟩) r
  have hcap (r : Fin (2 * W + 1)) (j : ℕ) (hj : j < K) :
      2 * matrixHodgeLoss (cellCoreProducts W s K z r x j) +
        matrixHodgeLoss (cellResetProducts W s K z r x j) ≤ T := by
    simp only [cellCoreProducts, cellResetProducts, dif_pos hj]
    have hc := interval_hodgeLoss_le_cellTransferBudget I hI W s hW hs z _ (hcgood ⟨j, hj⟩) r
    have hr := interval_hodgeLoss_le_cellTransferBudget I hI W 3 hW (by omega) z _ (hrgood ⟨j, hj⟩) r
    linarith
  have hnonempty (r : Fin (2 * W + 1)) : Nonempty (Set.powersetCard (Fin W ⊕ Fin W) r.val) := by
    rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
    apply Nat.choose_pos
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hlower (r : Fin (2 * W + 1)) :
      (∑ k, clippedCoreLog A W s z r (completeCellCore W s (x k))) -
        (∑ k, cellIntervalResetLoss W s K k z r T x) ≤
      intervalDegreeLog W (K * (3 + s)) z r (flattenCompleteCells W (3 + s) K x) := by
    letI := hnonempty r
    have h := resetPrefixProduct_log_lower (cellCoreProducts W s K z r x)
      (cellResetProducts W s K z r x) K T (hunitc r) (hunitr r) (hcap r)
    rw [← intervalClearedProduct_flatten_eq_resetPrefixProduct] at h
    simp only [← Fin.sum_univ_eq_sum_range, cellCoreProducts_val,
      prefixResetLoss_eq_cellIntervalResetLoss] at h
    simpa only [intervalDegreeLog, ← hclip] using h
  have hupper (r : Fin (2 * W + 1)) :
      intervalDegreeLog W (K * (3 + s)) z r (flattenCompleteCells W (3 + s) K x) ≤
        (∑ k, clippedCoreLog A W s z r (completeCellCore W s (x k))) +
          (K : ℝ) * cellTransferBudget I W 3 z := by
    letI := hnonempty r
    have h := resetPrefixProduct_log_upper (cellCoreProducts W s K z r x)
      (cellResetProducts W s K z r x) K (hunitc r) (hunitr r)
    rw [← intervalClearedProduct_flatten_eq_resetPrefixProduct] at h
    simp only [← Fin.sum_univ_eq_sum_range, cellCoreProducts_val, cellResetProducts_val] at h
    have hreset : (∑ k, Real.log ‖intervalClearedProduct W 3 z (completeCellReset W s (x k)) r‖) ≤
        (K : ℝ) * cellTransferBudget I W 3 z := by
      calc
        _ ≤ ∑ _k : Fin K, cellTransferBudget I W 3 z := by
          apply Finset.sum_le_sum
          intro k _
          exact (le_abs_self _).trans
            (rademacherInterval_abs_logNorm_le_on_measurable_good I hI W 3 hW z _ (hrgood k) r)
        _ = _ := by simp
    have h' : Real.log ‖intervalClearedProduct W (K * (3 + s)) z
        (flattenCompleteCells W (3 + s) K x) r‖ ≤
        (∑ k : Fin K, Real.log ‖intervalClearedProduct W s z (completeCellCore W s (x k)) r‖) +
          (K : ℝ) * cellTransferBudget I W 3 z :=
      h.trans (add_le_add (le_refl _) hreset)
    simpa only [intervalDegreeLog, ← hclip] using h'
  apply finite_pressure_sandwich (clippedCorePressure μ A W s z)
    (fun r => ∑ k, clippedCoreLog A W s z r (completeCellCore W s (x k)))
    (fun r => intervalDegreeLog W (K * (3 + s)) z r (flattenCompleteCells W (3 + s) K x))
    (Nat.cast_nonneg K) _ (hlower _) hupper
  intro r
  have he : (∑ k, clippedCoreLog A W s z r (completeCellCore W s (x k))) -
      (K : ℝ) * clippedCorePressure μ A W s z r =
      ∑ k, (clippedCoreLog A W s z r (completeCellCore W s (x k)) -
        clippedCorePressure μ A W s z r) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [he]
  unfold completeCellCoreFluctuation
  exact le_finitePressureMax (fun q : Fin (2 * W + 1) =>
    |∑ k : Fin K, (clippedCoreLog A W s z q (completeCellCore W s (x k)) -
      clippedCorePressure μ A W s z q)|) r

end BernoulliSection8
