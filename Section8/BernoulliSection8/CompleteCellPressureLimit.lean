import BernoulliSection8.CellResetRates
import BernoulliSection8.ProbabilityComparison

/-! # Complete-cell pressure from actual concentration and capped resets -/

open Filter MeasureTheory
open scoped NNReal Topology BigOperators

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10 BernoulliSection10.ProbabilityLimits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

def completeCellPressureError (I : NguyenBottomSingularInput.{0, 0})
    (W K : ℕ) (z : ℂ) (x : Fin K → IntervalRows W (3 + coreSites W)) : ℝ :=
  (intervalMaxDegreeLog W (K * (3 + coreSites W)) z
      (flattenCompleteCells W (3 + coreSites W) K x) -
    (K : ℝ) * clippedMaxCorePressure rademacherLaw
      (cellClipBound (rademacherCellClipConstant I z) W) W (coreSites W) z) /
      ((K : ℝ) * cellLength W)

theorem completeCellPressureError_tendsto
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput.{0, 0})
    (hI : 1 ≤ I.subgaussianBound) (W K m : ℕ → ℕ)
    (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (hK : ∀ᶠ n in atTop, coreSites (W n) ≤ K n)
    (hm : ∀ᶠ n in atTop, K n * cellSites (W n) ≤ m n)
    (hlog : Tendsto (fun n => Real.log ((m n * W n : ℕ) : ℝ) / (W n : ℝ)) atTop (𝓝 0))
    (z : ℂ) :
    TendstoInProbabilityTri
      (fun n => independentCoreLaw rademacherLaw (W n) (3 + coreSites (W n)) (K n))
      (fun n => completeCellPressureError I (W n) (K n) z) 0 := by
  let μ := fun n => independentCoreLaw rademacherLaw (W n) (3 + coreSites (W n)) (K n)
  let A := fun n => cellClipBound (rademacherCellClipConstant I z) (W n)
  let F := fun n x => completeCellCoreFluctuation rademacherLaw (A n)
    (W n) (coreSites (W n)) (K n) z x / ((K n : ℝ) * cellLength (W n))
  let R := fun n x => optimizingCellResetLoss rademacherLaw (A n)
    (W n) (coreSites (W n)) (K n) z (rademacherResetCap I (W n) z) x /
      ((K n : ℝ) * cellLength (W n))
  let b := fun n => 3 * rademacherTransferLogConstant I z *
    (densityLogScale (W n) / cellSites (W n))
  let E := fun n => (flattenCompleteCells (W n) (3 + coreSites (W n)) (K n)) ⁻¹'
    (rademacherInterfaceGoodEvent I (W n) (K n * (3 + coreSites (W n))))ᶜ
  have hKpos : ∀ᶠ n in atTop, 0 < K n := hK.mono fun n hn =>
    (coreSites_pos (hW n)).trans_le hn
  have hF : TendstoInProbabilityTri μ F 0 :=
    completeCellCoreFluctuation_tendsto rademacherLaw _ (rademacherCellClipConstant_pos I z)
      W K hWtop hK z
  have hR : TendstoInProbabilityTri μ R 0 :=
    normalizedCellResetLoss_tendsto cook I hI W K m hW hWtop hKpos hm hlog z
      (fun n => clippedCoreOptimizingDegree rademacherLaw (A n) (W n) (coreSites (W n)) z)
  have hb : Tendsto b atTop (𝓝 0) := by
    simpa using (tendsto_logScale_div_cellSites.comp hWtop).const_mul
      (3 * rademacherTransferLogConstant I z)
  have hE : Tendsto (fun n => (μ n).real (E n)) atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg) _
      (tendsto_siteCount_mul_exp_neg_width m W hWtop hlog 3
        (half_pos (interfaceCombinedRate_pos I)))
    filter_upwards [hm, hWtop.eventually (eventually_ge_atTop (interfaceCanonicalLargeWThreshold I))]
      with n hmn hWn
    have h := (measurePreserving_real_preimage_le
      (flattenCompleteCells_measurePreserving rademacherLaw (W n) (3 + coreSites (W n)) (K n))
      (rademacherInterfaceGoodEvent I (W n) (K n * (3 + coreSites (W n))))ᶜ).trans
        (rademacherInterfaceGoodEvent_compl_probability_le I hI
          (W n) (K n * (3 + coreSites (W n))) hWn)
    apply h.trans
    have hcount : ((K n * (3 + coreSites (W n)) : ℕ) : ℝ) ≤ m n := by
      exact_mod_cast (show K n * (3 + coreSites (W n)) ≤ m n by
        simpa only [cellSites, Nat.add_comm] using hmn)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcount (by norm_num : (0 : ℝ) ≤ 3))
      (Real.exp_pos _).le
  have hsum : TendstoInProbabilityTri μ (fun n x => |F n x| + |R n x| + b n) 0 := by
    simpa only [zero_add] using
      ((tendstoInProbabilityTri_abs_zero μ hF).add μ
        (tendstoInProbabilityTri_abs_zero μ hR)).add μ
          (tendstoInProbabilityTri_const μ b 0 hb)
  apply tendstoInProbabilityTri_of_good_event_bound μ E hE hsum
  have hlogtop : Tendsto (fun n => Real.log (W n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hWtop)
  filter_upwards [hKpos,
    hWtop.eventually (eventually_ge_atTop (interfaceCanonicalLargeWThreshold I)),
    hlogtop.eventually (eventually_ge_atTop 1)] with n hKn hWn hlogn
  intro x hx
  have hxg : flattenCompleteCells (W n) (3 + coreSites (W n)) (K n) x ∈
      rademacherInterfaceGoodEvent I (W n) (K n * (3 + coreSites (W n))) := by
    simpa only [E, Set.mem_preimage, Set.mem_compl_iff, not_not] using hx
  have hs := complete_cell_pressure_sandwich I hI rademacherLaw (W n) (coreSites (W n))
    (K n) hWn (coreSites_pos (hW n)) z x hxg (A n)
    (rademacherCellClipBound_ge_budget I (W n) (hW n) z hlogn)
    (rademacherResetCap I (W n) z) (rademacherResetCap_ge_budget I (W n) (hW n) z)
  have hden : (0 : ℝ) < (K n : ℝ) * cellLength (W n) :=
    mul_pos (by exact_mod_cast hKn) (by exact_mod_cast cellLength_pos (hW n))
  have hfn : 0 ≤ completeCellCoreFluctuation rademacherLaw (A n)
      (W n) (coreSites (W n)) (K n) z x := completeCellCoreFluctuation_nonneg _ _ _ _ _ _ _
  have hrn : 0 ≤ optimizingCellResetLoss rademacherLaw (A n)
      (W n) (coreSites (W n)) (K n) z (rademacherResetCap I (W n) z) x :=
    Finset.sum_nonneg fun j _ => cappedSpliceLoss_nonneg
      (rademacherResetCap_pos I (W n) (hW n) z).le _ _ _
  have hbn : 0 ≤ b n := mul_nonneg
    (mul_nonneg (by norm_num) (rademacherTransferLogConstant_nonneg I z))
    (div_nonneg (densityLogScale_nonneg (hW n)) (Nat.cast_nonneg _))
  have hbudget : (K n : ℝ) * cellTransferBudget I (W n) 3 z /
      ((K n : ℝ) * cellLength (W n)) = b n := by
    have hKne : (K n : ℝ) ≠ 0 := by exact_mod_cast hKn.ne'
    have hWne : (W n : ℝ) ≠ 0 := by exact_mod_cast (hW n).ne'
    have hcne : (cellSites (W n) : ℝ) ≠ 0 := by
      exact_mod_cast (cellSites_pos (W n)).ne'
    dsimp [b, cellTransferBudget]
    rw [one_add_posLog_nat_eq_log_e_mul (W n) (hW n)]
    simp only [cellLength, Nat.cast_mul, Nat.cast_ofNat]
    change _ = 3 * rademacherTransferLogConstant I z *
      (Real.log (Real.exp 1 * (W n : ℝ)) / (cellSites (W n) : ℝ))
    field_simp [hKne, hWne, hcne] <;> ring
  have hlo := (div_le_div_of_nonneg_right hs.1 hden.le)
  have hup := (div_le_div_of_nonneg_right hs.2 hden.le)
  simp only [sub_div, add_div, hbudget] at hlo hup
  have habs : |completeCellPressureError I (W n) (K n) z x| ≤ F n x + R n x + b n := by
    apply abs_le.mpr
    dsimp [completeCellPressureError, F, R]
    rw [sub_div]
    constructor <;> linarith [div_nonneg hfn hden.le, div_nonneg hrn hden.le]
  have hf0 : 0 ≤ F n x := div_nonneg hfn hden.le
  have hr0 : 0 ≤ R n x := div_nonneg hrn hden.le
  simpa only [abs_of_nonneg hf0, abs_of_nonneg hr0,
    abs_of_nonneg (add_nonneg (add_nonneg hf0 hr0) hbn)] using habs

/-- The same observable on the literal finite interval law, obtained by
the proved inverse coordinate permutation. -/
theorem intervalCompleteCellPressureError_tendsto
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput.{0, 0})
    (hI : 1 ≤ I.subgaussianBound) (W K m : ℕ → ℕ)
    (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (hK : ∀ᶠ n in atTop, coreSites (W n) ≤ K n)
    (hm : ∀ᶠ n in atTop, K n * cellSites (W n) ≤ m n)
    (hlog : Tendsto (fun n => Real.log ((m n * W n : ℕ) : ℝ) / (W n : ℝ)) atTop (𝓝 0))
    (z : ℂ) :
    TendstoInProbabilityTri
      (fun n => intervalRowsLaw (W n) (K n * (3 + coreSites (W n))) rademacherLaw)
      (fun n x => completeCellPressureError I (W n) (K n) z
        (unflattenCompleteCells (W n) (3 + coreSites (W n)) (K n) x)) 0 := by
  exact tendstoInProbabilityTri_comp_measurePreserving _ _
    (fun n => unflattenCompleteCells (W n) (3 + coreSites (W n)) (K n))
    (fun n => unflattenCompleteCells_measurePreserving rademacherLaw
      (W n) (3 + coreSites (W n)) (K n)) _ 0
    (completeCellPressureError_tendsto cook I hI W K m hW hWtop hK hm hlog z)

/-- The complete-cell pressure compared on any ambient physical interval,
normalized by the ambient scalar dimension. -/
def embeddedCompleteCellPressureError (I : NguyenBottomSingularInput.{0, 0})
    (W K m : ℕ) (z : ℂ) (e : Fin (K * (3 + coreSites W)) ↪ Fin m)
    (x : IntervalRows W m) : ℝ :=
  (intervalMaxDegreeLog W (K * (3 + coreSites W)) z (intervalRestriction e x) -
    (K : ℝ) * clippedMaxCorePressure rademacherLaw
      (cellClipBound (rademacherCellClipConstant I z) W) W (coreSites W) z) /
      ((m : ℝ) * W)

theorem embeddedCompleteCellPressureError_tendsto
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput.{0, 0})
    (hI : 1 ≤ I.subgaussianBound) (W K m : ℕ → ℕ)
    (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (hK : ∀ᶠ n in atTop, coreSites (W n) ≤ K n)
    (hm : ∀ᶠ n in atTop, K n * cellSites (W n) ≤ m n)
    (hlog : Tendsto (fun n => Real.log ((m n * W n : ℕ) : ℝ) / (W n : ℝ)) atTop (𝓝 0))
    (z : ℂ) (e : ∀ n, Fin (K n * (3 + coreSites (W n))) ↪ Fin (m n)) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (m n) rademacherLaw)
      (fun n => embeddedCompleteCellPressureError I (W n) (K n) (m n) z (e n)) 0 := by
  let μ := fun n => intervalRowsLaw (W n) (m n) rademacherLaw
  have h := tendstoInProbabilityTri_comp_measurePreserving μ
    (fun n => intervalRowsLaw (W n) (K n * (3 + coreSites (W n))) rademacherLaw)
    (fun n => intervalRestriction (W := W n) (e n))
    (fun n => physicalRestriction_measurePreserving rademacherLaw (e n)) _ 0
    (intervalCompleteCellPressureError_tendsto cook I hI W K m hW hWtop hK hm hlog z)
  let a := fun n => (K n : ℝ) * cellLength (W n) / ((m n : ℝ) * W n)
  have hKpos : ∀ᶠ n in atTop, 0 < K n := hK.mono fun n hn =>
    (coreSites_pos (hW n)).trans_le hn
  have ha : ∀ᶠ n in atTop, |a n| ≤ 1 := by
    filter_upwards [hm, hKpos] with n hmn hKn
    have hmp : 0 < m n := (Nat.mul_pos hKn (cellSites_pos _)).trans_le hmn
    have hden : (0 : ℝ) < (m n : ℝ) * W n :=
      mul_pos (by exact_mod_cast hmp) (by exact_mod_cast hW n)
    have hle : (K n : ℝ) * cellLength (W n) ≤ (m n : ℝ) * W n := by
      exact_mod_cast (show K n * cellLength (W n) ≤ m n * W n by
        simpa only [cellLength, Nat.mul_assoc] using Nat.mul_le_mul_right (W n) hmn)
    dsimp [a]
    rw [abs_of_nonneg (by positivity), div_le_one hden]
    exact hle
  apply tendstoInProbabilityTri_eventually_congr μ
    (tendstoInProbabilityTri_mul_of_bounded μ h a (by norm_num : (0 : ℝ) < 1) ha)
  filter_upwards [hKpos, hm] with n hKn hmn x
  have hKne : (K n : ℝ) ≠ 0 := by exact_mod_cast hKn.ne'
  have hLne : (cellLength (W n) : ℝ) ≠ 0 := by exact_mod_cast (cellLength_pos (hW n)).ne'
  have hWne : (W n : ℝ) ≠ 0 := by exact_mod_cast (hW n).ne'
  have hmne : (m n : ℝ) ≠ 0 := by
    exact_mod_cast ((Nat.mul_pos hKn (cellSites_pos (W n))).trans_le hmn).ne'
  dsimp [a, completeCellPressureError, embeddedCompleteCellPressureError]
  rw [flatten_unflatten_completeCells]
  field_simp [hKne, hLne, hWne, hmne] <;> ring

end BernoulliSection8
