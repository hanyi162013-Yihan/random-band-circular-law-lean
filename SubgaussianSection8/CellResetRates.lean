import SubgaussianSection8.CellPressureSandwich
import SubgaussianSection8.TerminalRates
import BernoulliSection8.AveragedRates

/-! # Vanishing total reset loss in the actual complete-cell array -/

open Filter MeasureTheory
open scoped NNReal Topology BigOperators

noncomputable section

namespace SubgaussianSection8
open BernoulliSection8

open BernoulliSection9 BernoulliSection10 BernoulliSection10.ProbabilityLimits

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def subgaussianCellClipConstant (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0}) (z : ℂ) : ℝ≥0 :=
  ⟨2 * ((subgaussianTransferLogConstant Ξ) I z + 1), by
    have h := (subgaussianTransferLogConstant_nonneg Ξ) I z
    positivity⟩

theorem subgaussianCellClipConstant_pos (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0}) (z : ℂ) :
    0 < (subgaussianCellClipConstant Ξ) I z := by
  change 0 < (2 * ((subgaussianTransferLogConstant Ξ) I z + 1) : ℝ)
  have h := (subgaussianTransferLogConstant_nonneg Ξ) I z
  positivity

def subgaussianResetCapConstant (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0}) (z : ℂ) : ℝ :=
  3 * ((subgaussianTransferLogConstant Ξ) I z + 1)

def subgaussianResetCap (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0}) (W : ℕ) (z : ℂ) : ℝ :=
  (subgaussianResetCapConstant Ξ) I z * cellLength W * densityLogScale W

theorem subgaussianResetCap_pos (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0}) (W : ℕ)
    (hW : 0 < W) (z : ℂ) : 0 < (subgaussianResetCap Ξ) I W z := by
  have h1 := (subgaussianTransferLogConstant_nonneg Ξ) I z
  have h2 : (0 : ℝ) < cellLength W := by exact_mod_cast cellLength_pos hW
  have hl : 0 < densityLogScale W := by
    rw [densityLogScale_eq hW]
    have hlog := Real.log_natCast_nonneg W
    linarith
  unfold subgaussianResetCap subgaussianResetCapConstant
  positivity

theorem subgaussianCellClipBound_ge_budget (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0})
    (W : ℕ) (hW : 0 < W) (z : ℂ) (hlog : 1 ≤ Real.log W) :
    (cellTransferBudget Ξ) I W (coreSites W) z ≤ cellClipBound ((subgaussianCellClipConstant Ξ) I z) W := by
  have ht := (subgaussianTransferLogConstant_nonneg Ξ) I z
  rw [(cellTransferBudget Ξ), one_add_posLog_nat_eq_log_e_mul W hW, ← densityLogScale]
  rw [densityLogScale_eq hW]
  change (subgaussianTransferLogConstant Ξ) I z * ((coreSites W * W : ℕ) : ℝ) *
    (1 + Real.log W) ≤ 2 * ((subgaussianTransferLogConstant Ξ) I z + 1) *
      (cellLength W : ℝ) * Real.log W
  have hs : ((coreSites W * W : ℕ) : ℝ) ≤ cellLength W := by
    exact_mod_cast Nat.mul_le_mul_right W (by simp [cellSites] : coreSites W ≤ cellSites W)
  calc
    _ ≤ (subgaussianTransferLogConstant Ξ) I z * (cellLength W : ℝ) * (2 * Real.log W) := by
      gcongr
      linarith
    _ ≤ _ := by nlinarith [mul_nonneg (Nat.cast_nonneg (cellLength W)) (Real.log_natCast_nonneg W)]

theorem subgaussianResetCap_ge_budget (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0})
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    2 * (cellTransferBudget Ξ) I W (coreSites W) z + (cellTransferBudget Ξ) I W 3 z ≤
      (subgaussianResetCap Ξ) I W z := by
  have ht := (subgaussianTransferLogConstant_nonneg Ξ) I z
  have hl := densityLogScale_nonneg hW
  simp only [(cellTransferBudget Ξ), one_add_posLog_nat_eq_log_e_mul W hW,
    (subgaussianResetCap Ξ), (subgaussianResetCapConstant Ξ), cellLength, cellSites,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  change 2 * ((subgaussianTransferLogConstant Ξ) I z * ((coreSites W : ℝ) * W) * densityLogScale W) +
    (subgaussianTransferLogConstant Ξ) I z * (3 * W) * densityLogScale W ≤
    3 * ((subgaussianTransferLogConstant Ξ) I z + 1) * (((coreSites W : ℝ) + 3) * W) * densityLogScale W
  have hbase : 2 * ((subgaussianTransferLogConstant Ξ) I z * (coreSites W : ℝ)) +
      3 * (subgaussianTransferLogConstant Ξ) I z ≤
      3 * ((subgaussianTransferLogConstant Ξ) I z + 1) * ((coreSites W : ℝ) + 3) := by
    nlinarith [mul_nonneg ht (Nat.cast_nonneg (coreSites W))]
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbase
    (Nat.cast_nonneg W)) hl
  nlinarith

theorem measurable_cellIntervalResetLoss (Ξ : Atom) (W s K : ℕ) (j : Fin K)
    (z : ℂ) (r : Fin (2 * W + 1)) (T : ℝ) :
    Measurable ((cellIntervalResetLoss Ξ) W s K j z r T) := by
  have h := ((measurable_intervalResetLoss Ξ) W s (j.val * (3 + s)) z r T).comp
    ((cellThroughResetRows_measurePreserving Ξ) Ξ.law W s K j).measurable
  simpa only [Function.comp_def, ← (cellIntervalResetLoss_eq_intervalResetLoss Ξ)] using h

theorem integrable_cellIntervalResetLoss (Ξ : Atom) (W s K : ℕ) (j : Fin K)
    (z : ℂ) (r : Fin (2 * W + 1)) {T : ℝ} (hT : 0 ≤ T) :
    Integrable ((cellIntervalResetLoss Ξ) W s K j z r T)
      (independentCoreLaw Ξ.law W (3 + s) K) := by
  apply (integrable_const T).mono'
    ((measurable_cellIntervalResetLoss Ξ) W s K j z r T).aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_of_nonneg (show 0 ≤ (cellIntervalResetLoss Ξ) W s K j z r T x from
    cappedSpliceLoss_nonneg hT _ _ _)]
  exact cappedSpliceLoss_le_cap _ _ _ _

def subgaussianResetMeanError (Ξ : Atom) (cook : CookInput Ξ) (I : NguyenBottomSingularInput.{0, 0})
    (z : ℂ) (m W : ℕ) : ℝ :=
  averagedResetError ((subgaussianBoundaryLogConstant Ξ) I z + (subgaussianTerminalLossConstant Ξ) cook)
    ((subgaussianResetCapConstant Ξ) I z) (interfaceCombinedRate I / 2)
    ((subgaussianBoundaryBadProbability Ξ) cook) m W

theorem cellIntervalResetLoss_integral_le_meanError (Ξ : Atom)
    (cook : CookInput Ξ) (I : NguyenBottomSingularInput.{0, 0})
    (hI : Ξ.parameter ≤ I.subgaussianBound) (W K m : ℕ) (j : Fin K) (z : ℂ)
    (hW : (subgaussianBoundaryWidthThreshold Ξ) cook z ≤ W)
    (hWI : interfaceCanonicalLargeWThreshold I ≤ W)
    (hm : K * cellSites W ≤ m) (r : Fin (2 * W + 1)) :
    (∫ x, (cellIntervalResetLoss Ξ) W (coreSites W) K j z r ((subgaussianResetCap Ξ) I W z) x
      ∂independentCoreLaw Ξ.law W (3 + coreSites W) K) ≤
      (cellLength W : ℝ) * (subgaussianResetMeanError Ξ) cook I z m W := by
  have hW0 := ((subgaussianBoundaryWidthThreshold_pos Ξ) cook z).trans_le hW
  have hc := (cellIntervalResetLoss_integral_le Ξ) cook I hI W (coreSites W) K j z hW hWI r
    ((subgaussianResetCap_pos Ξ) I W hW0 z)
  have hb := (subgaussianBoundaryBaseLoss_le_of_threshold Ξ) cook W z hW
  have hs : coreSites W + j.val * (3 + coreSites W) ≤ m := by
    calc
      _ ≤ (j.val + 1) * cellSites W := by dsimp [cellSites]; nlinarith
      _ ≤ K * cellSites W := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt j.isLt)
      _ ≤ m := hm
  have hsr : (coreSites W : ℝ) + (j.val * (3 + coreSites W) : ℕ) ≤ (m : ℝ) := by
    exact_mod_cast hs
  have hp : (9 + 3 * ((coreSites W : ℝ) + (j.val * (3 + coreSites W) : ℕ))) *
      Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) ≤
      (9 + 3 * (m : ℝ)) * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
    gcongr
  have hcap := (subgaussianResetCap_pos Ξ) I W hW0 z
  have hmul := mul_le_mul_of_nonneg_left hp hcap.le
  have hid : (cellLength W : ℝ) * (subgaussianResetMeanError Ξ) cook I z m W =
      ((subgaussianBoundaryLogConstant Ξ) I z + (subgaussianTerminalLossConstant Ξ) cook) *
        W * densityLogScale W + (subgaussianResetCap Ξ) I W z *
          ((subgaussianBoundaryBadProbability Ξ) cook W + (9 + 3 * (m : ℝ)) *
            Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ))) := by
    have hcs : (cellSites W : ℝ) ≠ 0 := by exact_mod_cast (cellSites_pos W).ne'
    unfold subgaussianResetMeanError averagedResetError subgaussianResetCap
    simp only [cellLength, Nat.cast_mul]
    field_simp [hcs] <;> ring
  rw [hid]
  nlinarith

theorem tendsto_subgaussianResetMeanError (Ξ : Atom)
    (cook : CookInput Ξ) (I : NguyenBottomSingularInput.{0, 0}) (z : ℂ)
    (m W : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log ((m n * W n : ℕ) : ℝ) / (W n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => (subgaussianResetMeanError Ξ) cook I z (m n) (W n)) atTop (𝓝 0) :=
  tendsto_averagedResetError _ _ (half_pos (interfaceCombinedRate_pos I)) _
    ((tendsto_subgaussianBoundaryBadProbability_mul_logScale Ξ) cook) m W hW hlog

/-- Sum first and apply Markov once. No union bound over Cook failures is
present, including when the number of cells grows faster than any power. -/
theorem normalizedCellResetLoss_tendsto (Ξ : Atom)
    (cook : CookInput Ξ) (I : NguyenBottomSingularInput.{0, 0})
    (hI : Ξ.parameter ≤ I.subgaussianBound) (W K m : ℕ → ℕ)
    (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (hK : ∀ᶠ n in atTop, 0 < K n)
    (hm : ∀ᶠ n in atTop, K n * cellSites (W n) ≤ m n)
    (hlog : Tendsto (fun n => Real.log ((m n * W n : ℕ) : ℝ) / (W n : ℝ)) atTop (𝓝 0))
    (z : ℂ) (r : ∀ n, Fin (2 * W n + 1)) :
    TendstoInProbabilityTri
      (fun n => independentCoreLaw Ξ.law (W n) (3 + coreSites (W n)) (K n))
      (fun n x => (∑ j, (cellIntervalResetLoss Ξ) (W n) (coreSites (W n)) (K n) j z (r n)
        ((subgaussianResetCap Ξ) I (W n) z) x) / ((K n : ℝ) * cellLength (W n))) 0 := by
  intro ε hε
  have herr := ((tendsto_subgaussianResetMeanError Ξ) cook I z m W hWtop hlog).div_const ε
  simp only [zero_div] at herr
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg) _ herr
  filter_upwards [hWtop.eventually (eventually_ge_atTop ((subgaussianBoundaryWidthThreshold Ξ) cook z)),
    hWtop.eventually (eventually_ge_atTop (interfaceCanonicalLargeWThreshold I)), hK, hm]
    with n hWn hWIn hKn hmn
  have hden : (0 : ℝ) < (K n : ℝ) * cellLength (W n) :=
    mul_pos (by exact_mod_cast hKn) (by exact_mod_cast cellLength_pos (hW n))
  have hcap := ((subgaussianResetCap_pos Ξ) I (W n) (hW n) z).le
  have hn : ∀ x, 0 ≤ ∑ j, (cellIntervalResetLoss Ξ) (W n) (coreSites (W n)) (K n) j z
      (r n) ((subgaussianResetCap Ξ) I (W n) z) x := by
    intro x
    exact Finset.sum_nonneg fun j _ => cappedSpliceLoss_nonneg hcap _ _ _
  have hp := summed_loss_probability_le
    (independentCoreLaw Ξ.law (W n) (3 + coreSites (W n)) (K n))
    (fun j => (cellIntervalResetLoss Ξ) (W n) (coreSites (W n)) (K n) j z (r n)
      ((subgaussianResetCap Ξ) I (W n) z))
    (fun _ => (cellLength (W n) : ℝ) * (subgaussianResetMeanError Ξ) cook I z (m n) (W n))
    (fun j => (integrable_cellIntervalResetLoss Ξ) _ _ _ j _ _ hcap)
    (fun j => ae_of_all _ fun x => cappedSpliceLoss_nonneg hcap _ _ _)
    (fun j => (cellIntervalResetLoss_integral_le_meanError Ξ) cook I hI (W n) (K n) (m n) j z
      hWn hWIn hmn (r n)) (mul_pos hε hden)
  have he : {x | ε ≤ |(∑ j, (cellIntervalResetLoss Ξ) (W n) (coreSites (W n)) (K n) j z
      (r n) ((subgaussianResetCap Ξ) I (W n) z) x) / ((K n : ℝ) * cellLength (W n)) - 0|} =
      {x | ε * ((K n : ℝ) * cellLength (W n)) ≤ ∑ j,
        (cellIntervalResetLoss Ξ) (W n) (coreSites (W n)) (K n) j z (r n)
          ((subgaussianResetCap Ξ) I (W n) z) x} := by
    ext x
    simp only [Set.mem_setOf_eq, sub_zero,
      abs_of_nonneg (div_nonneg (hn x) hden.le), le_div_iff₀ hden]
  rw [he]
  apply hp.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hKne : (K n : ℝ) ≠ 0 := by exact_mod_cast hKn.ne'
  have hLne : (cellLength (W n) : ℝ) ≠ 0 := by exact_mod_cast (cellLength_pos (hW n)).ne'
  field_simp [hKne, hLne, hε.ne'] <;> ring

end SubgaussianSection8
