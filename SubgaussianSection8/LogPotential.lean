import SubgaussianSection8.CompleteCellPressureLimit
import SubgaussianSection8.PressureCalibration
import BernoulliSection8.AnchorBandwidth
import SubgaussianSection8.RemainderLimit
import SubgaussianSection8.SeamLimit

/-!
# The actual Bernoulli logarithmic potential

The local capped reset bounds, independent core concentration, incomplete
cell estimate, and terminal packet comparison are assembled before the
Section 3 anchor calibrates the deterministic pressure. Only Nguyen,
Cook, and the approved Section 3 input occur in the final theorem.
-/

open Filter MeasureTheory
open scoped Topology NNReal

noncomputable section

namespace SubgaussianSection8
open BernoulliSection8

open BernoulliSection9 BernoulliSection10 BernoulliSection10.ProbabilityLimits
open BernoulliSection10.DiskReference ShortRingAnchor

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The concrete long-interval comparison, before deterministic anchor
calibration. Every probabilistic comparison is proved on physical rows. -/
theorem subgaussian_long_log_potential_comparison (Ξ : Atom)
    (cook : CookInput Ξ) (I : NguyenBottomSingularInput.{0, 0})
    (hI : Ξ.parameter ≤ I.subgaussianBound) (W s : ℕ → ℕ)
    (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, anchorSize (W n) ≤ (s n + 3) * W n)
    (hlog : Tendsto (fun n => Real.log (((s n + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) Ξ.law)
      (fun n x => densityCyclicLogDet (W n) (s n) z x /
        (((s n + 3) * W n : ℕ) : ℝ) -
          targetPressureCenter Ξ.law ((subgaussianCellClipConstant Ξ) I z) (W n) (s n + 3) z) 0 := by
  let μ := fun n => intervalRowsLaw (W n) (s n + 3) Ξ.law
  have hK : ∀ᶠ n in atTop, coreSites (W n) ≤ targetCells (s n + 3) (W n) :=
    hlong.mono fun n hn => anchorCells_le_targetCells (hW n) hn
  have hm : ∀ᶠ n in atTop, targetCells (s n + 3) (W n) * cellSites (W n) ≤ s n + 3 :=
    Filter.Eventually.of_forall fun n =>
      (Nat.div_mul_le_self ((s n + 3) - 3) (cellSites (W n))).trans (Nat.sub_le _ _)
  have hp := (embeddedCompleteCellPressureError_tendsto Ξ) cook I hI W
    (fun n => targetCells (s n + 3) (W n)) (fun n => s n + 3)
    hW hWtop hK hm hlog z (fun n => targetCompleteCellsEmbedding (W n) (s n + 3))
  have hr := (subgaussianRemainderDifference_tendsto Ξ) I hI W s hWtop hlong hlog z
  have hs := (subgaussianCyclicSeamDifference_tendsto Ξ) cook I hI W s hWtop hlong hlog z
  have h := (hs.add μ hr).add μ hp
  apply h.congr
  · intro n x
    dsimp [cyclicSeamDifference, subgaussianRemainderDifference,
      embeddedCompleteCellPressureError, targetPressureCenter]
    simp only [Nat.cast_mul]
    ring
  · simp

theorem targetCells_anchorSites (Ξ : Atom) (W : ℕ) : targetCells (anchorSites W) W = anchorCells W := by
  unfold targetCells anchorSites
  rw [Nat.add_sub_cancel_right, Nat.mul_div_cancel _ (cellSites_pos W)]

theorem anchorPressureCenter_eq_target (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0}) (W : ℕ) (z : ℂ) :
    anchorPressureCenter Ξ.law ((subgaussianCellClipConstant Ξ) I z) W z =
      targetPressureCenter Ξ.law ((subgaussianCellClipConstant Ξ) I z) W (anchorSites W) z := by
  simp only [anchorPressureCenter, targetPressureCenter, (targetCells_anchorSites Ξ),
    anchorSize, Nat.cast_mul, mul_comm (W : ℝ)]

/-- The anchor comparison has no seam or pressure premise. -/
theorem subgaussian_anchor_pressure_comparison (Ξ : Atom)
    (cook : CookInput Ξ) (I : NguyenBottomSingularInput.{0, 0})
    (hI : Ξ.parameter ≤ I.subgaussianBound) (W : ℕ → ℕ)
    (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (anchorSites (W n)) Ξ.law)
      (fun n x => (anchorLogPotential Ξ) (W n) z x -
        anchorPressureCenter Ξ.law ((subgaussianCellClipConstant Ξ) I z) (W n) z) 0 := by
  have h := (subgaussian_long_log_potential_comparison Ξ) cook I hI W
    (fun n => anchorCells (W n) * cellSites (W n)) hW hWtop
    (Filter.Eventually.of_forall fun n => by simp [anchorSize, anchorSites, Nat.mul_comm])
    (tendsto_log_anchorSites_mul_width_div_width W hWtop) z
  simpa only [anchorLogPotential, (anchorPressureCenter_eq_target Ξ),
    anchorSize, anchorSites, Nat.mul_comm] using h

/-- The pressure limit obtained from the actual many-cell anchor and
Proposition 3.8. No pressure convergence certificate is an input. -/
theorem subgaussian_normalizedCorePressure_tendsto (Ξ : Atom)
    (cook : CookInput Ξ) (I : NguyenBottomSingularInput.{0, 0})
    (hI : Ξ.parameter ≤ I.subgaussianBound)
    (hSource : Section3Input Ξ)
    (W : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop) (z : ℂ) :
    Tendsto (fun n => normalizedCorePressure Ξ.law
      ((subgaussianCellClipConstant Ξ) I z) (W n) z) atTop (𝓝 (circularLogPotential z)) :=
  normalizedCorePressure_tendsto_of_anchor_comparison Ξ hSource
    ((subgaussianCellClipConstant Ξ) I z) W hW hWtop z
      ((subgaussian_anchor_pressure_comparison Ξ) cook I hI W hW hWtop z)

theorem subgaussian_long_rows_log_potential (Ξ : Atom)
    (cook : CookInput Ξ) (I : NguyenBottomSingularInput.{0, 0})
    (hI : Ξ.parameter ≤ I.subgaussianBound)
    (hSource : Section3Input Ξ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, anchorSize (W n) ≤ (s n + 3) * W n)
    (hlog : Tendsto (fun n => Real.log (((s n + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) Ξ.law)
      (fun n x => densityCyclicLogDet (W n) (s n) z x /
        (((s n + 3) * W n : ℕ) : ℝ)) (circularLogPotential z) := by
  let μ := fun n => intervalRowsLaw (W n) (s n + 3) Ξ.law
  have hratio := tendsto_target_dimension_ratio hWtop
    (Filter.Eventually.of_forall fun n => by omega : ∀ᶠ n in atTop, 3 ≤ s n + 3) hlong
  have hpressure := (subgaussian_normalizedCorePressure_tendsto Ξ) cook I hI hSource W hW hWtop z
  have hcenter : Tendsto (fun n => targetPressureCenter Ξ.law
      ((subgaussianCellClipConstant Ξ) I z) (W n) (s n + 3) z) atTop (𝓝 (circularLogPotential z)) := by
    have h := hratio.mul hpressure
    simp only [one_mul] at h
    exact h.congr' (Filter.Eventually.of_forall fun n =>
      (targetPressureCenter_factor _ _ _ _ (hW n) _).symm)
  have h := ((subgaussian_long_log_potential_comparison Ξ) cook I hI W s hW hWtop hlong hlog z).add μ
    (tendstoInProbabilityTri_const μ _ _ hcenter)
  apply h.congr
  · intro n x
    ring
  · simp

/-- At unused indices the independent many-cell anchor fills the long
branch. This construction is internal to the convergence proof. -/
def longOrAnchorCoreSites (Ξ : Atom) (W s : ℕ) : ℕ :=
  if anchorSize W ≤ (s + 3) * W then s else anchorCells W * cellSites W

def longBranchLogPotential (Ξ : Atom) (W s : ℕ) (z : ℂ) (x : IntervalRows W (s + 3)) : ℝ :=
  if anchorSize W ≤ (s + 3) * W then
    densityCyclicLogDet W s z x / (((s + 3) * W : ℕ) : ℝ)
  else circularLogPotential z

theorem subgaussian_long_branch_log_potential (Ξ : Atom)
    (cook : CookInput Ξ) (I : NguyenBottomSingularInput.{0, 0})
    (hI : Ξ.parameter ≤ I.subgaussianBound)
    (hSource : Section3Input Ξ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log (((s n + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) Ξ.law)
      (fun n => (longBranchLogPotential Ξ) (W n) (s n) z) (circularLogPotential z) := by
  have hlong : ∀ᶠ n in atTop,
      anchorSize (W n) ≤ ((longOrAnchorCoreSites Ξ) (W n) (s n) + 3) * W n := by
    apply Filter.Eventually.of_forall
    intro n
    unfold longOrAnchorCoreSites
    split
    · assumption
    · simp [anchorSize, anchorSites, Nat.mul_comm]
  have hlog' : Tendsto (fun n => Real.log
      ((((longOrAnchorCoreSites Ξ) (W n) (s n) + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0) := by
    have h := hlog.if' (tendsto_log_anchorSites_mul_width_div_width W hWtop)
      (p := fun n => anchorSize (W n) ≤ (s n + 3) * W n)
    convert h using 1
    funext n
    unfold longOrAnchorCoreSites
    split <;> simp_all only [anchorSites]
  have h := (subgaussian_long_rows_log_potential Ξ) cook I hI hSource W
    (fun n => (longOrAnchorCoreSites Ξ) (W n) (s n)) hW hWtop hlong hlog' z
  intro ε hε
  refine squeeze_zero (t₀ := (atTop : Filter ℕ))
    (f := fun n : ℕ => (intervalRowsLaw (W n) (s n + 3) Ξ.law).real
      {x : IntervalRows (W n) (s n + 3) |
        ε ≤ |(longBranchLogPotential Ξ) (W n) (s n) z x - circularLogPotential z|})
    (fun n : ℕ => measureReal_nonneg) ?_ (h ε hε)
  intro n
  by_cases hn : anchorSize (W n) ≤ (s n + 3) * W n
  · let F : ℕ → ℝ := fun q =>
      (intervalRowsLaw (W n) (q + 3) Ξ.law).real
        {x : IntervalRows (W n) (q + 3) |
          ε ≤ |densityCyclicLogDet (W n) q z x /
            (((q + 3) * W n : ℕ) : ℝ) - circularLogPotential z|}
    have hsites : (longOrAnchorCoreSites Ξ) (W n) (s n) = s n := by
      simp only [longOrAnchorCoreSites, if_pos hn]
    have hvalue : (intervalRowsLaw (W n) (s n + 3) Ξ.law).real
        {x : IntervalRows (W n) (s n + 3) |
          ε ≤ |(longBranchLogPotential Ξ) (W n) (s n) z x - circularLogPotential z|} =
        F (s n) := by
      simp only [F, longBranchLogPotential, if_pos hn]
    exact (hvalue.trans (congrArg F hsites).symm).le
  · simp only [longBranchLogPotential, if_neg hn, sub_self, abs_zero]
    have he : {x : IntervalRows (W n) (s n + 3) | ε ≤ (0 : ℝ)} = ∅ := by
      ext x
      simp [not_le_of_gt hε]
    rw [he, measureReal_empty]
    exact measureReal_nonneg

/-- Actual finite-row Bernoulli logarithmic potential, including arbitrary
alternation of the high-band and long branches. -/
theorem subgaussian_rows_log_potential (Ξ : Atom)
    (cook : CookInput Ξ) (I : NguyenBottomSingularInput.{0, 0})
    (hI : Ξ.parameter ≤ I.subgaussianBound)
    (hSource : Section3Input Ξ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hs : ∀ n, 0 < s n)
    (hWtop : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log (((s n + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) Ξ.law)
      (fun n x => densityCyclicLogDet (W n) (s n) z x /
        (((s n + 3) * W n : ℕ) : ℝ)) (circularLogPotential z) := by
  have hshort := (subgaussian_direct_branch_log_potential Ξ) hSource W s hW hs hWtop z
  have hlong := (subgaussian_long_branch_log_potential Ξ) cook I hI hSource W s hW hWtop hlog z
  have h := tendstoInProbabilityTri_branchSelected
    (fun n => intervalRowsLaw (W n) (s n + 3) Ξ.law)
    (fun n => decide ((s n + 3) * W n < anchorSize (W n)))
    (fun n => (directBranchLogPotential Ξ) (W n) (s n) z)
    (fun n => (longBranchLogPotential Ξ) (W n) (s n) z) (circularLogPotential z) hshort hlong
  apply h.congr
  · intro n x
    by_cases hn : (s n + 3) * W n < anchorSize (W n)
    · simp [branchSelectedTri, directBranchLogPotential, hn]
    · have hl := Nat.le_of_not_gt hn
      simp [branchSelectedTri, longBranchLogPotential, hn, hl]
  · rfl

/-- Caller-facing convergence on the actual IID subgaussian sequence. -/
theorem subgaussian_log_potential (Ξ : Atom)
    (cook : CookInput Ξ) (I : NguyenBottomSingularInput.{0, 0})
    (hI : Ξ.parameter ≤ I.subgaussianBound)
    (hSource : Section3Input Ξ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hs : ∀ n, 0 < s n)
    (hWtop : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log (((s n + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) (z : ℂ) :
    TendstoInMeasure (sequenceLaw Ξ)
      (fun n x => ShortRingAnchor.normalizedShiftLogDet (matrix (W n) (s n) x) z)
      atTop (fun _ => circularLogPotential z) :=
  ((subgaussian_log_converges_iff_physical_rows Ξ) W s z _).2
    ((subgaussian_rows_log_potential Ξ) cook I hI hSource W s hW hs hWtop hlog z)

end SubgaussianSection8
