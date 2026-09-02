import BernoulliSection8.CompleteCellPressureLimit
import BernoulliSection8.PressureCalibration
import BernoulliSection8.AnchorBandwidth
import BernoulliSection8.RademacherRemainderLimit
import BernoulliSection8.RademacherSeamLimit

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

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10 BernoulliSection10.ProbabilityLimits
open BernoulliSection10.DiskReference

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The concrete long-interval comparison, before deterministic anchor
calibration. Every probabilistic comparison is proved on physical rows. -/
theorem rademacher_long_log_potential_comparison
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput.{0, 0})
    (hI : 1 ≤ I.subgaussianBound) (W s : ℕ → ℕ)
    (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, anchorSize (W n) ≤ (s n + 3) * W n)
    (hlog : Tendsto (fun n => Real.log (((s n + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) rademacherLaw)
      (fun n x => densityCyclicLogDet (W n) (s n) z x /
        (((s n + 3) * W n : ℕ) : ℝ) -
          targetPressureCenter rademacherLaw (rademacherCellClipConstant I z) (W n) (s n + 3) z) 0 := by
  let μ := fun n => intervalRowsLaw (W n) (s n + 3) rademacherLaw
  have hK : ∀ᶠ n in atTop, coreSites (W n) ≤ targetCells (s n + 3) (W n) :=
    hlong.mono fun n hn => anchorCells_le_targetCells (hW n) hn
  have hm : ∀ᶠ n in atTop, targetCells (s n + 3) (W n) * cellSites (W n) ≤ s n + 3 :=
    Filter.Eventually.of_forall fun n =>
      (Nat.div_mul_le_self ((s n + 3) - 3) (cellSites (W n))).trans (Nat.sub_le _ _)
  have hp := embeddedCompleteCellPressureError_tendsto cook I hI W
    (fun n => targetCells (s n + 3) (W n)) (fun n => s n + 3)
    hW hWtop hK hm hlog z (fun n => targetCompleteCellsEmbedding (W n) (s n + 3))
  have hr := rademacherRemainderDifference_tendsto I hI W s hWtop hlong hlog z
  have hs := rademacherCyclicSeamDifference_tendsto cook I hI W s hWtop hlong hlog z
  have h := (hs.add μ hr).add μ hp
  apply h.congr
  · intro n x
    dsimp [cyclicSeamDifference, rademacherRemainderDifference,
      embeddedCompleteCellPressureError, targetPressureCenter]
    simp only [Nat.cast_mul]
    ring
  · simp

theorem targetCells_anchorSites (W : ℕ) : targetCells (anchorSites W) W = anchorCells W := by
  unfold targetCells anchorSites
  rw [Nat.add_sub_cancel_right, Nat.mul_div_cancel _ (cellSites_pos W)]

theorem anchorPressureCenter_eq_target (I : NguyenBottomSingularInput.{0, 0}) (W : ℕ) (z : ℂ) :
    anchorPressureCenter rademacherLaw (rademacherCellClipConstant I z) W z =
      targetPressureCenter rademacherLaw (rademacherCellClipConstant I z) W (anchorSites W) z := by
  simp only [anchorPressureCenter, targetPressureCenter, targetCells_anchorSites,
    anchorSize, Nat.cast_mul, mul_comm (W : ℝ)]

/-- The anchor comparison has no seam or pressure premise. -/
theorem rademacher_anchor_pressure_comparison
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput.{0, 0})
    (hI : 1 ≤ I.subgaussianBound) (W : ℕ → ℕ)
    (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (anchorSites (W n)) rademacherLaw)
      (fun n x => anchorLogPotential (W n) z x -
        anchorPressureCenter rademacherLaw (rademacherCellClipConstant I z) (W n) z) 0 := by
  have h := rademacher_long_log_potential_comparison cook I hI W
    (fun n => anchorCells (W n) * cellSites (W n)) hW hWtop
    (Filter.Eventually.of_forall fun n => by simp [anchorSize, anchorSites, Nat.mul_comm])
    (tendsto_log_anchorSites_mul_width_div_width W hWtop) z
  simpa only [anchorLogPotential, anchorPressureCenter_eq_target,
    anchorSize, anchorSites, Nat.mul_comm] using h

/-- The pressure limit obtained from the actual many-cell anchor and
Proposition 3.8. No pressure convergence certificate is an input. -/
theorem rademacher_normalizedCorePressure_tendsto
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput.{0, 0})
    (hI : 1 ≤ I.subgaussianBound)
    (hSource : Section3SubgaussianHighBandInput rademacherLaw 1)
    (W : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop) (z : ℂ) :
    Tendsto (fun n => normalizedCorePressure rademacherLaw
      (rademacherCellClipConstant I z) (W n) z) atTop (𝓝 (circularLogPotential z)) :=
  normalizedCorePressure_tendsto_of_anchor_comparison hSource
    (rademacherCellClipConstant I z) W hW hWtop z
      (rademacher_anchor_pressure_comparison cook I hI W hW hWtop z)

theorem rademacher_long_rows_log_potential
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput.{0, 0})
    (hI : 1 ≤ I.subgaussianBound)
    (hSource : Section3SubgaussianHighBandInput rademacherLaw 1)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, anchorSize (W n) ≤ (s n + 3) * W n)
    (hlog : Tendsto (fun n => Real.log (((s n + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) rademacherLaw)
      (fun n x => densityCyclicLogDet (W n) (s n) z x /
        (((s n + 3) * W n : ℕ) : ℝ)) (circularLogPotential z) := by
  let μ := fun n => intervalRowsLaw (W n) (s n + 3) rademacherLaw
  have hratio := tendsto_target_dimension_ratio hWtop
    (Filter.Eventually.of_forall fun n => by omega : ∀ᶠ n in atTop, 3 ≤ s n + 3) hlong
  have hpressure := rademacher_normalizedCorePressure_tendsto cook I hI hSource W hW hWtop z
  have hcenter : Tendsto (fun n => targetPressureCenter rademacherLaw
      (rademacherCellClipConstant I z) (W n) (s n + 3) z) atTop (𝓝 (circularLogPotential z)) := by
    have h := hratio.mul hpressure
    simp only [one_mul] at h
    exact h.congr' (Filter.Eventually.of_forall fun n =>
      (targetPressureCenter_factor _ _ _ _ (hW n) _).symm)
  have h := (rademacher_long_log_potential_comparison cook I hI W s hW hWtop hlong hlog z).add μ
    (tendstoInProbabilityTri_const μ _ _ hcenter)
  apply h.congr
  · intro n x
    ring
  · simp

/-- At unused indices the independent many-cell anchor fills the long
branch. This construction is internal to the convergence proof. -/
def longOrAnchorCoreSites (W s : ℕ) : ℕ :=
  if anchorSize W ≤ (s + 3) * W then s else anchorCells W * cellSites W

def longBranchLogPotential (W s : ℕ) (z : ℂ) (x : IntervalRows W (s + 3)) : ℝ :=
  if anchorSize W ≤ (s + 3) * W then
    densityCyclicLogDet W s z x / (((s + 3) * W : ℕ) : ℝ)
  else circularLogPotential z

theorem rademacher_long_branch_log_potential
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput.{0, 0})
    (hI : 1 ≤ I.subgaussianBound)
    (hSource : Section3SubgaussianHighBandInput rademacherLaw 1)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log (((s n + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) rademacherLaw)
      (fun n => longBranchLogPotential (W n) (s n) z) (circularLogPotential z) := by
  have hlong : ∀ᶠ n in atTop,
      anchorSize (W n) ≤ (longOrAnchorCoreSites (W n) (s n) + 3) * W n := by
    apply Filter.Eventually.of_forall
    intro n
    unfold longOrAnchorCoreSites
    split
    · assumption
    · simp [anchorSize, anchorSites, Nat.mul_comm]
  have hlog' : Tendsto (fun n => Real.log
      (((longOrAnchorCoreSites (W n) (s n) + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0) := by
    have h := hlog.if' (tendsto_log_anchorSites_mul_width_div_width W hWtop)
      (p := fun n => anchorSize (W n) ≤ (s n + 3) * W n)
    convert h using 1
    funext n
    unfold longOrAnchorCoreSites
    split <;> simp_all only [anchorSites]
  have h := rademacher_long_rows_log_potential cook I hI hSource W
    (fun n => longOrAnchorCoreSites (W n) (s n)) hW hWtop hlong hlog' z
  intro ε hε
  refine squeeze_zero (t₀ := (atTop : Filter ℕ))
    (f := fun n : ℕ => (intervalRowsLaw (W n) (s n + 3) rademacherLaw).real
      {x : IntervalRows (W n) (s n + 3) |
        ε ≤ |longBranchLogPotential (W n) (s n) z x - circularLogPotential z|})
    (fun n : ℕ => measureReal_nonneg) ?_ (h ε hε)
  intro n
  by_cases hn : anchorSize (W n) ≤ (s n + 3) * W n
  · simp only [longBranchLogPotential, longOrAnchorCoreSites, if_pos hn]
  · simp only [longBranchLogPotential, if_neg hn, sub_self, abs_zero]
    have he : {x : IntervalRows (W n) (s n + 3) | ε ≤ (0 : ℝ)} = ∅ := by
      ext x
      simp [not_le_of_gt hε]
    rw [he, measureReal_empty]
    exact measureReal_nonneg

/-- Actual finite-row Bernoulli logarithmic potential, including arbitrary
alternation of the high-band and long branches. -/
theorem rademacher_rows_log_potential
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput.{0, 0})
    (hI : 1 ≤ I.subgaussianBound)
    (hSource : Section3SubgaussianHighBandInput rademacherLaw 1)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hs : ∀ n, 0 < s n)
    (hWtop : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log (((s n + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) rademacherLaw)
      (fun n x => densityCyclicLogDet (W n) (s n) z x /
        (((s n + 3) * W n : ℕ) : ℝ)) (circularLogPotential z) := by
  have hshort := rademacher_direct_branch_log_potential hSource W s hW hs hWtop z
  have hlong := rademacher_long_branch_log_potential cook I hI hSource W s hW hWtop hlog z
  have h := tendstoInProbabilityTri_branchSelected
    (fun n => intervalRowsLaw (W n) (s n + 3) rademacherLaw)
    (fun n => decide ((s n + 3) * W n < anchorSize (W n)))
    (fun n => directBranchLogPotential (W n) (s n) z)
    (fun n => longBranchLogPotential (W n) (s n) z) (circularLogPotential z) hshort hlong
  apply h.congr
  · intro n x
    by_cases hn : (s n + 3) * W n < anchorSize (W n)
    · simp [branchSelectedTri, directBranchLogPotential, hn]
    · have hl := Nat.le_of_not_gt hn
      simp [branchSelectedTri, longBranchLogPotential, hn, hl]
  · rfl

/-- Caller-facing convergence on the actual IID Rademacher sequence. -/
theorem rademacher_log_potential
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput.{0, 0})
    (hI : 1 ≤ I.subgaussianBound)
    (hSource : Section3SubgaussianHighBandInput rademacherLaw 1)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hs : ∀ n, 0 < s n)
    (hWtop : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log (((s n + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) (z : ℂ) :
    TendstoInMeasure rademacherSequenceLaw
      (fun n x => ShortRingAnchor.normalizedShiftLogDet (rademacherMatrix (W n) (s n) x) z)
      atTop (fun _ => circularLogPotential z) :=
  (rademacher_log_converges_iff_physical_rows W s z _).2
    (rademacher_rows_log_potential cook I hI hSource W s hW hs hWtop hlog z)

end BernoulliSection8
