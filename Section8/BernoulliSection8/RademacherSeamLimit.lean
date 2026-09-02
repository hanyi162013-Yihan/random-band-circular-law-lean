import BernoulliSection8.RademacherSeam
import BernoulliSection8.RademacherTerminalRates
import BernoulliSection8.RademacherCircularReduction
import BernoulliSection8.MesoscopicScales
import BernoulliSection10.AsymptoticErrors
import BernoulliSection10.ProbabilityTransport
import BernoulliSection10.PhysicalProbabilityInstances

/-! # Vanishing seam error on the actual Bernoulli ring

The long branch is the literal `N ≥ M_W` branch from Section 8. The
terminal cap is `εN/2`; its base loss and deterministic centering cost
are `O(W log(eW))`. The Cook term vanishes without a union bound, while
the Nguyen interface term is absorbed by `log N / W → 0`. Zero Fock
values are included in the same exceptional event throughout.
-/

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10 BernoulliSection10.ProbabilityLimits

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem tendsto_widthLogScale_div_dimension_of_anchor
    (W N : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, anchorSize (W n) ≤ N n) :
    Tendsto (fun n => (W n : ℝ) * densityLogScale (W n) / N n) atTop (𝓝 0) := by
  have hpos := hW.eventually (eventually_gt_atTop 0)
  have hp : ∀ᶠ n in atTop, (W n : ℝ) ^ (101 / 100 : ℝ) ≤ N n := by
    filter_upwards [hpos, hlong] with n hn hN
    exact (rpow_le_anchorSize hn).trans (by exact_mod_cast hN)
  apply squeeze_zero' _ _ (tendsto_densityTargetErrorScale hW hp)
  · filter_upwards [hpos] with n hn
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (densityLogScale_nonneg hn))
      (Nat.cast_nonneg _)
  · filter_upwards [hpos] with n hn
    have hL := densityLogScale_nonneg hn
    have hrest : 0 ≤ (W n : ℝ) * densityLogScale (W n) / densityAnchorSize (W n) +
        Real.sqrt ((W n : ℝ) / N n) * densityLogScale (W n) +
        (densityAnchorSize (W n) : ℝ) * densityLogScale (W n) / N n := by positivity
    have hlast : 0 ≤ densityLogScale (W n) / (W n : ℝ) ^ (1 / 400 : ℝ) := by positivity
    unfold densityTargetErrorScale
    linarith

theorem rademacherSeamCost_le (I : NguyenBottomSingularInput)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    rademacherSeamCost I W z ≤
      (rademacherBoundaryLogConstant I z + Real.log 2) * W * densityLogScale W := by
  have hlog := Real.log_nonneg (by exact_mod_cast hW : (1 : ℝ) ≤ W)
  have hL : 1 ≤ densityLogScale W := by rw [densityLogScale_eq hW]; linarith
  have hterm := mul_le_mul_of_nonneg_left hL
    (mul_nonneg (Nat.cast_nonneg W) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)))
  unfold rademacherSeamCost
  nlinarith

theorem tendsto_rademacherBoundaryBaseLoss_div_dimension
    (cook : CookDeformedSquareInput) (W N : ℕ → ℕ) (z : ℂ)
    (hW : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, anchorSize (W n) ≤ N n) :
    Tendsto (fun n => rademacherBoundaryBaseLoss cook (W n) z / N n) atTop (𝓝 0) := by
  have h := (tendsto_widthLogScale_div_dimension_of_anchor W N hW hlong).const_mul
    (rademacherTerminalLossConstant cook)
  simp only [mul_zero] at h
  apply squeeze_zero' (Eventually.of_forall fun n =>
    div_nonneg (rademacherBoundaryBaseLoss_nonneg cook (W n) z) (Nat.cast_nonneg _)) _ h
  filter_upwards [hW.eventually (eventually_ge_atTop (rademacherBoundaryWidthThreshold cook z))]
    with n hn
  have hb := div_le_div_of_nonneg_right
    (rademacherBoundaryBaseLoss_le_of_threshold cook (W n) z hn) (Nat.cast_nonneg (N n) : (0 : ℝ) ≤ N n)
  simpa only [mul_div_assoc, mul_assoc] using hb

theorem tendsto_rademacherSeamCost_div_dimension
    (I : NguyenBottomSingularInput) (W N : ℕ → ℕ) (z : ℂ)
    (hW : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, anchorSize (W n) ≤ N n) :
    Tendsto (fun n => rademacherSeamCost I (W n) z / N n) atTop (𝓝 0) := by
  have h := (tendsto_widthLogScale_div_dimension_of_anchor W N hW hlong).const_mul
    (rademacherBoundaryLogConstant I z + Real.log 2)
  simp only [mul_zero] at h
  have hpos := hW.eventually (eventually_gt_atTop 0)
  apply squeeze_zero' _ _ h
  · filter_upwards [hpos] with n hn
    exact div_nonneg (rademacherSeamCost_nonneg I (W n) hn z) (Nat.cast_nonneg _)
  · filter_upwards [hpos] with n hn
    have hb := div_le_div_of_nonneg_right (rademacherSeamCost_le I (W n) hn z)
      (Nat.cast_nonneg (N n) : (0 : ℝ) ≤ N n)
    simpa only [mul_div_assoc, mul_assoc] using hb

/-- The exact exceptional event, including every zero Fock value, has
vanishing probability at every positive macroscopic cap. -/
theorem rademacherSeamBadEvent_probability_tendsto_zero
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput)
    (hI : 1 ≤ I.subgaussianBound) (W s : ℕ → ℕ) (z : ℂ)
    (hW : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log (((s n + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0))
    (hlong : ∀ᶠ n in atTop, anchorSize (W n) ≤ (s n + 3) * W n)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (intervalRowsLaw (W n) (s n + 3) rademacherLaw).real
      (cyclicSeamBadEvent I (W n) (s n) z (ε * (((s n + 3) * W n : ℕ) : ℝ) / 2)))
      atTop (𝓝 0) := by
  let N := fun n => (s n + 3) * W n
  have hNtop : Tendsto N atTop atTop :=
    tendsto_atTop_mono' atTop
      (Eventually.of_forall fun n => Nat.le_mul_of_pos_left (W n) (by omega)) hW
  have hp := (tendsto_rademacherBoundaryBadProbability cook).comp hW
  have hb0 := tendsto_rademacherBoundaryBaseLoss_div_dimension cook W N z hW hlong
  have hb : Tendsto (fun n => rademacherBoundaryBaseLoss cook (W n) z /
      (ε * (N n : ℝ) / 2)) atTop (𝓝 0) := by
    convert hb0.div_const (ε / 2) using 1
    · funext n
      rw [div_div]
      congr 1
      ring
    · simp
  have he : Tendsto (fun n => Real.exp (-(2 * (ε * (N n : ℝ) / 2)))) atTop (𝓝 0) := by
    convert tendsto_exp_neg_width N hNtop hε using 1
    funext n
    congr 1
    ring
  have hi : Tendsto (fun n => (9 + 3 * (s n : ℝ)) *
      Real.exp (-(interfaceCombinedRate I / 2) * (W n : ℝ))) atTop (𝓝 0) := by
    convert tendsto_siteCount_mul_exp_neg_width (fun n => s n + 3) W hW hlog 3
      (half_pos (interfaceCombinedRate_pos I)) using 1
    funext n
    push_cast
    ring
  have hR := ((hp.add hb).add he).add hi
  simp only [zero_add] at hR
  apply squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) _ hR
  filter_upwards [hW.eventually (eventually_ge_atTop (rademacherBoundaryWidthThreshold cook z)),
    hW.eventually (eventually_ge_atTop (interfaceCanonicalLargeWThreshold I)),
    hW.eventually (eventually_gt_atTop 0)] with n hn hnI hn0
  have hN : (0 : ℝ) < N n := by
    dsimp [N]
    exact_mod_cast Nat.mul_pos (by omega : 0 < s n + 3) hn0
  exact cyclicSeamBadEvent_probability_le cook I hI (W n) (s n) z hn hnI (by positivity)

/-- The actual determinant trace is nonzero with probability tending to
one. Finite-size almost-sure invertibility is never asserted. -/
theorem rademacherCyclicFock_zero_probability_tendsto_zero
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput)
    (hI : 1 ≤ I.subgaussianBound) (W s : ℕ → ℕ) (z : ℂ)
    (hW : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log (((s n + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0))
    (hlong : ∀ᶠ n in atTop, anchorSize (W n) ≤ (s n + 3) * W n) :
    Tendsto (fun n => (intervalRowsLaw (W n) (s n + 3) rademacherLaw).real
      {x | cyclicFockValue (W n) (s n) z x = 0}) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => measureReal_nonneg) _
    (rademacherSeamBadEvent_probability_tendsto_zero cook I hI W s z hW hlog hlong 1 (by norm_num))
  intro n
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  exact Or.inl hx

/-- Vanishing normalized seam on the literal finite physical row spaces. -/
theorem rademacher_cyclicSeamDifference_tendstoInProbabilityTri
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput)
    (hI : 1 ≤ I.subgaussianBound) (W s : ℕ → ℕ) (z : ℂ)
    (hW : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log (((s n + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0))
    (hlong : ∀ᶠ n in atTop, anchorSize (W n) ≤ (s n + 3) * W n) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) rademacherLaw)
      (fun n x => cyclicSeamDifference (W n) (s n) z x /
        (((s n + 3) * W n : ℕ) : ℝ)) 0 := by
  intro ε hε
  let N := fun n => (s n + 3) * W n
  have hcost := tendsto_rademacherSeamCost_div_dimension I W N z hW hlong
  have hc : ∀ᶠ n in atTop, rademacherSeamCost I (W n) z / (N n : ℝ) < ε / 2 :=
    hcost.eventually (Iio_mem_nhds (half_pos hε))
  apply squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) _
    (rademacherSeamBadEvent_probability_tendsto_zero cook I hI W s z hW hlog hlong ε hε)
  filter_upwards [hc, hW.eventually (eventually_gt_atTop 0)] with n hcn hn0
  have hN : (0 : ℝ) < N n := by
    dsimp [N]
    exact_mod_cast Nat.mul_pos (by omega : 0 < s n + 3) hn0
  have hcostBound : rademacherSeamCost I (W n) z ≤ ε * (N n : ℝ) / 2 := by
    have h := (div_lt_iff₀ hN).mp hcn
    linarith
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  apply Or.inr
  change ε * (N n : ℝ) / 2 + rademacherSeamCost I (W n) z ≤
    |cyclicSeamDifference (W n) (s n) z x|
  change ε ≤ |cyclicSeamDifference (W n) (s n) z x / (N n : ℝ) - 0| at hx
  rw [sub_zero, abs_div, abs_of_pos hN] at hx
  have h := (le_div_iff₀ hN).mp hx
  linarith

/-- The same statement on the fixed, actual infinite IID Bernoulli
sample space used by the final circular-law reduction. -/
theorem rademacher_cyclicSeamDifference_tendstoInMeasure
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput)
    (hI : 1 ≤ I.subgaussianBound) (W s : ℕ → ℕ) (z : ℂ)
    (hW : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log (((s n + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0))
    (hlong : ∀ᶠ n in atTop, anchorSize (W n) ≤ (s n + 3) * W n) :
    TendstoInMeasure rademacherSequenceLaw
      (fun n x => cyclicSeamDifference (W n) (s n) z
        (physicalRowsFromSequence (W n) (s n) x) / (((s n + 3) * W n : ℕ) : ℝ))
      atTop (fun _ => 0) := by
  have h := (tendstoInProbabilityTri_measurePreserving_iff
    (fun _ => rademacherSequenceLaw)
    (fun n => intervalRowsLaw (W n) (s n + 3) rademacherLaw)
    (fun n => physicalRowsFromSequence (W n) (s n))
    (fun n => physicalRowsFromSequence_measurePreserving rademacherLaw (W n) (s n))
    (fun n x => cyclicSeamDifference (W n) (s n) z x / (((s n + 3) * W n : ℕ) : ℝ))
    (fun n => (measurable_cyclicSeamDifference (W n) (s n) z).div_const _) 0).2
      (rademacher_cyclicSeamDifference_tendstoInProbabilityTri cook I hI W s z hW hlog hlong)
  simpa only [TendstoInProbabilityTri, tendstoInMeasure_iff_measureReal_norm, Real.norm_eq_abs] using h

/-- Final-assembly argument order for the actual triangular ring law. -/
theorem rademacherCyclicSeamDifference_tendsto
    (cook : CookDeformedSquareInput.{0, 0}) (I : NguyenBottomSingularInput)
    (hI : 1 ≤ I.subgaussianBound) (W s : ℕ → ℕ)
    (hWtop : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, anchorSize (W n) ≤ (s n + 3) * W n)
    (hlog : Tendsto (fun n => Real.log (((s n + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) rademacherLaw)
      (fun n x => cyclicSeamDifference (W n) (s n) z x /
        (((s n + 3) * W n : ℕ) : ℝ)) 0 :=
  rademacher_cyclicSeamDifference_tendstoInProbabilityTri cook I hI W s z hWtop hlog hlong

end BernoulliSection8
