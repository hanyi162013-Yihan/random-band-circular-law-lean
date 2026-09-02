import CircularLawSection4.PaperOperatorAffineL2

/-! # Reuse the Section 4 row-log estimates with only a diagonal lower bound

The noncompact profile need not have comparable weights at the farthest
offsets. The Section 4 slope-selection proof only uses the distinguished
coefficient's lower bound. This adapter applies its existing small-ball,
logarithmic-moment, and normalized-row-energy theorems in that generality.
-/

open MeasureTheory CircularLawSection4
open scoped BigOperators ENNReal

noncomputable section

namespace CircularLawSection6

def affineRowLogBound (n : ℕ) (q L : ℝ) (z : ℂ) : ℝ :=
  2 * oneSidedLogSecondMomentBound ((max 1 (Real.pi * L)) / ((1 / 2 : ℝ) * q)) 1 +
    2 * (3 * (Real.log (n + 1 : ℝ)) ^ 2 + 3 * 1 + 3 * ‖z‖ ^ 2)

theorem affineRowLogBound_nonneg (n : ℕ) (q L : ℝ) (z : ℂ) :
    0 ≤ affineRowLogBound n q L z := by
  unfold affineRowLogBound oneSidedLogSecondMomentBound
  positivity

theorem complex_affine_log_memLp_of_diagonal
    {E F : Type*} [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (ν : Measure ℂ) [IsProbabilityMeasure ν] {L : ℝ}
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    {n : ℕ} (i₀ : Fin (n + 1)) (b : Fin (n + 1) → ℂ)
    (M : Fin (n + 1) → E →L[ℂ] F) (z : ℂ)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hb : q ≤ ‖b i₀‖)
    (hscale : 0 < operatorAffineScale i₀ b M)
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    (∀ᵐ η ∂iidMeasure ν (n + 1), 0 < ‖operatorAffine b η M z (M i₀)‖) ∧
    MemLp (fun η : Fin (n + 1) → ℂ =>
      |Real.log ‖operatorAffine b η M z (M i₀)‖ - Real.log (operatorAffineScale i₀ b M)|)
      2 (iidMeasure ν (n + 1)) ∧
    (∫ η : Fin (n + 1) → ℂ,
      |Real.log ‖operatorAffine b η M z (M i₀)‖ - Real.log (operatorAffineScale i₀ b M)| ^ 2
      ∂iidMeasure ν (n + 1)) ≤ affineRowLogBound n q L z := by
  let μ := iidMeasure ν (n + 1)
  let scale := operatorAffineScale i₀ b M
  let radius : (Fin (n + 1) → ℂ) → ℝ := fun η => ‖operatorAffine b η M z (M i₀)‖
  let theta : ℝ := (1 / 2 : ℝ) * q
  let C := max 1 (Real.pi * L)
  let : IsProbabilityMeasure μ := iidMeasure_isProbability ν (n + 1)
  have htheta : 0 < theta := mul_pos (by norm_num) hq
  obtain ⟨s, x, ell, hx, hell, hslope⟩ := exists_large_scalarized_slope i₀ b M hq hq1 hb
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hscale
  have hm : Measurable radius := (continuous_operatorAffine_fin b M z (M i₀)).norm.measurable
  have hr0 (η) : 0 ≤ radius η := norm_nonneg _
  have hC : 0 ≤ C := zero_le_one.trans (le_max_left _ _)
  have hsmall : ∀ ρ : ℝ, 0 < ρ → μ {η | radius η ≤ theta * scale * ρ} ≤
      ENNReal.ofReal (C * ρ) := by
    intro ρ hρ
    have hquad := complex_iid_operatorAffine_arbitraryCoordinate_smallBall hν s b M z (M i₀)
      x ell hx.le hell hρ.le (mul_pos htheta hscale) hslope.le
    have hquad' : μ {η | radius η ≤ theta * scale * ρ} ≤
        ENNReal.ofReal (Real.pi * L) * ENNReal.ofReal ρ ^ 2 := by
      simpa only [μ, radius, theta, scale, ENNReal.ofReal_mul Real.pi_pos.le] using hquad
    exact probability_quadratic_smallBall_to_linear μ _ (Real.pi * L) ρ
      (mul_nonneg Real.pi_pos.le hL) hρ hquad'
  obtain ⟨hzero, hnegativeLp, hnegative⟩ :=
    zeroSet_memLp_two_and_integral_sq_logDeficit_of_threshold_linearSmallBall
      μ radius hm hr0 scale theta C hscale htheta hC hsmall
  have hrpos : ∀ᵐ η ∂μ, 0 < radius η := by
    rw [ae_iff]
    have he : {η | ¬ 0 < radius η} = {η | radius η = 0} := by
      ext η
      change (¬ 0 < radius η) ↔ radius η = 0
      constructor
      · intro h
        exact le_antisymm (le_of_not_gt h) (hr0 η)
      · intro h
        rw [h]
        exact lt_irrefl 0
    rw [he, hzero]
  have hcoord (i : Fin (n + 1)) :=
    iidMeasure_coordinate_norm_sq_integrable_and_integral_le_one i hInt hSecond
  obtain ⟨hscaledInt, hscaled⟩ := integrable_normalized_sum_sq_and_integral_le_one μ
    (fun (i : Fin (n + 1)) (η : Fin (n + 1) → ℂ) => ‖η i‖)
    (fun i => (measurable_pi_apply i).norm) (fun i => (hcoord i).1) (fun i => (hcoord i).2)
  obtain ⟨hpositiveLp, hpositive⟩ :=
    operatorAffine_memLp_two_and_integral_sq_logExcess_of_scaledSecondMoment
      μ i₀ b M z (fun η => η) hscale hm (by fun_prop) hrpos 1 hscaledInt hscaled
  refine ⟨hrpos, ?_⟩
  simpa only [affineRowLogBound, scale, theta, C, μ, radius, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one] using
    memLp_two_and_integral_sq_abs_log_sub_log_of_parts
      scale hnegativeLp hpositiveLp hnegative hpositive

/-- Degenerate frozen fibers require no exceptional-set input: at scale
zero their determinant-affine expression is identically zero and so is the
totalized logarithmic deviation. -/
theorem complex_affine_log_memLp_of_diagonal_all_scales
    {E F : Type*} [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (ν : Measure ℂ) [IsProbabilityMeasure ν] {L : ℝ}
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    {n : ℕ} (i₀ : Fin (n + 1)) (b : Fin (n + 1) → ℂ)
    (M : Fin (n + 1) → E →L[ℂ] F) (z : ℂ)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hb : q ≤ ‖b i₀‖)
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    MemLp (fun η : Fin (n + 1) → ℂ =>
      |Real.log ‖operatorAffine b η M z (M i₀)‖ - Real.log (operatorAffineScale i₀ b M)|)
      2 (iidMeasure ν (n + 1)) ∧
    (∫ η : Fin (n + 1) → ℂ,
      |Real.log ‖operatorAffine b η M z (M i₀)‖ - Real.log (operatorAffineScale i₀ b M)| ^ 2
      ∂iidMeasure ν (n + 1)) ≤ affineRowLogBound n q L z := by
  let : IsProbabilityMeasure (iidMeasure ν (n + 1)) := iidMeasure_isProbability ν (n + 1)
  by_cases hs : 0 < operatorAffineScale i₀ b M
  · exact (complex_affine_log_memLp_of_diagonal ν hν hL i₀ b M z hq hq1 hb hs hInt hSecond).2
  · have hzero : operatorAffineScale i₀ b M = 0 := le_antisymm (le_of_not_gt hs)
      ((norm_nonneg (M i₀)).trans (distinguished_operator_norm_le_scale i₀ b M))
    have hnorm (η : Fin (n + 1) → ℂ) : ‖operatorAffine b η M z (M i₀)‖ = 0 := by
      have h := operatorAffine_norm_le_scale_mul_sum i₀ b η M z
      rw [hzero, zero_mul] at h
      exact le_antisymm h (norm_nonneg _)
    simpa only [hnorm, hzero, Real.log_zero, sub_self, abs_zero, zero_pow (by decide : 2 ≠ 0),
      integral_zero] using
      And.intro (memLp_const (0 : ℝ) (μ := iidMeasure ν (n + 1)) (p := 2))
        (affineRowLogBound_nonneg n q L z)

end CircularLawSection6
