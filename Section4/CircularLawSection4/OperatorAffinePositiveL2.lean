import CircularLawSection4.OperatorAffineLog
import CircularLawSection4.PositiveLogMoment

/-!
# The positive-log `L²` half of the operator-affine estimate

The deterministic operator norm estimate bounds the logarithmic excess by
the positive logarithm of a normalized random sum.  This module packages
that comparison and feeds it into the scaled-second-moment estimate from
`PositiveLogMoment`.

The first measure-theoretic theorem is deliberately abstract: both the
positivity of the radius and its upper bound are only required almost
everywhere.  The final theorem specializes it to the operator-affine radius.
-/

open scoped BigOperators MeasureTheory
open MeasureTheory

namespace CircularLawSection4

/-- If a positive radius is at most `scale * T`, then its logarithmic excess
above `scale` is at most the positive part of `log T`. -/
theorem logExcess_le_max_zero_log_of_le_scale_mul
    {scale radius T : ℝ} (hscale : 0 < scale) (hradius : 0 < radius)
    (hT : 0 < T) (hradius_le : radius ≤ scale * T) :
    logExcess scale radius ≤ max 0 (Real.log T) := by
  unfold logExcess
  apply max_le
  · exact le_max_left _ _
  · have hlog : Real.log radius ≤ Real.log (scale * T) :=
      Real.log_le_log hradius hradius_le
    rw [Real.log_mul hscale.ne' hT.ne'] at hlog
    have hsub : Real.log radius - Real.log scale ≤ Real.log T := by
      linarith
    exact hsub.trans (le_max_right _ _)

/-- A scaled second moment for a nonnegative random majorant gives the
positive logarithmic excess in `L²`, with an explicit square-integral
bound.  The reference `card` need only be a real number at least one.

The absolute value on `z` makes this form convenient for both real shifts
and norms of complex spectral parameters. -/
theorem memLp_two_and_integral_sq_logExcess_of_scaledSecondMoment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (scale : ℝ) (hscale : 0 < scale)
    (radius S : Ω → ℝ)
    (hradiusMeas : Measurable radius) (hSmeas : Measurable S)
    (hS0 : ∀ ω, 0 ≤ S ω)
    (z card V : ℝ) (hcard : 1 ≤ card)
    (hradiusPos : ∀ᵐ ω ∂μ, 0 < radius ω)
    (hradiusUpper : ∀ᵐ ω ∂μ, radius ω ≤ scale * (S ω + |z|))
    (hscaledInt : Integrable (fun ω => (S ω / card) ^ 2) μ)
    (hscaled : ∫ ω, (S ω / card) ^ 2 ∂μ ≤ V) :
    MemLp (fun ω => logExcess scale (radius ω)) 2 μ ∧
      ∫ ω, logExcess scale (radius ω) ^ 2 ∂μ ≤
        3 * (Real.log card) ^ 2 + 3 * V + 3 * |z| ^ 2 := by
  let E : Ω → ℝ := fun ω => logExcess scale (radius ω)
  let Q : Ω → ℝ := fun ω => max 0 (Real.log (S ω + |z|))
  obtain ⟨hQsqInt, hQsq⟩ :=
    integrable_and_integral_positiveLogSquare_le_of_scaledSecondMoment
      μ S hSmeas hS0 |z| card V (abs_nonneg z) hcard hscaledInt hscaled
  have hEQ : E ≤ᵐ[μ] Q := by
    filter_upwards [hradiusPos, hradiusUpper] with ω hradiusω hupperω
    have hproduct : 0 < scale * (S ω + |z|) :=
      hradiusω.trans_le hupperω
    have hT : 0 < S ω + |z| :=
      pos_of_mul_pos_right hproduct hscale.le
    exact logExcess_le_max_zero_log_of_le_scale_mul
      hscale hradiusω hT hupperω
  have hE0 : ∀ ω, 0 ≤ E ω := fun ω => logExcess_nonneg _ _
  have hQ0 : ∀ ω, 0 ≤ Q ω := fun ω => le_max_left _ _
  have hEsqQsq : (λ ω => E ω ^ 2) ≤ᵐ[μ] (λ ω => Q ω ^ 2) := by
    filter_upwards [hEQ] with ω hω
    exact (sq_le_sq₀ (hE0 ω) (hQ0 ω)).2 hω
  have hEmeas : Measurable E := by
    exact measurable_logExcess scale hradiusMeas
  have hEsqInt : Integrable (fun ω => E ω ^ 2) μ := by
    apply hQsqInt.mono' (hEmeas.pow_const 2).aestronglyMeasurable
    filter_upwards [hEsqQsq] with ω hω
    simpa only [Real.norm_eq_abs, abs_sq] using hω
  refine ⟨(memLp_two_iff_integrable_sq hEmeas.aestronglyMeasurable).2 hEsqInt, ?_⟩
  calc
    (∫ ω, E ω ^ 2 ∂μ) ≤ ∫ ω, Q ω ^ 2 ∂μ :=
      integral_mono_ae hEsqInt hQsqInt hEsqQsq
    _ ≤ 3 * (Real.log card) ^ 2 + 3 * V + 3 * |z| ^ 2 := hQsq

/-- Operator-affine specialization of the abstract positive-log `L²`
bridge.  The deterministic radius bound is discharged by
`operatorAffine_norm_le_scale_mul_sum`; only measurability, almost-everywhere
nonvanishing, and the normalized second moment of the coordinate-norm sum
remain as probabilistic inputs. -/
theorem operatorAffine_memLp_two_and_integral_sq_logExcess_of_scaledSecondMoment
    {Ω ι 𝕜 E F : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype ι] [Nonempty ι]
    [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (i₀ : ι) (b : ι → 𝕜) (M : ι → E →L[𝕜] F)
    (z : 𝕜) (ξ : Ω → ι → 𝕜)
    (hscale : 0 < operatorAffineScale i₀ b M)
    (hradiusMeas : Measurable (fun ω =>
      ‖operatorAffine b (ξ ω) M z (M i₀)‖))
    (hSmeas : Measurable (fun ω => ∑ i, ‖ξ ω i‖))
    (hradiusPos : ∀ᵐ ω ∂μ,
      0 < ‖operatorAffine b (ξ ω) M z (M i₀)‖)
    (V : ℝ)
    (hscaledInt : Integrable (fun ω =>
      ((∑ i, ‖ξ ω i‖) / (Fintype.card ι : ℝ)) ^ 2) μ)
    (hscaled :
      ∫ ω, ((∑ i, ‖ξ ω i‖) / (Fintype.card ι : ℝ)) ^ 2 ∂μ ≤ V) :
    MemLp (fun ω => logExcess (operatorAffineScale i₀ b M)
      ‖operatorAffine b (ξ ω) M z (M i₀)‖) 2 μ ∧
      ∫ ω, logExcess (operatorAffineScale i₀ b M)
          ‖operatorAffine b (ξ ω) M z (M i₀)‖ ^ 2 ∂μ ≤
        3 * (Real.log (Fintype.card ι : ℝ)) ^ 2 + 3 * V +
          3 * ‖z‖ ^ 2 := by
  have hcard : 1 ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hS0 : ∀ ω, 0 ≤ ∑ i, ‖ξ ω i‖ := fun ω =>
    Finset.sum_nonneg fun i _ => norm_nonneg (ξ ω i)
  have hupper : ∀ᵐ ω ∂μ,
      ‖operatorAffine b (ξ ω) M z (M i₀)‖ ≤
        operatorAffineScale i₀ b M * ((∑ i, ‖ξ ω i‖) + |‖z‖|) := by
    filter_upwards with ω
    simpa only [abs_norm] using
      operatorAffine_norm_le_scale_mul_sum i₀ b (ξ ω) M z
  simpa only [abs_norm] using
    memLp_two_and_integral_sq_logExcess_of_scaledSecondMoment
      μ (operatorAffineScale i₀ b M) hscale
      (fun ω => ‖operatorAffine b (ξ ω) M z (M i₀)‖)
      (fun ω => ∑ i, ‖ξ ω i‖)
      hradiusMeas hSmeas hS0 ‖z‖ (Fintype.card ι : ℝ) V hcard
      hradiusPos hupper hscaledInt hscaled

end CircularLawSection4
