import BernoulliSection9.ArbitraryFrame
import BernoulliSection9.TerminalSmallBall
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Passing terminal small-ball estimates to arbitrary frames

This file formalizes the final limiting step of Section 9.2.  The
finite-dimensional exterior limits are supplied by `ArbitraryFrame`; here we
prove that the capped loss is continuous when the limiting coefficient norm
is positive, use its cap as a dominating function, and pass a uniform
terminal estimate through the artificial-frame limit.

The statements are deliberately phrased for abstract sequences of positive
coefficient norms and random complex values.  Consequently they can be
instantiated with `normalizedExteriorCoefficientNorm_tendsto` and the
artificial polynomials without exposing the internally chosen frame
completion in any theorem signature.
-/

open scoped Real

noncomputable section

namespace BernoulliSection9

open Filter MeasureTheory

/-- Joint pointwise continuity of the capped loss along an arbitrary filter,
at every point whose coefficient coordinate has positive limit.  The case
where the value tends to zero is nontrivial because `cappedLogLoss` has a
special value there; the cap makes the function eventually equal to `T`. -/
theorem cappedLogLoss_tendsto_of_pos
    {ι : Type*} {l : Filter ι} (T : ℝ)
    {c : ι → ℝ} {c₀ : ℝ} {w : ι → ℂ} {w₀ : ℂ}
    (hc : Tendsto c l (nhds c₀)) (hw : Tendsto w l (nhds w₀))
    (hc₀ : 0 < c₀) :
    Tendsto (fun i => cappedLogLoss T (c i) (w i)) l
      (nhds (cappedLogLoss T c₀ w₀)) := by
  by_cases hw₀ : w₀ = 0
  · subst w₀
    by_cases hT : T ≤ 0
    · have hall : ∀ (c' : ℝ) (w' : ℂ),
          cappedLogLoss T c' w' = T := by
        intro c' w'
        by_cases hw' : w' = 0
        · simp [hw']
        · rw [cappedLogLoss_of_ne_zero hw', min_eq_left]
          exact hT.trans Real.posLog_nonneg
      simp only [hall]
      exact tendsto_const_nhds
    · have hTpos : 0 < T := lt_of_not_ge hT
      have hcHalf : c₀ / 2 < c₀ := by linarith
      have hcEventually : ∀ᶠ i in l, c₀ / 2 < c i :=
        hc.eventually (Ioi_mem_nhds hcHalf)
      have hdelta : 0 < c₀ / (2 * Real.exp T) := by positivity
      have hwEventually : ∀ᶠ i in l,
          ‖w i‖ < c₀ / (2 * Real.exp T) := by
        have hn := hw.norm
        have hz : ‖(0 : ℂ)‖ < c₀ / (2 * Real.exp T) := by
          simpa using hdelta
        exact hn.eventually (Iio_mem_nhds hz)
      have heq : (fun i => cappedLogLoss T (c i) (w i)) =ᶠ[l]
          (fun _ => T) := by
        filter_upwards [hcEventually, hwEventually] with i hci hwi
        by_cases hwi₀ : w i = 0
        · simp [hwi₀]
        · rw [cappedLogLoss_of_ne_zero hwi₀, min_eq_left]
          rw [Real.posLog_apply]
          apply le_max_of_le_right
          have hciPos : 0 < c i := by linarith
          have hratioPos : 0 < c i / ‖w i‖ :=
            div_pos hciPos (norm_pos_iff.mpr hwi₀)
          apply (Real.le_log_iff_exp_le hratioPos).2
          apply (le_div_iff₀ (norm_pos_iff.mpr hwi₀)).2
          have hprod : Real.exp T * ‖w i‖ < c₀ / 2 := by
            calc
              Real.exp T * ‖w i‖ <
                  Real.exp T * (c₀ / (2 * Real.exp T)) :=
                mul_lt_mul_of_pos_left hwi (Real.exp_pos T)
              _ = c₀ / 2 := by field_simp
          exact (hprod.trans hci).le
      rw [cappedLogLoss_zero]
      exact tendsto_const_nhds.congr' heq.symm
  · rw [cappedLogLoss_of_ne_zero hw₀]
    have hratio : Tendsto (fun i => c i / ‖w i‖) l
        (nhds (c₀ / ‖w₀‖)) :=
      hc.div hw.norm (norm_ne_zero_iff.mpr hw₀)
    have hmain : Tendsto
        (fun i => min T (Real.posLog (c i / ‖w i‖))) l
        (nhds (min T (Real.posLog (c₀ / ‖w₀‖)))) :=
      tendsto_const_nhds.min
        (Real.continuous_posLog.continuousAt.tendsto.comp hratio)
    apply hmain.congr'
    filter_upwards [hw.eventually_ne hw₀] with i hwi
    exact (cappedLogLoss_of_ne_zero hwi).symm

/-- The capped loss is jointly continuous at every `(c,w)` with `c > 0`. -/
theorem continuousAt_cappedLogLoss (T : ℝ) {c : ℝ} {w : ℂ}
    (hc : 0 < c) :
    ContinuousAt (fun p : ℝ × ℂ => cappedLogLoss T p.1 p.2) (c, w) := by
  exact cappedLogLoss_tendsto_of_pos T continuousAt_fst continuousAt_snd hc

/-- In particular, for a fixed positive coefficient norm, capped loss is a
continuous function of the polynomial value. -/
theorem continuous_cappedLogLoss_right (T c : ℝ) (hc : 0 < c) :
    Continuous (fun w : ℂ => cappedLogLoss T c w) := by
  rw [continuous_iff_continuousAt]
  intro w
  exact cappedLogLoss_tendsto_of_pos T tendsto_const_nhds continuousAt_id hc

theorem aestronglyMeasurable_cappedLogLoss
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T c : ℝ) (value : Ω → ℂ) (hc : 0 < c)
    (hvalue : AEStronglyMeasurable value μ) :
    AEStronglyMeasurable (fun ω => cappedLogLoss T c (value ω)) μ := by
  exact (continuous_cappedLogLoss_right T c hc).comp_aestronglyMeasurable hvalue

/-- Dominated convergence for capped losses when measurability of the
capped integrands is already available.  The constant cap `T` is the
integrable dominating function. -/
theorem tendsto_integral_cappedLogLoss_of_measurable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (T : ℝ) (hT : 0 ≤ T)
    {c : ℕ → ℝ} {c₀ : ℝ} {value : ℕ → Ω → ℂ} {value₀ : Ω → ℂ}
    (hc : Tendsto c atTop (nhds c₀)) (hc₀ : 0 < c₀)
    (hvalue : ∀ᵐ ω ∂μ,
      Tendsto (fun n => value n ω) atTop (nhds (value₀ ω)))
    (hmeas : ∀ n, AEStronglyMeasurable
      (fun ω => cappedLogLoss T (c n) (value n ω)) μ) :
    Tendsto
      (fun n => ∫ ω, cappedLogLoss T (c n) (value n ω) ∂μ)
      atTop (nhds (∫ ω, cappedLogLoss T c₀ (value₀ ω) ∂μ)) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun _ : Ω => T) hmeas (MeasureTheory.integrable_const T)
  · intro n
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,
      abs_of_nonneg (cappedLogLoss_nonneg hT)]
    exact cappedLogLoss_le_cap
  · filter_upwards [hvalue] with ω hω
    exact cappedLogLoss_tendsto_of_pos T hc hω hc₀

/-- Dominated convergence stated using the natural assumptions that every
coefficient norm is positive and every random value is strongly measurable. -/
theorem tendsto_integral_cappedLogLoss
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (T : ℝ) (hT : 0 ≤ T)
    {c : ℕ → ℝ} {c₀ : ℝ} {value : ℕ → Ω → ℂ} {value₀ : Ω → ℂ}
    (hc : Tendsto c atTop (nhds c₀)) (hc₀ : 0 < c₀)
    (hcpos : ∀ n, 0 < c n)
    (hvalueMeas : ∀ n, AEStronglyMeasurable (value n) μ)
    (hvalue : ∀ᵐ ω ∂μ,
      Tendsto (fun n => value n ω) atTop (nhds (value₀ ω))) :
    Tendsto
      (fun n => ∫ ω, cappedLogLoss T (c n) (value n ω) ∂μ)
      atTop (nhds (∫ ω, cappedLogLoss T c₀ (value₀ ω) ∂μ)) := by
  apply tendsto_integral_cappedLogLoss_of_measurable μ T hT hc hc₀ hvalue
  intro n
  exact aestronglyMeasurable_cappedLogLoss μ T (c n) (value n)
    (hcpos n) (hvalueMeas n)

/-- A uniform-in-parameter capped integral estimate survives the
artificial-frame limit.  This is the abstract final passage in the proof of
the arbitrary-frame capped small-ball bound. -/
theorem cappedIntegral_limit_le_of_uniform_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (T : ℝ) (hT : 0 ≤ T)
    {c : ℕ → ℝ} {c₀ : ℝ} {value : ℕ → Ω → ℂ} {value₀ : Ω → ℂ}
    (hc : Tendsto c atTop (nhds c₀)) (hc₀ : 0 < c₀)
    (hcpos : ∀ n, 0 < c n)
    (hvalueMeas : ∀ n, AEStronglyMeasurable (value n) μ)
    (hvalue : ∀ᵐ ω ∂μ,
      Tendsto (fun n => value n ω) atTop (nhds (value₀ ω)))
    (B : ℝ)
    (huniform : ∀ n,
      ∫ ω, cappedLogLoss T (c n) (value n ω) ∂μ ≤ B) :
    ∫ ω, cappedLogLoss T c₀ (value₀ ω) ∂μ ≤ B := by
  exact le_of_tendsto'
    (tendsto_integral_cappedLogLoss μ T hT hc hc₀ hcpos
      hvalueMeas hvalue) huniform

/-- Variant in which a positive uniform coefficient lower bound supplies
both positivity of every `c n` and positivity of the limiting norm `c₀`. -/
theorem cappedIntegral_limit_le_of_uniform_bound_of_lower
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (T : ℝ) (hT : 0 ≤ T)
    {c : ℕ → ℝ} {c₀ lower : ℝ}
    {value : ℕ → Ω → ℂ} {value₀ : Ω → ℂ}
    (hc : Tendsto c atTop (nhds c₀)) (hlowerPos : 0 < lower)
    (hlower : ∀ n, lower ≤ c n)
    (hvalueMeas : ∀ n, AEStronglyMeasurable (value n) μ)
    (hvalue : ∀ᵐ ω ∂μ,
      Tendsto (fun n => value n ω) atTop (nhds (value₀ ω)))
    (B : ℝ)
    (huniform : ∀ n,
      ∫ ω, cappedLogLoss T (c n) (value n ω) ∂μ ≤ B) :
    ∫ ω, cappedLogLoss T c₀ (value₀ ω) ∂μ ≤ B := by
  have hc₀pos : 0 < c₀ :=
    hlowerPos.trans_le (ge_of_tendsto' hc hlower)
  have hcpos : ∀ n, 0 < c n := fun n => hlowerPos.trans_le (hlower n)
  exact cappedIntegral_limit_le_of_uniform_bound μ T hT hc hc₀pos
    hcpos hvalueMeas hvalue B huniform

/-- Closed intervals are preserved by limits: uniform two-sided estimates
for the artificial coefficient norms pass to the arbitrary-frame norm. -/
theorem limit_mem_interval_of_uniform_bounds
    {c : ℕ → ℝ} {c₀ lower upper : ℝ}
    (hc : Tendsto c atTop (nhds c₀))
    (hlower : ∀ n, lower ≤ c n) (hupper : ∀ n, c n ≤ upper) :
    lower ≤ c₀ ∧ c₀ ≤ upper := by
  exact ⟨ge_of_tendsto' hc hlower, le_of_tendsto' hc hupper⟩

/-- Scaled version used with the normalized graph-volume factor: if that
factor tends to one, bounds by `lower * scale n` and `upper * scale n`
converge to the same unscaled two-sided bounds. -/
theorem limit_mem_interval_of_scaled_bounds
    {c scale : ℕ → ℝ} {c₀ lower upper : ℝ}
    (hc : Tendsto c atTop (nhds c₀))
    (hscale : Tendsto scale atTop (nhds 1))
    (hlower : ∀ n, lower * scale n ≤ c n)
    (hupper : ∀ n, c n ≤ upper * scale n) :
    lower ≤ c₀ ∧ c₀ ≤ upper := by
  constructor
  · have hl := hscale.const_mul lower
    have h := le_of_tendsto_of_tendsto' hl hc hlower
    simpa using h
  · have hu := hscale.const_mul upper
    have h := le_of_tendsto_of_tendsto' hc hu hupper
    simpa using h

end BernoulliSection9
