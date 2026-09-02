import CircularLawSection4.MultiaffineLog
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Untruncated logarithmic moments from multiaffine small balls

The ordinary real-valued representative below is arbitrary on the zero set
because `Real.log 0 = 0` in Lean.  The power small-ball estimate proves that
this exceptional set is null.  Off that set the representative is exactly
`(log (scale / radius))₊`.
-/

open scoped ENNReal MeasureTheory Topology
open Set MeasureTheory Filter Measure

namespace CircularLawSection4

/-- A finite real-valued representative of the untruncated positive
logarithmic loss.  Its value at `radius = 0` is immaterial once the zero set
has been proved null. -/
noncomputable def positiveLogLoss (scale radius : ℝ) : ℝ :=
  max 0 (Real.log scale - Real.log radius)

theorem positiveLogLoss_nonneg (scale radius : ℝ) :
    0 ≤ positiveLogLoss scale radius := by
  exact le_max_left _ _

theorem measurable_positiveLogLoss
    {Ω : Type*} [MeasurableSpace Ω] (scale : ℝ)
    {radius : Ω → ℝ} (hradius : Measurable radius) :
    Measurable (fun ω => positiveLogLoss scale (radius ω)) := by
  unfold positiveLogLoss
  fun_prop

/-- At every positive radius, the finite representative is literally the
positive part of `log (scale / radius)`. -/
theorem positiveLogLoss_eq_log_div
    {scale radius : ℝ} (hscale : 0 < scale) (hradius : 0 < radius) :
    positiveLogLoss scale radius = max 0 (Real.log (scale / radius)) := by
  unfold positiveLogLoss
  rw [Real.log_div hscale.ne' hradius.ne']

/-- A positive tail of the untruncated logarithmic loss is contained in the
corresponding small-radius event. -/
theorem positiveLogLoss_tail_imp_radius_le
    {scale radius t : ℝ} (hscale : 0 < scale) (hradius0 : 0 ≤ radius)
    (ht : 0 < t) (h : t < positiveLogLoss scale radius) :
    radius ≤ scale * Real.exp (-t) := by
  by_cases hradius : radius = 0
  · rw [hradius]
    positivity
  have hradius_pos : 0 < radius := lt_of_le_of_ne hradius0 (Ne.symm hradius)
  have htarget : 0 < scale * Real.exp (-t) := mul_pos hscale (Real.exp_pos _)
  have htlog : t < Real.log scale - Real.log radius := by
    change t < max 0 (Real.log scale - Real.log radius) at h
    rcases (lt_max_iff.mp h) with hneg | hlog
    · linarith
    · exact hlog
  have hlogtarget :
      Real.log (scale * Real.exp (-t)) = Real.log scale - t := by
    rw [Real.log_mul hscale.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hlog : Real.log radius < Real.log (scale * Real.exp (-t)) := by
    rw [hlogtarget]
    linarith
  exact ((Real.log_lt_log_iff hradius_pos htarget).mp hlog).le

/-- A power small-ball bound rules out an atom at radius zero. -/
theorem measure_zeroSet_eq_zero_of_power_smallBall
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (radius : Ω → ℝ) (scale A : ℝ) (hscale : 0 < scale)
    (d m : ℕ) (hm : 0 < m)
    (hsmall : ∀ ρ : ℝ, 0 < ρ →
      μ {ω | radius ω ≤ scale * ρ ^ d} ≤ ENNReal.ofReal (A * ρ ^ m)) :
    μ {ω | radius ω = 0} = 0 := by
  have hbound : ∀ s : ℝ,
      μ {ω | radius ω = 0} ≤
        ENNReal.ofReal (A * (Real.exp (-s)) ^ m) := by
    intro s
    calc
      μ {ω | radius ω = 0} ≤
          μ {ω | radius ω ≤ scale * (Real.exp (-s)) ^ d} := by
        apply measure_mono
        intro ω hω
        change radius ω ≤ scale * (Real.exp (-s)) ^ d
        rw [hω]
        positivity
      _ ≤ ENNReal.ofReal (A * (Real.exp (-s)) ^ m) :=
        hsmall (Real.exp (-s)) (Real.exp_pos _)
  have hpow : Tendsto (fun s : ℝ => (Real.exp (-s)) ^ m) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.pow m using 1
    simp [Nat.ne_of_gt hm]
  have hreal : Tendsto (fun s : ℝ => A * (Real.exp (-s)) ^ m) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hpow using 1
    all_goals simp
  have henn :
      Tendsto (fun s : ℝ => ENNReal.ofReal (A * (Real.exp (-s)) ^ m))
        atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  apply le_antisymm ?_ bot_le
  exact ge_of_tendsto henn (Filter.Eventually.of_forall hbound)

/-- Once the zero set is null, `positiveLogLoss` agrees almost everywhere
with the manuscript expression `(log (scale / radius))₊`. -/
theorem positiveLogLoss_eq_log_div_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (radius : Ω → ℝ) {scale : ℝ} (hscale : 0 < scale)
    (hradius0 : ∀ ω, 0 ≤ radius ω)
    (hzero : μ {ω | radius ω = 0} = 0) :
    (fun ω => positiveLogLoss scale (radius ω)) =ᵐ[μ]
      (fun ω => max 0 (Real.log (scale / radius ω))) := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with ω hω
  apply positiveLogLoss_eq_log_div hscale
  have hne : radius ω ≠ 0 := by
    simpa only [mem_ofPred_eq] using hω
  exact lt_of_le_of_ne (hradius0 ω) (Ne.symm hne)

/-- For a fixed positive radius, the cutoff loss converges to the
untruncated representative. -/
theorem tendsto_truncatedLogLoss_atTop
    {scale radius : ℝ} (_hscale : 0 < scale) (hradius : 0 < radius) :
    Tendsto (fun cutoff : ℝ => truncatedLogLoss cutoff scale radius)
      atTop (𝓝 (positiveLogLoss scale radius)) := by
  have hfloor :
      Tendsto (fun cutoff : ℝ => scale * Real.exp (-cutoff)) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul Real.tendsto_exp_neg_atTop_nhds_zero using 1
    all_goals simp
  have heventually :
      ∀ᶠ cutoff : ℝ in atTop, scale * Real.exp (-cutoff) ≤ radius :=
    (hfloor.eventually_lt_const hradius).mono fun _ h => h.le
  apply tendsto_const_nhds.congr'
  filter_upwards [heventually] with cutoff hcutoff
  exact (truncatedLogLoss_eq_posLog_of_floor_le hcutoff).symm

/-- The natural-cutoff sequence converges almost everywhere to the
untruncated loss. -/
theorem ae_tendsto_truncatedLogLoss_nat
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (radius : Ω → ℝ) {scale : ℝ} (hscale : 0 < scale)
    (hradius0 : ∀ ω, 0 ≤ radius ω)
    (hzero : μ {ω | radius ω = 0} = 0) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => truncatedLogLoss (n : ℝ) scale (radius ω)) atTop
      (𝓝 (positiveLogLoss scale (radius ω))) := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with ω hω
  have hne : radius ω ≠ 0 := by
    simpa only [mem_ofPred_eq] using hω
  have hpos : 0 < radius ω := lt_of_le_of_ne (hradius0 ω) (Ne.symm hne)
  exact (tendsto_truncatedLogLoss_atTop hscale hpos).comp
    tendsto_natCast_atTop_atTop

/-- Increasing the cutoff can only increase the regularized logarithmic
loss. -/
theorem monotone_truncatedLogLoss
    {scale radius : ℝ} (hscale : 0 < scale) :
    Monotone (fun cutoff : ℝ => truncatedLogLoss cutoff scale radius) := by
  intro a b hab
  unfold truncatedLogLoss
  have hexp : Real.exp (-b) ≤ Real.exp (-a) :=
    Real.exp_le_exp.mpr (neg_le_neg hab)
  have hfloor : scale * Real.exp (-b) ≤ scale * Real.exp (-a) :=
    mul_le_mul_of_nonneg_left hexp hscale.le
  have hmax :
      max radius (scale * Real.exp (-b)) ≤
        max radius (scale * Real.exp (-a)) :=
    max_le_max le_rfl hfloor
  have hpos_b : 0 < max radius (scale * Real.exp (-b)) :=
    (mul_pos hscale (Real.exp_pos _)).trans_le (le_max_right _ _)
  have hpos_a : 0 < max radius (scale * Real.exp (-a)) :=
    (mul_pos hscale (Real.exp_pos _)).trans_le (le_max_right _ _)
  have hlog := Real.strictMonoOn_log.monotoneOn hpos_b hpos_a hmax
  exact max_le_max le_rfl (sub_le_sub_left hlog _)

/-- Monotone convergence for the natural-cutoff sequence, stated at the
`lintegral` level so it remains valid before integrability is known. -/
theorem tendsto_lintegral_truncatedLogLoss_nat
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (radius : Ω → ℝ) (hradius : Measurable radius)
    {scale : ℝ} (hscale : 0 < scale)
    (hradius0 : ∀ ω, 0 ≤ radius ω)
    (hzero : μ {ω | radius ω = 0} = 0) :
    Tendsto
      (fun n : ℕ => ∫⁻ ω,
        ENNReal.ofReal (truncatedLogLoss (n : ℝ) scale (radius ω)) ∂μ)
      atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (positiveLogLoss scale (radius ω)) ∂μ)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    exact (ENNReal.measurable_ofReal.comp
      (measurable_truncatedLogLoss (n : ℝ) scale hradius)).aemeasurable
  · exact Filter.Eventually.of_forall fun ω i j hij => by
      apply ENNReal.ofReal_le_ofReal
      exact monotone_truncatedLogLoss hscale (by exact_mod_cast hij)
  · filter_upwards [ae_tendsto_truncatedLogLoss_nat μ radius hscale hradius0 hzero]
      with ω hω
    exact ENNReal.tendsto_ofReal hω

/-- Full untruncated closure of a power small-ball estimate.  Besides the
expectation estimate, it records both the null zero set and the almost
everywhere identification with the manuscript's logarithmic ratio. -/
theorem zeroSet_aeLog_and_integrable_positiveLogLoss_of_power_smallBall
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (radius : Ω → ℝ) (hradius : Measurable radius)
    (hradius0 : ∀ ω, 0 ≤ radius ω)
    (scale A : ℝ) (hscale : 0 < scale)
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (hsmall : ∀ ρ : ℝ, 0 < ρ →
      μ {ω | radius ω ≤ scale * ρ ^ d} ≤ ENNReal.ofReal (A * ρ ^ m)) :
    μ {ω | radius ω = 0} = 0 ∧
      (fun ω => positiveLogLoss scale (radius ω)) =ᵐ[μ]
        (fun ω => max 0 (Real.log (scale / radius ω))) ∧
      Integrable (fun ω => positiveLogLoss scale (radius ω)) μ ∧
      ∫ ω, positiveLogLoss scale (radius ω) ∂μ ≤
        (Real.log (max 1 A) + 1) / ((m : ℝ) / (d : ℝ)) := by
  have hzero := measure_zeroSet_eq_zero_of_power_smallBall μ radius scale A hscale
    d m hm hsmall
  refine ⟨hzero, positiveLogLoss_eq_log_div_ae μ radius hscale hradius0 hzero, ?_⟩
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  apply integrable_and_expectation_le_of_exponential_tail μ
    (fun ω => positiveLogLoss scale (radius ω))
    (measurable_positiveLogLoss scale hradius)
    (fun ω => positiveLogLoss_nonneg scale (radius ω)) A
    ((m : ℝ) / (d : ℝ)) (div_pos hmR hdR)
  intro t ht
  let ρ : ℝ := Real.exp (-t / (d : ℝ))
  have hρ : 0 < ρ := Real.exp_pos _
  have hρd : ρ ^ d = Real.exp (-t) := by
    dsimp [ρ]
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp [ne_of_gt hdR]
  have hρm :
      ρ ^ m = Real.exp ((-((m : ℝ) / (d : ℝ))) * t) := by
    dsimp [ρ]
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp [ne_of_gt hdR]
  have hsubset :
      {ω | t < positiveLogLoss scale (radius ω)} ⊆
        {ω | radius ω ≤ scale * ρ ^ d} := by
    intro ω hω
    have hle := positiveLogLoss_tail_imp_radius_le hscale (hradius0 ω) ht hω
    change radius ω ≤ scale * ρ ^ d
    simpa only [hρd] using hle
  calc
    μ {ω | t < positiveLogLoss scale (radius ω)} ≤
        μ {ω | radius ω ≤ scale * ρ ^ d} := measure_mono hsubset
    _ ≤ ENNReal.ofReal (A * ρ ^ m) := hsmall ρ hρ
    _ = ENNReal.ofReal
        (A * Real.exp ((-((m : ℝ) / (d : ℝ))) * t)) := by rw [hρm]

/-- Untruncated real IID density theorem.  With `k = n + 1`, its constants
are `A = 2 k L` and tail rate `1 / k`. -/
theorem iid_real_positiveLogLoss_withDensity
    (f : ℝ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ x ∂(volume : Measure ℝ), f x ≤ ENNReal.ofReal L)
    {n : ℕ} (p : MultiAffine ℝ (n + 1))
    (htop : 0 < ‖p.topCoeff‖) :
    iidMeasure (volume.withDensity f) (n + 1) {x | ‖p.eval x‖ = 0} = 0 ∧
      (fun x => positiveLogLoss ‖p.topCoeff‖ ‖p.eval x‖) =ᵐ[
        iidMeasure (volume.withDensity f) (n + 1)]
        (fun x => max 0 (Real.log (‖p.topCoeff‖ / ‖p.eval x‖))) ∧
      Integrable
        (fun x => positiveLogLoss ‖p.topCoeff‖ ‖p.eval x‖)
        (iidMeasure (volume.withDensity f) (n + 1)) ∧
      ∫ x, positiveLogLoss ‖p.topCoeff‖ ‖p.eval x‖
          ∂iidMeasure (volume.withDensity f) (n + 1) ≤
        (Real.log
              (max 1 (((n + 1 : ℕ) : ℝ) * (2 * L))) + 1) /
          (((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  let _ := iidMeasure_isProbability (volume.withDensity f) (n + 1)
  apply zeroSet_aeLog_and_integrable_positiveLogLoss_of_power_smallBall
    (iidMeasure (volume.withDensity f) (n + 1))
    (fun x => ‖p.eval x‖) p.continuous_eval_real.norm.measurable
    (fun x => norm_nonneg _)
    ‖p.topCoeff‖ (((n + 1 : ℕ) : ℝ) * (2 * L)) htop
    (n + 1) 1 (Nat.succ_pos n) Nat.one_pos
  intro ρ hρ
  change iidMeasure (volume.withDensity f) (n + 1)
      (closedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤ _
  calc
    iidMeasure (volume.withDensity f) (n + 1)
        (closedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) *
          ((2 : ℝ≥0∞) * ENNReal.ofReal L) * ENNReal.ofReal ρ :=
      iid_real_multiaffine_bound_withDensity f hf hρ p htop
    _ = ENNReal.ofReal
        ((((n + 1 : ℕ) : ℝ) * (2 * L)) * ρ ^ 1) := by
      rw [pow_one, ← ENNReal.ofReal_natCast (n + 1),
        ← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_mul zero_le_two,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg (n + 1)),
        ← ENNReal.ofReal_mul
          (mul_nonneg (Nat.cast_nonneg (n + 1)) (mul_nonneg zero_le_two hL))]

/-- Untruncated complex IID density theorem.  With `k = n + 1`, planar
area gives `A = π k L` and tail rate `2 / k`. -/
theorem iid_complex_positiveLogLoss_withDensity
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ z ∂(volume : Measure ℂ), f z ≤ ENNReal.ofReal L)
    {n : ℕ} (p : MultiAffine ℂ (n + 1))
    (htop : 0 < ‖p.topCoeff‖) :
    iidMeasure (volume.withDensity f) (n + 1) {x | ‖p.eval x‖ = 0} = 0 ∧
      (fun x => positiveLogLoss ‖p.topCoeff‖ ‖p.eval x‖) =ᵐ[
        iidMeasure (volume.withDensity f) (n + 1)]
        (fun x => max 0 (Real.log (‖p.topCoeff‖ / ‖p.eval x‖))) ∧
      Integrable
        (fun x => positiveLogLoss ‖p.topCoeff‖ ‖p.eval x‖)
        (iidMeasure (volume.withDensity f) (n + 1)) ∧
      ∫ x, positiveLogLoss ‖p.topCoeff‖ ‖p.eval x‖
          ∂iidMeasure (volume.withDensity f) (n + 1) ≤
        (Real.log
              (max 1 (((n + 1 : ℕ) : ℝ) * (Real.pi * L))) + 1) /
          (((2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  let _ := iidMeasure_isProbability (volume.withDensity f) (n + 1)
  apply zeroSet_aeLog_and_integrable_positiveLogLoss_of_power_smallBall
    (iidMeasure (volume.withDensity f) (n + 1))
    (fun x => ‖p.eval x‖) p.continuous_eval_complex.norm.measurable
    (fun x => norm_nonneg _)
    ‖p.topCoeff‖ (((n + 1 : ℕ) : ℝ) * (Real.pi * L)) htop
    (n + 1) 2 (Nat.succ_pos n) (by norm_num)
  intro ρ hρ
  change iidMeasure (volume.withDensity f) (n + 1)
      (closedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤ _
  calc
    iidMeasure (volume.withDensity f) (n + 1)
        (closedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal Real.pi * ENNReal.ofReal L) * ENNReal.ofReal ρ ^ 2 :=
      iid_complex_multiaffine_bound_withDensity f hf hρ p htop
    _ = ENNReal.ofReal
        ((((n + 1 : ℕ) : ℝ) * (Real.pi * L)) * ρ ^ 2) := by
      rw [← ENNReal.ofReal_natCast (n + 1),
        ← ENNReal.ofReal_mul Real.pi_pos.le,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg (n + 1)),
        ← ENNReal.ofReal_pow hρ.le,
        ← ENNReal.ofReal_mul
          (mul_nonneg (Nat.cast_nonneg (n + 1))
            (mul_nonneg Real.pi_pos.le hL))]

end CircularLawSection4
