import CircularLawSection4.ProductSmallBall
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# From multiaffine small balls to logarithmic moments

This file turns a polynomial small-ball estimate into an honest finite bound
for a regularized positive logarithm.  The regularization only floors the
absolute value at `scale * exp (-cutoff)`; in particular it gives the value
`cutoff` at a zero of the polynomial (when the cutoff is nonnegative).
-/

open scoped ENNReal MeasureTheory
open Set MeasureTheory Filter Measure

namespace CircularLawSection4

/-- Layer-cake closure: an exponential upper tail with prefactor `A` and
rate `q` gives the explicit logarithmic-size bound
`(log (max 1 A) + 1) / q`.

The probability-measure hypothesis supplies the missing `min 1` for the
initial part of the tail. -/
theorem integrable_and_expectation_le_of_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (A q : ℝ) (hq : 0 < q)
    (htail : ∀ t : ℝ, 0 < t →
      μ {ω | t < Z ω} ≤ ENNReal.ofReal (A * Real.exp ((-q) * t))) :
    Integrable Z μ ∧
      ∫ ω, Z ω ∂μ ≤ (Real.log (max 1 A) + 1) / q := by
  let B : ℝ := max 1 A
  let c : ℝ := Real.log B / q
  have hB1 : 1 ≤ B := by simp [B]
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hc : 0 ≤ c := div_nonneg hlogB hq.le
  have hqc : (-q) * c = -Real.log B := by
    dsimp [c]
    field_simp [ne_of_gt hq]
  have hexp : Real.exp ((-q) * c) = B⁻¹ := by
    rw [hqc, Real.exp_neg, Real.exp_log hB]
  have hsmall :
      (∫⁻ t : ℝ in Ioc 0 c, μ {ω | t < Z ω}) ≤ ENNReal.ofReal c := by
    calc
      (∫⁻ t : ℝ in Ioc 0 c, μ {ω | t < Z ω})
          ≤ ∫⁻ _ : ℝ in Ioc 0 c, (1 : ℝ≥0∞) := by
              apply setLIntegral_mono measurable_const
              intro t ht
              calc
                μ {ω | t < Z ω} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
                _ = 1 := measure_univ
      _ = ENNReal.ofReal c := by simp [Real.volume_Ioc]
  have hlarge_int :
      IntegrableOn (fun t : ℝ => B * Real.exp ((-q) * t)) (Ioi c) :=
    (integrableOn_exp_mul_Ioi (a := -q) (neg_lt_zero.mpr hq) c).const_mul B
  have hlarge :
      (∫⁻ t : ℝ in Ioi c, μ {ω | t < Z ω}) ≤ ENNReal.ofReal (1 / q) := by
    calc
      (∫⁻ t : ℝ in Ioi c, μ {ω | t < Z ω})
          ≤ ∫⁻ t : ℝ in Ioi c, ENNReal.ofReal (B * Real.exp ((-q) * t)) := by
              apply setLIntegral_mono
              · fun_prop
              · intro t ht
                calc
                  μ {ω | t < Z ω}
                      ≤ ENNReal.ofReal (A * Real.exp ((-q) * t)) :=
                        htail t (hc.trans_lt ht)
                  _ ≤ ENNReal.ofReal (B * Real.exp ((-q) * t)) := by
                    apply ENNReal.ofReal_le_ofReal
                    exact mul_le_mul_of_nonneg_right (le_max_right 1 A)
                      (Real.exp_pos _).le
      _ = ENNReal.ofReal (∫ t : ℝ in Ioi c, B * Real.exp ((-q) * t)) := by
            rw [ofReal_integral_eq_lintegral_ofReal hlarge_int]
            exact ae_of_all _ fun t => mul_nonneg hB.le (Real.exp_pos _).le
      _ = ENNReal.ofReal (1 / q) := by
            congr 1
            rw [integral_const_mul,
              integral_exp_mul_Ioi (a := -q) (neg_lt_zero.mpr hq) c, hexp]
            field_simp [ne_of_gt hB, ne_of_gt hq]
  have htail_int :
      (∫⁻ t : ℝ in Ioi 0, μ {ω | t < Z ω})
        ≤ ENNReal.ofReal ((Real.log B + 1) / q) := by
    rw [← Ioc_union_Ioi_eq_Ioi hc,
      lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
    calc
      (∫⁻ t : ℝ in Ioc 0 c, μ {ω | t < Z ω}) +
          (∫⁻ t : ℝ in Ioi c, μ {ω | t < Z ω})
          ≤ ENNReal.ofReal c + ENNReal.ofReal (1 / q) := add_le_add hsmall hlarge
      _ = ENNReal.ofReal (c + 1 / q) := by
            rw [ENNReal.ofReal_add hc (one_div_nonneg.mpr hq.le)]
      _ = ENNReal.ofReal ((Real.log B + 1) / q) := by
            congr 1
            dsimp [c]
            field_simp [ne_of_gt hq]
  have hnn : 0 ≤ᵐ[μ] Z := ae_of_all μ hZ0
  have hlin :
      (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ)
        ≤ ENNReal.ofReal ((Real.log B + 1) / q) := by
    rw [lintegral_eq_lintegral_meas_lt μ hnn hZ.aemeasurable]
    exact htail_int
  have hZint : Integrable Z μ :=
    (lintegral_ofReal_ne_top_iff_integrable hZ.aestronglyMeasurable hnn).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin)
  have hR : 0 ≤ (Real.log B + 1) / q :=
    div_nonneg (add_nonneg hlogB zero_le_one) hq.le
  refine ⟨hZint, ?_⟩
  change ∫ ω, Z ω ∂μ ≤ (Real.log B + 1) / q
  apply (ENNReal.ofReal_le_ofReal_iff hR).mp
  rw [ofReal_integral_eq_lintegral_ofReal hZint hnn]
  exact hlin

/-- A finite version of `(log (scale / radius))₊`.  The radius is floored at
`scale * exp (-cutoff)`, so the expression remains finite even at radius zero. -/
noncomputable def truncatedLogLoss (cutoff scale radius : ℝ) : ℝ :=
  max 0
    (Real.log scale -
      Real.log (max radius (scale * Real.exp (-cutoff))))

theorem truncatedLogLoss_nonneg (cutoff scale radius : ℝ) :
    0 ≤ truncatedLogLoss cutoff scale radius := by
  exact le_max_left _ _

/-- Above the exponential floor, the regularized loss is exactly the usual
positive logarithmic deficit. -/
theorem truncatedLogLoss_eq_posLog_of_floor_le
    {cutoff scale radius : ℝ}
    (hfloor : scale * Real.exp (-cutoff) ≤ radius) :
    truncatedLogLoss cutoff scale radius =
      max 0 (Real.log scale - Real.log radius) := by
  simp only [truncatedLogLoss, max_eq_left hfloor]

/-- At radius zero, a nonnegative cutoff has exactly the advertised value. -/
theorem truncatedLogLoss_zero
    {cutoff scale : ℝ} (hcutoff : 0 ≤ cutoff) (hscale : 0 < scale) :
    truncatedLogLoss cutoff scale 0 = cutoff := by
  unfold truncatedLogLoss
  rw [max_eq_right (mul_pos hscale (Real.exp_pos _)).le]
  rw [Real.log_mul hscale.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring_nf
  simp [hcutoff]

theorem measurable_truncatedLogLoss
    {Ω : Type*} [MeasurableSpace Ω] (cutoff scale : ℝ)
    {radius : Ω → ℝ} (hradius : Measurable radius) :
    Measurable (fun ω => truncatedLogLoss cutoff scale (radius ω)) := by
  unfold truncatedLogLoss
  fun_prop

/-- A positive tail of the regularized log loss forces a small radius at the
corresponding exponential scale. -/
theorem truncatedLogLoss_tail_imp_radius_le
    {cutoff scale radius t : ℝ} (hscale : 0 < scale) (ht : 0 < t)
    (h : t < truncatedLogLoss cutoff scale radius) :
    radius ≤ scale * Real.exp (-t) := by
  let m : ℝ := max radius (scale * Real.exp (-cutoff))
  have hmpos : 0 < m := by
    exact (mul_pos hscale (Real.exp_pos _)).trans_le (le_max_right _ _)
  have htarget : 0 < scale * Real.exp (-t) := mul_pos hscale (Real.exp_pos _)
  have htlog : t < Real.log scale - Real.log m := by
    change t < max 0 (Real.log scale - Real.log m) at h
    rcases (lt_max_iff.mp h) with hneg | hlog
    · linarith
    · exact hlog
  have hlogtarget :
      Real.log (scale * Real.exp (-t)) = Real.log scale - t := by
    rw [Real.log_mul hscale.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hmlog : Real.log m < Real.log (scale * Real.exp (-t)) := by
    rw [hlogtarget]
    linarith
  have hm_lt : m < scale * Real.exp (-t) :=
    (Real.log_lt_log_iff hmpos htarget).mp hmlog
  exact (le_max_left radius (scale * Real.exp (-cutoff))).trans hm_lt.le

/-- Abstract bridge used by the real and complex product models below.
If the small-ball cost at scale `ρ` is `A ρ^m`, while the polynomial
threshold scales as `ρ^d`, then the logarithmic tail rate is `m / d`. -/
theorem integrable_truncatedLogLoss_of_power_smallBall
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (radius : Ω → ℝ) (hradius : Measurable radius)
    (cutoff scale A : ℝ) (hscale : 0 < scale)
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (hsmall : ∀ ρ : ℝ, 0 < ρ →
      μ {ω | radius ω ≤ scale * ρ ^ d} ≤ ENNReal.ofReal (A * ρ ^ m)) :
    Integrable (fun ω => truncatedLogLoss cutoff scale (radius ω)) μ ∧
      ∫ ω, truncatedLogLoss cutoff scale (radius ω) ∂μ ≤
        (Real.log (max 1 A) + 1) / ((m : ℝ) / (d : ℝ)) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  apply integrable_and_expectation_le_of_exponential_tail μ
    (fun ω => truncatedLogLoss cutoff scale (radius ω))
    (measurable_truncatedLogLoss cutoff scale hradius)
    (fun ω => truncatedLogLoss_nonneg cutoff scale (radius ω)) A
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
      {ω | t < truncatedLogLoss cutoff scale (radius ω)} ⊆
        {ω | radius ω ≤ scale * ρ ^ d} := by
    intro ω hω
    have hle := truncatedLogLoss_tail_imp_radius_le hscale ht hω
    change radius ω ≤ scale * ρ ^ d
    simpa only [hρd] using hle
  calc
    μ {ω | t < truncatedLogLoss cutoff scale (radius ω)} ≤
        μ {ω | radius ω ≤ scale * ρ ^ d} := measure_mono hsubset
    _ ≤ ENNReal.ofReal (A * ρ ^ m) := hsmall ρ hρ
    _ = ENNReal.ofReal
        (A * Real.exp ((-((m : ℝ) / (d : ℝ))) * t)) := by rw [hρm]

/-- Real IID density specialization.  For `k = n + 1` variables, the input
small-ball estimate has `A = 2 k L` and logarithmic tail rate `1 / k`.
The conclusion is uniform in the finite cutoff. -/
theorem iid_real_truncatedLogLoss_withDensity
    (f : ℝ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ x ∂(volume : Measure ℝ), f x ≤ ENNReal.ofReal L)
    (cutoff : ℝ) {n : ℕ} (p : MultiAffine ℝ (n + 1))
    (htop : 0 < ‖p.topCoeff‖) :
    Integrable
        (fun x => truncatedLogLoss cutoff ‖p.topCoeff‖ ‖p.eval x‖)
        (iidMeasure (volume.withDensity f) (n + 1)) ∧
      ∫ x, truncatedLogLoss cutoff ‖p.topCoeff‖ ‖p.eval x‖
          ∂iidMeasure (volume.withDensity f) (n + 1) ≤
        (Real.log
              (max 1 (((n + 1 : ℕ) : ℝ) * (2 * L))) + 1) /
          (((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  let _ := iidMeasure_isProbability (volume.withDensity f) (n + 1)
  apply integrable_truncatedLogLoss_of_power_smallBall
    (iidMeasure (volume.withDensity f) (n + 1))
    (fun x => ‖p.eval x‖) p.continuous_eval_real.norm.measurable
    cutoff ‖p.topCoeff‖ (((n + 1 : ℕ) : ℝ) * (2 * L)) htop
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

/-- Complex IID density specialization.  For `k = n + 1` variables, planar
disk area gives `A = π k L` and logarithmic tail rate `2 / k`. -/
theorem iid_complex_truncatedLogLoss_withDensity
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ z ∂(volume : Measure ℂ), f z ≤ ENNReal.ofReal L)
    (cutoff : ℝ) {n : ℕ} (p : MultiAffine ℂ (n + 1))
    (htop : 0 < ‖p.topCoeff‖) :
    Integrable
        (fun x => truncatedLogLoss cutoff ‖p.topCoeff‖ ‖p.eval x‖)
        (iidMeasure (volume.withDensity f) (n + 1)) ∧
      ∫ x, truncatedLogLoss cutoff ‖p.topCoeff‖ ‖p.eval x‖
          ∂iidMeasure (volume.withDensity f) (n + 1) ≤
        (Real.log
              (max 1 (((n + 1 : ℕ) : ℝ) * (Real.pi * L))) + 1) /
          (((2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  let _ := iidMeasure_isProbability (volume.withDensity f) (n + 1)
  apply integrable_truncatedLogLoss_of_power_smallBall
    (iidMeasure (volume.withDensity f) (n + 1))
    (fun x => ‖p.eval x‖) p.continuous_eval_complex.norm.measurable
    cutoff ‖p.topCoeff‖ (((n + 1 : ℕ) : ℝ) * (Real.pi * L)) htop
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
