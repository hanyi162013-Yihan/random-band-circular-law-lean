import TaoVuReplacement.RandomMatrixMeasurability
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Data.Multiset.Fintype
import Mathlib.MeasureTheory.Group.Integral

/-!
# Local `L²` bounds for the logarithmic kernel

This file formalizes the analytic estimate used in Tao--Vu, equation (27):
on every fixed bounded region of the complex plane, the translated kernel
`z ↦ log ‖w - z‖` has an `L²` bound growing at most quadratically in `‖w‖`.

The singular part is controlled uniformly by translation invariance of planar
Lebesgue measure.  The remaining part is bounded by the second moment.  The
last section records the finite-multiset Jensen/Cauchy estimate needed for
empirical logarithmic potentials.
-/

open Filter Set MeasureTheory Topology
open scoped BigOperators ENNReal Real Topology

noncomputable section

namespace TaoVuReplacement

/-- The squared real logarithmic kernel.  Mathlib uses the totalized value
`Real.log 0 = 0`; changing the value at the centre does not affect any planar
integral. -/
def logKernelSq (w z : ℂ) : ℝ := (Real.log ‖w - z‖) ^ 2

/-- An elementary domination used to prove local integrability at the
origin.  The deliberately loose constant `8` keeps the proof independent of
an exact evaluation of the radial integral. -/
private theorem log_sq_le_eight_mul_rpow_neg_one {x : ℝ}
    (hx : 0 ≤ x) (hx_two : x ≤ 2) :
    (Real.log x) ^ 2 ≤ 8 * x ^ (-1 : ℝ) := by
  rcases hx.eq_or_lt with rfl | hx_pos
  · simp
  by_cases hx_one : x ≤ 1
  · have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
    have h := Real.abs_log_mul_self_rpow_lt x (1 / 2 : ℝ)
      hx_pos hx_one hhalf
    have hrpow_pos : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx_pos _
    have hprod : |Real.log x| * x ^ (1 / 2 : ℝ) ≤ 2 := by
      have h' := h.le
      rw [abs_mul, abs_of_nonneg hrpow_pos.le] at h'
      norm_num at h'
      exact h'
    have hsq : (|Real.log x| * x ^ (1 / 2 : ℝ)) ^ 2 ≤ (2 : ℝ) ^ 2 :=
      (sq_le_sq₀ (mul_nonneg (abs_nonneg _) hrpow_pos.le) (by norm_num)).2 hprod
    have hrpow_sq : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
      rw [← Real.rpow_mul_natCast hx (1 / 2 : ℝ) 2]
      norm_num
    rw [mul_pow, sq_abs, hrpow_sq] at hsq
    rw [Real.rpow_neg_one, ← div_eq_mul_inv]
    apply (le_div_iff₀ hx_pos).2
    exact hsq.trans (by norm_num)
  · have hx_one' : 1 < x := lt_of_not_ge hx_one
    have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx_one'.le
    have hlog_one : Real.log x ≤ 1 := by
      exact (Real.log_le_sub_one_of_pos hx_pos).trans (by linarith)
    have hsq : (Real.log x) ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ hlog_nonneg zero_le_one).2 hlog_one
    have hone : (1 : ℝ) ≤ 8 * x ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      apply (le_div_iff₀ hx_pos).2
      simpa using hx_two.trans (by norm_num : (2 : ℝ) ≤ 8)
    exact hsq.trans (by simpa using hone)

/-- The centered squared logarithmic kernel is integrable on the closed unit
ball.  This is the sole singular-integrability input for the translated
estimate below, and is proved here from the standard `r⁻¹` local-integrability
criterion in real dimension two. -/
theorem integrableOn_logKernelSq_zero_closedBall_one :
    IntegrableOn (logKernelSq 0) (Metric.closedBall (0 : ℂ) 1) := by
  let f : ℂ → ℝ := fun z ↦ (Real.log ‖z‖) ^ 2
  have hf_meas : AEStronglyMeasurable f (volume : Measure ℂ) := by
    exact (((measurable_norm : Measurable fun z : ℂ ↦ ‖z‖).log).pow_const 2).aestronglyMeasurable
  have hball : IntegrableOn f (Metric.ball (0 : ℂ) 2) := by
    apply integrableOn_ball_of_norm_le_rpow (μ := (volume : Measure ℂ))
      (f := f) (by norm_num) (C := 8) (α := 1) (r := 2)
    · norm_num
    · filter_upwards [self_mem_ae_restrict measurableSet_ball] with z hz
      have hz_two : ‖z‖ ≤ 2 := by
        have : ‖z‖ < 2 := by
          simpa [Metric.mem_ball, dist_zero_right] using hz
        exact this.le
      have hbound := log_sq_le_eight_mul_rpow_neg_one
        (norm_nonneg z) hz_two
      change |(Real.log ‖z‖) ^ 2| ≤ 8 * ‖z‖ ^ (-1 : ℝ)
      rw [abs_of_nonneg (sq_nonneg _)]
      exact hbound
    · exact hf_meas
  have hsubset : Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball 0 2 := by
    intro z hz
    have hz_norm : ‖z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    simpa [Metric.mem_ball, dist_zero_right] using hz_norm.trans_lt one_lt_two
  rw [show logKernelSq 0 = f by funext z; simp [logKernelSq, f]]
  exact hball.mono_set hsubset

/-- The singular part of the centered kernel, cut off at unit distance. -/
def unitSingularLogKernelSq (z : ℂ) : ℝ :=
  (Metric.closedBall (0 : ℂ) 1).indicator (logKernelSq 0) z

theorem unitSingularLogKernelSq_nonneg (z : ℂ) :
    0 ≤ unitSingularLogKernelSq z := by
  by_cases hz : z ∈ Metric.closedBall (0 : ℂ) 1
  · simp [unitSingularLogKernelSq, hz, logKernelSq, sq_nonneg]
  · simp [unitSingularLogKernelSq, hz]

/-- The unit-distance singular part is globally integrable. -/
theorem integrable_unitSingularLogKernelSq :
    Integrable unitSingularLogKernelSq := by
  exact integrableOn_logKernelSq_zero_closedBall_one.integrable_indicator
    measurableSet_closedBall

/-- Translation preserves integrability of the cut-off singular part. -/
theorem integrable_unitSingularLogKernelSq_sub_right (w : ℂ) :
    Integrable (fun z ↦ unitSingularLogKernelSq (z - w)) :=
  integrable_unitSingularLogKernelSq.comp_sub_right w

/-- The logarithmic square is bounded by a quadratic term plus the translated
unit-distance singular part. -/
theorem logKernelSq_le_normSq_add_unitSingular (w z : ℂ) :
    logKernelSq w z ≤
      ‖w - z‖ ^ 2 + unitSingularLogKernelSq (z - w) := by
  by_cases hdist : ‖w - z‖ ≤ 1
  · have hmem : z - w ∈ Metric.closedBall (0 : ℂ) 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right, norm_sub_rev] using hdist
    rw [unitSingularLogKernelSq, Set.indicator_of_mem hmem]
    have heq : logKernelSq 0 (z - w) = logKernelSq w z := by
      simp [logKernelSq]
    rw [heq]
    exact le_add_of_nonneg_left (sq_nonneg _)
  · have hmem : z - w ∉ Metric.closedBall (0 : ℂ) 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right, norm_sub_rev] using hdist
    rw [unitSingularLogKernelSq, Set.indicator_of_notMem hmem, add_zero]
    have hdist' : 1 < ‖w - z‖ := lt_of_not_ge hdist
    have hlog_nonneg : 0 ≤ Real.log ‖w - z‖ :=
      Real.log_nonneg hdist'.le
    have hlog_le : Real.log ‖w - z‖ ≤ ‖w - z‖ :=
      (Real.log_le_sub_one_of_pos (zero_lt_one.trans hdist')).trans
        (sub_le_self _ zero_le_one)
    exact (sq_le_sq₀ hlog_nonneg (norm_nonneg _)).2 hlog_le

/-- On a fixed closed ball, the quadratic part of the translated kernel is
controlled by the centre's second moment. -/
theorem norm_sub_sq_le_two_mul_add_sq_of_mem_closedBall
    {R : ℝ} (hR : 0 ≤ R) (w : ℂ) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ‖w - z‖ ^ 2 ≤ 2 * (‖w‖ ^ 2 + R ^ 2) := by
  have hz_norm : ‖z‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hnorm : ‖w - z‖ ≤ ‖w‖ + R := by
    calc
      ‖w - z‖ ≤ ‖w‖ + ‖z‖ := norm_sub_le w z
      _ ≤ ‖w‖ + R := by gcongr
  have hsquare : ‖w - z‖ ^ 2 ≤ (‖w‖ + R) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) hR)).2 hnorm
  nlinarith [sq_nonneg (‖w‖ - R)]

/-- Every translated squared logarithmic kernel is integrable on every
closed ball. -/
theorem integrableOn_logKernelSq_closedBall (R : ℝ) (w : ℂ) :
    IntegrableOn (logKernelSq w) (Metric.closedBall (0 : ℂ) R) := by
  let q : ℂ → ℝ := fun z ↦ ‖w - z‖ ^ 2
  let s : ℂ → ℝ := fun z ↦ unitSingularLogKernelSq (z - w)
  have hq : IntegrableOn q (Metric.closedBall (0 : ℂ) R) := by
    exact (by fun_prop : Continuous q).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) R)
  have hs : IntegrableOn s (Metric.closedBall (0 : ℂ) R) :=
    (integrable_unitSingularLogKernelSq_sub_right w).integrableOn
  have hsum : IntegrableOn (fun z ↦ q z + s z)
      (Metric.closedBall (0 : ℂ) R) := hq.add hs
  apply hsum.mono'
  · exact ((((measurable_const.sub measurable_id).norm.log).pow_const 2)).aestronglyMeasurable.restrict
  · filter_upwards with z
    change |logKernelSq w z| ≤ q z + s z
    rw [abs_of_nonneg (sq_nonneg _)]
    exact logKernelSq_le_normSq_add_unitSingular w z

/-- A quantitative intermediate form of the local `L²` logarithmic-kernel
bound.  The two constants are the volume of the observation ball and the
fixed integral of the unit singularity. -/
theorem integral_logKernelSq_closedBall_le (R : ℝ) (hR : 0 ≤ R) (w : ℂ) :
    (∫ z in Metric.closedBall (0 : ℂ) R, logKernelSq w z) ≤
      (volume : Measure ℂ).real (Metric.closedBall 0 R) *
          (2 * (‖w‖ ^ 2 + R ^ 2)) +
        ∫ z : ℂ, unitSingularLogKernelSq z := by
  let B : Set ℂ := Metric.closedBall 0 R
  let q : ℂ → ℝ := fun z ↦ ‖w - z‖ ^ 2
  let s : ℂ → ℝ := fun z ↦ unitSingularLogKernelSq (z - w)
  have hlog : IntegrableOn (logKernelSq w) B := by
    simpa [B] using integrableOn_logKernelSq_closedBall R w
  have hq : IntegrableOn q B := by
    exact (by fun_prop : Continuous q).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) R)
  have hs_global : Integrable s :=
    integrable_unitSingularLogKernelSq_sub_right w
  have hs : IntegrableOn s B := hs_global.integrableOn
  have hsum : IntegrableOn (fun z ↦ q z + s z) B := hq.add hs
  have hfirst : (∫ z in B, logKernelSq w z) ≤ ∫ z in B, q z + s z :=
    setIntegral_mono_on hlog hsum measurableSet_closedBall fun z _hz ↦
      logKernelSq_le_normSq_add_unitSingular w z
  have hq_const : IntegrableOn (fun _z : ℂ ↦ 2 * (‖w‖ ^ 2 + R ^ 2)) B := by
    exact continuous_const.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) R)
  have hq_bound : (∫ z in B, q z) ≤
      ∫ _z in B, 2 * (‖w‖ ^ 2 + R ^ 2) :=
    setIntegral_mono_on hq hq_const measurableSet_closedBall fun z hz ↦
      norm_sub_sq_le_two_mul_add_sq_of_mem_closedBall hR w hz
  have hs_bound : (∫ z in B, s z) ≤ ∫ z : ℂ, s z := by
    exact setIntegral_le_integral hs_global
      (Filter.Eventually.of_forall fun z ↦ unitSingularLogKernelSq_nonneg (z - w))
  have hs_eq : (∫ z : ℂ, s z) = ∫ z : ℂ, unitSingularLogKernelSq z := by
    exact integral_sub_right_eq_self unitSingularLogKernelSq w
  calc
    (∫ z in Metric.closedBall (0 : ℂ) R, logKernelSq w z) =
        ∫ z in B, logKernelSq w z := rfl
    _ ≤ ∫ z in B, q z + s z := hfirst
    _ = (∫ z in B, q z) + ∫ z in B, s z := integral_add hq hs
    _ ≤ (∫ _z in B, 2 * (‖w‖ ^ 2 + R ^ 2)) + ∫ z : ℂ, s z :=
      add_le_add hq_bound hs_bound
    _ = (volume : Measure ℂ).real B * (2 * (‖w‖ ^ 2 + R ^ 2)) +
        ∫ z : ℂ, unitSingularLogKernelSq z := by
      rw [hs_eq]
      simp [B]
    _ = (volume : Measure ℂ).real (Metric.closedBall 0 R) *
          (2 * (‖w‖ ^ 2 + R ^ 2)) +
        ∫ z : ℂ, unitSingularLogKernelSq z := rfl

/-- Tao--Vu (27), single-atom local `L²` logarithmic-kernel bound, in a
real-integral formulation.  For each finite observation radius, one finite
nonnegative constant works for every centre `w`, with only quadratic growth
in `‖w‖`.

The constant is intentionally existential: the replacement principle uses
only its finiteness and uniformity in `w`, not its numerical value. -/
theorem exists_integral_logKernelSq_closedBall_le
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ,
      (∫ z in Metric.closedBall (0 : ℂ) R, logKernelSq w z) ≤
        C * (1 + ‖w‖ ^ 2) := by
  let V : ℝ := (volume : Measure ℂ).real (Metric.closedBall 0 R)
  let K : ℝ := ∫ z : ℂ, unitSingularLogKernelSq z
  let C : ℝ := 2 * V * (1 + R ^ 2) + K
  have hV : 0 ≤ V := measureReal_nonneg
  have hK : 0 ≤ K := by
    exact integral_nonneg fun z ↦ unitSingularLogKernelSq_nonneg z
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, fun w ↦ ?_⟩
  refine (integral_logKernelSq_closedBall_le R hR w).trans ?_
  change V * (2 * (‖w‖ ^ 2 + R ^ 2)) + K ≤
    C * (1 + ‖w‖ ^ 2)
  have h₁ : 0 ≤ 2 * V * (1 + R ^ 2 * ‖w‖ ^ 2) := by positivity
  have h₂ : 0 ≤ K * ‖w‖ ^ 2 := mul_nonneg hK (sq_nonneg _)
  dsimp [C]
  nlinarith

/-! ## Finite-multiset averages -/

/-- The arithmetic average over a multiset, using the occurrence type of the
multiset.  Thus repeated elements are counted with their multiplicities.  The
empty average is `0`, following the field convention `0 / 0 = 0`. -/
def multisetAverage {α : Type*} [DecidableEq α]
    (s : Multiset α) (f : α → ℝ) : ℝ :=
  (∑ x : ↥s, f (x : α)) / (s.card : ℝ)

/-- Finite Jensen/Cauchy for a multiset average.  This is the pointwise
inequality `|average aᵢ|² ≤ average |aᵢ|²`, with multiplicities retained. -/
theorem multisetAverage_sq_le_average_sq {α : Type*} [DecidableEq α]
    (s : Multiset α) (f : α → ℝ) :
    (multisetAverage s f) ^ 2 ≤ multisetAverage s (fun x ↦ (f x) ^ 2) := by
  simpa [multisetAverage, Multiset.card_coe] using
    (sum_div_card_sq_le_sum_sq_div_card
      (α := ℝ) (s := (Finset.univ : Finset ↥s))
      (f := fun x : ↥s ↦ f (x : α)))

/-- The logarithmic potential of a finite multiset, normalized by its
cardinality.  For an eigenvalue multiset this is the normalized log-potential
of the empirical spectral distribution. -/
def multisetLogPotential (s : Multiset ℂ) (z : ℂ) : ℝ :=
  multisetAverage s (fun w ↦ Real.log ‖w - z‖)

/-- Normalized spectral second moment of a finite multiset. -/
def multisetSecondMoment (s : Multiset ℂ) : ℝ :=
  multisetAverage s (fun w ↦ ‖w‖ ^ 2)

/-- Pointwise Jensen/Cauchy estimate for a finite empirical logarithmic
potential. -/
theorem multisetLogPotential_sq_le_average_logKernelSq
    (s : Multiset ℂ) (z : ℂ) :
    (multisetLogPotential s z) ^ 2 ≤
      multisetAverage s (fun w ↦ logKernelSq w z) := by
  exact multisetAverage_sq_le_average_sq s
    (fun w ↦ Real.log ‖w - z‖)

/-- The pointwise average of the squared kernels is integrable on a closed
ball. -/
theorem integrableOn_multisetAverage_logKernelSq
    (R : ℝ) (s : Multiset ℂ) :
    IntegrableOn (fun z ↦ multisetAverage s (fun w ↦ logKernelSq w z))
      (Metric.closedBall (0 : ℂ) R) := by
  classical
  unfold multisetAverage
  apply Integrable.div_const
  exact integrable_finsetSum Finset.univ fun w _hw ↦
    integrableOn_logKernelSq_closedBall R (w : ℂ)

/-- The square of the finite empirical logarithmic potential is integrable
on every closed ball. -/
theorem integrableOn_multisetLogPotential_sq
    (R : ℝ) (s : Multiset ℂ) :
    IntegrableOn (fun z ↦ (multisetLogPotential s z) ^ 2)
      (Metric.closedBall (0 : ℂ) R) := by
  have havg := integrableOn_multisetAverage_logKernelSq R s
  apply havg.mono'
  · have hmeas : Measurable (fun z ↦ (multisetLogPotential s z) ^ 2) := by
      unfold multisetLogPotential multisetAverage
      fun_prop
    exact hmeas.aestronglyMeasurable.restrict
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact multisetLogPotential_sq_le_average_logKernelSq s z

/-- Integrated Jensen/Cauchy for a finite multiset.  It moves the local `L²`
norm of the empirical log potential below the average of the one-atom local
`L²` norms. -/
theorem integral_multisetLogPotential_sq_le_average_integral_logKernelSq
    (R : ℝ) (s : Multiset ℂ) :
    (∫ z in Metric.closedBall (0 : ℂ) R,
        (multisetLogPotential s z) ^ 2) ≤
      multisetAverage s (fun w ↦
        ∫ z in Metric.closedBall (0 : ℂ) R, logKernelSq w z) := by
  let B : Set ℂ := Metric.closedBall 0 R
  have hleft : IntegrableOn (fun z ↦ (multisetLogPotential s z) ^ 2) B := by
    simpa [B] using integrableOn_multisetLogPotential_sq R s
  have hright : IntegrableOn
      (fun z ↦ multisetAverage s (fun w ↦ logKernelSq w z)) B := by
    simpa [B] using integrableOn_multisetAverage_logKernelSq R s
  calc
    (∫ z in Metric.closedBall (0 : ℂ) R,
        (multisetLogPotential s z) ^ 2) =
        ∫ z in B, (multisetLogPotential s z) ^ 2 := rfl
    _ ≤ ∫ z in B, multisetAverage s (fun w ↦ logKernelSq w z) :=
      setIntegral_mono_on hleft hright measurableSet_closedBall fun z _hz ↦
        multisetLogPotential_sq_le_average_logKernelSq s z
    _ = multisetAverage s (fun w ↦ ∫ z in B, logKernelSq w z) := by
      unfold multisetAverage
      rw [integral_div]
      rw [integral_finsetSum Finset.univ]
      intro w _hw
      exact integrableOn_logKernelSq_closedBall R (w : ℂ)
    _ = multisetAverage s (fun w ↦
        ∫ z in Metric.closedBall (0 : ℂ) R, logKernelSq w z) := rfl

/-! ## Uniform local `L²` bounds for empirical log potentials -/

/-- The occurrence-type sum used in `multisetAverage` is the ordinary mapped
multiset sum.  This bridge makes the analytic estimates directly usable with
the spectral sums from `EmpiricalSpectrum`. -/
theorem multisetAverage_eq_map_sum_div_card {α : Type*} [DecidableEq α]
    (s : Multiset α) (f : α → ℝ) :
    multisetAverage s f = (s.map f).sum / (s.card : ℝ) := by
  unfold multisetAverage
  congr 1
  rw [← Multiset.map_univ s f]
  rfl

/-- Averaging preserves pointwise inequalities.  The statement also covers
the empty multiset, for which both averages are zero. -/
theorem multisetAverage_mono {α : Type*} [DecidableEq α]
    (s : Multiset α) {f g : α → ℝ} (hfg : ∀ x ∈ s, f x ≤ g x) :
    multisetAverage s f ≤ multisetAverage s g := by
  unfold multisetAverage
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg s.card)
  apply Finset.sum_le_sum
  intro x _hx
  exact hfg (x : α) Multiset.coe_mem

/-- A nonempty multiset has average one equal to one. -/
theorem multisetAverage_one {α : Type*} [DecidableEq α]
    (s : Multiset α) (hs : s.card ≠ 0) :
    multisetAverage s (fun _ ↦ (1 : ℝ)) = 1 := by
  unfold multisetAverage
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs
  simp [Multiset.card_coe, hcard]

/-- Multiset averaging commutes with addition. -/
theorem multisetAverage_add {α : Type*} [DecidableEq α]
    (s : Multiset α) (f g : α → ℝ) :
    multisetAverage s (fun x ↦ f x + g x) =
      multisetAverage s f + multisetAverage s g := by
  unfold multisetAverage
  rw [Finset.sum_add_distrib, add_div]

/-- Multiset averaging commutes with multiplication by a scalar. -/
theorem multisetAverage_mul_left {α : Type*} [DecidableEq α]
    (s : Multiset α) (c : ℝ) (f : α → ℝ) :
    multisetAverage s (fun x ↦ c * f x) = c * multisetAverage s f := by
  unfold multisetAverage
  rw [← Finset.mul_sum]
  ring

/-- The normalized second moment is nonnegative. -/
theorem multisetSecondMoment_nonneg (s : Multiset ℂ) :
    0 ≤ multisetSecondMoment s := by
  unfold multisetSecondMoment multisetAverage
  exact div_nonneg
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    (Nat.cast_nonneg s.card)

/-- The average of the one-atom quadratic majorant is exactly the same
quadratic expression in the normalized second moment. -/
theorem multisetAverage_const_mul_one_add_norm_sq
    (s : Multiset ℂ) (hs : s.card ≠ 0) (C : ℝ) :
    multisetAverage s (fun w ↦ C * (1 + ‖w‖ ^ 2)) =
      C * (1 + multisetSecondMoment s) := by
  rw [show (fun w : ℂ ↦ C * (1 + ‖w‖ ^ 2)) =
      (fun w ↦ C * ((fun _ : ℂ ↦ (1 : ℝ)) w + (fun w : ℂ ↦ ‖w‖ ^ 2) w))
      by rfl]
  rw [multisetAverage_mul_left, multisetAverage_add,
    multisetAverage_one s hs]
  rfl

/-- Tao--Vu (27) for a nonempty finite empirical measure.  A single constant,
depending only on the observation radius, controls every finite spectrum by
its normalized second moment. -/
theorem exists_integral_multisetLogPotential_sq_closedBall_le
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : Multiset ℂ, s.card ≠ 0 →
      (∫ z in Metric.closedBall (0 : ℂ) R,
          (multisetLogPotential s z) ^ 2) ≤
        C * (1 + multisetSecondMoment s) := by
  obtain ⟨C, hC, hkernel⟩ := exists_integral_logKernelSq_closedBall_le R hR
  refine ⟨C, hC, fun s hs ↦ ?_⟩
  calc
    (∫ z in Metric.closedBall (0 : ℂ) R,
        (multisetLogPotential s z) ^ 2) ≤
        multisetAverage s (fun w ↦
          ∫ z in Metric.closedBall (0 : ℂ) R, logKernelSq w z) :=
      integral_multisetLogPotential_sq_le_average_integral_logKernelSq R s
    _ ≤ multisetAverage s (fun w ↦ C * (1 + ‖w‖ ^ 2)) :=
      multisetAverage_mono s fun w _hw ↦ hkernel w
    _ = C * (1 + multisetSecondMoment s) :=
      multisetAverage_const_mul_one_add_norm_sq s hs C

/-- The square of a difference is bounded by twice the sum of the two
squares.  Here it is recorded for empirical logarithmic potentials. -/
theorem multisetLogPotential_sub_sq_le
    (s t : Multiset ℂ) (z : ℂ) :
    (multisetLogPotential s z - multisetLogPotential t z) ^ 2 ≤
      2 * (multisetLogPotential s z) ^ 2 +
        2 * (multisetLogPotential t z) ^ 2 := by
  nlinarith [sq_nonneg (multisetLogPotential s z + multisetLogPotential t z)]

/-- The squared difference of two finite empirical log potentials is locally
integrable. -/
theorem integrableOn_multisetLogPotential_sub_sq
    (R : ℝ) (s t : Multiset ℂ) :
    IntegrableOn
      (fun z ↦ (multisetLogPotential s z - multisetLogPotential t z) ^ 2)
      (Metric.closedBall (0 : ℂ) R) := by
  have hs := (integrableOn_multisetLogPotential_sq R s).const_mul 2
  have ht := (integrableOn_multisetLogPotential_sq R t).const_mul 2
  apply (hs.add ht).mono'
  · have hmeas : Measurable
        (fun z ↦ (multisetLogPotential s z - multisetLogPotential t z) ^ 2) := by
      unfold multisetLogPotential multisetAverage
      fun_prop
    exact hmeas.aestronglyMeasurable.restrict
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact multisetLogPotential_sub_sq_le s t z

/-- Integrated form of the elementary difference-of-squares majorization. -/
theorem integral_multisetLogPotential_sub_sq_le_two
    (R : ℝ) (s t : Multiset ℂ) :
    (∫ z in Metric.closedBall (0 : ℂ) R,
        (multisetLogPotential s z - multisetLogPotential t z) ^ 2) ≤
      2 * (∫ z in Metric.closedBall (0 : ℂ) R,
        (multisetLogPotential s z) ^ 2) +
      2 * (∫ z in Metric.closedBall (0 : ℂ) R,
        (multisetLogPotential t z) ^ 2) := by
  let B : Set ℂ := Metric.closedBall 0 R
  have hdiff : IntegrableOn
      (fun z ↦ (multisetLogPotential s z - multisetLogPotential t z) ^ 2) B := by
    simpa [B] using integrableOn_multisetLogPotential_sub_sq R s t
  have hs : IntegrableOn (fun z ↦ (multisetLogPotential s z) ^ 2) B := by
    simpa [B] using integrableOn_multisetLogPotential_sq R s
  have ht : IntegrableOn (fun z ↦ (multisetLogPotential t z) ^ 2) B := by
    simpa [B] using integrableOn_multisetLogPotential_sq R t
  have hmajor : IntegrableOn
      (fun z ↦ 2 * (multisetLogPotential s z) ^ 2 +
        2 * (multisetLogPotential t z) ^ 2) B := by
    change IntegrableOn
      ((fun z ↦ 2 * (multisetLogPotential s z) ^ 2) +
        (fun z ↦ 2 * (multisetLogPotential t z) ^ 2)) B
    exact (hs.const_mul 2).add (ht.const_mul 2)
  calc
    (∫ z in Metric.closedBall (0 : ℂ) R,
        (multisetLogPotential s z - multisetLogPotential t z) ^ 2) =
        ∫ z in B,
          (multisetLogPotential s z - multisetLogPotential t z) ^ 2 := rfl
    _ ≤ ∫ z in B,
        (2 * (multisetLogPotential s z) ^ 2 +
          2 * (multisetLogPotential t z) ^ 2) :=
      setIntegral_mono_on hdiff hmajor
        measurableSet_closedBall fun z _hz ↦ multisetLogPotential_sub_sq_le s t z
    _ = 2 * (∫ z in B, (multisetLogPotential s z) ^ 2) +
        2 * (∫ z in B, (multisetLogPotential t z) ^ 2) := by
      rw [integral_add (hs.const_mul 2) (ht.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ = 2 * (∫ z in Metric.closedBall (0 : ℂ) R,
          (multisetLogPotential s z) ^ 2) +
        2 * (∫ z in Metric.closedBall (0 : ℂ) R,
          (multisetLogPotential t z) ^ 2) := rfl

/-- Uniform local `L²` bound for the difference of two nonempty empirical
logarithmic potentials. -/
theorem exists_integral_multisetLogPotential_sub_sq_closedBall_le
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : Multiset ℂ,
      s.card ≠ 0 → t.card ≠ 0 →
      (∫ z in Metric.closedBall (0 : ℂ) R,
          (multisetLogPotential s z - multisetLogPotential t z) ^ 2) ≤
        C * (1 + multisetSecondMoment s + multisetSecondMoment t) := by
  obtain ⟨C, hC, hsingle⟩ :=
    exists_integral_multisetLogPotential_sq_closedBall_le R hR
  refine ⟨4 * C, by positivity, fun s t hs ht ↦ ?_⟩
  have hsm := hsingle s hs
  have htm := hsingle t ht
  have hdiff := integral_multisetLogPotential_sub_sq_le_two R s t
  have hms := multisetSecondMoment_nonneg s
  have hmt := multisetSecondMoment_nonneg t
  nlinarith

/-- `lintegral` version of the preceding empirical-potential estimate.  The
integrand is written with `ENNReal.ofReal`; for a square this is exactly its
nonnegative extended-real value. -/
theorem exists_lintegral_multisetLogPotential_sq_closedBall_le
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : Multiset ℂ, s.card ≠ 0 →
      (∫⁻ z in Metric.closedBall (0 : ℂ) R,
          ENNReal.ofReal ((multisetLogPotential s z) ^ 2)) ≤
        ENNReal.ofReal (C * (1 + multisetSecondMoment s)) := by
  obtain ⟨C, hC, hreal⟩ :=
    exists_integral_multisetLogPotential_sq_closedBall_le R hR
  refine ⟨C, hC, fun s hs ↦ ?_⟩
  have hint := integrableOn_multisetLogPotential_sq R s
  have heq := ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun z ↦ sq_nonneg (multisetLogPotential s z))
  rw [← heq]
  exact ENNReal.ofReal_le_ofReal (hreal s hs)

/-- `lintegral` version for the difference of two empirical potentials. -/
theorem exists_lintegral_multisetLogPotential_sub_sq_closedBall_le
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : Multiset ℂ,
      s.card ≠ 0 → t.card ≠ 0 →
      (∫⁻ z in Metric.closedBall (0 : ℂ) R,
          ENNReal.ofReal
            ((multisetLogPotential s z - multisetLogPotential t z) ^ 2)) ≤
        ENNReal.ofReal
          (C * (1 + multisetSecondMoment s + multisetSecondMoment t)) := by
  obtain ⟨C, hC, hreal⟩ :=
    exists_integral_multisetLogPotential_sub_sq_closedBall_le R hR
  refine ⟨C, hC, fun s t hs ht ↦ ?_⟩
  have hint := integrableOn_multisetLogPotential_sub_sq R s t
  have heq := ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun z ↦
      sq_nonneg (multisetLogPotential s z - multisetLogPotential t z))
  rw [← heq]
  exact ENNReal.ofReal_le_ofReal (hreal s t hs ht)

/-! ## Spectral and normalized-matrix specializations -/

/-- For an eigenvalue multiset, `multisetLogPotential` is exactly the
real-valued empirical spectral test against the logarithmic kernel. -/
theorem multisetLogPotential_eigenvalueMultiset_eq_realEsdTest
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (z : ℂ) :
    multisetLogPotential (eigenvalueMultiset A) z =
      realEsdTest A (fun w ↦ Real.log ‖w - z‖) := by
  unfold multisetLogPotential realEsdTest realSpectralSum
  rw [multisetAverage_eq_map_sum_div_card, card_eigenvalueMultiset]

/-- The multiset second moment of a spectrum is the corresponding empirical
spectral test functional. -/
theorem multisetSecondMoment_eigenvalueMultiset_eq_realEsdTest
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    multisetSecondMoment (eigenvalueMultiset A) =
      realEsdTest A (fun w ↦ ‖w‖ ^ 2) := by
  unfold multisetSecondMoment realEsdTest realSpectralSum
  rw [multisetAverage_eq_map_sum_div_card, card_eigenvalueMultiset]

/-- Deterministic Weyl/Schur bridge from the second moment of the normalized
spectrum to the normalized Hilbert--Schmidt square. -/
theorem multisetSecondMoment_normalizedMatrix_le
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) :
    multisetSecondMoment (eigenvalueMultiset (normalizedMatrix A)) ≤
      hilbertSchmidtSq A / (Fintype.card n : ℝ) ^ 2 := by
  rw [multisetSecondMoment_eigenvalueMultiset_eq_realEsdTest]
  exact normalizedEsdSecondMoment_le_hilbertSchmidtSq A

/-- The same bridge in the `Fin (k+1)` notation used by the probabilistic
replacement-principle shell. -/
theorem multisetSecondMoment_normalizedMatrix_le_normalizedHilbertSchmidtSq
    {k : ℕ} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    multisetSecondMoment (eigenvalueMultiset (normalizedMatrix A)) ≤
      normalizedHilbertSchmidtSq A := by
  simpa [normalizedHilbertSchmidtSq] using
    (multisetSecondMoment_normalizedMatrix_le A)

/-- Deterministic extended-real moment bridge for a pair of normalized
matrices.  This is the exact right-hand side needed after applying the local
`L²` difference estimate. -/
theorem ennreal_one_add_normalizedSpectrumSecondMoments_le
    {k : ℕ}
    (A B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    ENNReal.ofReal
        (1 + multisetSecondMoment (eigenvalueMultiset (normalizedMatrix A)) +
          multisetSecondMoment (eigenvalueMultiset (normalizedMatrix B))) ≤
      ENNReal.ofReal
        (1 + normalizedHilbertSchmidtSq A + normalizedHilbertSchmidtSq B) := by
  apply ENNReal.ofReal_le_ofReal
  gcongr
  · exact multisetSecondMoment_normalizedMatrix_le_normalizedHilbertSchmidtSq A
  · exact multisetSecondMoment_normalizedMatrix_le_normalizedHilbertSchmidtSq B

/-- Tao--Vu (27), specialized to the empirical spectrum of a normalized
matrix.  The bound is now expressed solely through the matrix's normalized
Hilbert--Schmidt square. -/
theorem exists_integral_normalizedMatrixLogPotential_sq_closedBall_le
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {k : ℕ}
      (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
      (∫ z in Metric.closedBall (0 : ℂ) R,
          (multisetLogPotential
            (eigenvalueMultiset (normalizedMatrix A)) z) ^ 2) ≤
        C * (1 + normalizedHilbertSchmidtSq A) := by
  obtain ⟨C, hC, hmultiset⟩ :=
    exists_integral_multisetLogPotential_sq_closedBall_le R hR
  refine ⟨C, hC, fun {k} A ↦ ?_⟩
  have hcard : (eigenvalueMultiset (normalizedMatrix A)).card ≠ 0 := by
    rw [card_eigenvalueMultiset]
    simp
  calc
    (∫ z in Metric.closedBall (0 : ℂ) R,
        (multisetLogPotential
          (eigenvalueMultiset (normalizedMatrix A)) z) ^ 2) ≤
      C * (1 + multisetSecondMoment
        (eigenvalueMultiset (normalizedMatrix A))) :=
      hmultiset _ hcard
    _ ≤ C * (1 + normalizedHilbertSchmidtSq A) := by
      gcongr
      exact multisetSecondMoment_normalizedMatrix_le_normalizedHilbertSchmidtSq A

/-- Local `L²` bound for the difference of the empirical log potentials of
two normalized matrices, expressed through exactly the two normalized
Hilbert--Schmidt squares. -/
theorem exists_integral_normalizedMatrixLogPotential_sub_sq_closedBall_le
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {k : ℕ}
      (A B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
      (∫ z in Metric.closedBall (0 : ℂ) R,
          (multisetLogPotential (eigenvalueMultiset (normalizedMatrix A)) z -
            multisetLogPotential (eigenvalueMultiset (normalizedMatrix B)) z) ^ 2) ≤
        C * (1 + normalizedHilbertSchmidtSq A +
          normalizedHilbertSchmidtSq B) := by
  obtain ⟨C, hC, hmultiset⟩ :=
    exists_integral_multisetLogPotential_sub_sq_closedBall_le R hR
  refine ⟨C, hC, fun {k} A B ↦ ?_⟩
  have hcardA : (eigenvalueMultiset (normalizedMatrix A)).card ≠ 0 := by
    rw [card_eigenvalueMultiset]
    simp
  have hcardB : (eigenvalueMultiset (normalizedMatrix B)).card ≠ 0 := by
    rw [card_eigenvalueMultiset]
    simp
  calc
    (∫ z in Metric.closedBall (0 : ℂ) R,
        (multisetLogPotential (eigenvalueMultiset (normalizedMatrix A)) z -
          multisetLogPotential (eigenvalueMultiset (normalizedMatrix B)) z) ^ 2) ≤
      C * (1 + multisetSecondMoment
          (eigenvalueMultiset (normalizedMatrix A)) +
        multisetSecondMoment
          (eigenvalueMultiset (normalizedMatrix B))) :=
      hmultiset _ _ hcardA hcardB
    _ ≤ C * (1 + normalizedHilbertSchmidtSq A +
        normalizedHilbertSchmidtSq B) := by
      gcongr
      · exact multisetSecondMoment_normalizedMatrix_le_normalizedHilbertSchmidtSq A
      · exact multisetSecondMoment_normalizedMatrix_le_normalizedHilbertSchmidtSq B

/-- Extended-real version of the normalized-matrix difference estimate. -/
theorem exists_lintegral_normalizedMatrixLogPotential_sub_sq_closedBall_le
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {k : ℕ}
      (A B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
      (∫⁻ z in Metric.closedBall (0 : ℂ) R,
          ENNReal.ofReal
            ((multisetLogPotential (eigenvalueMultiset (normalizedMatrix A)) z -
              multisetLogPotential (eigenvalueMultiset (normalizedMatrix B)) z) ^ 2)) ≤
        ENNReal.ofReal
          (C * (1 + normalizedHilbertSchmidtSq A +
            normalizedHilbertSchmidtSq B)) := by
  obtain ⟨C, hC, hmultiset⟩ :=
    exists_lintegral_multisetLogPotential_sub_sq_closedBall_le R hR
  refine ⟨C, hC, fun {k} A B ↦ ?_⟩
  have hcardA : (eigenvalueMultiset (normalizedMatrix A)).card ≠ 0 := by
    rw [card_eigenvalueMultiset]
    simp
  have hcardB : (eigenvalueMultiset (normalizedMatrix B)).card ≠ 0 := by
    rw [card_eigenvalueMultiset]
    simp
  calc
    (∫⁻ z in Metric.closedBall (0 : ℂ) R,
        ENNReal.ofReal
          ((multisetLogPotential (eigenvalueMultiset (normalizedMatrix A)) z -
            multisetLogPotential (eigenvalueMultiset (normalizedMatrix B)) z) ^ 2)) ≤
      ENNReal.ofReal
        (C * (1 + multisetSecondMoment
            (eigenvalueMultiset (normalizedMatrix A)) +
          multisetSecondMoment
            (eigenvalueMultiset (normalizedMatrix B)))) :=
      hmultiset _ _ hcardA hcardB
    _ ≤ ENNReal.ofReal
        (C * (1 + normalizedHilbertSchmidtSq A +
          normalizedHilbertSchmidtSq B)) := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
      · exact multisetSecondMoment_normalizedMatrix_le_normalizedHilbertSchmidtSq A
      · exact multisetSecondMoment_normalizedMatrix_le_normalizedHilbertSchmidtSq B

end TaoVuReplacement

