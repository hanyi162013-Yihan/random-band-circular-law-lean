import CircularLawSection6.GinibreDysonImaginary
import ShortRingAnchor.SourceStatement
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! # Endpoints of the imaginary-axis Dyson primitive

The physical root is controlled by its algebraic equation, without an
assumption of continuity or differentiability in `t`.  A cubic gap estimate
handles the interior, exterior, and boundary of the unit disk together.
The resulting deterministic primitive has the circular logarithmic potential
at height zero and agrees asymptotically with `log t` at infinity.

These deterministic endpoints do not assert random log-potential convergence.
-/

open Filter Topology

noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace CircularLawSection6.GinibreDyson

/-- The nonnegative endpoint of the physical auxiliary parameter. -/
def endpointA (z : ℂ) : ℝ := Real.sqrt (max (1 - ‖z‖ ^ 2) 0)

/-- The explicit candidate logarithmic potential at positive height. -/
def dysonPotential (z : ℂ) (t : ℝ) : ℝ := profileF ‖z‖ (dysonA z t)

theorem endpointA_nonneg (z : ℂ) : 0 ≤ endpointA z := Real.sqrt_nonneg _

theorem endpointA_sq (z : ℂ) : (endpointA z) ^ 2 = max (1 - ‖z‖ ^ 2) 0 :=
  Real.sq_sqrt (le_max_right _ _)

theorem endpointA_den_ge_one (z : ℂ) : 1 ≤ (endpointA z) ^ 2 + ‖z‖ ^ 2 := by
  rw [endpointA_sq]
  have h := le_max_left (1 - ‖z‖ ^ 2) (0 : ℝ)
  linarith

theorem dysonA_le_t_add_one (z : ℂ) {t : ℝ} (ht : 0 < t) : dysonA z t ≤ t + 1 :=
  add_le_add le_rfl (dysonV_le_one z ht)

theorem endpointA_le_dysonA (z : ℂ) {t : ℝ} (ht : 0 < t) : endpointA z ≤ dysonA z t := by
  have ha := dysonA_pos z ht
  have hden := dysonA_sq_add_norm_sq_gt_one z ht
  have hmax : max (1 - ‖z‖ ^ 2) 0 ≤ (dysonA z t) ^ 2 :=
    max_le (by linarith) (sq_nonneg _)
  exact (Real.sqrt_le_sqrt hmax).trans_eq (Real.sqrt_sq ha.le)

/-- Cleared real Dyson equation, in the form useful for endpoint estimates. -/
theorem dysonA_mul_den_sub_one (z : ℂ) {t : ℝ} (ht : 0 < t) :
    dysonA z t * ((dysonA z t) ^ 2 + ‖z‖ ^ 2 - 1) =
      t * ((dysonA z t) ^ 2 + ‖z‖ ^ 2) := by
  have ha := dysonA_pos z ht
  have hden : 0 < (dysonA z t) ^ 2 + ‖z‖ ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg _)
  have hmul := (eq_div_iff hden.ne').1 (dysonV_eq_div z ht)
  unfold dysonA at hmul ⊢
  nlinarith only [hmul]

/-- Uniform algebraic gap estimate, including the critical radius `‖z‖ = 1`. -/
theorem dysonA_gap_cube_le (z : ℂ) {t : ℝ} (ht : 0 < t) :
    (dysonA z t - endpointA z) ^ 3 ≤ t * ((t + 1) ^ 2 + ‖z‖ ^ 2) := by
  have ha := dysonA_pos z ht
  have hb := endpointA_nonneg z
  have hba := endpointA_le_dysonA z ht
  have hgap : 0 ≤ dysonA z t - endpointA z := sub_nonneg.mpr hba
  have hlin : 0 ≤ 3 * dysonA z t - endpointA z := by linarith
  have hk : 0 ≤ ‖z‖ ^ 2 - 1 + (endpointA z) ^ 2 := by
    linarith [endpointA_den_ge_one z]
  have hfirst := mul_nonneg ha.le hk
  have hsecond := mul_nonneg (mul_nonneg hb hgap) hlin
  have hpoly := dysonA_mul_den_sub_one z ht
  have hbound : (dysonA z t - endpointA z) ^ 3 ≤
      t * ((dysonA z t) ^ 2 + ‖z‖ ^ 2) := by
    nlinarith only [hfirst, hsecond, hpoly]
  have hsquare := pow_le_pow_left₀ ha.le (dysonA_le_t_add_one z ht) 2
  exact hbound.trans (mul_le_mul_of_nonneg_left (add_le_add hsquare le_rfl) ht.le)

private theorem tendsto_zero_of_nonneg_cube_le {α : Type*} {l : Filter α}
    {f g : α → ℝ} (hf : ∀ᶠ x in l, 0 ≤ f x)
    (hfg : ∀ᶠ x in l, (f x) ^ 3 ≤ g x) (hg : Tendsto g l (𝓝 0)) :
    Tendsto f l (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    filter_upwards [hf] with x hx
    exact hb.trans_le hx
  · intro b hb
    filter_upwards [hfg, hg.eventually (gt_mem_nhds (pow_pos hb 3))] with x hx hsmall
    by_contra hnot
    have hpow := pow_le_pow_left₀ hb.le (le_of_not_gt hnot) 3
    exact (not_lt_of_ge (hpow.trans hx)) hsmall

/-- No parameter-continuity assumption is needed to determine the height-zero root. -/
theorem tendsto_dysonA_nhdsGT_zero (z : ℂ) :
    Tendsto (dysonA z) (𝓝[>] (0 : ℝ)) (𝓝 (endpointA z)) := by
  have ht0 : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hbound : Tendsto (fun t : ℝ => t * ((t + 1) ^ 2 + ‖z‖ ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ht0.mul (((ht0.add_const 1).pow 2).add_const (‖z‖ ^ 2))
  have hgap : Tendsto (fun t => dysonA z t - endpointA z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_zero_of_nonneg_cube_le (g := fun t => t * ((t + 1) ^ 2 + ‖z‖ ^ 2))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_nonneg.mpr (endpointA_le_dysonA z ht)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact dysonA_gap_cube_le z ht
    · exact hbound
  simpa using hgap.add_const (endpointA z)

/-- Evaluation of the endpoint, with exactly the manuscript's two disk branches. -/
theorem profileF_endpointA (z : ℂ) :
    profileF ‖z‖ (endpointA z) = ShortRingAnchor.circularLogPotential z := by
  by_cases hz : ‖z‖ ≤ 1
  · have hzsq : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    have hbsq : (endpointA z) ^ 2 = 1 - ‖z‖ ^ 2 := by
      rw [endpointA_sq, max_eq_left (sub_nonneg.mpr hzsq)]
    have hden : (endpointA z) ^ 2 + ‖z‖ ^ 2 = 1 := by linarith
    rw [ShortRingAnchor.circularLogPotential_of_norm_le hz]
    unfold profileF profileV
    rw [hden, Real.log_one, div_one, hbsq]
    ring
  · have hr : 1 < ‖z‖ := lt_of_not_ge hz
    have hr2 : 1 < ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hb : endpointA z = 0 := by
      unfold endpointA
      rw [max_eq_right (by linarith : 1 - ‖z‖ ^ 2 ≤ 0), Real.sqrt_zero]
    rw [ShortRingAnchor.circularLogPotential_of_one_lt_norm hr]
    simp only [profileF, profileV, hb, zero_pow (by decide : (2 : ℕ) ≠ 0),
      zero_add, zero_div, mul_zero, sub_zero]
    rw [Real.log_pow]
    ring

theorem tendsto_dysonPotential_nhdsGT_zero (z : ℂ) :
    Tendsto (dysonPotential z) (𝓝[>] (0 : ℝ))
      (𝓝 (ShortRingAnchor.circularLogPotential z)) := by
  unfold dysonPotential
  have hden : (endpointA z) ^ 2 + ‖z‖ ^ 2 ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (endpointA_den_ge_one z)).ne'
  have hF := (hasDerivAt_profileF hden).continuousAt.tendsto.comp
    (tendsto_dysonA_nhdsGT_zero z)
  simpa only [Function.comp_def, profileF_endpointA] using hF

theorem profileV_dysonA (z : ℂ) {t : ℝ} (ht : 0 < t) :
    profileV ‖z‖ (dysonA z t) = dysonV z t := (dysonV_eq_div z ht).symm

theorem dysonV_le_one_div (z : ℂ) {t : ℝ} (ht : 0 < t) : dysonV z t ≤ 1 / t := by
  have ha := dysonA_pos z ht
  have hta : t ≤ dysonA z t := by
    unfold dysonA
    linarith [dysonV_pos z ht]
  calc
    dysonV z t = dysonA z t / ((dysonA z t) ^ 2 + ‖z‖ ^ 2) := dysonV_eq_div z ht
    _ ≤ dysonA z t / (dysonA z t) ^ 2 :=
      div_le_div_of_nonneg_left ha.le (sq_pos_of_pos ha) (le_add_of_nonneg_right (sq_nonneg _))
    _ = 1 / dysonA z t := by field_simp [ha.ne']
    _ ≤ 1 / t := one_div_le_one_div_of_le ht hta

theorem tendsto_dysonV_atTop (z : ℂ) : Tendsto (dysonV z) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun t : ℝ => 1 / t)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (dysonV_pos z ht).le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact dysonV_le_one_div z ht
  · exact tendsto_const_nhds.div_atTop tendsto_id

theorem tendsto_dysonA_div_atTop (z : ℂ) :
    Tendsto (fun t : ℝ => dysonA z t / t) atTop (𝓝 1) := by
  have hv0 : ∀ᶠ t in atTop, 0 ≤ dysonV z t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (dysonV_pos z ht).le
  have hv1 : ∀ᶠ t in atTop, dysonV z t ≤ 1 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact dysonV_le_one z ht
  have hratio : Tendsto (fun t : ℝ => dysonV z t / t) atTop (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero hv0 hv1 tendsto_id
  have hsum : Tendsto (fun t : ℝ => 1 + dysonV z t / t) atTop (𝓝 1) := by
    simpa using hratio.const_add 1
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [dysonA, add_div, div_self ht.ne']

/-- Renormalization isolates a logarithm whose argument tends to one. -/
theorem profileF_sub_log_eq {r a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    profileF r a - Real.log t =
      (1 / 2 : ℝ) * Real.log ((a / t) ^ 2 + (r / t) ^ 2) -
        (1 / 2 : ℝ) * (profileV r a) ^ 2 := by
  have hden : 0 < a ^ 2 + r ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg r)
  have hratio : (a / t) ^ 2 + (r / t) ^ 2 = (a ^ 2 + r ^ 2) / t ^ 2 := by
    rw [div_pow, div_pow, ← add_div]
  unfold profileF
  rw [hratio, Real.log_div hden.ne' (pow_ne_zero 2 ht.ne'), Real.log_pow]
  ring

theorem tendsto_dysonPotential_sub_log_atTop (z : ℂ) :
    Tendsto (fun t => dysonPotential z t - Real.log t) atTop (𝓝 0) := by
  have hratio := tendsto_dysonA_div_atTop z
  have hr : Tendsto (fun t : ℝ => ‖z‖ / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hden : Tendsto (fun t : ℝ => (dysonA z t / t) ^ 2 + (‖z‖ / t) ^ 2)
      atTop (𝓝 1) := by
    simpa using (hratio.pow 2).add (hr.pow 2)
  have hlim : Tendsto
      (fun t : ℝ => (1 / 2 : ℝ) * Real.log ((dysonA z t / t) ^ 2 + (‖z‖ / t) ^ 2) -
        (1 / 2 : ℝ) * (dysonV z t) ^ 2) atTop (𝓝 0) := by
    simpa using ((hden.log one_ne_zero).const_mul (1 / 2 : ℝ)).sub
      (((tendsto_dysonV_atTop z).pow 2).const_mul (1 / 2 : ℝ))
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [dysonPotential, profileF_sub_log_eq (dysonA_pos z ht) ht, profileV_dysonA z ht]

end CircularLawSection6.GinibreDyson
