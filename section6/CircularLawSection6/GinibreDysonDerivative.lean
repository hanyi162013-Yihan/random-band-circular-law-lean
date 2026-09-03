import CircularLawSection6.GinibreDysonEndpoints
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Differentiating the physical Dyson potential

The explicit height map is strictly increasing above the physical endpoint.
The previously constructed Dyson root is its inverse there.  The inverse
function theorem therefore proves the root's regularity, instead of taking
that regularity as an input.  The chain rule then identifies the derivative
of the candidate potential with the imaginary part of the Dyson transform.
-/

open Filter Topology MeasureTheory Set

noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace CircularLawSection6.GinibreDyson

/-- Derivative of the explicit height map. -/
def profileTSlope (r a : ℝ) : ℝ :=
  1 - (r ^ 2 - a ^ 2) / (a ^ 2 + r ^ 2) ^ 2

theorem hasStrictDerivAt_profileT {r a : ℝ} (h : a ^ 2 + r ^ 2 ≠ 0) :
    HasStrictDerivAt (profileT r) (profileTSlope r a) a := by
  have hq : HasStrictDerivAt (fun x : ℝ => x ^ 2 + r ^ 2) (2 * a) a := by
    simpa using ((hasStrictDerivAt_id a).pow 2).add_const (r ^ 2)
  have hv : HasStrictDerivAt (profileV r)
      ((r ^ 2 - a ^ 2) / (a ^ 2 + r ^ 2) ^ 2) a := by
    refine ((hasStrictDerivAt_id a).fun_div hq h).congr_deriv ?_
    dsimp
    ring
  exact (hasStrictDerivAt_id a).sub hv

theorem profileTSlope_pos {r a : ℝ} (h : 1 < a ^ 2 + r ^ 2) :
    0 < profileTSlope r a := by
  have hd : 0 < a ^ 2 + r ^ 2 := zero_lt_one.trans h
  have hprod := mul_pos (sub_pos.mpr h) hd
  have hnum : r ^ 2 - a ^ 2 < (a ^ 2 + r ^ 2) ^ 2 := by
    nlinarith only [hprod, sq_nonneg a]
  exact sub_pos.mpr ((div_lt_one (pow_pos hd 2)).2 hnum)

theorem dysonA_gt_endpointA (z : ℂ) {t : ℝ} (ht : 0 < t) :
    endpointA z < dysonA z t := by
  have ha := dysonA_pos z ht
  have hden := dysonA_sq_add_norm_sq_gt_one z ht
  have hmax : max (1 - ‖z‖ ^ 2) 0 < (dysonA z t) ^ 2 :=
    max_lt (by linarith) (sq_pos_of_pos ha)
  exact (Real.sqrt_lt_sqrt (le_max_right _ _) hmax).trans_eq (Real.sqrt_sq ha.le)

theorem den_gt_one_of_endpointA_lt (z : ℂ) {a : ℝ} (ha : endpointA z < a) :
    1 < a ^ 2 + ‖z‖ ^ 2 := by
  have hsquare : (endpointA z) ^ 2 < a ^ 2 :=
    pow_lt_pow_left₀ ha (endpointA_nonneg z) (by decide : (2 : ℕ) ≠ 0)
  linarith [endpointA_den_ge_one z]

theorem profileT_pos_of_endpointA_lt (z : ℂ) {a : ℝ} (ha : endpointA z < a) :
    0 < profileT ‖z‖ a :=
  sub_pos.mpr (div_lt_self ((endpointA_nonneg z).trans_lt ha)
    (den_gt_one_of_endpointA_lt z ha))

/-- The branch used by the actual Dyson root has no competing real inverse. -/
theorem strictMonoOn_profileT (z : ℂ) :
    StrictMonoOn (profileT ‖z‖) (Ioi (endpointA z)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi (endpointA z))
  · intro a ha
    have hden : a ^ 2 + ‖z‖ ^ 2 ≠ 0 :=
      (zero_lt_one.trans (den_gt_one_of_endpointA_lt z ha)).ne'
    exact (hasDerivAt_profileT hden).continuousAt.continuousWithinAt
  · intro a ha
    have ha' : endpointA z < a := by simpa only [interior_Ioi, mem_Ioi] using ha
    have hden := den_gt_one_of_endpointA_lt z ha'
    rw [(hasDerivAt_profileT (zero_lt_one.trans hden).ne').deriv]
    exact profileTSlope_pos hden

theorem dysonA_profileT (z : ℂ) {a : ℝ} (ha : endpointA z < a) :
    dysonA z (profileT ‖z‖ a) = a := by
  have ht := profileT_pos_of_endpointA_lt z ha
  apply (strictMonoOn_profileT z).injOn (dysonA_gt_endpointA z ht) ha
  exact profileT_dysonA z ht

/-- Strict differentiability is obtained from the local inverse theorem. -/
theorem hasStrictDerivAt_dysonA (z : ℂ) {t : ℝ} (ht : 0 < t) :
    HasStrictDerivAt (dysonA z) (profileTSlope ‖z‖ (dysonA z t))⁻¹ t := by
  have hden := dysonA_sq_add_norm_sq_gt_one z ht
  have hslope := profileTSlope_pos hden
  have hT := hasStrictDerivAt_profileT (zero_lt_one.trans hden).ne'
  have hleft : ∀ᶠ a in 𝓝 (dysonA z t), dysonA z (profileT ‖z‖ a) = a := by
    filter_upwards [Ioi_mem_nhds (dysonA_gt_endpointA z ht)] with a ha
    exact dysonA_profileT z ha
  have hinverse := hT.to_local_left_inverse hslope.ne' hleft
  simpa only [profileT_dysonA z ht] using hinverse

theorem continuousAt_dysonA (z : ℂ) {t : ℝ} (ht : 0 < t) : ContinuousAt (dysonA z) t :=
  (hasStrictDerivAt_dysonA z ht).hasDerivAt.continuousAt

theorem continuousAt_dysonV (z : ℂ) {t : ℝ} (ht : 0 < t) : ContinuousAt (dysonV z) t := by
  have h := (continuousAt_dysonA z ht).sub continuousAt_id
  simpa only [dysonA, add_sub_cancel_left] using h

theorem continuousOn_dysonV (z : ℂ) : ContinuousOn (dysonV z) (Ioi 0) :=
  fun _ ht => (continuousAt_dysonV z ht).continuousWithinAt

/-- The deterministic logarithmic primitive has the required physical derivative. -/
theorem hasDerivAt_dysonPotential (z : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (dysonPotential z) (dysonV z t) t := by
  unfold dysonPotential
  have hden := dysonA_sq_add_norm_sq_gt_one z ht
  have hslope := profileTSlope_pos hden
  have hF := hasDerivAt_profileF (zero_lt_one.trans hden).ne'
  have hA := (hasStrictDerivAt_dysonA z ht).hasDerivAt
  refine (hF.comp t hA).congr_deriv ?_
  change (profileV ‖z‖ (dysonA z t) * profileTSlope ‖z‖ (dysonA z t)) *
    (profileTSlope ‖z‖ (dysonA z t))⁻¹ = dysonV z t
  rw [mul_inv_cancel_right₀ hslope.ne', profileV_dysonA z ht]

theorem deriv_dysonPotential (z : ℂ) {t : ℝ} (ht : 0 < t) :
    deriv (dysonPotential z) t = dysonV z t := (hasDerivAt_dysonPotential z ht).deriv

theorem intervalIntegrable_dysonV (z : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (dysonV z) volume a b := by
  have hsub : uIcc a b ⊆ Ioi (0 : ℝ) := by
    intro t ht
    exact (lt_min_iff.mpr ⟨ha, hb⟩).trans_le ht.1
  exact ((continuousOn_dysonV z).mono hsub).intervalIntegrable

/-- Exact integration formula between any two positive heights. -/
theorem integral_dysonV_eq_sub (z : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in a..b, dysonV z t) = dysonPotential z b - dysonPotential z a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (intervalIntegrable_dysonV z ha hb)
  intro t ht
  exact hasDerivAt_dysonPotential z ((lt_min_iff.mpr ⟨ha, hb⟩).trans_le ht.1)

end CircularLawSection6.GinibreDyson
