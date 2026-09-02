import CircularLawSection6.SparseProfileGeometry
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # The literal limiting core and tail masses

The tail is identified with the integral outside the compact window, not
merely with an abstract error parameter. Strict positivity, monotonicity,
and the eventual variance window are derived from the profile assumptions.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace CircularLawSection6.NoncompactProfile

def limitingCoreMass (p : NoncompactProfile) (R : ℝ) : ℝ :=
  ∫ x in -R..R, p.f x

def limitingTailMass (p : NoncompactProfile) (R : ℝ) : ℝ :=
  ∫ x in {x : ℝ | R < |x|}, p.f x

theorem limitingCoreMass_eq_setIntegral (p : NoncompactProfile) {R : ℝ} (hR : 0 ≤ R) :
    p.limitingCoreMass R = ∫ x in Icc (-R) R, p.f x := by
  rw [limitingCoreMass, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (neg_le_self hR)]

theorem limitingCoreMass_add_limitingTailMass (p : NoncompactProfile)
    {R : ℝ} (hR : 0 ≤ R) : p.limitingCoreMass R + p.limitingTailMass R = 1 := by
  have hset : {x : ℝ | R < |x|} = (Icc (-R) R)ᶜ := by
    ext x
    simp only [mem_setOf_eq, mem_compl_iff, mem_Icc, ← abs_le, not_le]
  rw [p.limitingCoreMass_eq_setIntegral hR, limitingTailMass, hset,
    integral_add_compl measurableSet_Icc p.integrable, p.integral_one]

theorem limitingCoreMass_nonneg (p : NoncompactProfile) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ p.limitingCoreMass R :=
  intervalIntegral.integral_nonneg_of_forall (neg_le_self hR) (fun x => (p.positive x).le)

theorem limitingCoreMass_pos (p : NoncompactProfile) {R : ℝ} (hR : 0 < R) :
    0 < p.limitingCoreMass R :=
  intervalIntegral.intervalIntegral_pos_of_pos p.integrable.intervalIntegrable p.positive
    (by linarith)

theorem limitingTailMass_nonneg (p : NoncompactProfile) (R : ℝ) :
    0 ≤ p.limitingTailMass R := integral_nonneg (fun x => (p.positive x).le)

theorem limitingCoreMass_le_one (p : NoncompactProfile) {R : ℝ} (hR : 0 ≤ R) :
    p.limitingCoreMass R ≤ 1 := by
  have hm := p.limitingCoreMass_add_limitingTailMass hR
  have ht := p.limitingTailMass_nonneg R
  linarith

theorem limitingCoreMass_monotoneOn (p : NoncompactProfile) :
    MonotoneOn p.limitingCoreMass (Ici 0) := by
  intro R hR S _ hRS
  exact intervalIntegral.integral_mono_interval (neg_le_neg hRS)
    (neg_le_self hR) hRS (ae_of_all _ (fun x => (p.positive x).le))
    p.integrable.intervalIntegrable

theorem limitingTailMass_antitone (p : NoncompactProfile) :
    Antitone p.limitingTailMass := by
  intro R S hRS
  exact setIntegral_mono_set p.integrable.integrableOn
    (ae_of_all _ (fun x => (p.positive x).le))
    (Eventually.of_forall (fun x hx => lt_of_le_of_lt hRS hx))

theorem limitingTailMass_eq_one_sub (p : NoncompactProfile) {R : ℝ} (hR : 0 ≤ R) :
    p.limitingTailMass R = 1 - p.limitingCoreMass R := by
  have h := p.limitingCoreMass_add_limitingTailMass hR
  linarith

theorem limitingTailMass_integral_tendsto_zero (p : NoncompactProfile) :
    Tendsto (fun R : ℕ => p.limitingTailMass R) atTop (𝓝 0) := by
  simpa only [p.limitingTailMass_eq_one_sub (Nat.cast_nonneg _), limitingCoreMass] using
    p.limitingTailMass_tendsto_zero

theorem limitingCoreMass_eventually_half (p : NoncompactProfile) :
    ∀ᶠ R : ℕ in atTop, (1 / 2 : ℝ) ≤ p.limitingCoreMass R ∧ p.limitingCoreMass R ≤ 1 := by
  filter_upwards [p.limitingCoreMass_tendsto_one.eventually
    (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))] with R hR
  exact ⟨hR.le, p.limitingCoreMass_le_one (Nat.cast_nonneg R)⟩

theorem limitingCoreRadius_tendsto_one (p : NoncompactProfile) :
    Tendsto (fun R : ℕ => Real.sqrt (p.limitingCoreMass R)) atTop (𝓝 1) := by
  simpa only [Real.sqrt_one] using Real.continuous_sqrt.continuousAt.tendsto.comp
    p.limitingCoreMass_tendsto_one

end CircularLawSection6.NoncompactProfile
