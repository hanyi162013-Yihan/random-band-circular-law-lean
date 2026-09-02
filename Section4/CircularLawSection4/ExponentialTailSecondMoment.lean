import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Exponential tails imply square integrability

This file gives a reusable layer-cake closure for a nonnegative random
variable with an exponential upper tail.  The final constant is deliberately
slightly loose: if

`P(Z > t) ≤ A exp (-q t)` with `A ≥ 0` and `q > 0`,

then `Z ∈ L²` and

`E[Z²] ≤ 4 ((log (max 1 A) + 1) / q)²`.
-/

open scoped ENNReal MeasureTheory
open Set MeasureTheory Filter Measure

namespace CircularLawSection4

private theorem intervalIntegral_two_mul (z : ℝ) :
    (∫ t : ℝ in 0..z, 2 * t) = z ^ 2 := by
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

private theorem integrableOn_two_mul_exp_neg_mul_Ioi
    {q : ℝ} (hq : 0 < q) :
    IntegrableOn (fun t : ℝ => 2 * t * Real.exp (-(q * t))) (Ioi 0) := by
  have hbase :
      IntegrableOn (fun x : ℝ => Real.exp (-x) * x) (Ioi 0) := by
    convert (Real.GammaIntegral_convergent (s := (2 : ℝ)) (by norm_num)) using 1
    funext x
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  have hcomp :
      IntegrableOn (fun t : ℝ => Real.exp (-(q * t)) * (q * t)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x) 0 hq).2
    simpa using hbase
  have hscaled := hcomp.const_mul (2 / q)
  apply hscaled.congr
  filter_upwards with t
  change (2 / q) * (Real.exp (-(q * t)) * (q * t)) =
    2 * t * Real.exp (-(q * t))
  field_simp [ne_of_gt hq]

private theorem integral_two_mul_exp_neg_mul_Ioi
    {q : ℝ} (hq : 0 < q) :
    (∫ t : ℝ in Ioi 0, 2 * t * Real.exp (-(q * t))) = 2 / q ^ 2 := by
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := q) (by norm_num) hq
  have hgamma' :
      (∫ t : ℝ in Ioi 0, t * Real.exp (-(q * t))) = (1 / q) ^ 2 := by
    calc
      (∫ t : ℝ in Ioi 0, t * Real.exp (-(q * t))) =
          ∫ t : ℝ in Ioi 0,
            t ^ ((2 : ℝ) - 1) * Real.exp (-(q * t)) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro t _
              dsimp only
              rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
      _ = (1 / q) ^ (2 : ℝ) * Real.Gamma 2 := hgamma
      _ = (1 / q) ^ 2 := by norm_num
  calc
    (∫ t : ℝ in Ioi 0, 2 * t * Real.exp (-(q * t))) =
        ∫ t : ℝ in Ioi 0, 2 * (t * Real.exp (-(q * t))) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t _
          ring
    _ = 2 * ∫ t : ℝ in Ioi 0, t * Real.exp (-(q * t)) := by
          rw [integral_const_mul]
    _ = 2 * (1 / q) ^ 2 := by rw [hgamma']
    _ = 2 / q ^ 2 := by
          field_simp [ne_of_gt hq]

/-- Unit-prefactor form of the second-moment layer-cake estimate. -/
theorem memLp_two_and_integral_sq_le_of_unit_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (q : ℝ) (hq : 0 < q)
    (htail : ∀ t : ℝ, 0 < t →
      μ {ω | t < Z ω} ≤ ENNReal.ofReal (Real.exp (-(q * t)))) :
    MemLp Z 2 μ ∧ ∫ ω, Z ω ^ 2 ∂μ ≤ 2 / q ^ 2 := by
  have hnn : 0 ≤ᵐ[μ] Z := ae_of_all μ hZ0
  have hsqnn : 0 ≤ᵐ[μ] fun ω => Z ω ^ 2 :=
    ae_of_all μ fun ω => sq_nonneg (Z ω)
  have hweightInt :
      IntegrableOn (fun t : ℝ => 2 * t * Real.exp (-(q * t))) (Ioi 0) :=
    integrableOn_two_mul_exp_neg_mul_Ioi hq
  have hlayer :
      (∫⁻ ω, ENNReal.ofReal (Z ω ^ 2) ∂μ) =
        ∫⁻ t : ℝ in Ioi 0, μ {ω | t < Z ω} * ENNReal.ofReal (2 * t) := by
    have h := lintegral_comp_eq_lintegral_meas_lt_mul μ hnn hZ.aemeasurable
      (g := fun t : ℝ => 2 * t)
      (fun _ _ => by
        have hc : Continuous (fun t : ℝ => 2 * t) := by fun_prop
        exact hc.intervalIntegrable (μ := volume) _ _)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg zero_le_two ht.le)
    simpa only [intervalIntegral_two_mul] using h
  have htailIntegral :
      (∫⁻ t : ℝ in Ioi 0, μ {ω | t < Z ω} * ENNReal.ofReal (2 * t)) ≤
        ENNReal.ofReal (2 / q ^ 2) := by
    calc
      (∫⁻ t : ℝ in Ioi 0, μ {ω | t < Z ω} * ENNReal.ofReal (2 * t)) ≤
          ∫⁻ t : ℝ in Ioi 0,
            ENNReal.ofReal (Real.exp (-(q * t))) * ENNReal.ofReal (2 * t) := by
              apply setLIntegral_mono
              · fun_prop
              · intro t ht
                exact mul_le_mul_of_nonneg_right (htail t ht) (by positivity)
      _ = ∫⁻ t : ℝ in Ioi 0,
            ENNReal.ofReal (2 * t * Real.exp (-(q * t))) := by
              apply setLIntegral_congr_fun measurableSet_Ioi
              intro t ht
              change ENNReal.ofReal (Real.exp (-(q * t))) * ENNReal.ofReal (2 * t) =
                ENNReal.ofReal (2 * t * Real.exp (-(q * t)))
              rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
              congr 1
              ring
      _ = ENNReal.ofReal
            (∫ t : ℝ in Ioi 0, 2 * t * Real.exp (-(q * t))) := by
              rw [ofReal_integral_eq_lintegral_ofReal hweightInt]
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              exact mul_nonneg (mul_nonneg zero_le_two ht.le) (Real.exp_pos _).le
      _ = ENNReal.ofReal (2 / q ^ 2) := by
              rw [integral_two_mul_exp_neg_mul_Ioi hq]
  have hlin :
      (∫⁻ ω, ENNReal.ofReal (Z ω ^ 2) ∂μ) ≤
        ENNReal.ofReal (2 / q ^ 2) := hlayer.trans_le htailIntegral
  have hZsqInt : Integrable (fun ω => Z ω ^ 2) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (by fun_prop) hsqnn).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin)
  refine ⟨(memLp_two_iff_integrable_sq hZ.aestronglyMeasurable).2 hZsqInt, ?_⟩
  have hR : 0 ≤ 2 / q ^ 2 := by positivity
  apply (ENNReal.ofReal_le_ofReal_iff hR).mp
  rw [ofReal_integral_eq_lintegral_ofReal hZsqInt hsqnn]
  exact hlin

/-- Exponential tails with an arbitrary nonnegative prefactor imply `L²`,
with an explicit logarithmic-size second-moment bound. -/
theorem memLp_two_and_integral_sq_le_of_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (A q : ℝ) (_hA : 0 ≤ A) (hq : 0 < q)
    (htail : ∀ t : ℝ, 0 < t →
      μ {ω | t < Z ω} ≤ ENNReal.ofReal (A * Real.exp (-(q * t)))) :
    MemLp Z 2 μ ∧
      ∫ ω, Z ω ^ 2 ∂μ ≤
        4 * ((Real.log (max 1 A) + 1) / q) ^ 2 := by
  let B : ℝ := max 1 A
  let c : ℝ := Real.log B / q
  let Y : Ω → ℝ := fun ω => max 0 (Z ω - c)
  have hB1 : 1 ≤ B := by simp [B]
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hc : 0 ≤ c := div_nonneg hlogB hq.le
  have hqc : (-q) * c = -Real.log B := by
    dsimp [c]
    field_simp [ne_of_gt hq]
  have hexp : Real.exp ((-q) * c) = B⁻¹ := by
    rw [hqc, Real.exp_neg, Real.exp_log hB]
  have hAB : A * B⁻¹ ≤ 1 := by
    calc
      A * B⁻¹ ≤ B * B⁻¹ :=
        mul_le_mul_of_nonneg_right (le_max_right 1 A) (inv_nonneg.mpr hB.le)
      _ = 1 := mul_inv_cancel₀ hB.ne'
  have hY : Measurable Y := by
    dsimp [Y]
    fun_prop
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => le_max_left _ _
  have hYtail : ∀ t : ℝ, 0 < t →
      μ {ω | t < Y ω} ≤ ENNReal.ofReal (Real.exp (-(q * t))) := by
    intro t ht
    have hsubset : {ω | t < Y ω} ⊆ {ω | c + t < Z ω} := by
      intro ω hω
      change t < max 0 (Z ω - c) at hω
      rcases (lt_max_iff.mp hω) with hzero | hdiff
      · exact (not_lt_of_ge ht.le hzero).elim
      · change c + t < Z ω
        linarith
    calc
      μ {ω | t < Y ω} ≤ μ {ω | c + t < Z ω} := measure_mono hsubset
      _ ≤ ENNReal.ofReal (A * Real.exp (-(q * (c + t)))) :=
        htail (c + t) (by positivity)
      _ ≤ ENNReal.ofReal (Real.exp (-(q * t))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [show -(q * (c + t)) = (-q) * c + -(q * t) by ring,
          Real.exp_add, hexp]
        calc
          A * (B⁻¹ * Real.exp (-(q * t))) =
              (A * B⁻¹) * Real.exp (-(q * t)) := by ring
          _ ≤ 1 * Real.exp (-(q * t)) :=
            mul_le_mul_of_nonneg_right hAB (Real.exp_pos _).le
          _ = Real.exp (-(q * t)) := one_mul _
  obtain ⟨hYL2, hYsq⟩ :=
    memLp_two_and_integral_sq_le_of_unit_exponential_tail
      μ Y hY hY0 q hq hYtail
  have hYsqInt : Integrable (fun ω => Y ω ^ 2) μ := hYL2.integrable_sq
  have hpoint : ∀ ω, Z ω ^ 2 ≤ 2 * c ^ 2 + 2 * Y ω ^ 2 := by
    intro ω
    have hYlower : Z ω - c ≤ Y ω := le_max_right _ _
    have hZupper : Z ω ≤ c + Y ω := by linarith
    nlinarith [hZ0 ω, hc, hY0 ω, sq_nonneg (c - Y ω)]
  have hconstInt : Integrable (fun _ : Ω => 2 * c ^ 2) μ := integrable_const _
  have hdomInt : Integrable (fun ω => 2 * c ^ 2 + 2 * Y ω ^ 2) μ :=
    hconstInt.add (hYsqInt.const_mul 2)
  have hZsqInt : Integrable (fun ω => Z ω ^ 2) μ := by
    apply hdomInt.mono' (by fun_prop)
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Z ω))]
    exact hpoint ω
  refine ⟨(memLp_two_iff_integrable_sq hZ.aestronglyMeasurable).2 hZsqInt, ?_⟩
  calc
    (∫ ω, Z ω ^ 2 ∂μ) ≤
        ∫ ω, (2 * c ^ 2 + 2 * Y ω ^ 2) ∂μ :=
      integral_mono hZsqInt hdomInt hpoint
    _ = 2 * c ^ 2 + 2 * ∫ ω, Y ω ^ 2 ∂μ := by
      rw [integral_add hconstInt (hYsqInt.const_mul 2), integral_const,
        integral_const_mul]
      simp
    _ ≤ 2 * c ^ 2 + 2 * (2 / q ^ 2) := by gcongr
    _ ≤ 4 * ((Real.log (max 1 A) + 1) / q) ^ 2 := by
      dsimp [c, B]
      field_simp [ne_of_gt hq]
      nlinarith

end CircularLawSection4
