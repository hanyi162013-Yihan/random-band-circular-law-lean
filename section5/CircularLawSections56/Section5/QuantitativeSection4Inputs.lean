import CircularLawSections56.Section5.LogarithmicSection4Bounds
import CircularLawSections56.Section5.Section4CompletedAssembly

/-! # Size-dependent finite Section 4 constants to the uniform Section 5 receiver

The inputs are exactly the finite raw seam and fiber-concentration estimates.
Uniformity for polynomial taper weights is a proved output of this adapter.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section
set_option maxHeartbeats 1200000
set_option autoImplicit false

namespace CircularLawSections56.Section5
open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

universe u
variable {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]

structure QuantitativeSection4PressureInput
    (μ : ∀ n, Measure (Ω n)) (active : ℕ → Bool) (d ell : ℕ → ℕ)
    (raw : ∀ n, Ω n → ℝ) (Y : ∀ n, ExteriorDegree (d n + 1) → Ω n → ℝ)
    (c₀ negative fiber : ℕ → ℝ) (z : ℂ) : Prop where
  seam_integrable : ∀ n, active n = true →
    Integrable (fun ω => |raw n ω - randomFiniteSignedMaxTri Y n ω|) (μ n)
  seam_bound : ∀ n, active n = true →
    (∫ ω, |raw n ω - randomFiniteSignedMaxTri Y n ω| ∂μ n) ≤
      paperIsolatedCoefficientLoss (d n) (c₀ n) + negative n + paperFreshPositiveBound (d n) z
  pressure_memLp : ∀ n, active n = true → ∀ r, MemLp (Y n r) 2 (μ n)
  pressure_bound : ∀ n, active n = true →
    (∫ ω, maxCenteredAbs (μ n) (Y n) ω ∂μ n) ≤
      Real.sqrt ((d n + 2 : ℝ) * 2 * (ell n : ℝ) * fiber n)

def logarithmicSection4Constant (A J V : ℝ) (z : ℂ) : ℝ :=
  6 * (A + 4 + J + uniformFreshPositiveConstant z) + Real.sqrt (54 * V)

theorem quantitativeSection4PressureInput_toCompleted
    (μ : ∀ n, Measure (Ω n)) (active : ℕ → Bool) (d ell scale W : ℕ → ℕ)
    (raw : ∀ n, Ω n → ℝ) (Y : ∀ n, ExteriorDegree (d n + 1) → Ω n → ℝ)
    (c₀ negative fiber : ℕ → ℝ) (z : ℂ) (A J V : ℝ)
    (hA : 0 ≤ A) (hJ : 0 ≤ J) (hV : 0 ≤ V)
    (hW : ∀ n, active n = true → 0 < W n)
    (hd : ∀ n, active n = true → d n + 1 = 2 * W n)
    (hell : ∀ n, active n = true → ell n ≤ scale n)
    (hc₀ : ∀ n, active n = true → 0 < c₀ n)
    (hc : ∀ n, active n = true → |Real.log (c₀ n)| ≤ A * dimensionLogScale (d n))
    (hnegative : ∀ n, active n = true →
      negative n ≤ J * (d n + 1 : ℝ) * dimensionLogScale (d n))
    (hfiber : ∀ n, active n = true → fiber n ≤ V * dimensionLogScale (d n) ^ 2)
    (h4 : QuantitativeSection4PressureInput μ active d ell raw Y c₀ negative fiber z) :
    CompletedSection4PressureInput μ active raw Y scale W (logarithmicSection4Constant A J V z) := by
  have hC : 0 ≤ 6 * (A + 4 + J + uniformFreshPositiveConstant z) := by
    unfold uniformFreshPositiveConstant
    positivity
  refine ⟨h4.seam_integrable, ?_, h4.pressure_memLp, ?_⟩
  · intro n hn
    have hlog : 0 ≤ paperLogEW W n := zero_le_one.trans
      (one_le_paperLogEW_of_bandwidth_pos W n (hW n hn))
    have hb := logarithmic_raw_seam_bound (d n) (W n) (hW n hn) (hd n hn)
      (c₀ n) A J (negative n) z (hc₀ n hn) hA hJ (hc n hn) (hnegative n hn)
    apply (h4.seam_bound n hn).trans (hb.trans ?_)
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (Real.sqrt_nonneg (54 * V)))
      (mul_nonneg (Nat.cast_nonneg _) hlog)
  · intro n hn
    have hlog : 0 ≤ paperLogEW W n := zero_le_one.trans
      (one_le_paperLogEW_of_bandwidth_pos W n (hW n hn))
    have hb := logarithmic_pressure_fluctuation_bound (d n) (W n) (ell n) (scale n)
      (hW n hn) (hd n hn) (hell n hn) (fiber n) V hV (hfiber n hn)
    apply (h4.pressure_bound n hn).trans (hb.trans ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (Real.sqrt_nonneg _)) hlog

abbrev RealQuantitativeSection4PressureInput
    (μ : ∀ n, Measure (Ω n)) (active : ℕ → Bool) (d ell : ℕ → ℕ)
    (raw : ∀ n, Ω n → ℝ) (Y : ∀ n, ExteriorDegree (d n + 1) → Ω n → ℝ)
    (c₀ : ℕ → ℝ) (L : ℝ) (z : ℂ) : Prop :=
  QuantitativeSection4PressureInput μ active d ell raw Y c₀
    (fun n => realFreshNegativeBound (d n) L)
    (fun n => realPaperPressureFiberL2Bound (d n) (c₀ n) L z (1 / 2)) z

abbrev ComplexQuantitativeSection4PressureInput
    (μ : ∀ n, Measure (Ω n)) (active : ℕ → Bool) (d ell : ℕ → ℕ)
    (raw : ∀ n, Ω n → ℝ) (Y : ∀ n, ExteriorDegree (d n + 1) → Ω n → ℝ)
    (c₀ : ℕ → ℝ) (L : ℝ) (z : ℂ) : Prop :=
  QuantitativeSection4PressureInput μ active d ell raw Y c₀
    (fun n => complexFreshNegativeBound (d n) L)
    (fun n => complexPaperPressureFiberL2Bound (d n) (c₀ n) L z) z

def realLogarithmicSection4Constant (A L : ℝ) (z : ℂ) : ℝ :=
  logarithmicSection4Constant A (realFreshLogConstant L) (logarithmicFiberConstant A (4 * L) z) z

def complexLogarithmicSection4Constant (A L : ℝ) (z : ℂ) : ℝ :=
  logarithmicSection4Constant A (uniformFreshNegativeConstant L)
    (logarithmicFiberConstant A (max 1 (Real.pi * L)) z) z

theorem RealQuantitativeSection4PressureInput.toCompleted
    {μ : ∀ n, Measure (Ω n)} {active : ℕ → Bool} {d ell : ℕ → ℕ}
    {raw : ∀ n, Ω n → ℝ} {Y : ∀ n, ExteriorDegree (d n + 1) → Ω n → ℝ}
    {c₀ : ℕ → ℝ} {L : ℝ} {z : ℂ}
    (h4 : RealQuantitativeSection4PressureInput μ active d ell raw Y c₀ L z)
    (scale W : ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hW : ∀ n, active n = true → 0 < W n)
    (hd : ∀ n, active n = true → d n + 1 = 2 * W n)
    (hell : ∀ n, active n = true → ell n ≤ scale n)
    (hc₀ : ∀ n, active n = true → 0 < c₀ n)
    (hc : ∀ n, active n = true → |Real.log (c₀ n)| ≤ A * dimensionLogScale (d n)) :
    CompletedSection4PressureInput μ active raw Y scale W (realLogarithmicSection4Constant A L z) :=
  quantitativeSection4PressureInput_toCompleted μ active d ell scale W raw Y c₀ _ _ z A _ _
    hA (realFreshLogConstant_nonneg L) (logarithmicFiberConstant_nonneg _ _ _)
    hW hd hell hc₀ hc (fun n _ => realFreshNegativeBound_le_uniform (d n) L)
    (fun n hn => realPaperPressureFiberL2Bound_le_logarithmic (d n) (c₀ n) A L z
      (hc₀ n hn) hA (hc n hn)) h4

theorem ComplexQuantitativeSection4PressureInput.toCompleted
    {μ : ∀ n, Measure (Ω n)} {active : ℕ → Bool} {d ell : ℕ → ℕ}
    {raw : ∀ n, Ω n → ℝ} {Y : ∀ n, ExteriorDegree (d n + 1) → Ω n → ℝ}
    {c₀ : ℕ → ℝ} {L : ℝ} {z : ℂ}
    (h4 : ComplexQuantitativeSection4PressureInput μ active d ell raw Y c₀ L z)
    (scale W : ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hW : ∀ n, active n = true → 0 < W n)
    (hd : ∀ n, active n = true → d n + 1 = 2 * W n)
    (hell : ∀ n, active n = true → ell n ≤ scale n)
    (hc₀ : ∀ n, active n = true → 0 < c₀ n)
    (hc : ∀ n, active n = true → |Real.log (c₀ n)| ≤ A * dimensionLogScale (d n)) :
    CompletedSection4PressureInput μ active raw Y scale W (complexLogarithmicSection4Constant A L z) :=
  quantitativeSection4PressureInput_toCompleted μ active d ell scale W raw Y c₀ _ _ z A _ _
    hA (by unfold uniformFreshNegativeConstant; linarith [Real.log_nonneg (le_max_left 1 (Real.pi * L))])
    (logarithmicFiberConstant_nonneg _ _ _) hW hd hell hc₀ hc
    (fun n _ => complexFreshNegativeBound_le_uniform (d n) L)
    (fun n hn => complexPaperPressureFiberL2Bound_le_logarithmic (d n) (c₀ n) A L z
      (hc₀ n hn) hA (hc n hn)) h4

end CircularLawSections56.Section5
