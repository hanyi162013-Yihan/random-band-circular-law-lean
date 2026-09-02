import CircularLawSection4.LogDeviationSecondMoment
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Positive logarithmic moments from a scaled second moment

The positive half of the operator-affine logarithm reduces to a random sum
`S`.  The manuscript scales this sum by the number of coordinates, applies
Cauchy--Schwarz, and uses `log (1+x) ≤ x`.  This module records that closing
argument with explicit constants.
-/

open scoped BigOperators MeasureTheory
open MeasureTheory

namespace CircularLawSection4

/-- Elementary pointwise estimate behind the positive logarithmic tail.
The scale is allowed to be any real number at least one. -/
theorem positiveLogSquare_le_scaledSquare
    {S z scale : ℝ} (hS : 0 ≤ S) (hz : 0 ≤ z) (hscale : 1 ≤ scale) :
    (max 0 (Real.log (S + z))) ^ 2 ≤
      3 * (Real.log scale) ^ 2 +
        3 * (S / scale) ^ 2 + 3 * z ^ 2 := by
  have hscale0 : 0 < scale := zero_lt_one.trans_le hscale
  have hlogscale : 0 ≤ Real.log scale := Real.log_nonneg hscale
  by_cases hzero : S + z = 0
  · have hS0 : S = 0 := by nlinarith
    have hz0 : z = 0 := by nlinarith
    simp [hS0, hz0, hlogscale]
  have hsum : 0 < S + z := lt_of_le_of_ne (add_nonneg hS hz) (Ne.symm hzero)
  let q : ℝ := S / scale + z
  have hq : 0 ≤ q := add_nonneg (div_nonneg hS hscale0.le) hz
  have hfactor : 0 < 1 + q := by positivity
  have hprod : 0 < scale * (1 + q) := mul_pos hscale0 hfactor
  have hle : S + z ≤ scale * (1 + q) := by
    have hid : scale * (1 + q) = scale + S + scale * z := by
      dsimp [q]
      field_simp [hscale0.ne']
      ring
    rw [hid]
    nlinarith [mul_nonneg (sub_nonneg.mpr hscale) hz]
  have hlog : Real.log (S + z) ≤ Real.log scale + Real.log (1 + q) := by
    have := Real.log_le_log hsum hle
    rw [Real.log_mul hscale0.ne' hfactor.ne'] at this
    exact this
  have hlogfactor : Real.log (1 + q) ≤ q := by
    have := Real.log_le_sub_one_of_pos hfactor
    simpa [q] using this
  let t : ℝ := max 0 (Real.log (S + z))
  have ht0 : 0 ≤ t := le_max_left _ _
  have ht : t ≤ Real.log scale + S / scale + z := by
    apply max_le
    · positivity
    · dsimp [q] at hlogfactor
      linarith
  have hscaled : 0 ≤ S / scale := div_nonneg hS hscale0.le
  have hsq :
      t ^ 2 ≤ (Real.log scale + S / scale + z) ^ 2 := by
    nlinarith [sq_nonneg ((Real.log scale + S / scale + z) - t)]
  have hthree :
      (Real.log scale + S / scale + z) ^ 2 ≤
        3 * (Real.log scale) ^ 2 +
          3 * (S / scale) ^ 2 + 3 * z ^ 2 := by
    nlinarith [sq_nonneg (Real.log scale - S / scale),
      sq_nonneg (Real.log scale - z), sq_nonneg (S / scale - z)]
  exact hsq.trans hthree

/-- Measure-theoretic closure: a second-moment bound for `S / scale`
implies an explicit second-moment bound for the positive logarithm. -/
theorem integrable_and_integral_positiveLogSquare_le_of_scaledSecondMoment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (S : Ω → ℝ) (hSmeas : Measurable S) (hS0 : ∀ ω, 0 ≤ S ω)
    (z scale V : ℝ) (hz : 0 ≤ z) (hscale : 1 ≤ scale)
    (hscaledInt : Integrable (fun ω => (S ω / scale) ^ 2) μ)
    (hscaled : ∫ ω, (S ω / scale) ^ 2 ∂μ ≤ V) :
    Integrable (fun ω => (max 0 (Real.log (S ω + z))) ^ 2) μ ∧
      ∫ ω, (max 0 (Real.log (S ω + z))) ^ 2 ∂μ ≤
        3 * (Real.log scale) ^ 2 + 3 * V + 3 * z ^ 2 := by
  let Z : Ω → ℝ := fun ω => (max 0 (Real.log (S ω + z))) ^ 2
  let D : Ω → ℝ := fun ω =>
    3 * (Real.log scale) ^ 2 + 3 * (S ω / scale) ^ 2 + 3 * z ^ 2
  have hDInt : Integrable D μ := by
    exact ((integrable_const (3 * (Real.log scale) ^ 2)).add
      (hscaledInt.const_mul 3)).add (integrable_const (3 * z ^ 2))
  have hpoint : ∀ ω, Z ω ≤ D ω := fun ω =>
    positiveLogSquare_le_scaledSquare (hS0 ω) hz hscale
  have hZmeas : Measurable Z := by
    dsimp [Z]
    fun_prop
  have hZInt : Integrable Z μ := by
    apply hDInt.mono' hZmeas.aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      dsimp [Z]
      positivity)]
    exact hpoint ω
  refine ⟨hZInt, ?_⟩
  calc
    (∫ ω, Z ω ∂μ) ≤ ∫ ω, D ω ∂μ :=
      integral_mono hZInt hDInt hpoint
    _ = 3 * (Real.log scale) ^ 2 +
          3 * ∫ ω, (S ω / scale) ^ 2 ∂μ + 3 * z ^ 2 := by
      have hc : Integrable (fun _ : Ω => 3 * (Real.log scale) ^ 2) μ :=
        integrable_const _
      have hs : Integrable (fun ω => 3 * (S ω / scale) ^ 2) μ :=
        hscaledInt.const_mul 3
      have hzint : Integrable (fun _ : Ω => 3 * z ^ 2) μ :=
        integrable_const _
      calc
        (∫ ω, D ω ∂μ) =
            ∫ ω, (3 * (Real.log scale) ^ 2 +
              3 * (S ω / scale) ^ 2) + 3 * z ^ 2 ∂μ := rfl
        _ = (∫ ω, 3 * (Real.log scale) ^ 2 +
              3 * (S ω / scale) ^ 2 ∂μ) +
              ∫ _ : Ω, 3 * z ^ 2 ∂μ :=
          integral_add (hc.add hs) hzint
        _ = ((∫ _ : Ω, 3 * (Real.log scale) ^ 2 ∂μ) +
              ∫ ω, 3 * (S ω / scale) ^ 2 ∂μ) +
              ∫ _ : Ω, 3 * z ^ 2 ∂μ := by rw [integral_add hc hs]
        _ = 3 * (Real.log scale) ^ 2 +
              3 * ∫ ω, (S ω / scale) ^ 2 ∂μ + 3 * z ^ 2 := by
          rw [integral_const_mul (μ := μ) 3
            (fun ω => (S ω / scale) ^ 2)]
          simp
    _ ≤ 3 * (Real.log scale) ^ 2 + 3 * V + 3 * z ^ 2 := by
      linarith

/-- Deterministic Cauchy--Schwarz normalization for a finite nonempty sum. -/
theorem normalized_finite_sum_sq_le_average_sq
    {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    ((∑ i, x i) / (Fintype.card ι : ℝ)) ^ 2 ≤
      (∑ i, x i ^ 2) / (Fintype.card ι : ℝ) := by
  simpa only [Finset.card_univ] using
    (sum_div_card_sq_le_sum_sq_div_card
      (s := (Finset.univ : Finset ι)) (f := x))

/-- Integrated Cauchy--Schwarz bound used for the random sum in the
operator-affine positive half. -/
theorem integrable_normalized_sum_sq_and_integral_le_one
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [Fintype ι] [Nonempty ι]
    (X : ι → Ω → ℝ) (hXmeas : ∀ i, Measurable (X i))
    (hXsqInt : ∀ i, Integrable (fun ω => (X i ω) ^ 2) μ)
    (hXsq : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ ≤ 1) :
    Integrable
        (fun ω => ((∑ i, X i ω) / (Fintype.card ι : ℝ)) ^ 2) μ ∧
      ∫ ω, ((∑ i, X i ω) / (Fintype.card ι : ℝ)) ^ 2 ∂μ ≤ 1 := by
  let Z : Ω → ℝ := fun ω =>
    ((∑ i, X i ω) / (Fintype.card ι : ℝ)) ^ 2
  let D : Ω → ℝ := fun ω =>
    (∑ i, (X i ω) ^ 2) / (Fintype.card ι : ℝ)
  have hsumInt : Integrable (fun ω => ∑ i, (X i ω) ^ 2) μ :=
    integrable_finsetSum Finset.univ fun i _ => hXsqInt i
  have hDInt : Integrable D μ := hsumInt.div_const _
  have hpoint : ∀ ω, Z ω ≤ D ω := fun ω =>
    normalized_finite_sum_sq_le_average_sq (fun i => X i ω)
  have hZmeas : Measurable Z := by
    dsimp [Z]
    fun_prop
  have hZInt : Integrable Z μ := by
    apply hDInt.mono' hZmeas.aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [Z]; positivity)]
    exact hpoint ω
  refine ⟨hZInt, ?_⟩
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  calc
    (∫ ω, Z ω ∂μ) ≤ ∫ ω, D ω ∂μ :=
      integral_mono hZInt hDInt hpoint
    _ = (∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) /
          (Fintype.card ι : ℝ) := by
      dsimp [D]
      rw [integral_div, integral_finsetSum Finset.univ
        (fun i _ => hXsqInt i)]
    _ ≤ (∑ _i : ι, (1 : ℝ)) / (Fintype.card ι : ℝ) := by
      apply div_le_div_of_nonneg_right _ hcard.le
      exact Finset.sum_le_sum fun i _ => hXsq i
    _ = 1 := by
      simp [hcard.ne']

end CircularLawSection4
