/- Source snapshot: upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/ProbabilityCore.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Mathlib.Probability.Density
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set

namespace LivshytsProjectionFormalization

/-- A bounded density bounds the probability of an interval. -/
theorem interval_small_ball_of_bounded_pdf
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    [HasPDF X P] {a b ρ : ℝ} (hρ : 0 ≤ ρ)
    (hpdf : ∀ᵐ x ∂(volume : Measure ℝ), pdf X P volume x ≤ ENNReal.ofReal ρ) :
    P (X ⁻¹' Icc a b) ≤ ENNReal.ofReal (ρ * (b - a)) := by
  rw [← Measure.map_apply_of_aemeasurable (HasPDF.aemeasurable X P volume) measurableSet_Icc]
  rw [map_eq_setLIntegral_pdf X P volume measurableSet_Icc]
  calc
    (∫⁻ x in Icc a b, pdf X P volume x ∂volume) ≤
        ∫⁻ _x in Icc a b, ENNReal.ofReal ρ ∂volume :=
      lintegral_mono_ae (ae_restrict_of_ae hpdf)
    _ = ENNReal.ofReal ρ * volume (Icc a b) := by simp
    _ = ENNReal.ofReal (ρ * (b - a)) := by
      rw [Real.volume_Icc, ← ENNReal.ofReal_mul hρ]

/-- Symmetric one-dimensional small-ball bound from an a.e. density sup bound. -/
theorem real_small_ball_of_bounded_pdf
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    [HasPDF X P] {center radius ρ : ℝ} (_hradius : 0 ≤ radius) (hρ : 0 ≤ ρ)
    (hpdf : ∀ᵐ x ∂(volume : Measure ℝ), pdf X P volume x ≤ ENNReal.ofReal ρ) :
    P (X ⁻¹' Icc (center - radius) (center + radius)) ≤
      ENNReal.ofReal (2 * ρ * radius) := by
  calc
    P (X ⁻¹' Icc (center - radius) (center + radius)) ≤
        ENNReal.ofReal (ρ * ((center + radius) - (center - radius))) :=
      interval_small_ball_of_bounded_pdf P X hρ hpdf
    _ = ENNReal.ofReal (2 * ρ * radius) := by
      congr 1
      ring

/-- Rescaling a real-valued random variable by nonzero `a` multiplies the small-ball radius by
    `1 / |a|`. -/
theorem real_scaled_small_ball_of_bounded_pdf
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    [HasPDF X P] {a center radius ρ : ℝ} (ha : a ≠ 0) (hρ : 0 ≤ ρ)
    (_hradius : 0 ≤ radius)
    (hpdf : ∀ᵐ x ∂(volume : Measure ℝ), pdf X P volume x ≤ ENNReal.ofReal ρ) :
    P ((fun ω => a * X ω) ⁻¹' Icc (center - radius) (center + radius)) ≤
      ENNReal.ofReal (2 * ρ * (radius / |a|)) := by
  by_cases ha_pos : 0 < a
  · have hpre :
      (fun ω => a * X ω) ⁻¹' Icc (center - radius) (center + radius) =
        X ⁻¹' Icc ((center - radius) / a) ((center + radius) / a) := by
      ext ω
      constructor
      · intro hω
        have hmul : X ω ∈ (fun t : ℝ => a * t) ⁻¹' Icc (center - radius) (center + radius) := by
          simpa using hω
        simpa [Set.preimage_const_mul_Icc₀ (a := center - radius) (b := center + radius) (c := a) ha_pos] using hmul
      · intro hω
        have hmul : X ω ∈ (fun t : ℝ => a * t) ⁻¹' Icc (center - radius) (center + radius) := by
          simpa [Set.preimage_const_mul_Icc₀ (a := center - radius) (b := center + radius) (c := a) ha_pos] using hω
        simpa using hmul
    have hsmall :
        P (X ⁻¹' Icc ((center - radius) / a) ((center + radius) / a)) ≤
          ENNReal.ofReal (ρ * (((center + radius) / a) - ((center - radius) / a))) :=
      interval_small_ball_of_bounded_pdf (P := P) (X := X)
        (a := (center - radius) / a) (b := (center + radius) / a) hρ hpdf
    have hlen :
        ρ * (((center + radius) / a) - ((center - radius) / a)) =
          2 * ρ * (radius / |a|) := by
      have hA : |a| = a := abs_of_pos ha_pos
      have hwidth : ((center + radius) / a) - ((center - radius) / a) = 2 * (radius / a) := by
        field_simp [ha_pos.ne']
        ring
      rw [hwidth, hA]
      ring
    simpa [hpre, hlen] using hsmall
  · have ha_nonpos : a ≤ 0 := le_of_not_gt ha_pos
    have ha_neg : a < 0 := lt_of_le_of_ne ha_nonpos ha
    have hpre :
        (fun ω => a * X ω) ⁻¹' Icc (center - radius) (center + radius) =
          X ⁻¹' Icc ((center + radius) / a) ((center - radius) / a) := by
      ext ω
      constructor
      · intro hω
        have hmul : X ω ∈ (fun t : ℝ => a * t) ⁻¹' Icc (center - radius) (center + radius) := by
          simpa using hω
        simpa [Set.preimage_const_mul_Icc_of_neg (a := center - radius) (b := center + radius)
          (c := a) ha_neg] using hmul
      · intro hω
        have hmul : X ω ∈ (fun t : ℝ => a * t) ⁻¹' Icc (center - radius) (center + radius) := by
          simpa [Set.preimage_const_mul_Icc_of_neg (a := center - radius) (b := center + radius)
            (c := a) ha_neg] using hω
        simpa using hmul
    have hsmall :
        P (X ⁻¹' Icc ((center + radius) / a) ((center - radius) / a)) ≤
          ENNReal.ofReal (ρ * (((center - radius) / a) - ((center + radius) / a))) :=
      interval_small_ball_of_bounded_pdf (P := P) (X := X)
        (a := (center + radius) / a) (b := (center - radius) / a) hρ hpdf
    have hlen :
        ρ * (((center - radius) / a) - ((center + radius) / a)) =
          2 * ρ * (radius / |a|) := by
      have hA : |a| = -a := abs_of_neg ha_neg
      have hwidth : ((center - radius) / a) - ((center + radius) / a) =
          2 * (radius / |a|) := by
        rw [hA]
        field_simp [ha]
        ring
      rw [hwidth]
      ring
    simpa [hpre, hlen] using hsmall

/-- Reorder a row-product into `L` equal terms; useful for tensorization bounds. -/
theorem prod_pair_rowBound {L r : ℕ} (b : Fin L → ENNReal) :
    (∏ p : Fin L × Fin r, b p.1) = ∏ j : Fin L, (b j) ^ r := by
  calc
    (∏ p : Fin L × Fin r, b p.1) =
        ∏ j : Fin L, ∏ _q : Fin r, b j := by
      rw [← Finset.univ_product_univ]
      simpa using (Finset.prod_product' (Finset.univ : Finset (Fin L))
        (Finset.univ : Finset (Fin r)) (fun j _q => b j))
    _ = ∏ j : Fin L, (b j) ^ r := by simp

/-- Tensorized small-ball data for independent coordinates. -/
structure TensorizedSmallBallInterface
    (Ω : Type*) [MeasurableSpace Ω] (L r : ℕ) (μ : Measure Ω) where
  targetEvent : Set Ω
  rowEvent : Fin L × Fin r → Set Ω
  row_measurable : ∀ p, MeasurableSet (rowEvent p)
  target_measurable : MeasurableSet targetEvent
  rowBound : Fin L → ENNReal
  target_subset : targetEvent ⊆ ⋂ p, rowEvent p
  independent_rows : ProbabilityTheory.iIndepSet rowEvent (μ := μ)
  row_small_ball : ∀ p, μ (rowEvent p) ≤ rowBound p.1

/-- Product bound from row-level bounds under independence. -/
theorem TensorizedSmallBallInterface.tensorized
    {Ω : Type*} [MeasurableSpace Ω] {L r : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (data : TensorizedSmallBallInterface Ω L r μ) :
    μ data.targetEvent ≤ ∏ j : Fin L, (data.rowBound j) ^ r := by
  letI : IsProbabilityMeasure μ := ‹IsProbabilityMeasure μ›
  calc
    μ data.targetEvent ≤ μ (⋂ p : Fin L × Fin r, data.rowEvent p) := measure_mono data.target_subset
    _ = ∏ p : Fin L × Fin r, μ (data.rowEvent p) := by
      simpa [Finset.set_biInter_coe, Set.biInter_univ] using
        (data.independent_rows.meas_biInter
          (μ := μ) (s := (Finset.univ : Finset (Fin L × Fin r)))
        )
    _ ≤ ∏ p : Fin L × Fin r, data.rowBound p.1 :=
      Finset.prod_le_prod' (fun p _ => data.row_small_ball p)
    _ = ∏ j : Fin L, (data.rowBound j) ^ r := prod_pair_rowBound data.rowBound

/-- Conditional tensorization interface; row bounds hold almost everywhere in conditioning data. -/
structure ConditionalTensorizedSmallBallInterface
    (Α Ω : Type*) [MeasurableSpace Α] [MeasurableSpace Ω]
    (L r : ℕ) (μ : Measure Α) (κ : Kernel Α Ω) where
  rowEvent : Fin L × Fin r → Set Ω
  targetEvent : Set Ω
  target_measurable : MeasurableSet targetEvent
  rowBound : Fin L → ENNReal
  target_subset : targetEvent ⊆ ⋂ p, rowEvent p
  independent_rows : ProbabilityTheory.Kernel.iIndepSet rowEvent κ μ
  row_small_ball : ∀ p, ∀ᵐ a ∂μ, κ a (rowEvent p) ≤ rowBound p.1

/-- Almost everywhere tensorized small-ball bound in conditional form. -/
theorem ConditionalTensorizedSmallBallInterface.tensorized_ae
    {Α Ω : Type*} [MeasurableSpace Α] [MeasurableSpace Ω]
    {L r : ℕ} {μ : Measure Α} {κ : Kernel Α Ω}
    (data : ConditionalTensorizedSmallBallInterface Α Ω L r μ κ) :
    ∀ᵐ a ∂μ, κ a data.targetEvent ≤ ∏ j : Fin L, (data.rowBound j) ^ r := by
  have hindependent := data.independent_rows.meas_biInter Finset.univ
  have hrows : ∀ᵐ a ∂μ, ∀ p, κ a (data.rowEvent p) ≤ data.rowBound p.1 :=
    ae_all_iff.mpr data.row_small_ball
  filter_upwards [hindependent, hrows] with a hinter hrow
  calc
    κ a data.targetEvent ≤ κ a (⋂ p, data.rowEvent p) := measure_mono data.target_subset
    _ = ∏ p : Fin L × Fin r, κ a (data.rowEvent p) := by
      simpa using hinter
    _ ≤ ∏ p : Fin L × Fin r, data.rowBound p.1 :=
      Finset.prod_le_prod' (fun p _ => hrow p)
    _ = ∏ j : Fin L, (data.rowBound j) ^ r := prod_pair_rowBound data.rowBound

/-- Integrating the almost-everywhere conditional tensorized bound. -/
theorem ConditionalTensorizedSmallBallInterface.bind_tensorized
    {Α Ω : Type*} [MeasurableSpace Α] [MeasurableSpace Ω]
    {L r : ℕ} {μ : Measure Α} [IsProbabilityMeasure μ] {κ : Kernel Α Ω}
    (data : ConditionalTensorizedSmallBallInterface Α Ω L r μ κ) :
    μ.bind κ data.targetEvent ≤ ∏ j : Fin L, (data.rowBound j) ^ r := by
  rw [Measure.bind_apply data.target_measurable κ.aemeasurable]
  calc
    (∫⁻ a, κ a data.targetEvent ∂μ) ≤
        ∫⁻ _a, (∏ j : Fin L, (data.rowBound j) ^ r) ∂μ :=
      lintegral_mono_ae data.tensorized_ae
    _ = ∏ j : Fin L, (data.rowBound j) ^ r := by simp

end LivshytsProjectionFormalization
