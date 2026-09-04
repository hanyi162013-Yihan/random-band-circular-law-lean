import CircularLawSections56.Section5.QuantitativeSection4Inputs
import CircularLawSections56.Section5.LiteralPhysicalPressureFluctuation
import CircularLawSections56.Section5.LiteralPhysicalDeterminantSeam
import CircularLawSections56.Section6.LiteralModelIdentification

/-! # Actual complex-density pressure inputs from the proved Section 4 estimates

The observables are the literal matrix determinant and the outside-row pressure,
on their original finite IID sample space. No concentration or seam estimate is
assumed here. The hypotheses concern only the atom law, deterministic weights and
finite geometry. These statements also apply to the circular Gaussian atom law.
-/

open MeasureTheory Filter Topology
open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open scoped BigOperators ENNReal

noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace CircularLawSections56.Section5
open Section6

/-- Section 4's lower-amplitude scale is at most one by the normalized
variance profile; it is not an additional deterministic assumption. -/
theorem normalized_profile_lower_scale_le_one
    (d : ℕ) {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1 := by
  have hq : profile.q 0 ≤ 1 := by
    calc
      _ ≤ ∑ s, profile.q s := Finset.single_le_sum
        (fun s _ => (profile.q_pos hc₀ s).le) (Finset.mem_univ 0)
      _ = 1 := profile.normalized
  apply Real.sqrt_le_one.mpr
  have hden : ((d + 1 : ℕ) : ℝ) + 1 = (d + 2 : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_one, add_assoc]
  have hlow := profile.lower 0
  rw [hden] at hlow
  exact hlow.trans hq

/-- Section 4 pressure concentration, transported to Section 5's actual full
sample and its calibration suffix. The empty suffix is included. -/
theorem complex_literalModelPressure_inputs
    (k d m : ℕ) (hm : m ≤ k + 1)
    {c₀ C₀ L : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1)) (z : ℂ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    (∀ q, MemLp (literalModelPressure k d m profile center z q) 2
      (iidMeasure ν ((k + 1) * (d + 2)))) ∧
    (∫ ω, maxCenteredAbs (iidMeasure ν ((k + 1) * (d + 2)))
      (literalModelPressure k d m profile center z) ω
      ∂iidMeasure ν ((k + 1) * (d + 2))) ≤
      Real.sqrt ((d + 2 : ℝ) * 2 * (m - (d + 1) : ℕ) *
        complexPaperPressureFiberL2Bound d c₀ L z) := by
  let := iidMeasure_isProbability ν ((k + 1) * (d + 2))
  have h := complex_literalPhysicalPressure_restriction_inputs
    (iidMeasure ν ((k + 1) * (d + 2))) d (m - (d + 1)) ν hν hL
    profile hc₀ hsqrt center z (literalCalibrationRows k d m)
    (literalCalibrationRows_measurePreserving k d m hm ν)
    (literalModelPressure k d m profile center z)
    (fun _ => Eventually.of_forall fun _ => rfl) hsecondInt hsecond
  exact ⟨h.1, by simpa only [mul_assoc] using h.2⟩

/-- Section 4 fresh-closure bound, identified with the actual full-size
determinant-minus-pressure observable used by Section 5. -/
theorem complex_literalModelRawDeterminant_seam
    (k d : ℕ) (hd : d + 1 ≤ k + 1)
    {c₀ C₀ L : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    (hL : 0 ≤ L) (hf : ∀ᵐ u ∂(volume : Measure ℂ), f u ≤ ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (volume.withDensity f))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂volume.withDensity f ≤ 1) :
    let μ := iidMeasure (volume.withDensity f) ((k + 1) * (d + 2))
    let gap := fun ω => |literalModelRawDeterminant k d center profile.b z ω -
      finiteSignedMax Finset.univ Finset.univ_nonempty
        (fun q => literalModelPressure k d (k + 1) profile center z q ω)|
    Integrable gap μ ∧ (∫ ω, gap ω ∂μ) ≤
      paperIsolatedCoefficientLoss d c₀ + complexFreshNegativeBound d L +
        paperFreshPositiveBound d z := by
  have h := complex_paperIndicatorXSubZI_det_suffixPressure_absLog_seam_withDensity
    (k + 1) d hd profile hc₀ hsqrt center hcenter z f hL hf hsecondInt hsecond
  simpa only [literalModelRawDeterminant, literalModelPressure,
    literalCalibrationRows_full_eq_suffix k d hd, literalPhysicalSuffixPressureMaximum,
    paperIndicatorSampleMeasure] using h

/-- The first `m` complete physical rows, retaining the existing flat-coordinate
ordering. This is model bookkeeping for Section 5's calibration ring. -/
def literalPressurePrefix (k d m : ℕ) (hm : m ≤ k + 1)
    (ω : Fin ((k + 1) * (d + 2)) → ℂ) : Fin (m * (d + 2)) → ℂ :=
  fun j => ω (Fin.castLE (Nat.mul_le_mul_right (d + 2) hm) j)

/-- Section 5 calibration uses an actual IID marginal, with no extra independence
assumption between the calibration matrix and the full matrix. -/
theorem literalPressurePrefix_measurePreserving (k d m : ℕ) (hm : m ≤ k + 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    MeasurePreserving (literalPressurePrefix k d m hm)
      (iidMeasure ν ((k + 1) * (d + 2))) (iidMeasure ν (m * (d + 2))) := by
  unfold literalPressurePrefix
  rw [iidMeasure_eq_pi, iidMeasure_eq_pi]
  exact measurePreserving_pi_restrict_injective
    (Fin.castLE (Nat.mul_le_mul_right (d + 2) hm))
    (Fin.castLE_injective _) ν

/-- The calibration suffix is exactly the suffix of the prefix matrix,
not merely an equal-in-law replacement. -/
theorem literalCalibrationRows_eq_prefix_suffix
    (k d m : ℕ) [NeZero m] (hm : m ≤ k + 1) (hd : d + 1 ≤ m)
    (ω : Fin ((k + 1) * (d + 2)) → ℂ) :
    literalCalibrationRows k d m ω =
      paperIndicatorSuffixRowsZero m d hd (literalPressurePrefix k d m hm ω) := by
  funext j s
  have hindex :
      finProdFinEquiv (literalCalibrationRowIndex k d m hm j, s) =
        Fin.castLE (Nat.mul_le_mul_right (d + 2) hm)
          (finProdFinEquiv (paperIndicatorSuffixRowIndexZero m d hd j, s)) :=
    Fin.ext rfl
  simpa only [literalCalibrationRows, dif_pos hm, paperIndicatorSuffixRowsZero,
    paperIndicatorFlatRowsEquiv, flatIIDRowsMeasurableEquiv_apply, literalPressurePrefix]
    using congrArg ω hindex

/-- Section 4's determinant/fresh-closure estimate for the actual calibration
ring, transported along its concrete prefix marginal. -/
theorem complex_literalModelCalibrationRaw_seam
    (k d m : ℕ) (hm : m ≤ k + 1) (hd : d + 1 ≤ m)
    {c₀ C₀ L : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    (hL : 0 ≤ L) (hf : ∀ᵐ u ∂(volume : Measure ℂ), f u ≤ ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (volume.withDensity f))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂volume.withDensity f ≤ 1) :
    let μ := iidMeasure (volume.withDensity f) ((k + 1) * (d + 2))
    let gap := fun ω => |literalModelCalibrationRaw k d m center profile.b z ω -
      finiteSignedMax Finset.univ Finset.univ_nonempty
        (fun q => literalModelPressure k d m profile center z q ω)|
    Integrable gap μ ∧ (∫ ω, gap ω ∂μ) ≤
      paperIsolatedCoefficientLoss d c₀ + complexFreshNegativeBound d L +
        paperFreshPositiveBound d z := by
  have hmpos : 0 < m := by omega
  let : NeZero m := ⟨hmpos.ne'⟩
  have h := complex_paperIndicatorXSubZI_det_suffixPressure_absLog_seam_withDensity
    m d hd profile hc₀ hsqrt center hcenter z f hL hf hsecondInt hsecond
  let gap : (Fin (m * (d + 2)) → ℂ) → ℝ := fun ω =>
    |Real.log ‖(paperIndicatorXSubZI m d center profile.b ω z).det‖ -
      literalPhysicalSuffixPressureMaximum m d hd profile center z ω|
  change Integrable gap (iidMeasure (volume.withDensity f) (m * (d + 2))) ∧
    (∫ ω, gap ω ∂iidMeasure (volume.withDensity f) (m * (d + 2))) ≤ _ at h
  have hp := literalPressurePrefix_measurePreserving k d m hm (volume.withDensity f)
  have heq : (fun ω => |literalModelCalibrationRaw k d m center profile.b z ω -
      finiteSignedMax Finset.univ Finset.univ_nonempty
        (fun q => literalModelPressure k d m profile center z q ω)|) =
      gap ∘ literalPressurePrefix k d m hm := by
    funext ω
    simp only [literalModelCalibrationRaw, dif_pos (And.intro hmpos hm),
      literalModelPressure, literalCalibrationRows_eq_prefix_suffix k d m hm hd,
      gap, Function.comp_apply, literalPressurePrefix, literalPhysicalSuffixPressureMaximum]
  dsimp only
  rw [heq]
  refine ⟨hp.integrable_comp_of_integrable h.1, ?_⟩
  rw [integral_comp_measurePreserving_eq hp gap h.1]
  exact h.2

/-- The complete finite Section 4 contract at calibration length: both seam
fields and both pressure fields are proved from the actual density model. -/
theorem complex_literalModelCalibration_quantitative
    (active : ℕ → Bool) (d m : ℕ → ℕ)
    {c₀ C₀ : ℕ → ℝ} {L : ℝ}
    (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n))
    (center : ∀ n, Fin (d n + 1)) (z : ℂ)
    (f : ℕ → ℂ → ℝ≥0∞) [∀ n, IsProbabilityMeasure (volume.withDensity (f n))]
    (hm : ∀ n, active n = true → m n ≤ n + 1)
    (hd : ∀ n, active n = true → d n + 1 ≤ m n)
    (hc₀ : ∀ n, active n = true → 0 < c₀ n)
    (hsqrt : ∀ n, active n = true → Real.sqrt (c₀ n / (d n + 2 : ℝ)) ≤ 1)
    (hcenter : ∀ n, active n = true → center n ≠ 0)
    (hL : 0 ≤ L)
    (hf : ∀ n, active n = true → ∀ᵐ u ∂(volume : Measure ℂ), f n u ≤ ENNReal.ofReal L)
    (hsecondInt : ∀ n, active n = true →
      Integrable (fun u : ℂ => ‖u‖ ^ 2) (volume.withDensity (f n)))
    (hsecond : ∀ n, active n = true → ∫ u : ℂ, ‖u‖ ^ 2 ∂volume.withDensity (f n) ≤ 1) :
    ComplexQuantitativeSection4PressureInput
      (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * (d n + 2)))
      active d (fun n => m n - (d n + 1))
      (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (m n) (profile n) (center n) z) c₀ L z := by
  have hs (n : ℕ) (hn : active n = true) := complex_literalModelCalibrationRaw_seam
    n (d n) (m n) (hm n hn) (hd n hn) (profile n) (hc₀ n hn) (hsqrt n hn)
    (center n) (hcenter n hn) z (f n) hL (hf n hn) (hsecondInt n hn) (hsecond n hn)
  have hp (n : ℕ) (hn : active n = true) := complex_literalModelPressure_inputs
    n (d n) (m n) (hm n hn) (profile n) (hc₀ n hn) (hsqrt n hn) (center n) z
    (volume.withDensity (f n)) (complexBallBound_withDensity (hf n hn)) hL
    (hsecondInt n hn) (hsecond n hn)
  exact ⟨fun n hn => (hs n hn).1, fun n hn => (hs n hn).2,
    fun n hn => (hp n hn).1, fun n hn => (hp n hn).2⟩

/-- The complete finite Section 4 contract at full matrix size, on the original
flat IID matrix samples. No finite pressure conclusion is an input. -/
theorem complex_literalModelFinal_quantitative
    (active : ℕ → Bool) (d : ℕ → ℕ)
    {c₀ C₀ : ℕ → ℝ} {L : ℝ}
    (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n))
    (center : ∀ n, Fin (d n + 1)) (z : ℂ)
    (f : ℕ → ℂ → ℝ≥0∞) [∀ n, IsProbabilityMeasure (volume.withDensity (f n))]
    (hd : ∀ n, active n = true → d n + 1 ≤ n + 1)
    (hc₀ : ∀ n, active n = true → 0 < c₀ n)
    (hsqrt : ∀ n, active n = true → Real.sqrt (c₀ n / (d n + 2 : ℝ)) ≤ 1)
    (hcenter : ∀ n, active n = true → center n ≠ 0)
    (hL : 0 ≤ L)
    (hf : ∀ n, active n = true → ∀ᵐ u ∂(volume : Measure ℂ), f n u ≤ ENNReal.ofReal L)
    (hsecondInt : ∀ n, active n = true →
      Integrable (fun u : ℂ => ‖u‖ ^ 2) (volume.withDensity (f n)))
    (hsecond : ∀ n, active n = true → ∫ u : ℂ, ‖u‖ ^ 2 ∂volume.withDensity (f n) ≤ 1) :
    ComplexQuantitativeSection4PressureInput
      (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * (d n + 2)))
      active d (fun n => n + 1 - (d n + 1))
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z) c₀ L z := by
  have hs (n : ℕ) (hn : active n = true) := complex_literalModelRawDeterminant_seam
    n (d n) (hd n hn) (profile n) (hc₀ n hn) (hsqrt n hn)
    (center n) (hcenter n hn) z (f n) hL (hf n hn) (hsecondInt n hn) (hsecond n hn)
  have hp (n : ℕ) (hn : active n = true) := complex_literalModelPressure_inputs
    n (d n) (n + 1) le_rfl (profile n) (hc₀ n hn) (hsqrt n hn) (center n) z
    (volume.withDensity (f n)) (complexBallBound_withDensity (hf n hn)) hL
    (hsecondInt n hn) (hsecond n hn)
  exact ⟨fun n hn => (hs n hn).1, fun n hn => (hs n hn).2,
    fun n hn => (hp n hn).1, fun n hn => (hp n hn).2⟩

end CircularLawSections56.Section5
