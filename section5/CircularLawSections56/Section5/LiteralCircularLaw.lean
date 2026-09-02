import CircularLawSections56.Section5.CircularLawFromPotential
import CircularLawSections56.Section6.LiteralModelIdentification

/-!
# Section 5: the literal matrix converges to circular area measure

The only random-matrix preinputs here are the specified Section 3 anchors and
the finite Section 4 ledger (constructed by `literalModel_completedSection4Data`).
There is no comparison matrix, comparison energy, comparison log-potential
limit, comparison ESD limit, or replacement implication among the hypotheses.

The short anchor is deliberately masked on the long branch.  Requiring the
unmasked full matrix sequence to converge would already assume the desired
Section 5 log-potential conclusion and would not be the Section 3 input.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1800000

namespace CircularLawSections56.Section5

open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open TaoVuReplacement ShortRingAnchor

/-- Only the actual short branch is a Section 3 target-size input. -/
def literalShortLogPotential
    (d : ℕ → ℕ) (center : ∀ n, Fin (d n + 1)) (b : ∀ n, Fin (d n + 2) → ℂ)
    (shortBranch : ℕ → Bool) (z : ℂ) (n : ℕ)
    (ω : Fin ((n + 1) * (d n + 2)) → ℂ) : ℝ :=
  if shortBranch n then
    physicalLogPotential (filledLiteralIndicatorMatrix n (d n) (center n) (b n) ω) z
  else circularLogPotential z

@[simp] theorem literalShortLogPotential_on_long
    (d : ℕ → ℕ) (center : ∀ n, Fin (d n + 1)) (b : ∀ n, Fin (d n + 2) → ℂ)
    (shortBranch : ℕ → Bool) (z : ℂ) (n : ℕ)
    (h : shortBranch n = false) (ω : Fin ((n + 1) * (d n + 2)) → ℂ) :
    literalShortLogPotential d center b shortBranch z n ω = circularLogPotential z := by
  simp [literalShortLogPotential, h]

section Literal

variable (d q m W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ L : ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀)
    (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)]
    (shortBranch : ℕ → Bool) (δ γ : ℝ)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hLong : ∀ᶠ n in atTop, literalLongActive shortBranch n = true →
      (W n : ℝ) ^ (1 + γ) < (n + 1 : ℝ))
    (hsize : ∀ n, literalLongActive shortBranch n = true → d n + 2 ≤ n + 1)
    (h4 : ∀ᵐ z ∂(volume : Measure ℂ), Nonempty (CompletedSection4LongBranchData
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2))) (literalLongActive shortBranch)
      (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (m n) (profile n) (center n) z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (literalModelLiftedPressure d q m ν profile center z) q m (fun n => n + 1) W δ
      (completedLiteralConstant c₀ L z)))
    (h3 :
      let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
        fun n => iidMeasure_isProbability (ν n) _
      ∀ᵐ z ∂(volume : Measure ℂ), Section3IndicatorAnchorsTri
        (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
        (literalShortLogPotential d center (fun n => (profile n).b) shortBranch z)
        (literalActiveNormalizedObservable (literalLongActive shortBranch)
          (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
          m (circularLogPotential z)) (circularLogPotential z))

include hδ hδγ hγ hW hLong hsize h4 h3

/-- Actual log-determinant convergence, using the two branch-restricted Section 3
anchors and the finite Section 4 data, with no comparison-model assumption. -/
theorem literal_indicator_logPotential_of_section34 :
    let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
      fun n => iidMeasure_isProbability (ν n) _
    ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
      (fun n ω => physicalLogPotential
        (filledLiteralIndicatorMatrix n (d n) (center n) (profile n).b ω) z)
      (circularLogPotential z) := by
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability (ν n) _
  filter_upwards [h4, h3] with z hz4 hz3
  have hgrowth : ∀ᶠ n in atTop, literalLongActive shortBranch n = true →
      (W n : ℝ) ^ (1 + γ) < ((fun n : ℕ => n + 1) n : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hLong
  let cert := completedSection4_literalCertificate
    (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2))) shortBranch
    (literalShortLogPotential d center (fun n => (profile n).b) shortBranch z)
    (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
    (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
    (fun n => literalModelPressure n (d n) (m n) (profile n) (center n) z)
    (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
    (literalModelLiftedPressure d q m ν profile center z) q m (fun n => n + 1) W
    (circularLogPotential z) δ γ (completedLiteralConstant c₀ L z)
    hδ hδγ hγ hW hgrowth hz4.some hz3
  have hSelected := tendstoInProbabilityTri_branchSelected
    (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2))) shortBranch
    (literalShortLogPotential d center (fun n => (profile n).b) shortBranch z)
    (literalActiveNormalizedObservable (literalLongActive shortBranch)
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => n + 1) (circularLogPotential z)) (circularLogPotential z)
    hz3.target_size cert.tendstoInProbability
  apply hSelected.congr (fun n ω => ?_) rfl
  have heq := literalModel_logPotential_branch d center (fun n => (profile n).b)
    shortBranch (circularLogPotential z) z hsize n ω
  rw [heq]
  cases hb : shortBranch n <;> simp [branchSelectedTri, literalShortLogPotential, hb]

/-- The stronger log-potential conclusion also holds for the unfilled paper
matrix; changing the finitely many non-fitting indices has no effect. -/
theorem literal_indicator_actual_logPotential_of_section34
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1) :
    let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
      fun n => iidMeasure_isProbability (ν n) _
    ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
      (fun n ω => physicalLogPotential
        (literalIndicatorMatrix n (d n) (center n) (profile n).b ω) z)
      (circularLogPotential z) := by
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability (ν n) _
  have hFilled := literal_indicator_logPotential_of_section34 d q m W center profile ν
    shortBranch δ γ hδ hδγ hγ hW hLong hsize h4 h3
  filter_upwards [hFilled] with z hz
  intro ε hε
  apply (hz ε hε).congr' ?_
  filter_upwards [hfit] with n hn
  simp only [filledLiteralIndicatorMatrix, if_pos hn]

/-- The literal indicator matrix converges to normalized area on the unit disk.
The finite-prefix filler is removed. All three former comparison-model inputs
are proved by the diagonal disk reference ensemble, not added to `h3` or `h4`. -/
theorem literal_indicator_circularLaw_of_section34
    (hc₀ : 0 < c₀)
    (hInt : ∀ n, Integrable (fun u : ℂ => ‖u‖ ^ 2) (ν n))
    (hSecond : ∀ n, ∫ u : ℂ, ‖u‖ ^ 2 ∂ν n ≤ 1)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure
        (Measure.infinitePi (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2))))
        (fun n ω => realEsdTest
          (literalIndicatorMatrix n (d n) (center n) (profile n).b (ω n)) f)
        atTop (fun _ => ∫ w, f w ∂circularMeasure) := by
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability (ν n) _
  have hEnergy := fun n => filledLiteralIndicatorMatrix_energy_integrable_and_le_one
    n (d n) (center n) (profile n) hc₀ (ν n) (hInt n) (hSecond n)
  have hLimit := triangular_circularLaw_of_logPotential
    (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
    (fun n ω => filledLiteralIndicatorMatrix n (d n) (center n) (profile n).b ω)
    (fun n => filledLiteralIndicatorMatrix_measurable n (d n) (center n) (profile n).b)
    1 zero_le_one (fun n => (hEnergy n).1) (fun n => (hEnergy n).2)
    (literal_indicator_logPotential_of_section34 d q m W center profile ν shortBranch δ γ
      hδ hδγ hγ hW hLong hsize h4 h3)
  intro f hf hc
  apply (hLimit f hf hc).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hfit] with n hn
  exact ae_of_all _ fun ω => by simp only [filledLiteralIndicatorMatrix, if_pos hn]

end Literal

/-- Public finite-input version for the complex-density indicator model.  The
caller supplies only the two finite Section 4 pressure estimates; cells,
inverse-row increments and terminal identifications are constructed here. -/
theorem complex_literal_indicator_circularLaw_of_section34
    (d q m W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ L : ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀)
    (f : ℕ → ℂ → ℝ≥0∞) [∀ n, IsProbabilityMeasure (volume.withDensity (f n))]
    (shortBranch : ℕ → Bool) (δ γ : ℝ)
    (hc₀ : 0 < c₀) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hLong : ∀ᶠ n in atTop, literalLongActive shortBranch n = true →
      (W n : ℝ) ^ (1 + γ) < (n + 1 : ℝ))
    (hsize : ∀ n, literalLongActive shortBranch n = true → d n + 2 ≤ n + 1)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1)
    (hWpos : ∀ n, literalLongActive shortBranch n = true → 0 < W n)
    (hd : ∀ n, literalLongActive shortBranch n = true → d n + 1 = 2 * W n)
    (hm0 : ∀ n, literalLongActive shortBranch n = true → 0 < paperMesoscopicCellLength δ W n)
    (hReserve : ∀ n, literalLongActive shortBranch n = true → 2 * W n ≤ n + 1)
    (hFit : ∀ n, literalLongActive shortBranch n = true →
      2 * paperMesoscopicCellLength δ W n ≤ n + 1 - 2 * W n)
    (hCount : ∀ n, literalLongActive shortBranch n = true →
      q n = balancedCellCount (n + 1 - 2 * W n) (paperMesoscopicCellLength δ W n))
    (hLength : ∀ n, literalLongActive shortBranch n = true →
      m n = balancedCellLength (n + 1 - 2 * W n) (paperMesoscopicCellLength δ W n))
    (hWidth : ∀ n, literalLongActive shortBranch n = true → d n + 1 ≤ m n)
    (hmN : ∀ n, literalLongActive shortBranch n = true → m n ≤ n + 1)
    (hsqrt : ∀ n, literalLongActive shortBranch n = true → Real.sqrt (c₀ / (d n + 2 : ℝ)) ≤ 1)
    (hcenter : ∀ n, literalLongActive shortBranch n = true → center n ≠ 0)
    (hf : ∀ n, literalLongActive shortBranch n = true →
      ∀ᵐ w ∂(volume : Measure ℂ), f n w ≤ ENNReal.ofReal L)
    (hInt : ∀ n, Integrable (fun u : ℂ => ‖u‖ ^ 2) (volume.withDensity (f n)))
    (hSecond : ∀ n, ∫ u : ℂ, ‖u‖ ^ 2 ∂volume.withDensity (f n) ≤ 1)
    (hCalibration : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * (d n + 2)))
      (literalLongActive shortBranch)
      (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (m n) (profile n) (center n) z)
      m W (completedLiteralConstant c₀ L z))
    (hFinal : ∀ᵐ z ∂(volume : Measure ℂ), CompletedSection4PressureInput
      (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * (d n + 2)))
      (literalLongActive shortBranch)
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (fun n => n + 1) W (completedLiteralConstant c₀ L z))
    (h3 :
      let : ∀ n, IsProbabilityMeasure
          (iidMeasure (volume.withDensity (f n)) ((n + 1) * (d n + 2))) :=
        fun n => iidMeasure_isProbability (volume.withDensity (f n)) _
      ∀ᵐ z ∂(volume : Measure ℂ), Section3IndicatorAnchorsTri
        (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * (d n + 2)))
        (literalShortLogPotential d center (fun n => (profile n).b) shortBranch z)
        (literalActiveNormalizedObservable (literalLongActive shortBranch)
          (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
          m (circularLogPotential z)) (circularLogPotential z)) :
    ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      TendstoInMeasure
        (Measure.infinitePi (fun n => iidMeasure (volume.withDensity (f n))
          ((n + 1) * (d n + 2))))
        (fun n ω => realEsdTest
          (literalIndicatorMatrix n (d n) (center n) (profile n).b (ω n)) g)
        atTop (fun _ => ∫ w, g w ∂circularMeasure) := by
  apply literal_indicator_circularLaw_of_section34 (L := L) d q m W center profile
    (fun n => volume.withDensity (f n)) shortBranch δ γ hδ hδγ hγ hW hLong hsize
    ?_ h3 hc₀ hInt hSecond hfit
  filter_upwards [hCalibration, hFinal] with z hzCal hzFinal
  exact ⟨literalModel_completedSection4Data (literalLongActive shortBranch) d q m W
    profile center z δ f hc₀ hL hWpos hd hm0 hReserve hFit hCount hLength hWidth hmN
    hsqrt hcenter hf hInt hSecond hzCal hzFinal⟩

end CircularLawSections56.Section5
