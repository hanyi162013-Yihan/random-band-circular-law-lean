import CircularLawSections56.Section5.GenericLiteralModel
import CircularLawSections56.Section5.LiteralCircularLaw

/-! # Circular law for logarithmically controlled, dimension-dependent weights

The same branch selection and replacement proof now permits polynomial taper.
The constant is fixed in size, and the lower profile parameter is not.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1800000

namespace CircularLawSections56.Section5

open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open TaoVuReplacement ShortRingAnchor

section Logarithmic

variable (d q m W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ : ℕ → ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n))
    (C : ℂ → ℝ)
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
      (logarithmicModelLiftedPressure d q m ν profile center z) q m (fun n => n + 1) W δ
      (C z)))
    (h3 :
      let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
        fun n => iidMeasure_isProbability (ν n) _
      ∀ᵐ z ∂(volume : Measure ℂ), Section3IndicatorAnchorsTri
        (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
        (literalShortLogPotential d center (fun n => (profile n).b) shortBranch z)
        (literalActiveNormalizedObservable (literalLongActive shortBranch)
          (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
          m (circularLogPotential z)) (circularLogPotential z))

include hδ hδγ hγ hW hLong hsize

/-- Fixed-spectral-parameter form of the Section 3/4 assembly.  This is the
actual proof kernel: no planar exceptional set is used once the two inputs are
available at the chosen `z`.  The historical a.e.-parameter theorem below is
obtained from this theorem by filtering the corresponding inputs. -/
theorem logarithmic_profile_logPotential_at_of_section34 (z : ℂ)
    (h4z : Nonempty (CompletedSection4LongBranchData
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2))) (literalLongActive shortBranch)
      (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (m n) (profile n) (center n) z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (logarithmicModelLiftedPressure d q m ν profile center z) q m (fun n => n + 1) W δ
      (C z)))
    (h3z :
      let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
        fun n => iidMeasure_isProbability (ν n) _
      Section3IndicatorAnchorsTri
        (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
        (literalShortLogPotential d center (fun n => (profile n).b) shortBranch z)
        (literalActiveNormalizedObservable (literalLongActive shortBranch)
          (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
          m (circularLogPotential z)) (circularLogPotential z)) :
    let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
      fun n => iidMeasure_isProbability (ν n) _
    TendstoInProbabilityTri
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
      (fun n ω => physicalLogPotential
        (filledLiteralIndicatorMatrix n (d n) (center n) (profile n).b ω) z)
      (circularLogPotential z) := by
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability (ν n) _
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
    (logarithmicModelLiftedPressure d q m ν profile center z) q m (fun n => n + 1) W
    (circularLogPotential z) δ γ (C z)
    hδ hδγ hγ hW hgrowth h4z.some h3z
  have hSelected := tendstoInProbabilityTri_branchSelected
    (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2))) shortBranch
    (literalShortLogPotential d center (fun n => (profile n).b) shortBranch z)
    (literalActiveNormalizedObservable (literalLongActive shortBranch)
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => n + 1) (circularLogPotential z)) (circularLogPotential z)
    h3z.target_size cert.tendstoInProbability
  apply hSelected.congr (fun n ω => ?_) rfl
  have heq := literalModel_logPotential_branch d center (fun n => (profile n).b)
    shortBranch (circularLogPotential z) z hsize n ω
  rw [heq]
  cases hb : shortBranch n <;> simp [branchSelectedTri, literalShortLogPotential, hb]

include h4 h3

/-- Actual log-determinant convergence, using the two branch-restricted Section 3
anchors and the finite Section 4 data, with no comparison-model assumption. -/
theorem logarithmic_profile_logPotential_of_section34 :
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
  exact logarithmic_profile_logPotential_at_of_section34 d q m W center profile C ν
    shortBranch δ γ hδ hδγ hγ hW hLong hsize z hz4 hz3

/-- Fixed-spectral-parameter actual-matrix conclusion.  Removing the filler
uses only eventual band fit and therefore preserves the chosen `z`. -/
omit h4 h3 in
theorem logarithmic_profile_actual_logPotential_at_of_section34
    (z : ℂ)
    (h4z : Nonempty (CompletedSection4LongBranchData
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2))) (literalLongActive shortBranch)
      (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (m n) (profile n) (center n) z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (logarithmicModelLiftedPressure d q m ν profile center z) q m (fun n => n + 1) W δ
      (C z)))
    (h3z :
      let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
        fun n => iidMeasure_isProbability (ν n) _
      Section3IndicatorAnchorsTri
        (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
        (literalShortLogPotential d center (fun n => (profile n).b) shortBranch z)
        (literalActiveNormalizedObservable (literalLongActive shortBranch)
          (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
          m (circularLogPotential z)) (circularLogPotential z))
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1) :
    let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
      fun n => iidMeasure_isProbability (ν n) _
    TendstoInProbabilityTri
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
      (fun n ω => physicalLogPotential
        (literalIndicatorMatrix n (d n) (center n) (profile n).b ω) z)
      (circularLogPotential z) := by
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability (ν n) _
  dsimp only
  have hFilled := logarithmic_profile_logPotential_at_of_section34 d q m W center profile C ν
    shortBranch δ γ hδ hδγ hγ hW hLong hsize z h4z h3z
  intro ε hε
  apply (hFilled ε hε).congr' ?_
  filter_upwards [hfit] with n hn
  simp only [filledLiteralIndicatorMatrix, if_pos hn]

/-- The stronger log-potential conclusion also holds for the unfilled paper
matrix; changing the finitely many non-fitting indices has no effect. -/
theorem logarithmic_profile_actual_logPotential_of_section34
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
  have hFilled := logarithmic_profile_logPotential_of_section34 d q m W center profile C ν
    shortBranch δ γ hδ hδγ hγ hW hLong hsize h4 h3
  filter_upwards [hFilled] with z hz
  intro ε hε
  apply (hz ε hε).congr' ?_
  filter_upwards [hfit] with n hn
  simp only [filledLiteralIndicatorMatrix, if_pos hn]

/-- The literal indicator matrix converges to normalized area on the unit disk.
The finite-prefix filler is removed. All three former comparison-model inputs
are proved by the diagonal disk reference ensemble, not added to `h3` or `h4`. -/
theorem logarithmic_profile_circularLaw_of_section34
    (hc₀ : ∀ n, 0 < c₀ n)
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
    n (d n) (center n) (profile n) (hc₀ n) (ν n) (hInt n) (hSecond n)
  have hLimit := triangular_circularLaw_of_logPotential
    (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
    (fun n ω => filledLiteralIndicatorMatrix n (d n) (center n) (profile n).b ω)
    (fun n => filledLiteralIndicatorMatrix_measurable n (d n) (center n) (profile n).b)
    1 zero_le_one (fun n => (hEnergy n).1) (fun n => (hEnergy n).2)
    (logarithmic_profile_logPotential_of_section34 d q m W center profile C ν shortBranch δ γ
      hδ hδγ hγ hW hLong hsize h4 h3)
  intro f hf hc
  apply (hLimit f hf hc).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hfit] with n hn
  exact ae_of_all _ fun ω => by simp only [filledLiteralIndicatorMatrix, if_pos hn]

end Logarithmic

end CircularLawSections56.Section5
