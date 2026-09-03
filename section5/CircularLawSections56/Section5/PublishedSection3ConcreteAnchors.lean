import CircularLawSections56.Section5.PublishedSection3ConcreteRings

/-! # The actual Section 5 short and calibration anchors

Inactive dimensions are filled by an auxiliary mesoscopic ring, not by an
assumed matrix limit. The actual observable remains filled by its target
constant. Calibration uses exactly the prefix of the original finite iid
sample, with the physical ring length as its normalization.
-/

open MeasureTheory Filter Topology ShortRingAnchor
open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

namespace CircularLawSections56.Section5.PublishedSection3Concrete
open Section6

theorem masked_ringPotential_limit
    (hBBV : BBVComparisonInput) (hBC12 : BC12GinibreInput)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hMom : AtomMomentAssumption21 ν id)
    (hDensity : DensityInput ν)
    (k d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1)) {c₀ C₀ : ℝ}
    (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (hwidth : ∀ n, d n + 2 = 2 * W n + 1) (hcenter : ∀ n, (center n).val = W n)
    (active : ℕ → Bool) (δ γ : ℝ)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hvalid : ∀ᶠ n in atTop, active n = true →
      2 * W n + 1 ≤ k n + 1 ∧
      (k n + 1 : ℝ) ^ (8 / 9 + section3Margin γ) ≤ W n) (z : ℂ) :
    TendstoInProbabilityTri (fun _ => sampleLaw ν)
      (fun n ω => if active n then ringPotential (k n) (d n) (center n) (profile n).b z ω
        else circularLogPotential z) (circularLogPotential z) := by
  let k' : ℕ → ℕ := fun n => if active n then k n else paperMesoscopicCellLength δ W n - 1
  have hvalid' : ∀ᶠ n in atTop, 2 * W n + 1 ≤ k' n + 1 ∧
      (k' n + 1 : ℝ) ^ (8 / 9 + section3Margin γ) ≤ W n := by
    filter_upwards [hvalid, eventually_mesoscopic_ring_band_fits W δ hδ hW,
      eventually_all_mesoscopic_lengths_high_band W δ γ hδ hδγ hγ hW]
      with n hn hfit hband
    cases ha : active n with
    | true => simpa only [k', ha, ↓reduceIte] using hn ha
    | false =>
      have hf := hfit (paperMesoscopicCellLength δ W n) le_rfl
      have hm : 0 < paperMesoscopicCellLength δ W n := by omega
      have he : k' n + 1 = paperMesoscopicCellLength δ W n := by
        simp only [k', ha, Bool.false_eq_true, ↓reduceIte]
        omega
      constructor
      · simpa only [he] using hf
      · have hb := hband (paperMesoscopicCellLength δ W n) (by omega)
        have her : (k' n : ℝ) + 1 = (paperMesoscopicCellLength δ W n : ℝ) := by
          exact_mod_cast he
        simpa only [her] using hb
  have hM : Tendsto (fun n => k' n + 1) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hW
    filter_upwards [hvalid'] with n hn
    omega
  have hω := section3Margin_spec γ (hδ.trans hδγ) hγ
  have hlim := ringPotential_limit hBBV hBC12 ν hMom hDensity k' d W center profile hc₀
    hwidth hcenter hM hW (section3Margin γ) ⟨hω.1, hω.2.1⟩ hvalid' z
  have hconst : TendstoInProbabilityTri (fun _ => sampleLaw ν)
      (fun _ _ => circularLogPotential z) (circularLogPotential z) :=
    tendstoInProbabilityTri_const (fun _ => sampleLaw ν) _ _ tendsto_const_nhds
  have hmasked := tendstoInProbabilityTri_branchSelected (fun _ => sampleLaw ν) active
    (fun n => ringPotential (k' n) (d n) (center n) (profile n).b z)
    (fun _ _ => circularLogPotential z) (circularLogPotential z) hlim hconst
  apply hmasked.congr _ rfl
  intro n ω
  cases ha : active n <;> simp only [branchSelectedTri, k', ha, Bool.false_eq_true, ↓reduceIte]

theorem calibrationRaw_prefix_normalization
    (n d m : ℕ) (center : Fin (d + 1)) (b : Fin (d + 2) → ℂ)
    (hm : 0 < m) (hmN : m ≤ n + 1) (z : ℂ) (ω : Sample) :
    literalModelCalibrationRaw n d m center b z (samples ((n + 1) * (d + 2)) ω) / (m : ℝ) =
      ringPotential (m - 1) d center b z ω := by
  cases m with
  | zero => omega
  | succ m =>
    simp only [Nat.succ_sub_one]
    unfold ringPotential
    rw [literalIndicatorMatrix_logPotential]
    have hvalid : 0 < m + 1 ∧ m + 1 ≤ n + 1 := ⟨hm, hmN⟩
    simp only [literalModelCalibrationRaw, dif_pos hvalid, samples,
      Nat.cast_add, Nat.cast_one]
    rfl

theorem short_anchor_on_common_space
    (hBBV : BBVComparisonInput) (hBC12 : BC12GinibreInput)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hMom : AtomMomentAssumption21 ν id)
    (hDensity : DensityInput ν)
    (d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1)) {c₀ C₀ : ℝ}
    (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (hwidth : ∀ n, d n + 2 = 2 * W n + 1) (hcenter : ∀ n, (center n).val = W n)
    (δ γ : ℝ) (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8)
    (hW : Tendsto W atTop atTop) (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1) (z : ℂ) :
    TendstoInProbabilityTri (fun _ => sampleLaw ν)
      (fun n ω => literalShortLogPotential d center (fun j => (profile j).b)
        (paperNaturalShortBranch W γ) z n (samples ((n + 1) * (d n + 2)) ω))
      (circularLogPotential z) := by
  have hv : ∀ᶠ n in atTop, paperNaturalShortBranch W γ n = true →
      2 * W n + 1 ≤ n + 1 ∧ (n + 1 : ℝ) ^ (8 / 9 + section3Margin γ) ≤ W n := by
    filter_upwards [hfit, hW.eventually_ge_atTop 1] with n hn hw ha
    exact ⟨by rw [← hwidth n]; exact hn,
      natural_short_branch_high_band W γ (hδ.trans hδγ) hγ n (by omega) ha⟩
  have hlim := masked_ringPotential_limit hBBV hBC12 ν hMom hDensity id d W center
    profile hc₀ hwidth hcenter (paperNaturalShortBranch W γ) δ γ hδ hδγ hγ hW hv z
  intro ε hε
  apply (hlim ε hε).congr'
  filter_upwards [hfit] with n hn
  simp only [literalShortLogPotential, filledLiteralIndicatorMatrix, if_pos hn, ringPotential,
    id_eq]

theorem calibration_anchor_on_common_space
    (hBBV : BBVComparisonInput) (hBC12 : BC12GinibreInput)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hMom : AtomMomentAssumption21 ν id)
    (hDensity : DensityInput ν)
    (d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1)) {c₀ C₀ : ℝ}
    (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (hwidth : ∀ n, d n + 2 = 2 * W n + 1) (hcenter : ∀ n, (center n).val = W n)
    (δ γ : ℝ) (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8)
    (hW : Tendsto W atTop atTop) (z : ℂ) :
    TendstoInProbabilityTri (fun _ => sampleLaw ν)
      (fun n ω => literalActiveNormalizedObservable
        (literalLongActive (paperSafeShortBranch W δ γ))
        (fun j => literalModelCalibrationRaw j (d j) (paperBandCellLength W δ j)
          (center j) (profile j).b z)
        (paperBandCellLength W δ) (circularLogPotential z) n
        (samples ((n + 1) * (d n + 2)) ω)) (circularLogPotential z) := by
  let active := literalLongActive (paperSafeShortBranch W δ γ)
  let m := paperBandCellLength W δ
  have hg (n : ℕ) (ha : active n = true) :
      0 < m n ∧ m n ≤ n + 1 ∧ paperMesoscopicCellLength δ W n ≤ m n ∧
        m n ≤ 2 * paperMesoscopicCellLength δ W n := by
    have hr := (paperSafeShortBranch_active W δ γ n ha).2
    have hs := paperTransferReady_geometry W δ n hr
    have hb := balanced_cell_division_spec (n + 1 - 2 * W n)
      (paperMesoscopicCellLength δ W n) hs.1 hr.2.2
    exact ⟨lt_of_lt_of_le hs.1 hs.2.2.2.1, hs.2.2.2.2.2, hs.2.2.2.1, hb.2.2.1.le⟩
  have hv : ∀ᶠ n in atTop, active n = true → 2 * W n + 1 ≤ m n - 1 + 1 ∧
      ((m n - 1 : ℕ) + 1 : ℝ) ^ (8 / 9 + section3Margin γ) ≤ W n := by
    filter_upwards [eventually_mesoscopic_ring_band_fits W δ hδ hW,
      eventually_all_mesoscopic_lengths_high_band W δ γ hδ hδγ hγ hW]
      with n hfit hband ha
    have hm := hg n ha
    have he : m n - 1 + 1 = m n := by omega
    constructor
    · rw [he]
      exact hfit (m n) hm.2.2.1
    · have her : ((m n - 1 : ℕ) : ℝ) + 1 = (m n : ℝ) := by exact_mod_cast he
      rw [her]
      exact hband (m n) hm.2.2.2
  have hlim := masked_ringPotential_limit hBBV hBC12 ν hMom hDensity (fun n => m n - 1)
    d W center profile hc₀ hwidth hcenter active δ γ hδ hδγ hγ hW hv z
  apply hlim.congr _ rfl
  intro n ω
  change (if active n then ringPotential (m n - 1) (d n) (center n) (profile n).b z ω
    else circularLogPotential z) =
      (if active n then literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z
        (samples ((n + 1) * (d n + 2)) ω) / (m n : ℝ) else circularLogPotential z)
  cases ha : active n with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]
  | true =>
    have hm := hg n ha
    simpa only [ha, ↓reduceIte] using
      (calibrationRaw_prefix_normalization n (d n) (m n) (center n) (profile n).b
        hm.1 hm.2.1 z ω).symm

/-- Both original finite-iid anchors are consequences, not assumptions.
All finite sample maps, matrix identities, active fillers and cutoffs are internal. -/
theorem literal_anchors
    (hBBV : BBVComparisonInput) (hBC12 : BC12GinibreInput)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hMom : AtomMomentAssumption21 ν id)
    (hDensity : DensityInput ν)
    (d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1)) {c₀ C₀ : ℝ}
    (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (hwidth : ∀ n, d n + 2 = 2 * W n + 1) (hcenter : ∀ n, (center n).val = W n)
    (δ γ : ℝ) (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8)
    (hW : Tendsto W atTop atTop) (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1) (z : ℂ) :
    let : ∀ n, IsProbabilityMeasure (iidMeasure ν ((n + 1) * (d n + 2))) :=
      fun _n => iidMeasure_isProbability ν _
    Section3IndicatorAnchorsTri (fun n => iidMeasure ν ((n + 1) * (d n + 2)))
      (literalShortLogPotential d center (fun n => (profile n).b) (paperNaturalShortBranch W γ) z)
      (literalActiveNormalizedObservable (literalLongActive (paperSafeShortBranch W δ γ))
        (fun n => literalModelCalibrationRaw n (d n) (paperBandCellLength W δ n)
          (center n) (profile n).b z)
        (paperBandCellLength W δ) (circularLogPotential z)) (circularLogPotential z) := by
  let : ∀ n, IsProbabilityMeasure (iidMeasure ν ((n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability ν _
  apply Section3IndicatorAnchorsTri.of_measurePreserving (fun _ => sampleLaw ν)
    (fun n => iidMeasure ν ((n + 1) * (d n + 2)))
    (fun n => samples ((n + 1) * (d n + 2))) (fun n => samples_measurePreserving ν _)
  · exact measurable_literalShortLogPotential d center _ _ z
  · exact measurable_literalActiveNormalizedObservable _ _ _ _
      (fun n => measurable_literalModelCalibrationRaw n (d n) (paperBandCellLength W δ n)
        (center n) (profile n).b z)
  · exact ⟨short_anchor_on_common_space hBBV hBC12 ν hMom hDensity d W center profile hc₀
      hwidth hcenter δ γ hδ hδγ hγ hW hfit z,
      calibration_anchor_on_common_space hBBV hBC12 ν hMom hDensity d W center profile hc₀
        hwidth hcenter δ γ hδ hδγ hγ hW z⟩

end CircularLawSections56.Section5.PublishedSection3Concrete
