import CircularLawSections56.Section5.VerifiedGinibreSources
import CircularLawSections56.Section5.PublishedSection3Transport
import CircularLawSections56.Section5.Section3ScaleEligibility

/-! # Concrete cyclic matrices, with all finite model and scale data constructed

The endpoint calls the checked Section 3 theorem. Its only random-matrix
literature premise is BBV (and GBL in the real density branch).
The Gaussian negative moment and full-log reference are proved internally.
Finite-prefix changes are handled here, not imposed as new all-index hypotheses.
-/

open MeasureTheory Filter Topology ShortRingAnchor Arxiv2410V3
open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace CircularLawSections56.Section5.PublishedSection3Concrete
open Section6

def DensityInput (ν : Measure ℂ) : Prop :=
  Nonempty (HasBoundedDensityWithRespectTo (Measure.map id ν) (volume : Measure ℂ)) ∨
    (AtomDensityAlternative21 ν id ∧
      LivshytsProjectionFormalization.RealFiniteGeometricBrascampLieb)

def concreteModel
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (k d W : ℕ → ℕ) {c₀ C₀ : ℝ}
    (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (hwidth : ∀ n, d n + 2 = 2 * W n + 1) (hfit : ∀ n, 2 * W n + 1 ≤ k n + 1)
    (hMom : AtomMomentAssumption21 ν id) :
    PublishedSection3Model (sampleLaw ν) ν circularComplexGaussian (fun n => k n + 1) W c₀ C₀ :=
  publishedSection3ModelOfSamples (sampleLaw ν) ν circularComplexGaussian k d W profile hc₀
    hwidth hfit (fun n => samples ((k n + 1) * (d n + 2))) (fun n => denseSamples (k n + 1))
    (fun _n => samples_measurePreserving ν _) (fun _n => denseSamples_measurePreserving ν _)
    hMom gaussianMoments gaussianDensityAlternative

theorem concreteModel_sources
    (hBBV : BBVComparisonInput)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (k d W : ℕ → ℕ) {c₀ C₀ : ℝ}
    (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (hwidth : ∀ n, d n + 2 = 2 * W n + 1) (hfit : ∀ n, 2 * W n + 1 ≤ k n + 1)
    (hMom : AtomMomentAssumption21 ν id)
    (hM : Tendsto (fun n => k n + 1) atTop atTop) (hW : Tendsto W atTop atTop)
    (ω₀ : ℝ) (hω : 0 < ω₀ ∧ ω₀ < 1 / 9)
    (hband : ∀ n, (k n + 1 : ℝ) ^ v3BandwidthExponent ω₀ ≤ W n) (z : ℂ) :
    Nonempty ((concreteModel ν k d W profile hc₀ hwidth hfit hMom).Sources z) := by
  let D := concreteModel ν k d W profile hc₀ hwidth hfit hMom
  obtain ⟨C, _, hC⟩ := hBBV
  obtain ⟨χ, κ, τ, hparam⟩ := exists_hardEdgeAdmissible_of_omega hω.1
  obtain ⟨p, hp, hneg, hfull⟩ :=
    bc12_on_sampleLaw (provedGinibreInput hBBV) ν (fun n => k n + 1) (fun n => Nat.succ_pos _) hM z
  refine ⟨{
    comparisonConstant := C
    omega := ω₀
    chi := χ
    kappa := κ
    tau := τ
    K := C₀ ^ (1 / 8 : ℝ)
    p := p
    R := fun r => (r : ℝ) + (Real.sqrt (Real.exp 1) + 1)
    omega_range := hω
    parameters := hparam
    dimension_tendsto := hM
    bandwidth_tendsto := hW
    bandwidth_lower := by simpa only [Nat.cast_add, Nat.cast_one] using hband
    cutoff_constant := le_rfl
    radius_tendsto := tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    radius_lower := fun r => by have := Nat.cast_nonneg (α := ℝ) r; linarith
    bbvA := ?_
    bbvG := ?_
    negative_exponent_pos := hp
    bc12_negative := hneg
    bc12_full := hfull }⟩
  · intro n η hη
    exact canonicalBBVAt_mono
      (hC Sample ℂ (sampleLaw ν) ν (k n + 1) (Nat.succ_pos _)
        _ _ (cyclicVarianceProfile_isBandwidth (D.weights n) (D.fit n)) z η hη)
      (D.weights n).bandwidthParameter_pos hη (le_max_left _ _)
  · intro n u
    have hη : 0 < (spectralParameter u
        (localBulkHeight (v3BandwidthExponent ω₀ / 2) ((k n + 1 : ℕ) : ℝ))).im := by
      have hv : 0 < localBulkHeight (v3BandwidthExponent ω₀ / 2) ((k n + 1 : ℕ) : ℝ) := by
        unfold localBulkHeight
        positivity
      simpa [spectralParameter] using hv
    exact canonicalBBVAt_mono
      (hC Sample ℂ (sampleLaw ν) circularComplexGaussian (k n + 1) (Nat.succ_pos _)
        _ _ (denseVarianceProfile_isBandwidth (Nat.succ_pos _)) z _ hη)
      (by positivity) hη (le_max_left _ _)

def ringPotential (k d : ℕ) (center : Fin (d + 1)) (b : Fin (d + 2) → ℂ)
    (z : ℂ) (ω : Sample) : ℝ :=
  physicalLogPotential
    (literalIndicatorMatrix k d center b (samples ((k + 1) * (d + 2)) ω)) z

theorem ringPotential_limit_all
    (hBBV : BBVComparisonInput)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hMom : AtomMomentAssumption21 ν id)
    (hDensity : DensityInput ν)
    (k d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1)) {c₀ C₀ : ℝ}
    (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (hwidth : ∀ n, d n + 2 = 2 * W n + 1) (hcenter : ∀ n, (center n).val = W n)
    (hfit : ∀ n, 2 * W n + 1 ≤ k n + 1)
    (hM : Tendsto (fun n => k n + 1) atTop atTop) (hW : Tendsto W atTop atTop)
    (ω₀ : ℝ) (hω : 0 < ω₀ ∧ ω₀ < 1 / 9)
    (hband : ∀ n, (k n + 1 : ℝ) ^ v3BandwidthExponent ω₀ ≤ W n) (z : ℂ) :
    TendstoInProbabilityTri (fun _ => sampleLaw ν)
      (fun n => ringPotential (k n) (d n) (center n) (profile n).b z) (circularLogPotential z) := by
  let D := concreteModel ν k d W profile hc₀ hwidth hfit hMom
  obtain ⟨hS⟩ := concreteModel_sources hBBV ν k d W profile hc₀ hwidth hfit hMom
    hM hW ω₀ hω hband z
  have hlim : TendstoInProbabilityTri (fun _ => sampleLaw ν)
      (fun n ω => normalizedShiftLogDet (D.matrix n ω) z) (circularLogPotential z) := by
    rcases hDensity with hd | ⟨hd, hGBL⟩
    · exact hS.planar_tri D z (Classical.choice hd)
    · exact hS.density_tri D z hd hGBL
  apply hlim.congr _ rfl
  intro n ω
  exact (literalPhysicalLogPotential_eq_section3 (k n) (d n) (W n) (hwidth n)
    (center n) (hcenter n) (profile n) hc₀ (hfit n) _ z).symm

/-- The actual hypotheses need hold only eventually. Repeating the first valid
model at the finitely many earlier indices proves the all-index Section 3 input. -/
theorem ringPotential_limit
    (hBBV : BBVComparisonInput)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hMom : AtomMomentAssumption21 ν id)
    (hDensity : DensityInput ν)
    (k d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1)) {c₀ C₀ : ℝ}
    (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (hwidth : ∀ n, d n + 2 = 2 * W n + 1) (hcenter : ∀ n, (center n).val = W n)
    (hM : Tendsto (fun n => k n + 1) atTop atTop) (hW : Tendsto W atTop atTop)
    (ω₀ : ℝ) (hω : 0 < ω₀ ∧ ω₀ < 1 / 9)
    (hvalid : ∀ᶠ n in atTop, 2 * W n + 1 ≤ k n + 1 ∧
      (k n + 1 : ℝ) ^ v3BandwidthExponent ω₀ ≤ W n) (z : ℂ) :
    TendstoInProbabilityTri (fun _ => sampleLaw ν)
      (fun n => ringPotential (k n) (d n) (center n) (profile n).b z) (circularLogPotential z) := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 hvalid
  let r : ℕ → ℕ := fun n => max n K
  have hr : Tendsto r atTop atTop := by
    apply tendsto_atTop_mono (fun n => le_max_left n K) tendsto_id
  have hlim := ringPotential_limit_all hBBV ν hMom hDensity
    (fun n => k (r n)) (fun n => d (r n)) (fun n => W (r n))
    (fun n => center (r n)) (fun n => profile (r n)) hc₀
    (fun n => hwidth (r n)) (fun n => hcenter (r n))
    (fun n => (hK (r n) (le_max_right n K)).1) (hM.comp hr) (hW.comp hr)
    ω₀ hω (fun n => (hK (r n) (le_max_right n K)).2) z
  intro ε hε
  apply (hlim ε hε).congr'
  filter_upwards [eventually_ge_atTop K] with n hn
  let probability : ℕ → ℝ := fun j => (sampleLaw ν).real
    {ω | ε ≤ |ringPotential (k j) (d j) (center j) (profile j).b z ω - circularLogPotential z|}
  change probability (r n) = probability n
  exact congrArg probability (max_eq_left hn)

end CircularLawSections56.Section5.PublishedSection3Concrete
