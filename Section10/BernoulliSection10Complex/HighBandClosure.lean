import BernoulliSection10Complex.DensityCircularLaw

/-!
# Section 10 closure from its proved high-band anchor

This is an internal composition lemma, not the final caller-facing theorem.
The source-connected endpoint must construct `HighBandLogLimit` from the
repository's Section 3 proofs. Factoring here avoids asking that endpoint to
construct unused, stronger versions of all four historical `Section3Inputs`
fields. None of the stable conditional theorems is changed.
-/

open Filter MeasureTheory Set Topology
noncomputable section
namespace BernoulliSection10Complex
open BernoulliSection10

open SourceInputs ShortRingAnchor ProbabilityLimits Replacement DiskReference TaoVuReplacement

set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Internal Proposition 10.1 conclusion. The final source adapter proves this;
it is not an additional literature assumption. -/
def HighBandLogLimit (μ : Measure ℂ) : Prop :=
  ∀ (W s : ℕ → ℕ), (∀ n, 0 < W n) → Tendsto W atTop atTop →
  ∀ ω : ℝ, 0 < ω → ω < 1 / 9 →
  (∀ᶠ n in atTop, (((s n + 3) * W n : ℕ) : ℝ) ^ (8 / 9 + ω) ≤ W n) →
  ∀ z : ℂ, ConvergesInProbability (inputLaw μ)
    (fun n sample => normalizedShiftLogDet
      (profileMatrix (physicalProfile (W n) (s n)) sample) z)
    (circularLogPotential z)

theorem density_high_band_ring_log_limit_of_highBand
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (hHighBand : HighBandLogLimit μ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (ω : ℝ) (hω : 0 < ω) (hω1 : ω < 1 / 9)
    (hhigh : ∀ᶠ n in atTop, (((s n + 3) * W n : ℕ) : ℝ) ^ (8 / 9 + ω) ≤ W n)
    (z : ℂ) :
    letI := hμ.toIsProbabilityMeasure
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) μ)
      (fun n x => densityCyclicLogDet (W n) (s n) z x / (((s n + 3) * W n : ℕ) : ℝ))
      (circularLogPotential z) := by
  letI := hμ.toIsProbabilityMeasure
  exact (profile_log_converges_iff_physical_rows μ W s z (circularLogPotential z)).mp
    (hHighBand W s hW hWtop ω hω hω1 hhigh z)

theorem densityCorePressureDensity_limit_of_highBand
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (hHighBand : HighBandLogLimit μ)
    (W : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop) (z : ℂ) :
    Tendsto (fun n => densityCorePressureDensity μ (W n) z) atTop
      (𝓝 (circularLogPotential z)) := by
  letI := hμ.toIsProbabilityMeasure
  have hhigh := hWtop.eventually eventually_density_anchor_highBand
  have hrows := density_high_band_ring_log_limit_of_highBand hμ hHighBand W
    (fun n => densityCoreSites (W n)) hW hWtop (1 / 20)
    (by norm_num) (by norm_num) hhigh z
  exact densityCorePressureDensity_tendsto_of_anchor hμ W hW hWtop z
    (circularLogPotential z) hrows

theorem density_long_ring_log_limit_of_highBand
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (hHighBand : HighBandLogLimit μ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, (W n : ℝ) ^ (101 / 100 : ℝ) ≤ ((s n + 3) * W n : ℕ))
    (z : ℂ) :
    letI := hμ.toIsProbabilityMeasure
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) μ)
      (fun n x => densityCyclicLogDet (W n) (s n) z x / (((s n + 3) * W n : ℕ) : ℝ))
      (circularLogPotential z) := by
  letI := hμ.toIsProbabilityMeasure
  let N := fun n => (s n + 3) * W n
  let K := fun n => densityCellCount (s n + 3) (W n)
  let q := fun n => densityRemainderSites (s n + 3) (W n)
  have hs (n : ℕ) : K n * densityCellSites (W n) + q n = s n :=
    Nat.add_right_cancel (densityCell_partition (m := s n + 3) (by omega) (W n))
  have herror := tendsto_cyclicStitchedPressureError_div L z W K q N hWtop
    (Eventually.of_forall fun n => (densityRemainderSites_lt (s n + 3) (W n)).le)
    (Eventually.of_forall fun n => by rw [hs n]) hlong
  have hratio := tendsto_densityCell_dimension_ratio (m := fun n => s n + 3) hWtop
    (Eventually.of_forall fun _ => by omega) (by simpa only [Nat.cast_mul] using hlong)
  have hcore := densityCorePressureDensity_limit_of_highBand hμ hHighBand W hW hWtop z
  have he (n : ℕ) :
      ((K n : ℝ) * densityAnchorSize (W n) / (((s n + 3 : ℕ) : ℝ) * W n)) *
        densityCorePressureDensity μ (W n) z =
      (K n : ℝ) * densityMaxCorePressure μ (W n) z / (N n : ℝ) := by
    have hne : (densityAnchorSize (W n) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (densityAnchorSize_pos (hW n)).ne'
    simp only [densityCorePressureDensity, N, Nat.cast_mul]
    field_simp
  have hcenter : Tendsto
      (fun n => (K n : ℝ) * densityMaxCorePressure μ (W n) z / (N n : ℝ))
      atTop (𝓝 (circularLogPotential z)) := by
    have hproduct : Tendsto
        (fun n => ((K n : ℝ) * densityAnchorSize (W n) /
          (((s n + 3 : ℕ) : ℝ) * W n)) * densityCorePressureDensity μ (W n) z)
        atTop (𝓝 (circularLogPotential z)) := by
      simpa only [one_mul] using hratio.mul hcore
    exact hproduct.congr (fun n => he n)
  apply tendstoInProbabilityTri_of_center_tendsto_and_L1_close
    (fun n => intervalRowsLaw (W n) (s n + 3) μ)
    (fun n x => densityCyclicLogDet (W n) (s n) z x / (N n : ℝ))
    (fun n => (K n : ℝ) * densityMaxCorePressure μ (W n) z / (N n : ℝ))
    (fun n => cyclicStitchedPressureError L (W n) (K n) (q n) z / (N n : ℝ))
    (circularLogPotential z) hcenter
  · intro n
    exact (((densityCyclicLogDet_integrable hμ (W n) (s n) (hW n) z).div_const _).sub
      (integrable_const _)).abs
  · intro n
    have hbound (t : ℕ) (ht : K n * densityCellSites (W n) + q n = t) :
        (∫ x : IntervalRows (W n) (t + 3),
          |densityCyclicLogDet (W n) t z x / (((t + 3) * W n : ℕ) : ℝ) -
            (K n : ℝ) * densityMaxCorePressure μ (W n) z /
              (((t + 3) * W n : ℕ) : ℝ)| ∂intervalRowsLaw (W n) (t + 3) μ) ≤
          cyclicStitchedPressureError L (W n) (K n) (q n) z /
            (((t + 3) * W n : ℕ) : ℝ) := by
      subst t
      exact cyclicStitchedPressure_normalized_L1_bound hμ (W n) (K n) (q n) (hW n) z
    exact hbound (s n) (hs n)
  · exact herror

theorem density_long_profile_log_limit_of_highBand
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (hHighBand : HighBandLogLimit μ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, (W n : ℝ) ^ (101 / 100 : ℝ) ≤ ((s n + 3) * W n : ℕ))
    (z : ℂ) :
    ConvergesInProbability (inputLaw μ)
      (fun n ω => normalizedShiftLogDet (profileMatrix (physicalProfile (W n) (s n)) ω) z)
      (circularLogPotential z) := by
  letI := hμ.toIsProbabilityMeasure
  exact (profile_log_converges_iff_physical_rows μ W s z _).mpr
    (density_long_ring_log_limit_of_highBand hμ hHighBand W s hW hWtop hlong z)

theorem density_profile_log_limit_of_highBand
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (hHighBand : HighBandLogLimit μ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (z : ℂ) :
    ConvergesInProbability (inputLaw μ)
      (fun n ω => normalizedShiftLogDet (profileMatrix (physicalProfile (W n) (s n)) ω) z)
      (circularLogPotential z) := by
  classical
  have hshort := hHighBand W
    (fun n => densityDirectAuxSites (W n) (s n)) hW hWtop (1 / 20)
    (by norm_num) (by norm_num) (densityDirectAuxSites_highBand W s hW hWtop) z
  have hlong := density_long_profile_log_limit_of_highBand hμ hHighBand W
    (fun n => densityLongAuxSites (W n) (s n)) hW hWtop
    (Eventually.of_forall fun n => densityLongAuxSites_long (W n) (s n) (hW n)) z
  rw [convergesInProbability_iff_norm] at hshort hlong ⊢
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using (hshort ε hε).add (hlong ε hε))
    (fun _ => zero_le)
  intro n
  apply (measure_mono ?_).trans (measure_union_le _ _)
  intro sample hsample
  have hsame (t : ℕ) (ht : t = s n) :
      ε ≤ ‖normalizedShiftLogDet (profileMatrix (physicalProfile (W n) t) sample) z -
        circularLogPotential z‖ := by
    subst t
    exact hsample
  by_cases h : densityDirectCondition (W n) (s n)
  · apply Or.inl
    exact hsame (densityDirectAuxSites (W n) (s n)) (by simp [densityDirectAuxSites, h])
  · apply Or.inr
    exact hsame (densityLongAuxSites (W n) (s n)) (by simp [densityLongAuxSites, h])

/-- The same result for the literal finite physical-row probability spaces;
there is no infinite-array or auxiliary-Gaussian premise on the caller. -/
theorem density_ring_log_limit_of_highBand
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (hHighBand : HighBandLogLimit μ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (z : ℂ) :
    letI := hμ.toIsProbabilityMeasure
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) μ)
      (fun n x => densityCyclicLogDet (W n) (s n) z x / (((s n + 3) * W n : ℕ) : ℝ))
      (circularLogPotential z) := by
  letI := hμ.toIsProbabilityMeasure
  exact (profile_log_converges_iff_physical_rows μ W s z _).mp
    (density_profile_log_limit_of_highBand hμ hHighBand W s hW hWtop z)

theorem density_profile_circular_law_of_highBand
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (hHighBand : HighBandLogLimit μ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (f : BoundedContinuousFunction ℂ ℝ) :
    TendstoInMeasure (inputLaw μ)
      (fun n ω => realEsdTest (profileMatrix (physicalProfile (W n) (s n)) ω) f) atTop
      (fun _ => ∫ z, f z ∂circularMeasure) := by
  letI := hμ.toIsProbabilityMeasure
  let N := fun n => (s n + 3) * W n
  have hN (n : ℕ) : 0 < N n := Nat.mul_pos (by omega) (hW n)
  letI (n : ℕ) : Nonempty (Fin (N n)) := ⟨⟨0, hN n⟩⟩
  have hNtop : Tendsto N atTop atTop :=
    tendsto_atTop_mono' atTop
      (Eventually.of_forall fun n => Nat.le_mul_of_pos_left (W n) (by omega)) hWtop
  let σ := fun n => physicalProfile (W n) (s n)
  let X := fun n ω => positiveMatrixIndex (hN n) (profileMatrix (σ n) ω)
  have hX : ∀ n i j, Measurable (fun ω => X n ω i j) := fun n i j =>
    measurable_positiveMatrixIndex_entry (hN n) (profileMatrix (σ n))
      (measurable_profileMatrix_entry (σ n)) i j
  have hXi (n : ℕ) : Integrable (fun ω => physicalEnergy (X n ω)) (inputLaw μ) := by
    simp only [X, positiveMatrixIndex_energy]
    exact (profileMatrix_energy_integrable hμ (σ n)).div_const _
  have hXm (n : ℕ) : (∫ ω, physicalEnergy (X n ω) ∂inputLaw μ) ≤ 1 := by
    simp only [X, positiveMatrixIndex_energy]
    rw [integral_div, integral_profileMatrix_energy hμ (σ n)
      (physicalProfile_doublyStochastic (W n) (s n) (hW n)),
      div_self (Nat.cast_ne_zero.mpr (hN n).ne')]
  have hXlog : ∀ᵐ z ∂(volume : Measure ℂ), TendstoInMeasure (inputLaw μ)
      (fun n ω => physicalLogPotential (X n ω) z) atTop (fun _ => circularLogPotential z) := by
    apply ae_of_all
    intro z
    simpa only [X, positiveMatrixIndex_log, σ, ShortRingAnchor.ConvergesInProbability] using
      density_profile_log_limit_of_highBand hμ hHighBand W s hW hWtop z
  have hcompact := physical_circularLaw_of_logPotential (inputLaw μ)
    (fun n => N n - 1) (tendsto_pred_dimension hNtop) X hX 1 (by norm_num) hXi hXm hXlog
  apply circularLaw_boundedContinuousMap_of_compactSupport (inputLaw μ)
    (fun n ω => profileMatrix (σ n) ω) _ f
  intro g hg hgc
  simpa only [X, positiveMatrixIndex_esd] using hcompact g hg hgc

/-- Theorem 2.10, planar-complex-IID bounded-density finite-third-moment branch,
for the actual normalized cyclic full-block matrices. -/
theorem density_circular_law_of_highBand
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (hHighBand : HighBandLogLimit μ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (f : BoundedContinuousFunction ℂ ℝ) :
    TendstoInMeasure (Measure.infinitePi fun _ : ℕ => μ)
      (fun n ω => realEsdTest
        (densityCyclicMatrix (W n) (s n) (physicalRowsFromSequence (W n) (s n) ω)) f)
      atTop (fun _ => ∫ z, f z ∂circularMeasure) := by
  letI := hμ.toIsProbabilityMeasure
  have h := density_profile_circular_law_of_highBand hμ hHighBand W s hW hWtop f
  apply (tendstoInMeasure_prod_fst_iff
    (Measure.infinitePi fun _ : ℕ => μ)
    (Measure.infinitePi fun _ : ℕ => circularGaussianPairLaw)
    (fun n ω => realEsdTest
      (densityCyclicMatrix (W n) (s n) (physicalRowsFromSequence (W n) (s n) ω)) f)
    (∫ z, f z ∂circularMeasure)).mp
  simpa only [← densityCyclicMatrix_physicalRowsFromInput, physicalRowsFromInput, inputLaw] using h

end BernoulliSection10Complex

