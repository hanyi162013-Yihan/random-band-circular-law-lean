import CircularLawSection6.NoncompactReferenceMean
import CircularLawSection6.GaussianSandwichPointwise
import CircularLawSection6.FinitePrefixCoreBridgePointwise
import CircularLawSection6.CanonicalCoreComparisonPointwise
import CircularLawSection6.GinibreBBVLogPotential

/-! # Fixed-shift sparse Gaussian-profile mean

This is the pointwise reconstruction of the Section 6 analytic squeeze.  The
compact raw mean comes from the fixed-`z` Section 5 endpoint, the positive-cutoff
core comparison is extended from its full-measure set by Lipschitz continuity,
and the Ginibre raw/cutoff inputs are the proved pointwise BBV consequences.
-/

open MeasureTheory Filter Topology
open CircularLawSections56.Section5 CircularLawSections56.Section6
open CircularLawSections56.Section5.PublishedSection3Concrete (BBVComparisonInput)

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem ginibre_iterated_cutoff_error_of_bbv_at (hBBV : BBVComparisonInput)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop) (z : ℂ)
    (a : ℕ → ℝ) (ha : ∀ R, 0 < a R) (ha1 : ∀ R, a R ≤ 1)
    (ha0 : Tendsto a atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ R in atTop, ∀ᶠ n in atTop,
      (∫ ω, matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) (a R)
        ∂cyclicAtomLaw (N n) circularComplexGaussian) ≤
      (∫ ω, matrixRawPotential (ginibreMatrix (N n) ω - z • 1)
        ∂cyclicAtomLaw (N n) circularComplexGaussian) + ε := by
  intro ε hε
  have hL1 := ginibre_iterated_lowerCutoff_L1_of_bbv hBBV N hN z a ha ha1 ha0 ε hε
  filter_upwards [hL1] with R hR
  filter_upwards [hR] with n hn
  have hiRaw := (ginibre_raw_memLp (N n) z).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  have hiCut := integrable_matrixCutoffPotential
    (cyclicAtomLaw (N n) circularComplexGaussian)
    (fun ω => ginibreMatrix (N n) ω - z • 1)
    ((ginibreMatrix_measurable (N n)).sub measurable_const)
    (ginibre_shifted_det_ne_zero (N n) z)
    (ginibre_shifted_expected_energy (N n) z).1 (ha R)
  have hbound := (le_abs_self (∫ ω,
    matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) (a R) -
      matrixRawPotential (ginibreMatrix (N n) ω - z • 1)
    ∂cyclicAtomLaw (N n) circularComplexGaussian)).trans abs_integral_le_integral_abs
  rw [integral_sub hiCut hiRaw] at hbound
  linarith

namespace NoncompactProfile

theorem sparse_profile_mean_of_bbv_section5_at (p : NoncompactProfile)
    (hBBV : BBVComparisonInput)
    (size : ℕ → ℕ) (hsize : Tendsto (fun n => size n + 2) atTop atTop)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (size n + 2 : ℕ)) atTop (𝓝 0))
    (hSection5 : ∀ R : ℕ, p.CanonicalCoreSection5InputPointwise size W (R + 1))
    (z : ℂ) :
    Tendsto (fun n => (∫ ω, p.rawProfileLogDet (size n + 2) (W n) z ω
      ∂gaussianProfileLaw (size n + 2)) / (size n + 2 : ℕ)) atTop
      (𝓝 (circularRadialPotential ‖z‖)) := by
  let N := fun n => size n + 2
  let a := p.referenceCoreCutoff
  have hmass (R : ℕ) : Tendsto
      (fun n => p.coreMass (N n) ⌊(R + 1 : ℝ) * W n⌋₊ (W n))
      atTop (𝓝 (p.limitingCoreMass (R + 1))) :=
    p.coreMass_tendsto_sparse N hsize W hW hWlim hsparse (by positivity)
  have htail (R : ℕ) : Tendsto
      (fun n => p.tailMass (N n) ⌊(R + 1 : ℝ) * W n⌋₊ (W n))
      atTop (𝓝 (p.limitingTailMass (R + 1))) := by
    rw [p.limitingTailMass_eq_one_sub (by positivity : (0 : ℝ) ≤ R + 1)]
    exact p.tailMass_tendsto_sparse N hsize W hW hWlim hsparse (by positivity)
  have herror (R : ℕ) : Tendsto (fun n =>
      (Real.sqrt (p.tailMass (N n) ⌊(R + 1 : ℝ) * W n⌋₊ (W n)) +
        |Real.sqrt (p.coreMass (N n) ⌊(R + 1 : ℝ) * W n⌋₊ (W n)) - 1|) / a R)
      atTop (𝓝 (p.unitCoreReferenceErrorLimit (R + 1))) := by
    simpa only [unitCoreReferenceErrorLimit, a, referenceCoreCutoff,
      Nat.cast_add, Nat.cast_one] using
      ((htail R).sqrt.add ((hmass R).sqrt.sub tendsto_const_nhds).abs).div_const (a R)
  have herror0 : Tendsto (fun R => p.unitCoreReferenceErrorLimit (R + 1))
      atTop (𝓝 0) :=
    p.unitCoreReferenceErrorLimit_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  have htarget : Tendsto (fun R : ℕ =>
      varianceScaledRadialPotential (p.limitingCoreMass (R + 1)) ‖z‖)
      atTop (𝓝 (circularRadialPotential ‖z‖)) := by
    simpa only [limitingCoreMass, Nat.cast_add, Nat.cast_one, Function.comp_apply] using
      varianceScaledRadialPotential_tendsto_one
        (p.limitingCoreMass_tendsto_one.comp (tendsto_add_atTop_nat 1)) ‖z‖
  apply mean_tendsto_of_reference_cutoff_squeeze _ _ _ _ _ _ _ _
    (circularRadialPotential ‖z‖)
    (fun R => Eventually.of_forall fun n =>
      (p.gaussian_expected_unitCore_upper_at (N n)
        ⌊(R + 1 : ℝ) * W n⌋₊ (W n) z (p.referenceCoreCutoff_pos R)).1)
    (fun R => Eventually.of_forall fun n =>
      (p.gaussian_expected_unitCore_upper_at (N n)
        ⌊(R + 1 : ℝ) * W n⌋₊ (W n) z (p.referenceCoreCutoff_pos R)).2)
    (fun R => p.canonical_core_raw_mean_of_eventual_section5_at size hsize W hW hWlim
      hsparse (by positivity) (hSection5 R) z)
    htarget
    (by simpa only [ShortRingAnchor.circularLogPotential, circularRadialPotential] using
      ginibre_raw_mean_of_bbv hBBV N hsize z)
    (fun R => CoreRadiusBounds.canonical_core_cutoff_comparison_of_bbv_at
      (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1))
      hBBV N hsize W hW hWlim hsparse (by positivity) (p.referenceCoreCutoff_pos R) z)
    herror herror0
  exact ginibre_iterated_cutoff_error_of_bbv_at hBBV N hsize z a
    p.referenceCoreCutoff_pos p.referenceCoreCutoff_le_one p.referenceCoreCutoff_tendsto_zero

theorem sparse_profile_probability_of_bbv_section5_at (p : NoncompactProfile)
    (hBBV : BBVComparisonInput)
    (size : ℕ → ℕ) (hsize : Tendsto (fun n => size n + 2) atTop atTop)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (size n + 2 : ℕ)) atTop (𝓝 0))
    (hSection5 : ∀ R : ℕ, p.CanonicalCoreSection5InputPointwise size W (R + 1))
    (z : ℂ) :
    TendstoInProbabilityTri (fun n => gaussianProfileLaw (size n + 2))
      (fun n ω => matrixRawPotential (p.matrix (size n + 2) (W n) ω - z • 1))
      (circularRadialPotential ‖z‖) :=
  p.full_profile_probability_of_mean (fun n => size n + 2) hsize W z
    (p.sparse_profile_mean_of_bbv_section5_at hBBV size hsize W hW hWlim
      hsparse hSection5 z)

end NoncompactProfile
end CircularLawSection6
