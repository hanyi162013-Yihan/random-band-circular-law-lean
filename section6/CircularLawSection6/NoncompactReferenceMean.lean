import CircularLawSection6.GinibreIteratedCutoff
import CircularLawSection6.ReferenceCutoffSqueeze
import CircularLawSection6.UnitCoreUpperSandwich
import CircularLawSection6.FourthRootNormalizationError
import CircularLawSection6.PotentialContinuity

/-! # Actual noncompact-profile mean from finite-reference inputs

All tail, normalization, integrability and iterated-cutoff estimates are
discharged for the literal Gaussian profile. Two compact-core inputs remain
visible: the Section 5 raw-core mean consequence and the fixed-cutoff
comparison to finite Ginibre. Subsequent adapters can discharge these
without changing this analytic assembly.
-/

open MeasureTheory Filter Topology
open CircularLawSections56.Section5 CircularLawSections56.Section6

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

def referenceCoreCutoff (p : NoncompactProfile) (R : ℕ) : ℝ :=
  fourthRoot (p.limitingTailMass (R + 1))

theorem referenceCoreCutoff_pos (p : NoncompactProfile) (R : ℕ) : 0 < p.referenceCoreCutoff R :=
  fourthRoot_pos (p.limitingTailMass_pos (R + 1))

theorem referenceCoreCutoff_le_one (p : NoncompactProfile) (R : ℕ) : p.referenceCoreCutoff R ≤ 1 := by
  simpa only [referenceCoreCutoff, Nat.cast_add, Nat.cast_one] using p.limitingTail_fourthRoot_le_one (R + 1)

theorem referenceCoreCutoff_tendsto_zero (p : NoncompactProfile) :
    Tendsto p.referenceCoreCutoff atTop (𝓝 0) := by
  change Tendsto (fun R : ℕ => Real.sqrt (Real.sqrt (p.limitingTailMass (R + 1)))) atTop (𝓝 0)
  have ht := p.limitingTailMass_integral_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  simpa only [Nat.cast_add, Nat.cast_one,
    Real.sqrt_zero, Function.comp_apply] using ht.sqrt.sqrt

theorem sparse_profile_mean_of_core_and_reference_inputs (p : NoncompactProfile)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (N n : ℝ)) atTop (𝓝 0))
    (hCore : ∀ R : ℕ, ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => (∫ ω, p.rawCoreLogDet (N n) ⌊(R + 1 : ℝ) * W n⌋₊ (W n) z ω
        ∂gaussianProfileLaw (N n)) / (N n : ℝ)) atTop
        (𝓝 (varianceScaledRadialPotential (p.limitingCoreMass (R + 1)) ‖z‖)))
    (hComparison : ∀ R : ℕ, ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n =>
        (∫ ω, matrixCutoffPotential (p.unitCoreMatrix (N n) ⌊(R + 1 : ℝ) * W n⌋₊ (W n) ω - z • 1)
          (p.referenceCoreCutoff R) ∂gaussianProfileLaw (N n)) -
        ∫ ω, matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) (p.referenceCoreCutoff R)
          ∂cyclicAtomLaw (N n) circularComplexGaussian) atTop (𝓝 0))
    (hGinibre : ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbabilityTri (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
        (fun n ω => matrixRawPotential (ginibreMatrix (N n) ω - z • 1)) (circularRadialPotential ‖z‖))
    (hNegative : ∀ᵐ z ∂(volume : Measure ℂ), ∃ q : ℝ, 0 < q ∧ BC12GinibreNegativeMomentTightnessTri N z q) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => (∫ ω, p.rawProfileLogDet (N n) (W n) z ω ∂gaussianProfileLaw (N n)) / (N n : ℝ))
        atTop (𝓝 (circularRadialPotential ‖z‖)) := by
  have hmass (R : ℕ) : Tendsto (fun n => p.coreMass (N n) ⌊(R + 1 : ℝ) * W n⌋₊ (W n))
      atTop (𝓝 (p.limitingCoreMass (R + 1))) :=
    p.coreMass_tendsto_sparse N hN W hW hWlim hsparse (by positivity)
  have htail (R : ℕ) : Tendsto (fun n => p.tailMass (N n) ⌊(R + 1 : ℝ) * W n⌋₊ (W n))
      atTop (𝓝 (p.limitingTailMass (R + 1))) := by
    rw [p.limitingTailMass_eq_one_sub (by positivity : (0 : ℝ) ≤ R + 1)]
    exact p.tailMass_tendsto_sparse N hN W hW hWlim hsparse (by positivity)
  have herror (R : ℕ) : Tendsto (fun n =>
      (Real.sqrt (p.tailMass (N n) ⌊(R + 1 : ℝ) * W n⌋₊ (W n)) +
        |Real.sqrt (p.coreMass (N n) ⌊(R + 1 : ℝ) * W n⌋₊ (W n)) - 1|) / p.referenceCoreCutoff R)
      atTop (𝓝 (p.unitCoreReferenceErrorLimit (R + 1))) := by
    simpa only [unitCoreReferenceErrorLimit, referenceCoreCutoff, Nat.cast_add, Nat.cast_one] using
      ((htail R).sqrt.add ((hmass R).sqrt.sub tendsto_const_nhds).abs).div_const (p.referenceCoreCutoff R)
  have herror0 : Tendsto (fun R => p.unitCoreReferenceErrorLimit (R + 1)) atTop (𝓝 0) :=
    p.unitCoreReferenceErrorLimit_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  filter_upwards [ae_all_iff.2 hCore, ae_all_iff.2 hComparison, hGinibre, hNegative,
    p.gaussian_expected_unitCore_upper_triangular N W, ginibre_iterated_cutoff_error_ae N hN]
    with z hc hcmp hg hneg hsand hcut
  obtain ⟨q, hq, hn⟩ := hneg
  have htarget : Tendsto (fun R : ℕ =>
      varianceScaledRadialPotential (p.limitingCoreMass (R + 1)) ‖z‖)
      atTop (𝓝 (circularRadialPotential ‖z‖)) := by
    simpa only [limitingCoreMass, Nat.cast_add, Nat.cast_one, Function.comp_apply] using
      varianceScaledRadialPotential_tendsto_one
        (p.limitingCoreMass_tendsto_one.comp (tendsto_add_atTop_nat 1)) ‖z‖
  apply mean_tendsto_of_reference_cutoff_squeeze _ _ _ _ _ _ _ _ (circularRadialPotential ‖z‖)
    (fun R => Eventually.of_forall fun n =>
      (hsand n ⌊(R + 1 : ℝ) * W n⌋₊ (p.referenceCoreCutoff R) (p.referenceCoreCutoff_pos R)).1)
    (fun R => Eventually.of_forall fun n =>
      (hsand n ⌊(R + 1 : ℝ) * W n⌋₊ (p.referenceCoreCutoff R) (p.referenceCoreCutoff_pos R)).2)
    hc htarget (ginibre_raw_mean_of_probability N hN z hg) hcmp herror herror0
  exact hcut _ hg q hq hn p.referenceCoreCutoff p.referenceCoreCutoff_pos
    p.referenceCoreCutoff_le_one p.referenceCoreCutoff_tendsto_zero

end CircularLawSection6.NoncompactProfile
