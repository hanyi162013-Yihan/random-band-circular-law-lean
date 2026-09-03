import ShortRingAnchor.CyclicRealHighBandModel
import ShortRingAnchor.HighBandRealLSVProbability
import ShortRingAnchor.Theorem31CyclicPlanar

/-!
# Theorem 3.1 for the actual cyclic model: real-density branch

This module faithfully retains the upstream geometric Brascamp--Lieb
premise. It does not postulate any least-value, conditional projection,
matrix-law, or Hilbert--Schmidt probability estimate.
-/

open Filter MeasureTheory ProbabilityTheory HighBandLSV LivshytsProjectionFormalization
open scoped ENNReal Topology
noncomputable section
namespace ShortRingAnchor

/-- Manuscript Theorem 3.1 and the step before (3.10), real-density case,
under precisely the geometric BL premise of the copied real theorem. -/
theorem theorem31MinimumSingularValueInput_cyclic_real
    {Omega OmegaXi : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {M W : ℕ → ℕ} {c0 C0 beta chi kappa : ℝ}
    (weights : ∀ k, AdmissibleWeights (W k) c0 C0)
    (hfit : ∀ k, 2 * W k + 1 ≤ M k)
    (hMpos : ∀ k, 0 < M k) (hM : Tendsto M atTop atTop)
    (entry : ∀ k, Omega → Fin (M k) → BandOffset (W k) → ℂ)
    (atom : OmegaXi → ℂ) (hatom : AtomMomentAssumption21 nu atom)
    (hcopies : ∀ k, IndependentAtomCopies21 mu nu atom
      (fun is : Fin (M k) × BandOffset (W k) => fun sample => entry k sample is.1 is.2))
    (him : ∀ᵐ x ∂nu, (atom x).im = 0)
    (hdensity : HasBoundedDensityWithRespectTo
      (Measure.map (fun x => (atom x).re) nu) (volume : Measure ℝ))
    (hGBL : RealFiniteGeometricBrascampLieb)
    (hchi : 0 < chi) (hchibeta : 1 / 2 + chi < beta) (hbeta : beta ≤ 1) (hk : 0 < kappa)
    (hband : ∀ k, (M k : ℝ) ^ beta ≤ (W k : ℝ)) (z : ℂ) :
    ∃ good, Theorem31MinimumSingularValueInput hMpos mu
      (fun k => cyclicShortRingRandomMatrix (weights k) (hfit k) (entry k)) z
      (sourceHardEdgeScale M W kappa) good := by
  obtain ⟨rho, hrho, f, hf, hbound, hflaw⟩ := hdensity.exists_measurable_bounded_density
  letI : IsProbabilityMeasure (Measure.map (fun x => (atom x).re) nu) :=
    Measure.isProbabilityMeasure_map (Complex.measurable_re.comp hatom.measurable).aemeasurable
  have hint : ∫⁻ x, f x = 1 := by
    calc
      _ = (volume.withDensity f) Set.univ := by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      _ = 1 := by rw [hflaw]; exact measure_univ
  have hWpos (k) : 0 < W k := by
    have hn : (0 : ℝ) < M k := by exact_mod_cast hMpos k
    exact_mod_cast (Real.rpow_pos_of_pos hn beta).trans_le (hband k)
  let m := fun k => cyclicRealBandModel (weights k) (hfit k) (hWpos k) f hf hint hbound
  have hlaw (k) : IdentDistrib (cyclicShortRingRandomMatrix (weights k) (hfit k) (entry k))
      (m k).matrix mu (m k).law :=
    cyclicRealBandModel_matrix_identDistrib (weights k) (hfit k) (hWpos k)
      (entry k) atom hatom (hcopies k) him f hf hint hbound hflaw
  have hc : 0 < c0 / 3 := div_pos (weights 0).c0_pos (by norm_num)
  have hband' : ∀ᶠ k in atTop, (M k : ℝ) ^ (1 / 2 + chi) ≤ W k := by
    apply Eventually.of_forall
    intro k
    exact (Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ M k by exact_mod_cast hMpos k) hchibeta.le).trans (hband k)
  have hupper : ∀ᶠ k in atTop, (W k : ℝ) ≤ M k := by
    apply Eventually.of_forall
    intro k
    exact_mod_cast (show W k ≤ M k by have := hfit k; omega)
  apply theorem31MinimumInput_of_truncated_estimate hMpos hM _ z hk
    (D := 2 * Real.sqrt 2 * Real.exp 1 * rho / Real.sqrt (c0 / 3))
    (RingEntryMomentCopies21.centeredMatrixRowSecondMomentInputs weights hfit entry
      (ringEntryMomentCopies21_of_independentAtomCopies entry hatom hcopies))
  intro R hR
  filter_upwards [eventually_real_lsv_along_dimensions m hGBL hM hc hrho hchi
    (by linarith : chi ≤ 1 / 2) hk hR (norm_nonneg z)
    (Eventually.of_forall hWpos) hband' hupper] with k hb
  exact (highBand_strict_bad_le_of_identDistrib (hMpos k) (hlaw k) z _ R).trans
    (hb z le_rfl _ (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- Assumption 2.1 and Theorem 3.1: discharge the least-value interface for
either density branch. The BL premise is needed only when the real branch
is selected; the planar-only theorem has no such premise. -/
theorem theorem31MinimumSingularValueInput_cyclic_of_densityAlternative
    {Omega OmegaXi : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {M W : ℕ → ℕ} {c0 C0 beta chi kappa : ℝ}
    (weights : ∀ k, AdmissibleWeights (W k) c0 C0)
    (hfit : ∀ k, 2 * W k + 1 ≤ M k)
    (hMpos : ∀ k, 0 < M k) (hM : Tendsto M atTop atTop)
    (entry : ∀ k, Omega → Fin (M k) → BandOffset (W k) → ℂ)
    (atom : OmegaXi → ℂ) (hatom : AtomMomentAssumption21 nu atom)
    (hcopies : ∀ k, IndependentAtomCopies21 mu nu atom
      (fun is : Fin (M k) × BandOffset (W k) => fun sample => entry k sample is.1 is.2))
    (hdensity : AtomDensityAlternative21 nu atom) (hGBL : RealFiniteGeometricBrascampLieb)
    (hchi : 0 < chi) (hchibeta : 1 / 2 + chi < beta) (hbeta : beta ≤ 1) (hk : 0 < kappa)
    (hband : ∀ k, (M k : ℝ) ^ beta ≤ (W k : ℝ)) (z : ℂ) :
    ∃ good, Theorem31MinimumSingularValueInput hMpos mu
      (fun k => cyclicShortRingRandomMatrix (weights k) (hfit k) (entry k)) z
      (sourceHardEdgeScale M W kappa) good := by
  cases hdensity with
  | real him hd =>
    exact theorem31MinimumSingularValueInput_cyclic_real weights hfit hMpos hM entry atom hatom hcopies
      him hd hGBL hchi hchibeta hbeta hk hband z
  | complex hd =>
    exact theorem31MinimumSingularValueInput_cyclic_planar weights hfit hMpos hM entry atom hatom hcopies
      hd hchi hchibeta hbeta hk hband z

end ShortRingAnchor
