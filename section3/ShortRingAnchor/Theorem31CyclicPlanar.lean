import ShortRingAnchor.CyclicPlanarHighBandModel
import ShortRingAnchor.HighBandLSVProbability

/-!
# Theorem 3.1 for the manuscript's actual cyclic model: planar-density branch

The probabilistic least-value theorem is reused from the user's published
high-band project. The present proof only builds its profile and product
law, transfers the event, substitutes `t=M^-2`, and removes the HS cutoff.
There is no external least-value or projection premise in this branch.
-/

open Filter MeasureTheory ProbabilityTheory HighBandLSV
open scoped ENNReal Topology
noncomputable section
namespace ShortRingAnchor

/-- Manuscript Theorem 3.1 and the step before (3.10), planar-density case.
All inputs are source atom/model assumptions and bandwidth growth; the
least-singular-value estimate is called from the copied, proved theorem. -/
theorem theorem31MinimumSingularValueInput_cyclic_planar
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
    (hdensity : HasBoundedDensityWithRespectTo (Measure.map atom nu) (volume : Measure ℂ))
    (hchi : 0 < chi) (hchibeta : 1 / 2 + chi < beta) (hbeta : beta ≤ 1) (hk : 0 < kappa)
    (hband : ∀ k, (M k : ℝ) ^ beta ≤ (W k : ℝ)) (z : ℂ) :
    ∃ good, Theorem31MinimumSingularValueInput hMpos mu
      (fun k => cyclicShortRingRandomMatrix (weights k) (hfit k) (entry k)) z
      (sourceHardEdgeScale M W kappa) good := by
  obtain ⟨L, hL, hd⟩ := hdensity.exists_pos_measure_le
  letI : IsProbabilityMeasure (Measure.map atom nu) := Measure.isProbabilityMeasure_map hatom.measurable.aemeasurable
  have hWpos (k) : 0 < W k := by
    have hn : (0 : ℝ) < M k := by exact_mod_cast hMpos k
    exact_mod_cast (Real.rpow_pos_of_pos hn beta).trans_le (hband k)
  let m := fun k => cyclicPlanarBandModel (weights k) (hfit k) (hWpos k) (Measure.map atom nu) hd
  have hlaw (k) : IdentDistrib (cyclicShortRingRandomMatrix (weights k) (hfit k) (entry k))
      (m k).matrix mu (m k).law :=
    cyclicPlanarBandModel_matrix_identDistrib (weights k) (hfit k) (hWpos k)
      (entry k) atom hatom (hcopies k) hd
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
    (D := Real.sqrt (Real.pi * L / (c0 / 3)))
    (RingEntryMomentCopies21.centeredMatrixRowSecondMomentInputs weights hfit entry
      (ringEntryMomentCopies21_of_independentAtomCopies entry hatom hcopies))
  intro R hR
  filter_upwards [eventually_planar_lsv_along_dimensions m hM hc hL.le hchi
    (by linarith : chi ≤ 1 / 2) hk hR (norm_nonneg z)
    (Eventually.of_forall hWpos) hband' hupper] with k hb
  exact (highBand_strict_bad_le_of_identDistrib (hMpos k) (hlaw k) z _ R).trans
    (hb z le_rfl _ (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end ShortRingAnchor
