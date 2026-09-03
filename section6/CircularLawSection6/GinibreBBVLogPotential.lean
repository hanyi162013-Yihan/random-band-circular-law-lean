import CircularLawSection6.GinibreRegularizedMean
import CircularLawSection6.GinibrePointwiseMoments
import CircularLawSection6.RegularizedMeanRemoval
import CircularLawSection6.GinibreReducedSources

/-! # The actual Ginibre logarithmic potential from BBV alone

The positive-height expected limit is anchored at infinity. Its height-zero
limit is identified with the circular potential. Tight negative moments and
Gaussian concentration supply the uniform logarithmic moments needed to
remove the cutoff before identifying the raw mean. Concentration then gives
the raw probability limit, transported to the original common Gaussian law.

Every statement holds at each fixed complex shift, not merely almost every
shift. No Ginibre logarithmic-potential or circular-law conclusion is assumed.
-/

open MeasureTheory Filter Topology TaoVuReplacement ShortRingAnchor
open CircularLawSections56.Section5 CircularLawSections56.Section6
open CircularLawSections56.Section5.PublishedSection3Concrete
  (BBVComparisonInput gaussianSequenceLaw ginibreOnSequence)

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem ginibre_raw_mean_of_bbv (hBBV : BBVComparisonInput)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop) (z : ℂ) :
    Tendsto (fun n => ∫ ω, matrixRawPotential (ginibreMatrix (N n) ω - z • 1)
      ∂cyclicAtomLaw (N n) circularComplexGaussian) atTop (𝓝 (circularLogPotential z)) := by
  let a : ℕ → ℝ := fun k => 1 / (k + 1 : ℝ)
  have ha (k : ℕ) : 0 < a k := by dsimp only [a]; positivity
  have ha1 (k : ℕ) : a k ≤ 1 := by
    dsimp only [a]
    exact (div_le_one (by positivity : (0 : ℝ) < k + 1)).2
      (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht0 : Tendsto (fun k => a k ^ 2) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, Eventually.of_forall fun k => sq_pos_of_pos (ha k)⟩
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using ha0.pow 2
  have hc := (GinibreDyson.tendsto_dysonPotential_nhdsGT_zero z).comp ht0
  change Tendsto (fun k => GinibreDyson.dysonPotential z (a k ^ 2))
    atTop (𝓝 (circularLogPotential z)) at hc
  apply matrixRaw_mean_of_regularized_mean_limits
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
    (fun n ω => ginibreMatrix (N n) ω - z • 1)
    (fun n => (ginibreMatrix_measurable (N n)).sub measurable_const)
    (fun n => ginibre_shifted_det_ne_zero (N n) z)
    (fun n => (ginibre_shifted_expected_energy (N n) z).1)
    (fun n => (ginibre_raw_memLp (N n) z).integrable (by norm_num))
    a (fun k => GinibreDyson.dysonPotential z (a k ^ 2)) (circularLogPotential z)
    ha ha0 hc
    (fun k => GinibreBBV.ginibre_cyclic_regularizedMean_tendsto_of_bbv hBBV N hN z
      (sq_pos_of_pos (ha k)))
  exact ginibre_iterated_lowerCutoff_L1_of_bbv hBBV N hN z a ha ha1 ha0

theorem ginibre_raw_probability_of_bbv (hBBV : BBVComparisonInput)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop) (z : ℂ) :
    TendstoInProbabilityTri (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
      (fun n ω => matrixRawPotential (ginibreMatrix (N n) ω - z • 1))
      (circularLogPotential z) := by
  have hc := ginibre_raw_centered_tendsto N hN z
  have hm := tendstoInProbabilityTri_const
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian) _ (circularLogPotential z)
    (ginibre_raw_mean_of_bbv hBBV N hN z)
  simpa only [sub_add_cancel, zero_add] using
    hc.add (fun n => cyclicAtomLaw (N n) circularComplexGaussian) hm

/-- The original common-array Ginibre reference input is now a theorem
from uniform BBV, rather than a separate literature hypothesis. -/
theorem ginibreLogPotential_of_bbv (hBBV : BBVComparisonInput) :
    GinibreLogPotentialInput := by
  intro N hNpos hN z
  let instN (n : ℕ) : NeZero (N n) := ⟨(hNpos n).ne'⟩
  apply (tendstoInMeasure_iff_tri gaussianSequenceLaw _ (circularLogPotential z)).2
  have htri := ginibre_raw_probability_of_bbv hBBV N hN z
  intro ε hε
  apply (htri ε hε).congr'
  apply Eventually.of_forall
  intro n
  have hA : Measurable (fun ω : ZMod (N n) × ZMod (N n) → ℂ =>
      ginibreMatrix (N n) ω - z • 1) :=
    (ginibreMatrix_measurable (N n)).sub measurable_const
  have hraw : Measurable (fun ω : ZMod (N n) × ZMod (N n) → ℂ =>
      matrixRawPotential (ginibreMatrix (N n) ω - z • 1)) :=
    (measurable_log_norm_matrix_det _ (fun i j =>
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA))).div_const _
  have hm : Measurable (fun ω : ZMod (N n) × ZMod (N n) → ℂ =>
      |matrixRawPotential (ginibreMatrix (N n) ω - z • 1) - circularLogPotential z|) := by
    simpa only [Real.norm_eq_abs] using (hraw.sub_const (circularLogPotential z)).norm
  have he := (GinibreReferenceSources.cyclicSamples_measurePreserving (N n)).measureReal_preimage
    (measurableSet_le (measurable_const (a := ε)) hm).nullMeasurableSet
  simpa only [Set.preimage_ofPred_eq, GinibreReferenceSources.cyclicSamples_raw] using he.symm

end CircularLawSection6
