import CircularLawSection6.GinibreGaussianLaw
import CircularLawSection6.SingularValueMeasurability
import CircularLawSection6.GinibreLowerCutoff

/-! # Closing the actual Ginibre negative-moment source

The event is measurable because ordered singular values are continuous.
The exact common-array projection therefore transports its probability,
including the real/ENNReal convention and finite-index normalization.
Both the compatibility BC12 route and the stronger BBV-only route are given.
-/

open MeasureTheory Filter Topology ShortRingAnchor
open CircularLawSections56.Section5
open CircularLawSections56.Section5.PublishedSection3Concrete (BBVComparisonInput BC12GinibreInput)
noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace CircularLawSection6
namespace GinibreReferenceSources

theorem cyclicSamples_negative (N : ℕ) [NeZero N] (ω : ℕ → ℂ) (z : ℂ) (p : ℝ) :
    matrixNegativeMoment (ginibreMatrix N (cyclicSamples N ω) - z • 1) p =
      normalizedNegativeMoment p (shiftedSingularValueFamily
        (CircularLawSections56.Section5.PublishedSection3Concrete.ginibreOnSequence N ω) z) := by
  have hm := cyclicSamples_shifted_matrix N ω z
  rw [← matrixNegativeMoment_reindex (ZMod.finEquiv N).toEquiv.symm
    (ginibreMatrix N (cyclicSamples N ω) - z • 1) p, hm]
  simp only [matrixNegativeMoment, Fintype.card_fin, shiftedSingularValueFamily,
    shiftedSingularValue, matrixSingularValue]

theorem negative_on_sequence_to_tri
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (z : ℂ) (p : ℝ)
    (hnegative : BC12GinibreNegativeMomentTightness
      CircularLawSections56.Section5.PublishedSection3Concrete.gaussianSequenceLaw p
      (shiftedSingularValueProcess
        (fun n => CircularLawSections56.Section5.PublishedSection3Concrete.ginibreOnSequence (N n)) z)) :
    BC12GinibreNegativeMomentTightnessTri N z p := by
  intro δ hδ
  obtain ⟨C, hC, htail⟩ := hnegative (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)
  refine ⟨C, hC, ?_⟩
  filter_upwards [htail] with n hn
  have hm : Measurable (fun ω : ZMod (N n) × ZMod (N n) → ℂ =>
      |matrixNegativeMoment (ginibreMatrix (N n) ω - z • 1) p|) := by
    simpa only [Real.norm_eq_abs] using
      ((measurable_matrixNegativeMoment p).comp
        ((ginibreMatrix_measurable (N n)).sub measurable_const)).norm
  have hprob : (cyclicAtomLaw (N n) circularComplexGaussian)
      {ω | C < |matrixNegativeMoment (ginibreMatrix (N n) ω - z • 1) p|} < ENNReal.ofReal δ := by
    rw [← (cyclicSamples_measurePreserving (N n)).measure_preimage
      (measurableSet_lt (measurable_const (a := C)) hm).nullMeasurableSet]
    simpa only [Set.preimage_ofPred_eq, cyclicSamples_negative, Real.norm_eq_abs,
      shiftedSingularValueProcess] using hn
  simpa only [measureReal_def, ENNReal.toReal_ofReal hδ.le] using
    (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 hprob

end GinibreReferenceSources

/-- Compatibility route: there is no second negative-moment literature
premise beyond the Section 5 BC12 source. -/
theorem ginibre_negative_of_bc12
    (hBC12 : BC12GinibreInput) (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (z : ℂ) :
    ∃ p : ℝ, 0 < p ∧ BC12GinibreNegativeMomentTightnessTri N z p := by
  obtain ⟨p, hp, hnegative, _hraw⟩ := hBC12 N (fun n => NeZero.pos (N n)) hN z
  exact ⟨p, hp, GinibreReferenceSources.negative_on_sequence_to_tri N z p hnegative⟩

/-- Stronger route: the actual Gaussian negative moment is derived using
only uniform BBV and the proved polynomial Gaussian lower edge. -/
theorem ginibre_negative_of_bbv
    (hBBV : BBVComparisonInput) (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (z : ℂ) :
    BC12GinibreNegativeMomentTightnessTri N z (1 / 128) :=
  GinibreReferenceSources.negative_on_sequence_to_tri N z (1 / 128)
    (GinibreReferenceSources.ginibre_negative_on_sequence_of_bbv hBBV N
      (fun n => NeZero.pos (N n)) hN z)

/-- Once the separate raw log-potential result is available, uniform BBV
constructs the whole old BC12 bundle. The displayed `hLog` premise is
retained explicitly; this theorem does not claim to prove that limit. -/
theorem bc12_of_bbv_and_logPotential
    (hBBV : BBVComparisonInput)
    (hLog : ∀ (N : ℕ → ℕ), (∀ n, 0 < N n) → Tendsto N atTop atTop →
      ∀ z : ℂ, ConvergesInProbability
        CircularLawSections56.Section5.PublishedSection3Concrete.gaussianSequenceLaw
        (fun n ω => normalizedShiftLogDet
          (CircularLawSections56.Section5.PublishedSection3Concrete.ginibreOnSequence (N n) ω) z)
        (circularLogPotential z)) :
    BC12GinibreInput := by
  intro N hNpos hN z
  exact ⟨1 / 128, by norm_num,
    GinibreReferenceSources.ginibre_negative_on_sequence_of_bbv hBBV N hNpos hN z,
    hLog N hNpos hN z⟩

end CircularLawSection6
