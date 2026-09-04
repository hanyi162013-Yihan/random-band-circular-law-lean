import CircularLawSection6.ProfileReplacement
import CircularLawSection6.GaussianTailJensen
import CircularLawSections56.Section5.CircularLawFromPotential
import CircularLawSections56.Section5.VerifiedGinibreSources

/-! # The actual Ginibre circular law is not a second literature assumption

The Section 5 BC12 source uses a single countable Gaussian array, whereas
Section 6 uses finite row/displacement arrays. The coordinate map below
constructs the exact common law and preserves the square-root normalization.
The existing, proved disk-reference replacement theorem then supplies the
Ginibre spectral limit. No Ginibre circular law is assumed separately.

The verified route uses Section 5's proved Gaussian log limit, with no BBV
or BC12 premise. Older conditional helpers remain as compatibility wrappers.
-/

open MeasureTheory Filter Topology TaoVuReplacement ShortRingAnchor
open CircularLawSections56.Section5 CircularLawSections56.Section6
open CircularLawSections56.Section5.PublishedSection3Concrete (BC12GinibreInput)
noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace CircularLawSection6

namespace GinibreReferenceSources

/-- A cyclic displacement `(i,d)` is the dense matrix entry `(i,i+d)`. -/
def cyclicCoordinate (N : ℕ) [NeZero N] (ij : ZMod N × ZMod N) : ℕ :=
  CircularLawSections56.Section5.PublishedSection3Concrete.denseCoordinate ((ZMod.finEquiv N).symm ij.1,
    (ZMod.finEquiv N).symm (ij.1 + ij.2))

theorem cyclicCoordinate_injective (N : ℕ) [NeZero N] :
    Function.Injective (cyclicCoordinate N) := by
  intro x y h
  have hp := CircularLawSections56.Section5.PublishedSection3Concrete.denseCoordinate_injective N h
  have hr := (ZMod.finEquiv N).symm.injective (congrArg Prod.fst hp)
  have hc := (ZMod.finEquiv N).symm.injective (congrArg Prod.snd hp)
  exact Prod.ext hr (by rw [hr] at hc; exact add_left_cancel hc)

def cyclicSamples (N : ℕ) [NeZero N] (ω : ℕ → ℂ) : ZMod N × ZMod N → ℂ :=
  fun ij => ω (cyclicCoordinate N ij)

theorem cyclicSamples_measurePreserving (N : ℕ) [NeZero N] :
    MeasurePreserving (cyclicSamples N)
      CircularLawSections56.Section5.PublishedSection3Concrete.gaussianSequenceLaw
      (cyclicAtomLaw N circularComplexGaussian) :=
  CircularLawSections56.Section5.PublishedSection3Concrete.selectedCoordinates_measurePreserving circularComplexGaussian
    (cyclicCoordinate N) (cyclicCoordinate_injective N)

/-- The physical matrix, not just its moments, agrees after reindexing. -/
theorem cyclicSamples_matrix (N : ℕ) [NeZero N] (ω : ℕ → ℂ) :
    (ginibreMatrix N (cyclicSamples N ω)).submatrix (ZMod.finEquiv N)
      (ZMod.finEquiv N) = CircularLawSections56.Section5.PublishedSection3Concrete.ginibreOnSequence N ω := by
  ext i j
  simp [ginibreMatrix, weightedCyclicMatrix, cyclicSamples, cyclicCoordinate,
    CircularLawSections56.Section5.PublishedSection3Concrete.ginibreOnSequence, div_eq_mul_inv, mul_comm]

theorem cyclicSamples_shifted_matrix (N : ℕ) [NeZero N] (ω : ℕ → ℂ) (z : ℂ) :
    (ginibreMatrix N (cyclicSamples N ω) - z • 1).submatrix
      (ZMod.finEquiv N) (ZMod.finEquiv N) =
        CircularLawSections56.Section5.PublishedSection3Concrete.ginibreOnSequence N ω - z • 1 := by
  ext i j
  simpa only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, (ZMod.finEquiv N).injective.eq_iff] using
    congrArg (fun A : Matrix (Fin N) (Fin N) ℂ => (A - z • 1) i j)
      (cyclicSamples_matrix N ω)

theorem cyclicSamples_raw (N : ℕ) [NeZero N] (ω : ℕ → ℂ) (z : ℂ) :
    matrixRawPotential (ginibreMatrix N (cyclicSamples N ω) - z • 1) =
      normalizedShiftLogDet
        (CircularLawSections56.Section5.PublishedSection3Concrete.ginibreOnSequence N ω) z := by
  have hdet : (CircularLawSections56.Section5.PublishedSection3Concrete.ginibreOnSequence N ω -
      z • 1).det = (ginibreMatrix N (cyclicSamples N ω) - z • 1).det :=
    (congrArg Matrix.det (cyclicSamples_shifted_matrix N ω z).symm).trans
      (Matrix.det_submatrix_equiv_self (ZMod.finEquiv N).toEquiv
        (ginibreMatrix N (cyclicSamples N ω) - z • 1))
  unfold matrixRawPotential normalizedShiftLogDet
  rw [hdet, ZMod.card]

end GinibreReferenceSources

/-- Transport a single common-array Gaussian log limit to the cyclic law.
No negative-moment estimate is needed for this measure-preserving transport. -/
theorem ginibre_raw_of_sequence_log_limit
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (z : ℂ)
    (hraw : ConvergesInProbability
      CircularLawSections56.Section5.PublishedSection3Concrete.gaussianSequenceLaw
      (fun n ω => normalizedShiftLogDet
        (CircularLawSections56.Section5.PublishedSection3Concrete.ginibreOnSequence (N n) ω) z)
      (circularLogPotential z)) :
    TendstoInProbabilityTri (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
      (fun n ω => matrixRawPotential (ginibreMatrix (N n) ω - z • 1))
      (circularRadialPotential ‖z‖) := by
  have htri := (tendstoInMeasure_iff_tri
    CircularLawSections56.Section5.PublishedSection3Concrete.gaussianSequenceLaw
    (fun n ω => normalizedShiftLogDet
      (CircularLawSections56.Section5.PublishedSection3Concrete.ginibreOnSequence (N n) ω) z)
    (circularLogPotential z)).1 hraw
  intro ε hε
  apply (htri ε hε).congr'
  apply Eventually.of_forall
  intro n
  have hm : Measurable (fun ω : ZMod (N n) × ZMod (N n) → ℂ =>
      |matrixRawPotential (ginibreMatrix (N n) ω - z • 1) - circularRadialPotential ‖z‖|) := by
    have hA : Measurable (fun ω : ZMod (N n) × ZMod (N n) → ℂ =>
        ginibreMatrix (N n) ω - z • 1) :=
      (ginibreMatrix_measurable (N n)).sub measurable_const
    have hraw : Measurable (fun ω : ZMod (N n) × ZMod (N n) → ℂ =>
        matrixRawPotential (ginibreMatrix (N n) ω - z • 1)) :=
      (measurable_log_norm_matrix_det _ (fun i j =>
        (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA))).div_const _
    simpa only [Real.norm_eq_abs] using (hraw.sub_const (circularRadialPotential ‖z‖)).norm
  have he := (GinibreReferenceSources.cyclicSamples_measurePreserving (N n)).measureReal_preimage
    (measurableSet_le (measurable_const (a := ε)) hm).nullMeasurableSet
  simpa only [Set.preimage_ofPred_eq, GinibreReferenceSources.cyclicSamples_raw,
    circularRadialPotential, circularLogPotential] using he

/-- Compatibility wrapper for callers with the historical BC12 bundle. -/
theorem ginibre_raw_of_bc12
    (hBC12 : BC12GinibreInput) (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (z : ℂ) :
    TendstoInProbabilityTri (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
      (fun n ω => matrixRawPotential (ginibreMatrix (N n) ω - z • 1))
      (circularRadialPotential ‖z‖) := by
  obtain ⟨_p, _hp, _hnegative, hraw⟩ := hBC12 N (fun n => NeZero.pos (N n)) hN z
  exact ginibre_raw_of_sequence_log_limit N z hraw

/-- The actual cyclic Ginibre log limit, with no external mathematical input. -/
theorem ginibre_raw_verified
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop) (z : ℂ) :
    TendstoInProbabilityTri (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
      (fun n ω => matrixRawPotential (ginibreMatrix (N n) ω - z • 1))
      (circularRadialPotential ‖z‖) :=
  ginibre_raw_of_sequence_log_limit N z
    (CircularLawSections56.Section5.PublishedSection3Concrete.ginibre_logPotential_on_sequence
      N (fun n => NeZero.pos (N n)) hN z)

/-- Actual Ginibre ESD convergence on the Section 6 product sample space.
The comparison law, its energy, its potential, and replacement are all proved
inside Section 5; none is an additional Ginibre premise here. -/
theorem ginibre_spectral_of_raw_limit
    (hraw : ∀ z : ℂ,
      TendstoInProbabilityTri (fun n => cyclicAtomLaw (n + 1) circularComplexGaussian)
        (fun n ω => matrixRawPotential (ginibreMatrix (n + 1) ω - z • 1))
        (circularRadialPotential ‖z‖)) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix n (ginibreMatrix (n + 1) (ω n).2)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) := by
  let X := fun n (ω : (ZMod (n + 1) × ZMod (n + 1) → ℂ) ×
      (ZMod (n + 1) × ZMod (n + 1) → ℂ)) =>
    cyclicPhysicalMatrix n (ginibreMatrix (n + 1) ω.2)
  have hX (n : ℕ) (i j : Fin (n + 1)) : Measurable (fun ω => X n ω i j) :=
    (cyclicPhysicalMatrix_entry_measurable n _ (ginibreMatrix_measurable (n + 1)) i j).comp
      measurable_snd
  have hE (n : ℕ) : Integrable (fun ω => physicalEnergy
      (cyclicPhysicalMatrix n (ginibreMatrix (n + 1) ω)))
      (cyclicAtomLaw (n + 1) circularComplexGaussian) ∧
      (∫ ω, physicalEnergy (cyclicPhysicalMatrix n (ginibreMatrix (n + 1) ω))
        ∂cyclicAtomLaw (n + 1) circularComplexGaussian) = 1 := by
    simp only [cyclicPhysicalMatrix_energy, cyclicEnergy]
    refine ⟨(ginibre_expected_energy (n + 1)).1.div_const _, ?_⟩
    rw [integral_div, (ginibre_expected_energy (n + 1)).2,
      div_self (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)]
  apply triangular_circularLaw_of_logPotential profileGinibrePairLaw X hX 1 zero_le_one
    (fun n => measurePreserving_snd.integrable_comp_of_integrable (hE n).1) ?_ ?_
  · intro n
    exact ((integral_comp_of_measurePreserving_aes measurePreserving_snd _
      (hE n).1.aestronglyMeasurable).trans (hE n).2).le
  · apply ae_of_all
    intro z
    have hr := hraw z
    have hp : TendstoInProbabilityTri (fun n => cyclicAtomLaw (n + 1) circularComplexGaussian)
        (fun n ω => physicalLogPotential (cyclicPhysicalMatrix n (ginibreMatrix (n + 1) ω)) z)
        (circularLogPotential z) := by
      simpa only [cyclicPhysicalMatrix_logPotential, circularRadialPotential,
        circularLogPotential] using hr
    exact tendstoInProbabilityTri_comp_measurePreserving profileGinibrePairLaw
      (fun n => cyclicAtomLaw (n + 1) circularComplexGaussian) (fun _ => Prod.snd)
      (fun _ => measurePreserving_snd) _
      (fun n => measurable_physicalLogPotential _
        (cyclicPhysicalMatrix_entry_measurable n _ (ginibreMatrix_measurable _)) z) hp

/-- Compatibility wrapper; only the log-limit component of BC12 is used. -/
theorem ginibre_spectral_of_bc12 (hBC12 : BC12GinibreInput) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix n (ginibreMatrix (n + 1) (ω n).2)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) :=
  ginibre_spectral_of_raw_limit
    (fun z => ginibre_raw_of_bc12 hBC12 (fun n => n + 1) (tendsto_add_atTop_nat 1) z)

/-- The actual Ginibre circular law, without BBV or BC12 as a premise.
The disk-reference replacement and Gaussian log limit are both proved. -/
theorem ginibre_spectral_verified :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix n (ginibreMatrix (n + 1) (ω n).2)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) :=
  ginibre_spectral_of_raw_limit
    (fun z => ginibre_raw_verified (fun n => n + 1) (tendsto_add_atTop_nat 1) z)

end CircularLawSection6
