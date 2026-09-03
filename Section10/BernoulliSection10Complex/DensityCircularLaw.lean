import BernoulliSection10Complex.TargetRingLimit
import BernoulliSection10.PositiveMatrixIndex
import BernoulliSection10.CircularLawFromPotential
import BernoulliSection10.WeakCircularLaw
import BernoulliSection10Complex.DensityEnergyLimit

/-!
# The bounded-density full-block circular law

This internal assembly temporarily takes the exact Section 3 statements.
The final source-connected wrapper must discharge this staging interface
using the repository's Section 3 proofs, with BBV/BC12 dependencies explicit.
The pressure calibration, independent resets, end seam, remainder,
Hilbert--Schmidt bound, comparison ensemble, and replacement principle
are constructed or proved inside the imported modules.

The last theorem uses just an infinite sequence of complex IID atoms. Its
finite displayed-coordinate marginals are exactly `intervalRowsLaw`, by
`physicalRowsFromSequence_measurePreserving`. No independence between
different matrix sizes is required for convergence in probability.
-/

open Filter MeasureTheory Topology

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open SourceInputs ShortRingAnchor Replacement DiskReference TaoVuReplacement

set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem density_profile_circular_law
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (h3 : Integrable (fun x : ℂ => ‖x‖ ^ 3) μ) (hSource : Section3Inputs μ L)
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
      density_profile_log_limit hμ h3 hSource W s hW hWtop z
  have hcompact := physical_circularLaw_of_logPotential (inputLaw μ)
    (fun n => N n - 1) (tendsto_pred_dimension hNtop) X hX 1 (by norm_num) hXi hXm hXlog
  apply circularLaw_boundedContinuousMap_of_compactSupport (inputLaw μ)
    (fun n ω => profileMatrix (σ n) ω) _ f
  intro g hg hgc
  simpa only [X, positiveMatrixIndex_esd] using hcompact g hg hgc

/-- Theorem 2.10, planar-complex-IID bounded-density finite-third-moment branch,
for the actual normalized cyclic full-block matrices. -/
theorem density_circular_law
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (h3 : Integrable (fun x : ℂ => ‖x‖ ^ 3) μ) (hSource : Section3Inputs μ L)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (f : BoundedContinuousFunction ℂ ℝ) :
    TendstoInMeasure (Measure.infinitePi fun _ : ℕ => μ)
      (fun n ω => realEsdTest
        (densityCyclicMatrix (W n) (s n) (physicalRowsFromSequence (W n) (s n) ω)) f)
      atTop (fun _ => ∫ z, f z ∂circularMeasure) := by
  letI := hμ.toIsProbabilityMeasure
  have h := density_profile_circular_law hμ h3 hSource W s hW hWtop f
  apply (tendstoInMeasure_prod_fst_iff
    (Measure.infinitePi fun _ : ℕ => μ)
    (Measure.infinitePi fun _ : ℕ => circularGaussianPairLaw)
    (fun n ω => realEsdTest
      (densityCyclicMatrix (W n) (s n) (physicalRowsFromSequence (W n) (s n) ω)) f)
    (∫ z, f z ∂circularMeasure)).mp
  simpa only [← densityCyclicMatrix_physicalRowsFromInput, physicalRowsFromInput, inputLaw] using h

end BernoulliSection10Complex
