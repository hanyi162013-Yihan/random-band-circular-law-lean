import SubgaussianSection8.Energy
import BernoulliSection10.PositiveMatrixIndex
import BernoulliSection10.CircularLawFromPotential
import BernoulliSection10.WeakCircularLaw

/-! The circular-law reduction with general-law energy and coordinate transport. -/
open Filter MeasureTheory Topology
open scoped BigOperators
noncomputable section
namespace SubgaussianSection8
open BernoulliSection10 BernoulliSection10.SourceInputs
open BernoulliSection10.Replacement BernoulliSection10.DiskReference
open TaoVuReplacement ShortRingAnchor

set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

def sequenceLaw (A : Atom) : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => A.law

instance (A : Atom) : IsProbabilityMeasure (sequenceLaw A) := by
  unfold sequenceLaw
  infer_instance

/-- Matrix entries and normalization do not depend on which atom law is selected. -/
def matrix (W s : ℕ) (ω : ℕ → ℝ) :
    Matrix (Fin ((s + 3) * W)) (Fin ((s + 3) * W)) ℂ :=
  densityCyclicMatrix W s (physicalRowsFromSequence W s ω)

theorem matrix_entry_measurable (W s : ℕ)
    (i j : Fin ((s + 3) * W)) : Measurable (fun ω => matrix W s ω i j) := by
  simp only [matrix, densityCyclicMatrix_from_sequence]
  fun_prop

theorem matrix_energy_integrable_and_integral
    (A : Atom) (W s : ℕ) (hW : 0 < W) :
    Integrable (fun ω => squaredEntryMass (matrix W s ω) /
      (((s + 3) * W : ℕ) : ℝ)) (sequenceLaw A) ∧
    (∫ ω, squaredEntryMass (matrix W s ω) /
      (((s + 3) * W : ℕ) : ℝ) ∂sequenceLaw A) = 1 := by
  have hp := physicalRowsFromSequence_measurePreserving A.law W s
  have hi := cyclicMatrix_energy_integrable_and_integral A W s hW
  refine ⟨hp.integrable_comp_of_integrable hi.1, ?_⟩
  have he : Measurable (fun x : IntervalRows W (s + 3) =>
      (∑ i, ∑ j, ‖densityCyclicMatrix W s x i j‖ ^ 2) /
        (((s + 3) * W : ℕ) : ℝ)) := by
    simp_rw [densityCyclicMatrix_normalized_energy W s hW]
    unfold BernoulliSection10.intervalMeanAtomSquare
    fun_prop
  exact (real_integral_comp_measurePreserving hp he).trans hi.2

/-- Internal final reduction: after the actual subgaussian matrix's
log-determinant limit has been proved, no reference-ensemble, energy,
replacement or tightness certificate remains to be supplied. -/
theorem circular_law_of_log_potential (A : Atom)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (hLog : ∀ᵐ z ∂(volume : Measure ℂ), TendstoInMeasure (sequenceLaw A)
      (fun n ω => normalizedShiftLogDet (matrix (W n) (s n) ω) z)
      atTop (fun _ => circularLogPotential z))
    (f : BoundedContinuousFunction ℂ ℝ) :
    TendstoInMeasure (sequenceLaw A)
      (fun n ω => realEsdTest (matrix (W n) (s n) ω) f) atTop
      (fun _ => ∫ z, f z ∂circularMeasure) := by
  let N := fun n => (s n + 3) * W n
  have hN (n : ℕ) : 0 < N n := Nat.mul_pos (by omega) (hW n)
  letI (n : ℕ) : Nonempty (Fin (N n)) := ⟨⟨0, hN n⟩⟩
  have hNtop : Tendsto N atTop atTop :=
    tendsto_atTop_mono' atTop
      (Eventually.of_forall fun n => Nat.le_mul_of_pos_left (W n) (by omega)) hWtop
  let X := fun n ω => positiveMatrixIndex (hN n) (matrix (W n) (s n) ω)
  have hX : ∀ n i j, Measurable (fun ω => X n ω i j) := fun n i j =>
    measurable_positiveMatrixIndex_entry (hN n) (matrix (W n) (s n))
      (matrix_entry_measurable (W n) (s n)) i j
  have hXi (n : ℕ) : Integrable (fun ω => physicalEnergy (X n ω))
      (sequenceLaw A) := by
    simp only [X, positiveMatrixIndex_energy]
    exact ((matrix_energy_integrable_and_integral A) (W n) (s n) (hW n)).1
  have hXm (n : ℕ) : (∫ ω, physicalEnergy (X n ω) ∂(sequenceLaw A)) ≤ 1 := by
    simp only [X, positiveMatrixIndex_energy]
    exact ((matrix_energy_integrable_and_integral A) (W n) (s n) (hW n)).2.le
  have hXlog : ∀ᵐ z ∂(volume : Measure ℂ), TendstoInMeasure (sequenceLaw A)
      (fun n ω => physicalLogPotential (X n ω) z) atTop
      (fun _ => circularLogPotential z) := by
    simpa only [X, positiveMatrixIndex_log] using hLog
  have hcompact := physical_circularLaw_of_logPotential (sequenceLaw A)
    (fun n => N n - 1) (tendsto_pred_dimension hNtop) X hX 1 (by norm_num) hXi hXm hXlog
  apply circularLaw_boundedContinuousMap_of_compactSupport (sequenceLaw A)
    (fun n ω => matrix (W n) (s n) ω) _ f
  intro g hg hgc
  simpa only [X, positiveMatrixIndex_esd] using hcompact g hg hgc


end SubgaussianSection8
