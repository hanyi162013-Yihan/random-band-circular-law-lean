import BernoulliSection8.RademacherEnergy
import BernoulliSection10.PositiveMatrixIndex
import BernoulliSection10.CircularLawFromPotential
import BernoulliSection10.WeakCircularLaw

/-!
# The proved circular-law reduction for the Bernoulli physical model

This module discharges the entire Tao--Vu, comparison-law, energy,
measurability and bounded-continuous-test part of the Bernoulli conclusion.
The sole random-matrix estimate in the internal bridge is the actual
matrix's log-potential limit. It remains explicit here and is to be supplied
by the Section 8 pressure argument; this conditional reduction is not the
unconditional Section 8 theorem.
-/

open Filter MeasureTheory Topology

noncomputable section

namespace BernoulliSection8

open BernoulliSection10 BernoulliSection10.SourceInputs
open BernoulliSection10.Replacement BernoulliSection10.DiskReference
open TaoVuReplacement ShortRingAnchor

set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- One fixed infinite IID Rademacher sample space. Only each finite
matrix's marginal law matters in convergence in probability. -/
def rademacherSequenceLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => rademacherLaw

instance rademacherSequenceLaw_isProbabilityMeasure :
    IsProbabilityMeasure rademacherSequenceLaw := by
  unfold rademacherSequenceLaw
  infer_instance

/-- The actual normalized cyclic full-block Bernoulli matrix, with
`m = s + 3`, `N = mW`, and the entry normalization `1 / sqrt (3W)`. -/
def rademacherMatrix (W s : ℕ) (ω : ℕ → ℝ) :
    Matrix (Fin ((s + 3) * W)) (Fin ((s + 3) * W)) ℂ :=
  densityCyclicMatrix W s (physicalRowsFromSequence W s ω)

theorem rademacherMatrix_entry_measurable (W s : ℕ)
    (i j : Fin ((s + 3) * W)) : Measurable (fun ω => rademacherMatrix W s ω i j) := by
  simp only [rademacherMatrix, densityCyclicMatrix_from_sequence]
  fun_prop

theorem rademacherMatrix_energy_ae_one (W s : ℕ) (hW : 0 < W) :
    ∀ᵐ ω ∂rademacherSequenceLaw,
      squaredEntryMass (rademacherMatrix W s ω) / (((s + 3) * W : ℕ) : ℝ) = 1 :=
  (physicalRowsFromSequence_measurePreserving rademacherLaw W s).quasiMeasurePreserving.ae
    (rademacherCyclicMatrix_energy_ae_one W s hW)

theorem rademacherMatrix_energy_integrable_and_integral
    (W s : ℕ) (hW : 0 < W) :
    Integrable (fun ω => squaredEntryMass (rademacherMatrix W s ω) /
      (((s + 3) * W : ℕ) : ℝ)) rademacherSequenceLaw ∧
    (∫ ω, squaredEntryMass (rademacherMatrix W s ω) /
      (((s + 3) * W : ℕ) : ℝ) ∂rademacherSequenceLaw) = 1 := by
  have h := rademacherMatrix_energy_ae_one W s hW
  refine ⟨(integrable_const 1).congr (Filter.EventuallyEq.symm h), ?_⟩
  rw [integral_congr_ae h]
  simp

/-- Internal final reduction: after the actual Bernoulli matrix's
log-determinant limit has been proved, no reference-ensemble, energy,
replacement or tightness certificate remains to be supplied. -/
theorem rademacher_circular_law_of_log_potential
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (hLog : ∀ᵐ z ∂(volume : Measure ℂ), TendstoInMeasure rademacherSequenceLaw
      (fun n ω => normalizedShiftLogDet (rademacherMatrix (W n) (s n) ω) z)
      atTop (fun _ => circularLogPotential z))
    (f : BoundedContinuousFunction ℂ ℝ) :
    TendstoInMeasure rademacherSequenceLaw
      (fun n ω => realEsdTest (rademacherMatrix (W n) (s n) ω) f) atTop
      (fun _ => ∫ z, f z ∂circularMeasure) := by
  let N := fun n => (s n + 3) * W n
  have hN (n : ℕ) : 0 < N n := Nat.mul_pos (by omega) (hW n)
  letI (n : ℕ) : Nonempty (Fin (N n)) := ⟨⟨0, hN n⟩⟩
  have hNtop : Tendsto N atTop atTop :=
    tendsto_atTop_mono' atTop
      (Eventually.of_forall fun n => Nat.le_mul_of_pos_left (W n) (by omega)) hWtop
  let X := fun n ω => positiveMatrixIndex (hN n) (rademacherMatrix (W n) (s n) ω)
  have hX : ∀ n i j, Measurable (fun ω => X n ω i j) := fun n i j =>
    measurable_positiveMatrixIndex_entry (hN n) (rademacherMatrix (W n) (s n))
      (rademacherMatrix_entry_measurable (W n) (s n)) i j
  have hXi (n : ℕ) : Integrable (fun ω => physicalEnergy (X n ω))
      rademacherSequenceLaw := by
    simp only [X, positiveMatrixIndex_energy]
    exact (rademacherMatrix_energy_integrable_and_integral (W n) (s n) (hW n)).1
  have hXm (n : ℕ) : (∫ ω, physicalEnergy (X n ω) ∂rademacherSequenceLaw) ≤ 1 := by
    simp only [X, positiveMatrixIndex_energy]
    exact (rademacherMatrix_energy_integrable_and_integral (W n) (s n) (hW n)).2.le
  have hXlog : ∀ᵐ z ∂(volume : Measure ℂ), TendstoInMeasure rademacherSequenceLaw
      (fun n ω => physicalLogPotential (X n ω) z) atTop
      (fun _ => circularLogPotential z) := by
    simpa only [X, positiveMatrixIndex_log] using hLog
  have hcompact := physical_circularLaw_of_logPotential rademacherSequenceLaw
    (fun n => N n - 1) (tendsto_pred_dimension hNtop) X hX 1 (by norm_num) hXi hXm hXlog
  apply circularLaw_boundedContinuousMap_of_compactSupport rademacherSequenceLaw
    (fun n ω => rademacherMatrix (W n) (s n) ω) _ f
  intro g hg hgc
  simpa only [X, positiveMatrixIndex_esd] using hcompact g hg hgc

end BernoulliSection8
