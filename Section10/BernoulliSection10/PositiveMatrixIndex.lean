import BernoulliSection10.PhysicalReplacement
import BernoulliSection10.Section3Inputs

/-! # Removing the replacement library's syntactic successor-size convention -/

open Filter MeasureTheory

noncomputable section

namespace BernoulliSection10

open Replacement SourceInputs TaoVuReplacement ShortRingAnchor

def positiveMatrixIndex {N : ℕ} (hN : 0 < N) (A : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin (N - 1 + 1)) (Fin (N - 1 + 1)) ℂ :=
  A.reindex (finCongr (Nat.sub_add_cancel hN).symm) (finCongr (Nat.sub_add_cancel hN).symm)

theorem positiveMatrixIndex_succ (k : ℕ) (h : 0 < k + 1)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : positiveMatrixIndex h A = A := by
  ext i j
  rfl

theorem positiveMatrixIndex_log {N : ℕ} (hN : 0 < N)
    (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) :
    physicalLogPotential (positiveMatrixIndex hN A) z = normalizedShiftLogDet A z := by
  cases N with
  | zero => omega
  | succ k =>
    rw [positiveMatrixIndex_succ]
    simp only [physicalLogPotential, normalizedShiftLogDet, Nat.add_sub_cancel,
      Nat.cast_add, Nat.cast_one]

theorem positiveMatrixIndex_energy {N : ℕ} (hN : 0 < N)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    physicalEnergy (positiveMatrixIndex hN A) = squaredEntryMass A / (N : ℝ) := by
  cases N with
  | zero => omega
  | succ k =>
    rw [positiveMatrixIndex_succ]
    simp only [physicalEnergy, hilbertSchmidtSq, squaredEntryMass, Nat.add_sub_cancel,
      Nat.cast_add, Nat.cast_one]
    rfl

theorem positiveMatrixIndex_esd {N : ℕ} (hN : 0 < N)
    (A : Matrix (Fin N) (Fin N) ℂ) (f : ℂ → ℝ) :
    realEsdTest (positiveMatrixIndex hN A) f = realEsdTest A f := by
  cases N with
  | zero => omega
  | succ k => rw [positiveMatrixIndex_succ]

theorem measurable_positiveMatrixIndex_entry
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (hN : 0 < N)
    (A : Ω → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j))
    (i j : Fin (N - 1 + 1)) :
    Measurable (fun ω => positiveMatrixIndex hN (A ω) i j) := by
  exact hA _ _

theorem tendsto_pred_dimension {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => N n - 1) atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [hN.eventually_ge_atTop (k + 1)] with n hn
  omega

end BernoulliSection10
