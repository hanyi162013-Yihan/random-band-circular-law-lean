import BernoulliSection8.ClippedLog
import BernoulliSection10.CyclicPhysicalModel

/-!
# The Section 8 full-Fock formula for the actual normalized cyclic matrix

The reused physical matrix has `s + 3` sites and normalization `1/sqrt(3W)`.
The Section 8 model uses `s ≥ 1`; the identities here hold even at `s = 0`.
These formulas hold at singular interface matrices and at zero determinant.
Only the independent logarithmic estimate, not this identity, needs good
interface events. Existing identifiers containing `density` are definitions
of the physical matrix and carry no density hypothesis.
-/

open scoped Matrix BigOperators

noncomputable section

namespace BernoulliSection8

open BernoulliLinearAlgebra BernoulliSection10

def cyclicFockValue (W s : ℕ) (z : ℂ) (x : IntervalRows W (s + 3)) : ℂ :=
  polynomialClearedSignedCompoundTrace (physicalIntervalSteps W (s + 3) z x)

/-- Equation (8.15), including all singular-interface samples. -/
theorem cyclicFockValue_eq_signed_det (W s : ℕ) (z : ℂ)
    (x : IntervalRows W (s + 3)) :
    cyclicFockValue W s z x =
      floquetSign (R := ℂ) (m := s + 2) (w := Fin W) *
        (densityShiftedCyclicMatrix W s z x).det := by
  unfold cyclicFockValue physicalIntervalSteps densityShiftedCyclicMatrix
  rw [Matrix.det_reindex_self]
  exact polynomialClearedSignedCompoundTrace_listOfFn_eq_physical
    (fun j => (intervalSiteBlocks z x j).B)
    (fun j => (intervalSiteBlocks z x j).D)
    (fun j => (intervalSiteBlocks z x j).C) (by omega)

theorem norm_cyclicFockValue (W s : ℕ) (z : ℂ)
    (x : IntervalRows W (s + 3)) :
    ‖cyclicFockValue W s z x‖ = ‖(densityShiftedCyclicMatrix W s z x).det‖ := by
  rw [cyclicFockValue_eq_signed_det, norm_mul]
  rcases floquetSign_spec (R := ℂ) (m := s + 2) (w := Fin W) with h | h <;>
    simp [h]

theorem cyclicFockValue_eq_zero_iff (W s : ℕ) (z : ℂ)
    (x : IntervalRows W (s + 3)) :
    cyclicFockValue W s z x = 0 ↔ (densityShiftedCyclicMatrix W s z x).det = 0 := by
  rw [← norm_eq_zero, norm_cyclicFockValue, norm_eq_zero]

def clippedCyclicLogDet (B : ℝ) (W s : ℕ) (z : ℂ)
    (x : IntervalRows W (s + 3)) : ℝ :=
  clippedLog B ‖(densityShiftedCyclicMatrix W s z x).det‖

theorem clippedCyclicLogDet_eq_fock (B : ℝ) (W s : ℕ) (z : ℂ)
    (x : IntervalRows W (s + 3)) :
    clippedCyclicLogDet B W s z x = clippedLog B ‖cyclicFockValue W s z x‖ := by
  rw [norm_cyclicFockValue]
  rfl

theorem clippedCyclicLogDet_of_det_zero {B : ℝ} (hB : 0 ≤ B)
    (W s : ℕ) (z : ℂ) (x : IntervalRows W (s + 3))
    (hx : (densityShiftedCyclicMatrix W s z x).det = 0) :
    clippedCyclicLogDet B W s z x = -B := by
  simp [clippedCyclicLogDet, hx, clippedLog_zero hB]

theorem abs_clippedCyclicLogDet_le {B : ℝ} (hB : 0 ≤ B)
    (W s : ℕ) (z : ℂ) (x : IntervalRows W (s + 3)) :
    |clippedCyclicLogDet B W s z x| ≤ B :=
  abs_clippedLog_le hB _

end BernoulliSection8
