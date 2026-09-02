import TaoVuReplacement.MatrixScaling
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Measurability of the random-matrix quantities

This file supplies the elementary measurability layer needed to state
Tao--Vu, Theorem 2.1 for random matrices of size `k + 1`.  Entrywise
measurability is enough because the determinant and the Hilbert--Schmidt
square are finite polynomials (followed, for the logarithmic potential, by
norm and the real logarithm).

`Real.log` is totalized in Lean, with `Real.log 0 = 0`.  Accordingly,
`normalizedLogDet` below is a total measurable function.  The replacement
principle separately records the source theorem's nonsingularity semantics;
none of the measurability results in this file pretends that a determinant is
nonzero.
-/

open scoped BigOperators

noncomputable section

namespace TaoVuReplacement

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The normalized logarithmic determinant appearing in Tao--Vu,
Theorem 2.1, for a matrix of size `k + 1`:

`(1 / (k+1)) log |det ((k+1)^(-1/2) A - z I)|`.

The logarithm is Lean's totalized `Real.log`; nonsingularity is imposed
separately in the final replacement-principle statement. -/
def normalizedLogDet {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (z : ℂ) : ℝ :=
  Real.log ‖(normalizedMatrix A -
      z • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)).det‖ /
    ((k + 1 : ℕ) : ℝ)

/-- The normalized log-determinant difference in hypothesis (ii) of
Tao--Vu, Theorem 2.1. -/
def normalizedLogDetDifference {k : ℕ}
    (A B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (z : ℂ) : ℝ :=
  normalizedLogDet A z - normalizedLogDet B z

/-- The normalized Hilbert--Schmidt square in hypothesis (i) of Tao--Vu,
Theorem 2.1: `‖A‖_HS^2 / (k+1)^2`. -/
def normalizedHilbertSchmidtSq {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ℝ :=
  hilbertSchmidtSq A / (((k + 1 : ℕ) : ℝ) ^ 2)

/-- The determinant of an entrywise-measurable finite complex matrix is
measurable. -/
theorem measurable_det_of_entrywise {k : ℕ}
    (A : Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ i j, Measurable fun omega ↦ A omega i j) :
    Measurable fun omega ↦ (A omega).det := by
  simp_rw [Matrix.det_apply']
  apply Finset.measurable_sum
  intro sigma _hsigma
  exact measurable_const.mul <|
    Finset.measurable_prod _ fun i _hi ↦ hA (sigma i) i

/-- For each deterministic `z`, the normalized logarithmic determinant of
an entrywise-measurable random matrix is measurable in the sample point. -/
theorem measurable_normalizedLogDet_fixed_of_entrywise {k : ℕ}
    (A : Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ i j, Measurable fun omega ↦ A omega i j) (z : ℂ) :
    Measurable fun omega ↦ normalizedLogDet (A omega) z := by
  have hdet : Measurable fun omega ↦
      (normalizedMatrix (A omega) -
        z • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)).det :=
    measurable_det_of_entrywise _ fun i j ↦ by
      change Measurable fun omega ↦
        inverseSqrtDimension (Fin (k + 1)) * A omega i j -
          (z • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) i j
      exact ((hA i j).const_mul _).sub measurable_const
  exact (Real.measurable_log.comp hdet.norm).div_const _

/-- The normalized logarithmic determinant is jointly measurable in the
spectral parameter `z` and the sample point. -/
theorem measurable_normalizedLogDet_joint_of_entrywise {k : ℕ}
    (A : Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ i j, Measurable fun omega ↦ A omega i j) :
    Measurable fun p : ℂ × Omega ↦ normalizedLogDet (A p.2) p.1 := by
  have hdet : Measurable fun p : ℂ × Omega ↦
      (normalizedMatrix (A p.2) -
        p.1 • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)).det :=
    measurable_det_of_entrywise _ fun i j ↦ by
      change Measurable fun p : ℂ × Omega ↦
        inverseSqrtDimension (Fin (k + 1)) * A p.2 i j -
          p.1 * (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j
      exact ((hA i j).comp measurable_snd).const_mul _ |>.sub
        (measurable_fst.mul_const _)
  exact (Real.measurable_log.comp hdet.norm).div_const _

/-- For fixed `z`, the normalized log-determinant difference of two
entrywise-measurable random matrices is measurable. -/
theorem measurable_normalizedLogDetDifference_fixed_of_entrywise {k : ℕ}
    (A B : Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ i j, Measurable fun omega ↦ A omega i j)
    (hB : ∀ i j, Measurable fun omega ↦ B omega i j) (z : ℂ) :
    Measurable fun omega ↦ normalizedLogDetDifference (A omega) (B omega) z := by
  exact (measurable_normalizedLogDet_fixed_of_entrywise A hA z).sub
    (measurable_normalizedLogDet_fixed_of_entrywise B hB z)

/-- The normalized log-determinant difference is jointly measurable in `z`
and the sample point. -/
theorem measurable_normalizedLogDetDifference_joint_of_entrywise {k : ℕ}
    (A B : Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ i j, Measurable fun omega ↦ A omega i j)
    (hB : ∀ i j, Measurable fun omega ↦ B omega i j) :
    Measurable fun p : ℂ × Omega ↦
      normalizedLogDetDifference (A p.2) (B p.2) p.1 := by
  exact (measurable_normalizedLogDet_joint_of_entrywise A hA).sub
    (measurable_normalizedLogDet_joint_of_entrywise B hB)

/-- The normalized Hilbert--Schmidt square of an entrywise-measurable random
matrix is measurable. -/
theorem measurable_normalizedHilbertSchmidtSq_of_entrywise {k : ℕ}
    (A : Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ i j, Measurable fun omega ↦ A omega i j) :
    Measurable fun omega ↦ normalizedHilbertSchmidtSq (A omega) := by
  unfold normalizedHilbertSchmidtSq hilbertSchmidtSq
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _hi
  apply Finset.measurable_sum
  intro j _hj
  exact (hA i j).norm.pow_const 2

end TaoVuReplacement

