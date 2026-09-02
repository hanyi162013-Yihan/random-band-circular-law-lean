import BernoulliSection9.CookTruncation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FunProp

/-!
# Entrywise strong measurability for finite complex matrix algebra

These elementary closure lemmas let the concrete CUR formula inherit the
global-complement measurability of its packet atoms, including through
mathlib's nonsingular inverse (adjugate divided by determinant, and zero at
singular matrices).
-/

noncomputable section

namespace BernoulliSection9

open MeasureTheory

theorem matrix_det_stronglyMeasurable
    {Omega n : Type*} [mOmega : MeasurableSpace Omega]
    [Fintype n] [DecidableEq n]
    (m : MeasurableSpace Omega)
    (A : Omega → Matrix n n Complex)
    (hA : ∀ i j,
      @StronglyMeasurable Omega Complex _ m (fun omega => A omega i j)) :
    @StronglyMeasurable Omega Complex _ m (fun omega => (A omega).det) := by
  letI : MeasurableSpace Omega := m
  simp_rw [Matrix.det_apply]
  fun_prop

theorem matrix_adjugate_entry_stronglyMeasurable
    {Omega n : Type*} [mOmega : MeasurableSpace Omega]
    [Fintype n] [DecidableEq n]
    (m : MeasurableSpace Omega)
    (A : Omega → Matrix n n Complex)
    (hA : ∀ i j,
      @StronglyMeasurable Omega Complex _ m (fun omega => A omega i j))
    (i j : n) :
    @StronglyMeasurable Omega Complex _ m
      (fun omega => (A omega).adjugate i j) := by
  rw [show (fun omega => (A omega).adjugate i j) =
      fun omega => ((A omega).updateRow j (Pi.single i 1)).det by
    funext omega
    exact Matrix.adjugate_apply (A omega) i j]
  apply matrix_det_stronglyMeasurable m
  intro a b
  by_cases h : a = j
  · subst a
    have heq : (fun omega =>
        (A omega).updateRow j (Pi.single i 1) j b) =
        (fun _ : Omega => (Pi.single i (1 : Complex) : n → Complex) b) := by
      funext omega
      exact congrFun (Matrix.updateRow_self (M := A omega)
        (i := j) (b := Pi.single i 1)) b
    rw [heq]
    exact stronglyMeasurable_const
  · have heq : (fun omega =>
        (A omega).updateRow j (Pi.single i 1) a b) =
        (fun omega => A omega a b) := by
      funext omega
      exact congrFun (Matrix.updateRow_ne (M := A omega)
        (b := Pi.single i 1) h) b
    rw [heq]
    exact hA a b

theorem matrix_nonsingInv_entry_stronglyMeasurable
    {Omega n : Type*} [mOmega : MeasurableSpace Omega]
    [Fintype n] [DecidableEq n]
    (m : MeasurableSpace Omega)
    (A : Omega → Matrix n n Complex)
    (hA : ∀ i j,
      @StronglyMeasurable Omega Complex _ m (fun omega => A omega i j))
    (i j : n) :
    @StronglyMeasurable Omega Complex _ m
      (fun omega => (A omega)⁻¹ i j) := by
  letI : MeasurableSpace Omega := m
  have hdet := matrix_det_stronglyMeasurable m A hA
  have hadj := matrix_adjugate_entry_stronglyMeasurable m A hA i j
  have heq : (fun omega => (A omega)⁻¹ i j) =
      (fun omega => (A omega).det)⁻¹ *
        (fun omega => (A omega).adjugate i j) := by
    funext omega
    simp [Matrix.inv_def, Ring.inverse_eq_inv]
  rw [heq]
  exact hdet.inv₀.mul hadj

theorem matrix_mul_entry_stronglyMeasurable
    {Omega m n p : Type*} [mOmega : MeasurableSpace Omega]
    [Fintype n]
    (ms : MeasurableSpace Omega)
    (A : Omega → Matrix m n Complex)
    (B : Omega → Matrix n p Complex)
    (hA : ∀ i j,
      @StronglyMeasurable Omega Complex _ ms (fun omega => A omega i j))
    (hB : ∀ i j,
      @StronglyMeasurable Omega Complex _ ms (fun omega => B omega i j))
    (i : m) (j : p) :
    @StronglyMeasurable Omega Complex _ ms
      (fun omega => (A omega * B omega) i j) := by
  letI : MeasurableSpace Omega := ms
  simp_rw [Matrix.mul_apply]
  fun_prop

end BernoulliSection9
