import BernoulliLinearAlgebra.CoefficientTranslation
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Coefficientwise continuity of parameterized polynomials

The final dense-chart argument needs continuity of a determinant coefficient
vector as the boundary matrix varies.  The lemmas here provide a reusable
route: coefficientwise-continuous polynomial families are closed under all
ring operations, finite products, finite sums, and finite matrix
determinants.  No topology on the whole `MvPolynomial` type is required.
-/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open MvPolynomial Matrix

variable {X v : Type*} [TopologicalSpace X]

/-- Every fixed polynomial coefficient varies continuously with the
parameter. -/
def CoeffwiseContinuous (p : X → MvPolynomial v ℂ) : Prop :=
  ∀ d : v →₀ ℕ, Continuous fun x => coeff d (p x)

namespace CoeffwiseContinuous

theorem const (p : MvPolynomial v ℂ) :
    CoeffwiseContinuous (fun _ : X => p) := by
  intro d
  fun_prop

theorem C {f : X → ℂ} (hf : Continuous f) :
    CoeffwiseContinuous (fun x =>
      MvPolynomial.C (σ := v) (f x)) := by
  intro d
  classical
  by_cases hd : d = (0 : v →₀ ℕ)
  · subst d
    simpa using hf
  · simpa [MvPolynomial.coeff_C, hd, Ne.symm hd] using
      (continuous_const : Continuous fun _ : X => (0 : ℂ))

theorem add {p q : X → MvPolynomial v ℂ}
    (hp : CoeffwiseContinuous p) (hq : CoeffwiseContinuous q) :
    CoeffwiseContinuous (fun x => p x + q x) := by
  intro d
  have heq : (fun x => coeff d (p x + q x)) =
      fun x => coeff d (p x) + coeff d (q x) := by
    funext x
    simp
  rw [heq]
  exact (hp d).add (hq d)

theorem neg {p : X → MvPolynomial v ℂ}
    (hp : CoeffwiseContinuous p) :
    CoeffwiseContinuous (fun x => -p x) := by
  intro d
  have heq : (fun x => coeff d (-p x)) =
      fun x => -(coeff d (p x)) := by
    funext x
    simp
  rw [heq]
  exact (hp d).neg

theorem sub {p q : X → MvPolynomial v ℂ}
    (hp : CoeffwiseContinuous p) (hq : CoeffwiseContinuous q) :
    CoeffwiseContinuous (fun x => p x - q x) := by
  simpa [sub_eq_add_neg] using hp.add hq.neg

theorem mul [DecidableEq v] {p q : X → MvPolynomial v ℂ}
    (hp : CoeffwiseContinuous p) (hq : CoeffwiseContinuous q) :
    CoeffwiseContinuous (fun x => p x * q x) := by
  intro d
  simp_rw [MvPolynomial.coeff_mul]
  apply continuous_finsetSum
  intro ab hab
  exact (hp ab.1).mul (hq ab.2)

theorem finsetSum {ι : Type*} (s : Finset ι)
    {p : ι → X → MvPolynomial v ℂ}
    (hp : ∀ i ∈ s, CoeffwiseContinuous (p i)) :
    CoeffwiseContinuous (fun x => ∑ i ∈ s, p i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (X := X) (v := v) 0)
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hp i (by simp)).add <| ih fun j hj => hp j (by simp [hj])

theorem finsetProd [DecidableEq v] {ι : Type*} (s : Finset ι)
    {p : ι → X → MvPolynomial v ℂ}
    (hp : ∀ i ∈ s, CoeffwiseContinuous (p i)) :
    CoeffwiseContinuous (fun x => ∏ i ∈ s, p i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (X := X) (v := v) 1)
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (hp i (by simp)).mul <| ih fun j hj => hp j (by simp [hj])

end CoeffwiseContinuous

section Determinant

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite determinant is coefficientwise continuous whenever each matrix
entry is coefficientwise continuous. -/
theorem coeffwiseContinuous_det [DecidableEq v]
    (A : X → Matrix ι ι (MvPolynomial v ℂ))
    (hA : ∀ i j, CoeffwiseContinuous fun x => A x i j) :
    CoeffwiseContinuous fun x => (A x).det := by
  classical
  have hterm : ∀ σ : Equiv.Perm ι,
      CoeffwiseContinuous fun x =>
        (((Equiv.Perm.sign σ : ℤ) : MvPolynomial v ℂ)) *
          ∏ i, A x (σ i) i := by
    intro σ
    apply (CoeffwiseContinuous.const
      (X := X) (v := v)
      (((Equiv.Perm.sign σ : ℤ) : MvPolynomial v ℂ))).mul
    exact CoeffwiseContinuous.finsetProd Finset.univ
      (fun i _ => hA (σ i) i)
  have hsum := CoeffwiseContinuous.finsetSum
    (X := X) (v := v) Finset.univ (fun σ _ => hterm σ)
  intro d
  have heq : (fun x => (A x).det) =
      fun x => ∑ σ : Equiv.Perm ι,
        (((Equiv.Perm.sign σ : ℤ) : MvPolynomial v ℂ)) *
          ∏ i, A x (σ i) i := by
    funext x
    exact Matrix.det_apply' (A x)
  rw [heq]
  exact hsum d

end Determinant

section CoefficientNorm

variable [Fintype v]

/-- The Euclidean norm of a finite coefficient family is continuous when
every coefficient is continuous. -/
theorem continuous_coeffVector_norm
    (c : X → CoeffSpace v)
    (hc : ∀ S : Finset v, Continuous fun x => c x S) :
    Continuous fun x => ‖c x‖ := by
  simp_rw [EuclideanSpace.norm_eq]
  apply Real.continuous_sqrt.comp
  apply continuous_finsetSum
  intro S hS
  exact (hc S).norm.pow 2

/-- Coefficientwise continuity gives continuity of the norm of any fixed
finite selection of polynomial coefficients. -/
theorem CoeffwiseContinuous.continuous_selectedCoeffNorm
    [DecidableEq v] (exponent : Finset v → (v →₀ ℕ))
    (p : X → MvPolynomial v ℂ) (hp : CoeffwiseContinuous p) :
    Continuous fun x =>
      ‖(WithLp.toLp 2 (fun S : Finset v =>
          coeff (exponent S) (p x)) : CoeffSpace v)‖ := by
  apply continuous_coeffVector_norm
  intro S
  exact hp (exponent S)

end CoefficientNorm

end BernoulliLinearAlgebra
