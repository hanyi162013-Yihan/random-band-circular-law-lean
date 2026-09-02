import BernoulliSection9.SingularValueMinMax
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

/-!
# Gram volume and singular values

The graph map `x |-> (x, T x)` has squared volume
`prod_i (1 + s_i(T)^2)`.  This gives a basis-free bridge between the
all-minor Gram volume from the read-only Section 9.1.3 dependency and the
large-singular-value product extracted by RRQR.
-/

open scoped BigOperators InnerProductSpace Matrix

noncomputable section

namespace BernoulliSection9

open Module

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace Complex E]
variable [NormedAddCommGroup F] [InnerProductSpace Complex F]
variable [FiniteDimensional Complex E] [FiniteDimensional Complex F]

/-- The injective graph map associated with a linear map. -/
def singularGraph (T : E →ₗ[Complex] F) :
    E →ₗ[Complex] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 Complex (E × F)).symm.toLinearMap.comp
    (LinearMap.prod LinearMap.id T)

@[simp] theorem singularGraph_apply (T : E →ₗ[Complex] F) (x : E) :
    singularGraph T x = WithLp.toLp 2 (x, T x) := rfl

/-- In the right singular-vector basis, the graph Gram matrix is diagonal. -/
theorem singularGraph_gram_eigenvectorBasis (T : E →ₗ[Complex] F) :
    Matrix.gram Complex
        (fun i : Fin (finrank Complex E) =>
          singularGraph T
            (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i)) =
      Matrix.diagonal (fun i : Fin (finrank Complex E) =>
        ((1 + T.singularValues i ^ 2 : Real) : Complex)) := by
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  ext i j
  change inner Complex (b i) (b j) + inner Complex (T (b i)) (T (b j)) =
    if i = j then ((1 + T.singularValues i ^ 2 : Real) : Complex) else 0
  rw [← LinearMap.adjoint_inner_right T (b i) (T (b j))]
  change inner Complex (b i) (b j) +
      inner Complex (b i) ((LinearMap.adjoint T ∘ₗ T) (b j)) = _
  change inner Complex (b i) (b j) +
      inner Complex (b i)
        ((LinearMap.adjoint T ∘ₗ T)
          ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl) j)) = _
  rw [T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis]
  rw [inner_smul_right]
  change inner Complex (b i) (b j) +
      ((T.isSymmetric_adjoint_comp_self.eigenvalues rfl j : Real) : Complex) *
        inner Complex (b i) (b j) = _
  rw [b.inner_eq_ite]
  rw [T.sq_singularValues_fin rfl]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

/-- Exact squared graph volume as the product of `1 + s_i(T)^2`. -/
theorem singularGraph_normDet_sq (T : E →ₗ[Complex] F) :
    (singularGraph T).normDet ^ 2 =
      ∏ i : Fin (finrank Complex E), (1 + T.singularValues i ^ 2) := by
  have hgram := (singularGraph T).normDet_sq_eq_det_gram
    (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl)
  rw [singularGraph_gram_eigenvectorBasis, Matrix.det_diagonal] at hgram
  norm_cast at hgram
  exact Complex.ofReal_injective hgram

/-- Product of the singular values whose indices precede the cutoff `r`.
Writing the cutoff this way also covers `r` larger than the ambient
dimension without a separate coercion convention. -/
def largeSingularProduct (T : E →ₗ[Complex] F) (r : Nat) : Real :=
  ∏ i ∈ (Finset.univ.filter fun i : Fin (finrank Complex E) => (i : Nat) < r),
    T.singularValues i

theorem largeSingularProduct_nonneg (T : E →ₗ[Complex] F) (r : Nat) :
    0 <= largeSingularProduct T r := by
  exact Finset.prod_nonneg fun i _ => T.singularValues_nonneg i

theorem largeSingularProduct_pos
    (T : E →ₗ[Complex] F) (r : Nat) (tau : Real)
    (htau : 0 <= tau)
    (hlarge : ∀ i : Fin (finrank Complex E), (i : Nat) < r ->
      tau < T.singularValues i) :
    0 < largeSingularProduct T r := by
  apply Finset.prod_pos
  intro i hi
  exact htau.trans_lt (hlarge i (by simpa [largeSingularProduct] using hi))

theorem largeSingularProduct_sq_eq_prod_ite
    (T : E →ₗ[Complex] F) (r : Nat) :
    largeSingularProduct T r ^ 2 =
      ∏ i : Fin (finrank Complex E),
        (if (i : Nat) < r then T.singularValues i ^ 2 else 1) := by
  rw [largeSingularProduct, ← Finset.prod_pow]
  simpa using
    (Fintype.prod_ite_mem
      (Finset.univ.filter fun i : Fin (finrank Complex E) => (i : Nat) < r)
      (fun i => T.singularValues i ^ 2)).symm

/-- The selected large-singular-value product is always bounded above by
the graph volume. -/
theorem largeSingularProduct_le_graph_normDet
    (T : E →ₗ[Complex] F) (r : Nat) :
    largeSingularProduct T r <= (singularGraph T).normDet := by
  rw [← sq_le_sq₀ (largeSingularProduct_nonneg T r)
    (LinearMap.normDet_nonneg (singularGraph T)), singularGraph_normDet_sq]
  let selected : Finset (Fin (finrank Complex E)) :=
    Finset.univ.filter fun i => (i : Nat) < r
  have hfactor : ∀ i : Fin (finrank Complex E),
      (if i ∈ selected then T.singularValues i ^ 2 else 1) <=
        1 + T.singularValues i ^ 2 := by
    intro i
    split_ifs
    · linarith
    · exact le_add_of_nonneg_right (sq_nonneg _)
  calc
    largeSingularProduct T r ^ 2 =
        ∏ i : Fin (finrank Complex E),
          (if i ∈ selected then T.singularValues i ^ 2 else 1) := by
      simpa [selected] using largeSingularProduct_sq_eq_prod_ite T r
    _ <= ∏ i : Fin (finrank Complex E),
        (1 + T.singularValues i ^ 2) :=
      Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hfactor i)

/-- If precisely the indices before `r` are above a threshold `tau >= 1`,
the graph volume loses only the explicit polynomial factor
`(2*tau)^dim`. -/
theorem graph_normDet_le_threshold_factor_mul_largeSingularProduct
    (T : E →ₗ[Complex] F) (r : Nat) (tau : Real)
    (htau : 1 <= tau)
    (hlarge : ∀ i : Fin (finrank Complex E), (i : Nat) < r ->
      tau < T.singularValues i)
    (hsmall : ∀ i : Fin (finrank Complex E), r <= (i : Nat) ->
      T.singularValues i <= tau) :
    (singularGraph T).normDet <=
      (2 * tau) ^ (finrank Complex E) * largeSingularProduct T r := by
  have hK : 0 <= 2 * tau := by positivity
  have hright : 0 <=
      (2 * tau) ^ (finrank Complex E) * largeSingularProduct T r :=
    mul_nonneg (pow_nonneg hK _) (largeSingularProduct_nonneg T r)
  rw [← sq_le_sq₀ (LinearMap.normDet_nonneg (singularGraph T)) hright,
    singularGraph_normDet_sq]
  let selected : Finset (Fin (finrank Complex E)) :=
    Finset.univ.filter fun i => (i : Nat) < r
  have hKsq : 2 <= (2 * tau) ^ 2 := by nlinarith [sq_nonneg tau]
  have hfactor : ∀ i : Fin (finrank Complex E),
      1 + T.singularValues i ^ 2 <=
        (2 * tau) ^ 2 *
          (if i ∈ selected then T.singularValues i ^ 2 else 1) := by
    intro i
    by_cases hi : i ∈ selected
    · rw [if_pos hi]
      have hir : (i : Nat) < r := by simpa [selected] using hi
      have hs1 : 1 <= T.singularValues i :=
        htau.trans (hlarge i hir).le
      have hone : 1 + T.singularValues i ^ 2 <=
          2 * T.singularValues i ^ 2 := by nlinarith
      exact hone.trans
        (mul_le_mul_of_nonneg_right hKsq (sq_nonneg _))
    · rw [if_neg hi, mul_one]
      have hir : r <= (i : Nat) := by
        simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        omega
      have hs0 := T.singularValues_nonneg i
      have hs := hsmall i hir
      nlinarith [sq_nonneg (tau - T.singularValues i), sq_nonneg tau]
  have hprod :
      (∏ i : Fin (finrank Complex E), (1 + T.singularValues i ^ 2)) <=
        ∏ i : Fin (finrank Complex E),
          ((2 * tau) ^ 2 *
            (if i ∈ selected then T.singularValues i ^ 2 else 1)) := by
    exact Finset.prod_le_prod (fun i _ => by positivity)
      (fun i _ => hfactor i)
  calc
    ∏ i : Fin (finrank Complex E), (1 + T.singularValues i ^ 2) <=
        ∏ i : Fin (finrank Complex E),
          ((2 * tau) ^ 2 *
            (if i ∈ selected then T.singularValues i ^ 2 else 1)) := hprod
    _ = ((2 * tau) ^ 2) ^ (finrank Complex E) *
          largeSingularProduct T r ^ 2 := by
      rw [Finset.prod_mul_distrib]
      rw [show (∏ i : Fin (finrank Complex E),
          (if i ∈ selected then T.singularValues i ^ 2 else 1)) =
          largeSingularProduct T r ^ 2 by
        simpa [selected] using (largeSingularProduct_sq_eq_prod_ite T r).symm]
      simp
    _ = ((2 * tau) ^ (finrank Complex E) *
          largeSingularProduct T r) ^ 2 := by
      conv_rhs => rw [mul_pow]
      congr 1
      calc
        ((2 * tau) ^ 2) ^ (finrank Complex E) =
            (2 * tau) ^ (2 * finrank Complex E) := by
          rw [pow_mul]
        _ = (2 * tau) ^ (finrank Complex E * 2) := by
          congr 1
          omega
        _ = ((2 * tau) ^ (finrank Complex E)) ^ 2 := by
          rw [pow_mul]

end BernoulliSection9
