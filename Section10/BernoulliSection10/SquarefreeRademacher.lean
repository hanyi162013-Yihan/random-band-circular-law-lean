import BernoulliSection10.RademacherTensor
import BernoulliSection10.PacketFrameProbability

open scoped BigOperators

noncomputable section

namespace BernoulliSection10

open MvPolynomial BernoulliLinearAlgebra

set_option maxHeartbeats 800000

/-- Split a Boolean cube into its first bit and remaining tail, with the
first bit indexed by the two affine coefficients. -/
def finTwoTailEquiv (n : ℕ) :
    (Fin 2 × (Fin n → Bool)) ≃ (Fin (n + 1) → Bool) :=
  (Equiv.prodCongr finTwoEquiv (Equiv.refl _)).trans
    (Fin.insertNthEquiv (fun _ : Fin (n + 1) ↦ Bool) 0)

@[simp] theorem finTwoTailEquiv_apply (n : ℕ)
    (j : Fin 2) (b : Fin n → Bool) :
    finTwoTailEquiv n (j, b) = Fin.cons (finTwoEquiv j) b := by
  funext i
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · simp [finTwoTailEquiv, Fin.insertNthEquiv, Fin.insertNth_zero']
  · simp [finTwoTailEquiv, Fin.insertNthEquiv, Fin.insertNth_zero']

/-- Reshape the coefficient function on a Boolean cube into the recursive
Euclidean tensor with one scalar atom in each group. -/
def boolCoefficientTensor : ∀ (n : ℕ),
    ((Fin n → Bool) → ℂ) →
      MultiAffineTensor ℂ (List.replicate n 1)
  | 0, c => c (fun i ↦ Fin.elim0 i)
  | n + 1, c => WithLp.toLp 2 (fun j : Fin 2 ↦
      boolCoefficientTensor n (fun b ↦ c (finTwoTailEquiv n (j, b))))

theorem norm_boolCoefficientTensor_sq : ∀ (n : ℕ)
    (c : (Fin n → Bool) → ℂ),
    ‖boolCoefficientTensor n c‖ ^ 2 = ∑ b, ‖c b‖ ^ 2 := by
  intro n
  induction n with
  | zero =>
      intro c
      rw [show (∑ b : Fin 0 → Bool, ‖c b‖ ^ 2) =
          ‖c (fun i ↦ Fin.elim0 i)‖ ^ 2 by
        apply Fintype.sum_unique]
      rfl
  | succ n ih =>
      intro c
      change ‖(WithLp.toLp 2 (fun j : Fin 2 ↦
        boolCoefficientTensor n
          (fun b ↦ c (finTwoTailEquiv n (j, b)))) :
          PiLp 2 (fun _ : Fin 2 ↦
            MultiAffineTensor ℂ (List.replicate n 1)))‖ ^ 2 = _
      rw [PiLp.norm_sq_eq_of_L2]
      simp_rw [ih]
      symm
      calc
        (∑ b : Fin (n + 1) → Bool, ‖c b‖ ^ 2) =
            ∑ q : Fin 2 × (Fin n → Bool),
              ‖c (finTwoTailEquiv n q)‖ ^ 2 := by
          exact Fintype.sum_equiv (finTwoTailEquiv n).symm
            (fun b : Fin (n + 1) → Bool ↦ ‖c b‖ ^ 2)
            (fun q : Fin 2 × (Fin n → Bool) ↦
              ‖c (finTwoTailEquiv n q)‖ ^ 2)
            (fun b ↦ by simp)
        _ = ∑ j : Fin 2, ∑ b : Fin n → Bool,
              ‖c (finTwoTailEquiv n (j, b))‖ ^ 2 := by
          rw [Fintype.sum_prod_type]

/-- Walsh evaluation of a coefficient function on the Boolean cube. -/
def boolWalshEval (n : ℕ) (c : (Fin n → Bool) → ℂ)
    (x : Fin n → ℝ) : ℂ :=
  ∑ b, c b * ∏ i, if b i then (x i : ℂ) else 1

theorem multiAffineEval_boolCoefficientTensor : ∀ (n : ℕ)
    (c : (Fin n → Bool) → ℂ) (x : Fin n → ℝ),
    multiAffineEval (boolCoefficientTensor n c)
      (finRowsToMultiAffineRows 1 n (fun i _ ↦ x i)) =
        boolWalshEval n c x := by
  intro n
  induction n with
  | zero =>
      intro c x
      unfold boolWalshEval
      rw [Fintype.sum_unique]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
      change c _ = c _
      apply congrArg c
      exact Subsingleton.elim _ _
  | succ n ih =>
      intro c x
      let c0 := boolCoefficientTensor n
        (fun b ↦ c (finTwoTailEquiv n (0, b)))
      let c1 := boolCoefficientTensor n
        (fun b ↦ c (finTwoTailEquiv n (1, b)))
      have hhead : multiAffineHeadEval (boolCoefficientTensor (n + 1) c)
          (fun _ : Fin 1 ↦ x 0) = c0 + x 0 • c1 := by
        change affineValue c0 (fun _ : Fin 1 ↦ c1) (fun _ ↦ x 0) = _
        simp [affineValue]
      change multiAffineEval
          (multiAffineHeadEval (boolCoefficientTensor (n + 1) c)
            (fun _ : Fin 1 ↦ x 0))
          (finRowsToMultiAffineRows 1 n
            (fun i _ ↦ Fin.tail x i)) = _
      rw [hhead, multiAffineEval_add, multiAffineEval_smul,
        ih, ih]
      unfold boolWalshEval
      rw [show (∑ b : Fin (n + 1) → Bool,
          c b * ∏ i, if b i then (x i : ℂ) else 1) =
          ∑ q : Fin 2 × (Fin n → Bool),
            c (finTwoTailEquiv n q) *
              ∏ i, if finTwoTailEquiv n q i then (x i : ℂ) else 1 by
        exact Fintype.sum_equiv (finTwoTailEquiv n).symm
          (fun b : Fin (n + 1) → Bool ↦
            c b * ∏ i, if b i then (x i : ℂ) else 1)
          (fun q : Fin 2 × (Fin n → Bool) ↦
            c (finTwoTailEquiv n q) *
              ∏ i, if finTwoTailEquiv n q i then (x i : ℂ) else 1)
          (fun b ↦ by simp)]
      rw [Fintype.sum_prod_type, Fin.sum_univ_two]
      simp only [finTwoTailEquiv_apply]
      simp [Fin.prod_univ_succ, finTwoEquiv, c0, c1, Fin.tail]
      rw [Finset.mul_sum]
      ring

/-- Boolean membership functions are equivalent to finite subsets on a
finite type. -/
def boolFunctionFinsetEquiv (v : Type*) [Fintype v] [DecidableEq v] :
    (v → Bool) ≃ Finset v where
  toFun b := Finset.univ.filter (fun i ↦ b i = true)
  invFun S := fun i ↦ decide (i ∈ S)
  left_inv b := by
    funext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases h : b i <;> simp [h]
  right_inv S := by
    ext i
    simp

@[simp] theorem mem_boolFunctionFinsetEquiv
    {v : Type*} [Fintype v] [DecidableEq v]
    (b : v → Bool) (i : v) :
    i ∈ boolFunctionFinsetEquiv v b ↔ b i = true := by
  simp [boolFunctionFinsetEquiv]

/-- Enumerate an arbitrary finite variable type and then read a Boolean
cube point as its corresponding finite subset. -/
def finBoolCubeFinsetEquiv (v : Type*) [Fintype v] [DecidableEq v] :
    (Fin (Fintype.card v) → Bool) ≃ Finset v :=
  (Equiv.arrowCongr (Fintype.equivFin v).symm (Equiv.refl Bool)).trans
    (boolFunctionFinsetEquiv v)

@[simp] theorem mem_finBoolCubeFinsetEquiv
    {v : Type*} [Fintype v] [DecidableEq v]
    (b : Fin (Fintype.card v) → Bool) (i : v) :
    i ∈ finBoolCubeFinsetEquiv v b ↔
      b (Fintype.equivFin v i) = true := by
  simp [finBoolCubeFinsetEquiv, Equiv.arrowCongr]

/-- The Boolean-cube tensor of all squarefree coefficients has exactly the
paper's complete Euclidean coefficient norm. -/
theorem norm_boolCoefficientTensor_squarefree_coeff
    {v : Type*} [Fintype v] [DecidableEq v]
    (P : MvPolynomial v ℂ) :
    ‖boolCoefficientTensor (Fintype.card v)
        (fun b ↦ coeff (squarefreeExponent (finBoolCubeFinsetEquiv v b)) P)‖ =
      ‖(WithLp.toLp 2 (fun S : Finset v ↦
          coeff (squarefreeExponent S) P) : CoeffSpace v)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_boolCoefficientTensor_sq, PiLp.norm_sq_eq_of_L2]
  exact Fintype.sum_equiv (finBoolCubeFinsetEquiv v)
    (fun b ↦ ‖coeff (squarefreeExponent (finBoolCubeFinsetEquiv v b)) P‖ ^ 2)
    (fun S ↦ ‖coeff (squarefreeExponent S) P‖ ^ 2)
    (fun b ↦ rfl)

theorem prod_finBoolCubeFinsetEquiv
    {v : Type*} [Fintype v] [DecidableEq v]
    (b : Fin (Fintype.card v) → Bool)
    (x : Fin (Fintype.card v) → ℝ) :
    (∏ i : finBoolCubeFinsetEquiv v b,
        (x (Fintype.equivFin v i) : ℂ)) =
      ∏ j, if b j then (x j : ℂ) else 1 := by
  classical
  let S : Finset v := finBoolCubeFinsetEquiv v b
  let T : Finset (Fin (Fintype.card v)) :=
    Finset.univ.filter (fun j ↦ b j = true)
  let e : S ≃ T := Equiv.subtypeEquiv (Fintype.equivFin v) (by
    intro i
    simp [S, T])
  calc
    (∏ i : S, (x (Fintype.equivFin v i) : ℂ)) =
        ∏ j : T, (x j : ℂ) := by
      exact Fintype.prod_equiv e
        (fun i : S ↦ (x (Fintype.equivFin v i) : ℂ))
        (fun j : T ↦ (x j : ℂ)) (fun i ↦ rfl)
    _ = ∏ j ∈ T, (x j : ℂ) := by
      exact Finset.prod_coe_sort (s := T) (f := fun j ↦ (x j : ℂ))
    _ = ∏ j, if b j then (x j : ℂ) else 1 := by
      dsimp only [T]
      rw [Finset.prod_filter]

/-- The Walsh sum of the complete squarefree coefficient vector is exactly
the original polynomial evaluation at the corresponding real sign
assignment. -/
theorem boolWalshEval_squarefree_coeff_eq_eval
    {v : Type*} [Fintype v] [DecidableEq v]
    (P : MvPolynomial v ℂ) (hP : HasSquarefreeSupport P)
    (x : Fin (Fintype.card v) → ℝ) :
    boolWalshEval (Fintype.card v)
        (fun b ↦ coeff (squarefreeExponent (finBoolCubeFinsetEquiv v b)) P) x =
      eval (fun i ↦ (x (Fintype.equivFin v i) : ℂ)) P := by
  rw [eval_eq_sum_squarefree_coeff P hP]
  unfold boolWalshEval
  symm
  apply Fintype.sum_equiv (finBoolCubeFinsetEquiv v).symm
  intro S
  simp only [Equiv.apply_symm_apply]
  congr 1
  have hp := prod_finBoolCubeFinsetEquiv
    ((finBoolCubeFinsetEquiv v).symm S) x
  have hS : finBoolCubeFinsetEquiv v
      ((finBoolCubeFinsetEquiv v).symm S) = S :=
    (finBoolCubeFinsetEquiv v).apply_symm_apply S
  rw [hS] at hp
  exact hp

/-- A squarefree complex polynomial has a real sign assignment whose
evaluation norm dominates the complete Euclidean coefficient norm. -/
theorem exists_squarefree_rademacher_norm_le_eval
    {v : Type*} [Fintype v] [DecidableEq v]
    (P : MvPolynomial v ℂ) (hP : HasSquarefreeSupport P) :
    ∃ a : v → ℝ,
      (∀ i, a i = 1 ∨ a i = -1) ∧
      ‖(WithLp.toLp 2 (fun S : Finset v ↦
          coeff (squarefreeExponent S) P) : CoeffSpace v)‖ ≤
        ‖eval (fun i ↦ (a i : ℂ)) P‖ := by
  let c := boolCoefficientTensor (Fintype.card v)
    (fun b ↦ coeff (squarefreeExponent (finBoolCubeFinsetEquiv v b)) P)
  obtain ⟨x, hx, hbound⟩ :=
    exists_rademacherRows_norm_le (Fintype.card v) c
  let a : v → ℝ := fun i ↦ x (Fintype.equivFin v i) 0
  refine ⟨a, ?_, ?_⟩
  · intro i
    exact hx (Fintype.equivFin v i) 0
  · rw [← norm_boolCoefficientTensor_squarefree_coeff P]
    change ‖c‖ ≤ ‖eval (fun i ↦ (a i : ℂ)) P‖
    calc
      ‖c‖ ≤ ‖multiAffineEval c
          (finRowsToMultiAffineRows 1 (Fintype.card v) x)‖ := hbound
      _ = ‖multiAffineEval c
          (finRowsToMultiAffineRows 1 (Fintype.card v)
            (fun i _ ↦ x i 0))‖ := by
        congr 3
        funext i j
        exact Fin.eq_zero j ▸ rfl
      _ = ‖boolWalshEval (Fintype.card v)
          (fun b ↦ coeff
            (squarefreeExponent (finBoolCubeFinsetEquiv v b)) P)
          (fun i ↦ x i 0)‖ := by
        rw [multiAffineEval_boolCoefficientTensor]
      _ = ‖eval (fun i ↦ (a i : ℂ)) P‖ := by
        rw [boolWalshEval_squarefree_coeff_eq_eval P hP]

end BernoulliSection10
