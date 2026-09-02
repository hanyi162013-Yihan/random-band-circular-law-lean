import BernoulliSection10.MultiAffine
import BernoulliSection10.HodgeIntegrability
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Coefficient-tensor bounds from zero/one-hot corners

The canonical coefficient tensor of a separately affine function is obtained
by iterated finite differences.  This module gives a deliberately coarse but
dimensionally sharp bound on its Euclidean norm using only the values where
each row is zero or a standard coordinate vector.
-/

open scoped BigOperators Matrix Matrix.Norms.Frobenius

noncomputable section

namespace BernoulliSection10

/-- Recursive row configurations in which every row is either zero or a
standard coordinate vector. -/
def IsReplicatedCorner (p : ℕ) :
    (n : ℕ) → MultiAffineRows (List.replicate n p) → Prop
  | 0, _ => True
  | n + 1, x =>
      (x.1 = 0 ∨ ∃ s : Fin p, x.1 = Pi.single s 1) ∧
        IsReplicatedCorner p n x.2

/-- Every scalar coordinate of a zero/one-hot corner has absolute value at
most one, after flattening the recursive row representation. -/
theorem abs_multiAffineRowsToFinRows_le_one_of_corner
    (p : ℕ) : ∀ (n : ℕ)
    (x : MultiAffineRows (List.replicate n p)),
    IsReplicatedCorner p n x →
    ∀ (i : Fin n) (a : Fin p),
      |multiAffineRowsToFinRows p n x i a| ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro x hx i
      exact Fin.elim0 i
  | succ n ih =>
      intro x hx i a
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · rcases hx.1 with hzero | ⟨s, hs⟩
        · simp [multiAffineRowsToFinRows, hzero]
        · change |x.1 a| ≤ 1
          rw [hs]
          classical
          by_cases ha : a = s <;> simp [Pi.single_apply, ha]
      · simpa [multiAffineRowsToFinRows] using ih x.2 hx.2 j a

/-- The Euclidean norm of a finite `PiLp 2` tuple is bounded by the sum of
the component norms. -/
theorem norm_piLp_two_le_sum
    {ι : Type*} [Fintype ι]
    {β : ι → Type*} [∀ i, SeminormedAddCommGroup (β i)]
    (x : PiLp 2 β) :
    ‖x‖ ≤ ∑ i, ‖x i‖ := by
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  calc
    ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := PiLp.norm_sq_eq_of_L2 β x
    _ ≤ (∑ i, ‖x i‖) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg
        (fun _ _ ↦ norm_nonneg _)

/-- A coarse Frobenius bound by a uniform entry bound.  Using the product of
the two dimensions, rather than its square root, keeps later arithmetic
elementary and is more than sufficient after taking logarithms. -/
theorem frobenius_norm_le_card_mul_of_entry_norm_le
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ i j, ‖A i j‖ ≤ M) :
    ‖A‖ ≤ (Fintype.card m : ℝ) * Fintype.card n * M := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp_rw [Real.rpow_two]
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · let C : ℕ := Fintype.card m * Fintype.card n
    have hsum : ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤
        ∑ _i : m, ∑ _j : n, M ^ 2 := by
      gcongr with i j
      nlinarith [norm_nonneg (A i j), h i j]
    have hcount : (∑ _i : m, ∑ _j : n, M ^ 2) = (C : ℝ) * M ^ 2 := by
      simp [C]
      ring
    rw [hcount] at hsum
    rw [← Nat.cast_mul]
    change ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ ((C : ℝ) * M) ^ 2
    by_cases hC : C = 0
    · simpa [hC] using hsum
    · have hC1 : (1 : ℝ) ≤ C := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hC)
      have hC0 : (0 : ℝ) ≤ C := by positivity
      have hCC : (C : ℝ) ≤ (C : ℝ) * C := by
        calc
          (C : ℝ) = (C : ℝ) * 1 := by ring
          _ ≤ (C : ℝ) * C := mul_le_mul_of_nonneg_left hC1 hC0
      calc
        ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ (C : ℝ) * M ^ 2 := hsum
        _ ≤ ((C : ℝ) * C) * M ^ 2 :=
          mul_le_mul_of_nonneg_right hCC (sq_nonneg M)
        _ = ((C : ℝ) * M) ^ 2 := by ring

/-- The standard Leibniz bound for a minor of a complex matrix whose entries
are uniformly bounded. -/
theorem norm_minor_le_factorial_mul_pow
    {m n : Type*} [Fintype m] [LinearOrder m]
    [Fintype n] [LinearOrder n]
    (k : ℕ) (A : Matrix m n ℂ) (s : Set.powersetCard m k)
    (t : Set.powersetCard n k) (M : ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ M) :
    ‖BernoulliLinearAlgebra.minor k A s t‖ ≤ k.factorial * M ^ k := by
  unfold BernoulliLinearAlgebra.minor
  change (NormedField.toAbsoluteValue ℂ)
      (A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
        (Set.powersetCard.ofFinEmbEquiv.symm t)).det ≤
    k.factorial * M ^ k
  simpa only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_factorial] using
    (Matrix.det_le (A := A.submatrix
      (Set.powersetCard.ofFinEmbEquiv.symm s)
      (Set.powersetCard.ofFinEmbEquiv.symm t))
      (abv := NormedField.toAbsoluteValue ℂ) (x := M)
      (fun i j ↦ h _ _))

/-- If a function is bounded by `M` at every zero/one-hot row corner, its
canonical Euclidean coefficient tensor is bounded by
`(1+2p)^n M`.  The factor comes from one constant coefficient and `p`
first differences at each row. -/
theorem norm_multiAffineTensorOfFunction_le_of_corner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℕ) : ∀ (n : ℕ)
    (F : MultiAffineRows (List.replicate n p) → E) (M : ℝ),
    0 ≤ M →
    (∀ x, IsReplicatedCorner p n x → ‖F x‖ ≤ M) →
    ‖multiAffineTensorOfFunction F‖ ≤
      (1 + 2 * (p : ℝ)) ^ n * M := by
  intro n
  induction n with
  | zero =>
      intro F M hM hcorner
      change ‖(show E from multiAffineTensorOfFunction F)‖ ≤
        (1 + 2 * (p : ℝ)) ^ 0 * M
      change ‖F PUnit.unit‖ ≤ (1 + 2 * (p : ℝ)) ^ 0 * M
      simpa only [pow_zero, one_mul] using hcorner PUnit.unit trivial
  | succ n ih =>
      intro F M hM hcorner
      let F₀ : MultiAffineRows (List.replicate n p) → E :=
        fun tail ↦ F (0, tail)
      let FΔ : Fin p → MultiAffineRows (List.replicate n p) → E :=
        fun s tail ↦ F (Pi.single s 1, tail) - F (0, tail)
      have h₀ : ‖multiAffineTensorOfFunction F₀‖ ≤
          (1 + 2 * (p : ℝ)) ^ n * M := by
        apply ih F₀ M hM
        intro tail htail
        exact hcorner (0, tail) ⟨Or.inl rfl, htail⟩
      have hΔ (s : Fin p) : ‖multiAffineTensorOfFunction (FΔ s)‖ ≤
          (1 + 2 * (p : ℝ)) ^ n * (2 * M) := by
        apply ih (FΔ s) (2 * M) (mul_nonneg (by norm_num) hM)
        intro tail htail
        calc
          ‖FΔ s tail‖ ≤
              ‖F (Pi.single s 1, tail)‖ + ‖F (0, tail)‖ := by
            exact norm_sub_le _ _
          _ ≤ M + M := add_le_add
            (hcorner (Pi.single s 1, tail)
              ⟨Or.inr ⟨s, rfl⟩, htail⟩)
            (hcorner (0, tail) ⟨Or.inl rfl, htail⟩)
          _ = 2 * M := by ring
      let T := multiAffineTensorOfFunction F
      change ‖(show PiLp 2 (fun _ : Fin (p + 1) ↦
          MultiAffineTensor E (List.replicate n p)) from T)‖ ≤ _
      calc
        ‖(show PiLp 2 (fun _ : Fin (p + 1) ↦
            MultiAffineTensor E (List.replicate n p)) from T)‖ ≤
            ∑ a : Fin (p + 1),
              ‖multiAffineTensorHead T a‖ := by
          exact norm_piLp_two_le_sum _
        _ = ‖multiAffineTensorHead T 0‖ +
            ∑ s : Fin p, ‖multiAffineTensorHead T s.succ‖ := by
          rw [Fin.sum_univ_succ]
        _ ≤ (1 + 2 * (p : ℝ)) ^ n * M +
            ∑ _s : Fin p,
              ((1 + 2 * (p : ℝ)) ^ n * (2 * M)) := by
          apply add_le_add
          · simpa only [T, F₀,
              multiAffineTensorHead_tensorOfFunction_zero] using h₀
          · apply Finset.sum_le_sum
            intro s _hs
            simpa only [T, FΔ,
              multiAffineTensorHead_tensorOfFunction_succ] using hΔ s
        _ = (1 + 2 * (p : ℝ)) ^ (n + 1) * M := by
          rw [pow_succ]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring

end BernoulliSection10
