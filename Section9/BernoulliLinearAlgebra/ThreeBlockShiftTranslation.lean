import BernoulliLinearAlgebra.ThreeBlockMaskExpansion
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Spectral translation of the three-block determinant coefficients

The spectral parameter in the concrete terminal matrix subtracts `z` from
exactly the fresh diagonal variables.  This file identifies that substitution
with the triangular coefficient operator from `CoefficientTranslation`, and
then transports any zero-shift terminal comparison to an arbitrary spectral
parameter.
-/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix MvPolynomial

section SquarefreeTranslation

variable {v : Type*} [Fintype v] [DecidableEq v]

/-- Reconstruct a multiaffine polynomial from its squarefree coefficient
vector. -/
def squarefreePolynomial (c : CoeffSpace v) : MvPolynomial v ℂ :=
  ∑ S : Finset v, monomial (squarefreeExponent S) (c S)

@[simp] theorem coeff_squarefreePolynomial
    (c : CoeffSpace v) (S : Finset v) :
    coeff (squarefreeExponent S) (squarefreePolynomial c) = c S := by
  classical
  simp only [squarefreePolynomial, coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single S]
  · simp
  · intro T _ hTS
    rw [if_neg]
    exact fun h => hTS (squarefreeExponent_injective h)
  · simp

/-- Substitute `X i + t` for the variable `X i`. -/
def singleShiftPolynomial (i : v) (t : ℂ) :
    MvPolynomial v ℂ →ₐ[ℂ] MvPolynomial v ℂ :=
  bind₁ fun j => if j = i then X j + C t else X j

omit [Fintype v] in
theorem singleShiftPolynomial_prod_X
    (i : v) (t : ℂ) (S : Finset v) :
    singleShiftPolynomial i t
        (∏ j ∈ S, (X j : MvPolynomial v ℂ)) =
      (∏ j ∈ S, (X j : MvPolynomial v ℂ)) +
        if i ∈ S then
          C t * ∏ j ∈ S.erase i, (X j : MvPolynomial v ℂ)
        else 0 := by
  classical
  rw [map_prod]
  simp only [singleShiftPolynomial, bind₁_X_right]
  by_cases hi : i ∈ S
  · rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hi]
    simp only [hi, if_pos, Finset.sdiff_singleton_eq_erase]
    have hrest :
        (∏ j ∈ S.erase i,
            (if j = i then X j + C t else X j)) =
          ∏ j ∈ S.erase i, (X j : MvPolynomial v ℂ) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [if_neg (Finset.ne_of_mem_erase hj)]
    rw [hrest, add_mul]
    have hprod := Finset.prod_erase_mul S
      (fun j => (X j : MvPolynomial v ℂ)) hi
    rw [← hprod]
    ac_rfl
  · have hif : ∀ j ∈ S,
        (if j = i then X j + C t else X j) =
          (X j : MvPolynomial v ℂ) := by
      intro j hj
      rw [if_neg (fun h : j = i => hi (h ▸ hj))]
    rw [Finset.prod_congr rfl hif]
    simp [hi]

omit [Fintype v] in
theorem singleShiftPolynomial_monomial_squarefree
    (i : v) (t a : ℂ) (S : Finset v) :
    singleShiftPolynomial i t (monomial (squarefreeExponent S) a) =
      monomial (squarefreeExponent S) a +
        if i ∈ S then
          monomial (squarefreeExponent (S.erase i)) (a * t)
        else 0 := by
  classical
  have hmono : monomial (squarefreeExponent S) a =
      C a * ∏ j ∈ S, (X j : MvPolynomial v ℂ) := by
    rw [prod_X_eq_monomial, C_mul_monomial]
    simp
  have hC : singleShiftPolynomial i t (C a) = C a := by
    exact bind₁_C_right _ _
  rw [hmono, map_mul, hC, singleShiftPolynomial_prod_X]
  by_cases hi : i ∈ S
  · simp only [hi, if_pos]
    rw [mul_add, prod_X_eq_monomial, prod_X_eq_monomial,
      C_mul_monomial]
    rw [← mul_assoc, ← C_mul, C_mul_monomial]
    simp
  · simp [hi, prod_X_eq_monomial]

/-- Polynomial substitution by `X i + t` is exactly
`singleTranslateCoeff i t` on squarefree coefficient vectors. -/
theorem singleShiftPolynomial_squarefreePolynomial
    (i : v) (t : ℂ) (c : CoeffSpace v) :
    singleShiftPolynomial i t (squarefreePolynomial c) =
      squarefreePolynomial (singleTranslateCoeff i t c) := by
  classical
  unfold squarefreePolynomial
  rw [map_sum]
  simp_rw [singleShiftPolynomial_monomial_squarefree]
  rw [Finset.sum_add_distrib]
  have hsum :
      (∑ S : Finset v,
        if i ∈ S then
          monomial (squarefreeExponent (S.erase i)) (c S * t)
        else 0) =
      ∑ T : Finset v,
        if i ∈ T then 0 else
          monomial (squarefreeExponent T) (t * c (insert i T)) := by
    simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, zero_add]
    refine Finset.sum_bij (fun S _ => S.erase i) ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      exact Finset.notMem_erase i S
    · intro S₁ hS₁ S₂ hS₂ hEq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS₁ hS₂
      rw [← Finset.insert_erase hS₁, ← Finset.insert_erase hS₂, hEq]
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      refine ⟨insert i T, ?_, ?_⟩
      · simp
      · simp [hT]
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      rw [Finset.insert_erase hS, mul_comm]
  rw [hsum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  rw [show singleTranslateCoeff i t c S =
      if i ∈ S then c S else c S + t * c (insert i S) from rfl]
  by_cases hi : i ∈ S
  · simp [hi]
  · simp only [hi, if_false]
    exact (map_add (monomial (squarefreeExponent S)) _ _).symm

/-- Iterate polynomial substitutions in the same order as
`translateCoeffList`. -/
def translatePolynomialList :
    List (v × ℂ) → MvPolynomial v ℂ → MvPolynomial v ℂ
  | [], p => p
  | (i, t) :: shifts, p =>
      translatePolynomialList shifts (singleShiftPolynomial i t p)

theorem translatePolynomialList_squarefreePolynomial
    (shifts : List (v × ℂ)) (c : CoeffSpace v) :
    translatePolynomialList shifts (squarefreePolynomial c) =
      squarefreePolynomial (translateCoeffList shifts c) := by
  induction shifts generalizing c with
  | nil => rfl
  | cons it shifts ih =>
      rcases it with ⟨i, t⟩
      simp only [translatePolynomialList, translateCoeffList]
      rw [singleShiftPolynomial_squarefreePolynomial]
      exact ih _

end SquarefreeTranslation

section SquarefreeSupport

variable {v : Type*} [Fintype v] [DecidableEq v]

/-- Every nonzero monomial of `p` has a squarefree exponent. -/
def HasSquarefreeSupport (p : MvPolynomial v ℂ) : Prop :=
  ∀ m, (¬ ∃ S : Finset v, m = squarefreeExponent S) → coeff m p = 0

/-- A polynomial supported on squarefree exponents is recovered from its
squarefree coefficient vector. -/
theorem squarefreePolynomial_coefficients_eq
    (p : MvPolynomial v ℂ) (hp : HasSquarefreeSupport p) :
    squarefreePolynomial
        (WithLp.toLp 2 (fun S => coeff (squarefreeExponent S) p)) = p := by
  ext m
  by_cases hm : ∃ S : Finset v, m = squarefreeExponent S
  · rcases hm with ⟨S, rfl⟩
    rw [coeff_squarefreePolynomial]
  · rw [hp m hm]
    simp only [squarefreePolynomial, coeff_sum, coeff_monomial]
    apply Finset.sum_eq_zero
    intro S _
    rw [if_neg]
    exact fun h => hm ⟨S, h.symm⟩

omit [Fintype v] in
/-- A product of affine factors in pairwise distinct variables has only
squarefree monomials. -/
theorem hasSquarefreeSupport_prod_X_add_C_of_injective
    {i : Type*} [Fintype i] [DecidableEq i]
    (e : i → v) (he : Function.Injective e) (a : i → ℂ) :
    HasSquarefreeSupport
      (∏ j, ((X (e j) : MvPolynomial v ℂ) + C (a j))) := by
  intro m hm
  rw [Fintype.prod_add]
  simp only [coeff_sum]
  apply Finset.sum_eq_zero
  intro t _
  rw [prod_X_image_of_injective e he t, prod_X_eq_monomial,
    coeff_monomial_mul_prod_C]
  rw [if_neg]
  exact fun h => hm ⟨t.image e, h.symm⟩

end SquarefreeSupport

section ThreeBlockSupport

variable {w : Type*} [Fintype w] [DecidableEq w]

theorem hasSquarefreeSupport_threeBlockPermutationProduct
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ)
    (σ : Equiv.Perm (ThreeBlockIndex w)) :
    HasSquarefreeSupport
      (∏ j, threeBlockHPolynomial Q 0 (σ j) j) := by
  intro m hm
  rw [threeBlockPermutationPolynomialProduct_eq, mul_comm, coeff_C_mul,
    hasSquarefreeSupport_prod_X_add_C_of_injective
      (threeBlockPermutationVariable σ)
      (threeBlockPermutationVariable_injective σ)
      (fun j => threeBlockEmb Q (σ j) j) m hm,
    mul_zero]

/-- The zero-shift three-block determinant is genuinely multiaffine: no
nonsquarefree exponent occurs in its support. -/
theorem hasSquarefreeSupport_threeBlockDetPolynomial_zero
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ) :
    HasSquarefreeSupport (threeBlockDetPolynomial Q 0) := by
  intro m hm
  rw [threeBlockDetPolynomial, Matrix.det_apply]
  simp only [coeff_sum, coeff_smul]
  apply Finset.sum_eq_zero
  intro σ _
  rw [hasSquarefreeSupport_threeBlockPermutationProduct Q σ m hm]
  simp

/-- Exact reconstruction of the zero-shift determinant from the coefficient
vector already exposed by `ThreeBlockTerminal`. -/
theorem threeBlockDetPolynomial_zero_eq_squarefreePolynomial
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ) :
    threeBlockDetPolynomial Q 0 =
      squarefreePolynomial (threeBlockDetCoeffVector Q 0) := by
  symm
  change squarefreePolynomial
      (WithLp.toLp 2 (fun S => coeff (squarefreeExponent S)
        (threeBlockDetPolynomial Q 0))) = threeBlockDetPolynomial Q 0
  exact squarefreePolynomial_coefficients_eq (threeBlockDetPolynomial Q 0)
    (hasSquarefreeSupport_threeBlockDetPolynomial_zero Q)

end ThreeBlockSupport

section ListEvaluation

variable {v : Type*} [Fintype v] [DecidableEq v]

/-- The point obtained by applying a list of affine coordinate shifts.  The
tail is applied first, matching `translatePolynomialList`. -/
def translatePointList : List (v × ℂ) → (v → ℂ) → v → ℂ
  | [], x => x
  | (i, t) :: shifts, x =>
      Function.update (translatePointList shifts x) i
        (translatePointList shifts x i + t)

omit [Fintype v] in
theorem eval_singleShiftPolynomial
    (i : v) (t : ℂ) (x : v → ℂ) (p : MvPolynomial v ℂ) :
    eval x (singleShiftPolynomial i t p) =
      eval (Function.update x i (x i + t)) p := by
  let f : v → MvPolynomial v ℂ :=
    fun j => if j = i then X j + C t else X j
  calc
    eval x (singleShiftPolynomial i t p) =
        eval (fun j => eval x (f j)) p := by
      simpa [singleShiftPolynomial, f] using
        (aeval_bind₁ x f p)
    _ = eval (Function.update x i (x i + t)) p := by
      apply congrArg (fun y : v → ℂ => eval y p)
      funext j
      by_cases h : j = i
      · subst j
        simp [f]
      · simp [f, h]

omit [Fintype v] in
theorem eval_translatePolynomialList
    (shifts : List (v × ℂ)) (x : v → ℂ)
    (p : MvPolynomial v ℂ) :
    eval x (translatePolynomialList shifts p) =
      eval (translatePointList shifts x) p := by
  induction shifts generalizing x p with
  | nil => rfl
  | cons it shifts ih =>
      rcases it with ⟨i, t⟩
      rw [translatePolynomialList, ih,
        eval_singleShiftPolynomial]
      rfl

omit [Fintype v] in
theorem translatePointList_map_const
    {a : Type*} (f : a → v) (hf : Function.Injective f)
    (l : List a) (hl : l.Nodup) (t : ℂ) (x : v → ℂ) (e : v) :
    translatePointList (l.map fun j => (f j, t)) x e =
      if e ∈ l.map f then x e + t else x e := by
  induction l with
  | nil => simp [translatePointList]
  | cons j l ih =>
      have hj : j ∉ l := (List.nodup_cons.mp hl).1
      have hl' : l.Nodup := (List.nodup_cons.mp hl).2
      have hfj : f j ∉ l.map f := by
        intro h
        rcases List.mem_map.mp h with ⟨k, hk, hkf⟩
        exact hj ((hf hkf).symm ▸ hk)
      simp only [List.map_cons, translatePointList]
      by_cases he : e = f j
      · subst e
        rw [Function.update_self, ih hl']
        simp [hfj]
      · rw [Function.update_of_ne he, ih hl']
        by_cases hem : e ∈ l.map f <;> simp [he, hem]

end ListEvaluation

section ConcreteDiagonalList

variable {w : Type*} [Fintype w] [DecidableEq w]

/-- The fresh variable at a physical diagonal position. -/
def threeBlockDiagonalVariable (i : ThreeBlockIndex w) :
    ThreeBlockVariable w :=
  ⟨(i, i), threeBlockFresh_refl i⟩

omit [Fintype w] [DecidableEq w] in
theorem threeBlockDiagonalVariable_injective :
    Function.Injective (@threeBlockDiagonalVariable w) := by
  intro i j h
  exact congrArg (fun e : ThreeBlockVariable w => e.1.1) h

/-- Every diagonal variable occurs exactly once, with translation `-z`. -/
def threeBlockDiagonalShifts (z : ℂ) :
    List (ThreeBlockVariable w × ℂ) :=
  (Finset.univ : Finset (ThreeBlockIndex w)).toList.map
    fun i => (threeBlockDiagonalVariable i, -z)

omit [DecidableEq w] in
theorem threeBlockDiagonalShifts_nodup (z : ℂ) :
    (threeBlockDiagonalShifts (w := w) z).Nodup := by
  unfold threeBlockDiagonalShifts
  apply (Finset.nodup_toList
    (Finset.univ : Finset (ThreeBlockIndex w))).map
  intro i j h
  exact threeBlockDiagonalVariable_injective (congrArg Prod.fst h)

omit [DecidableEq w] in
theorem mem_threeBlockDiagonalVariable_list
    (e : ThreeBlockVariable w) :
    e ∈ (Finset.univ : Finset (ThreeBlockIndex w)).toList.map
        threeBlockDiagonalVariable ↔
      e.1.1 = e.1.2 := by
  classical
  constructor
  · intro he
    rcases List.mem_map.mp he with ⟨i, _, rfl⟩
    rfl
  · intro he
    have heq : e = threeBlockDiagonalVariable e.1.1 := by
      apply Subtype.ext
      exact Prod.ext rfl he.symm
    rw [heq]
    exact List.mem_map.mpr ⟨e.1.1, by simp, rfl⟩

/-- The fresh-variable point transformation associated with the explicit
list is exactly the diagonal shift used by the concrete terminal matrix. -/
theorem translatePointList_threeBlockDiagonalShifts
    (z : ℂ) (x : ThreeBlockVariable w → ℂ) :
    translatePointList (threeBlockDiagonalShifts (w := w) z) x =
      threeBlockDiagonalShift z x := by
  funext e
  unfold threeBlockDiagonalShifts
  rw [translatePointList_map_const threeBlockDiagonalVariable
    threeBlockDiagonalVariable_injective
    (Finset.univ : Finset (ThreeBlockIndex w)).toList
    (Finset.nodup_toList _) (-z) x e]
  by_cases h : e.1.1 = e.1.2
  · have hm := (mem_threeBlockDiagonalVariable_list (w := w) e).2 h
    simp [hm, h, threeBlockDiagonalShift, sub_eq_add_neg]
  · have hm : e ∉
        (Finset.univ : Finset (ThreeBlockIndex w)).toList.map
          threeBlockDiagonalVariable :=
      fun he => h ((mem_threeBlockDiagonalVariable_list (w := w) e).1 he)
    simp [hm, h, threeBlockDiagonalShift]

/-- Polynomial form of the spectral translation, now using the explicit
duplicate-free list of all three physical diagonal blocks. -/
theorem threeBlockDetPolynomial_eq_translatePolynomialList
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ) (z : ℂ) :
    threeBlockDetPolynomial Q z =
      translatePolynomialList (threeBlockDiagonalShifts (w := w) z)
        (threeBlockDetPolynomial Q 0) := by
  apply MvPolynomial.funext
  intro x
  rw [eval_threeBlockDetPolynomial_shift,
    eval_translatePolynomialList,
    translatePointList_threeBlockDiagonalShifts]

/-- The requested exact coefficient-vector identity.  The sign is `-z`
because `H(Q;x)-zI` is obtained from the zero-shift polynomial by
`x_ii ↦ x_ii-z`. -/
theorem threeBlockDetCoeffVector_eq_translateCoeffList
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ) (z : ℂ) :
    threeBlockDetCoeffVector Q z =
      translateCoeffList (threeBlockDiagonalShifts (w := w) z)
        (threeBlockDetCoeffVector Q 0) := by
  have hp : threeBlockDetPolynomial Q z =
      squarefreePolynomial
        (translateCoeffList (threeBlockDiagonalShifts (w := w) z)
          (threeBlockDetCoeffVector Q 0)) := by
    calc
      threeBlockDetPolynomial Q z =
          translatePolynomialList (threeBlockDiagonalShifts (w := w) z)
            (threeBlockDetPolynomial Q 0) :=
        threeBlockDetPolynomial_eq_translatePolynomialList Q z
      _ = translatePolynomialList (threeBlockDiagonalShifts (w := w) z)
            (squarefreePolynomial (threeBlockDetCoeffVector Q 0)) := by
        rw [← threeBlockDetPolynomial_zero_eq_squarefreePolynomial Q]
      _ = squarefreePolynomial
            (translateCoeffList (threeBlockDiagonalShifts (w := w) z)
              (threeBlockDetCoeffVector Q 0)) :=
        translatePolynomialList_squarefreePolynomial _ _
  ext S
  change coeff (squarefreeExponent S) (threeBlockDetPolynomial Q z) = _
  rw [hp, coeff_squarefreePolynomial]

/-- The explicit norm-loss factor for translating all diagonal variables. -/
def threeBlockTranslationFactor (z : ℂ) : ℝ :=
  translationFactor (threeBlockDiagonalShifts (w := w) z)

theorem one_le_translationFactor {ι : Type*}
    (shifts : List (ι × ℂ)) :
    1 ≤ translationFactor shifts := by
  induction shifts with
  | nil => simp
  | cons it shifts ih =>
      rcases it with ⟨i, t⟩
      simp only [translationFactor_cons]
      simpa using mul_le_mul
        (show 1 ≤ 1 + ‖t‖ by linarith [norm_nonneg t]) ih
        (by norm_num) (by linarith [norm_nonneg t])

omit [DecidableEq w] in
theorem threeBlockTranslationFactor_one_le (z : ℂ) :
    1 ≤ threeBlockTranslationFactor (w := w) z :=
  one_le_translationFactor _

omit [DecidableEq w] in
theorem threeBlockTranslationFactor_pos (z : ℂ) :
    0 < threeBlockTranslationFactor (w := w) z :=
  translationFactor_pos _

/-- Upper norm comparison between arbitrary spectral shift and zero shift. -/
theorem threeBlockDetCoefficientNorm_shift_le
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ) (z : ℂ) :
    threeBlockDetCoefficientNorm Q z ≤
      threeBlockTranslationFactor (w := w) z *
        threeBlockDetCoefficientNorm Q 0 := by
  rw [threeBlockDetCoefficientNorm,
    threeBlockDetCoeffVector_eq_translateCoeffList Q z]
  exact norm_translateCoeffList_le _ _

/-- Lower norm comparison between arbitrary spectral shift and zero shift. -/
theorem threeBlockDetCoefficientNorm_shift_lower
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ) (z : ℂ) :
    (threeBlockTranslationFactor (w := w) z)⁻¹ *
        threeBlockDetCoefficientNorm Q 0 ≤
      threeBlockDetCoefficientNorm Q z := by
  change (threeBlockTranslationFactor (w := w) z)⁻¹ *
      ‖threeBlockDetCoeffVector Q 0‖ ≤ ‖threeBlockDetCoeffVector Q z‖
  rw [threeBlockDetCoeffVector_eq_translateCoeffList Q z]
  exact norm_translateCoeffList_lower _ _

/-- Packet-coordinate upper norm comparison. -/
theorem threeBlockTerminalCoefficientOnPacket_shift_le
    (z : ℂ) (Q : Matrix (w ⊕ w) (w ⊕ w) ℂ) :
    threeBlockTerminalCoefficientOnPacket (w := w) z Q ≤
      threeBlockTranslationFactor (w := w) z *
        threeBlockTerminalCoefficientOnPacket (w := w) 0 Q := by
  exact threeBlockDetCoefficientNorm_shift_le
    (threeBlockOuterOfPacket Q) z

/-- Packet-coordinate lower norm comparison. -/
theorem threeBlockTerminalCoefficientOnPacket_shift_lower
    (z : ℂ) (Q : Matrix (w ⊕ w) (w ⊕ w) ℂ) :
    (threeBlockTranslationFactor (w := w) z)⁻¹ *
        threeBlockTerminalCoefficientOnPacket (w := w) 0 Q ≤
      threeBlockTerminalCoefficientOnPacket (w := w) z Q := by
  exact threeBlockDetCoefficientNorm_shift_lower
    (threeBlockOuterOfPacket Q) z

end ConcreteDiagonalList

section ShiftedTerminalComparison

variable {w : Type*} [Fintype w] [DecidableEq w]

/-- Transport any proved zero-shift terminal comparison to an arbitrary
spectral parameter, with the explicit diagonal-translation loss. -/
theorem threeBlockTerminalCoefficientComparison_of_zero
    (z : ℂ) (K : ℝ)
    (hzero : TerminalCoefficientComparison
      (threeBlockTerminalCoefficientOnPacket (w := w) 0) K) :
    TerminalCoefficientComparison
      (threeBlockTerminalCoefficientOnPacket (w := w) z)
      (K * threeBlockTranslationFactor (w := w) z) where
  one_le := by
    have hK : 0 ≤ K := le_trans (by norm_num) hzero.one_le
    simpa using mul_le_mul hzero.one_le
      (threeBlockTranslationFactor_one_le (w := w) z) (by norm_num) hK
  lower := by
    intro Q
    calc
      (K * threeBlockTranslationFactor (w := w) z)⁻¹ * gramVolume Q =
          (threeBlockTranslationFactor (w := w) z)⁻¹ *
            (K⁻¹ * gramVolume Q) := by
        rw [_root_.mul_inv_rev]
        ring
      _ ≤ (threeBlockTranslationFactor (w := w) z)⁻¹ *
          threeBlockTerminalCoefficientOnPacket (w := w) 0 Q := by
        exact mul_le_mul_of_nonneg_left (hzero.lower Q)
          (inv_nonneg.mpr
            (threeBlockTranslationFactor_pos (w := w) z).le)
      _ ≤ threeBlockTerminalCoefficientOnPacket (w := w) z Q :=
        threeBlockTerminalCoefficientOnPacket_shift_lower z Q
  upper := by
    intro Q
    calc
      threeBlockTerminalCoefficientOnPacket (w := w) z Q ≤
          threeBlockTranslationFactor (w := w) z *
            threeBlockTerminalCoefficientOnPacket (w := w) 0 Q :=
        threeBlockTerminalCoefficientOnPacket_shift_le z Q
      _ ≤ threeBlockTranslationFactor (w := w) z *
          (K * gramVolume Q) := by
        exact mul_le_mul_of_nonneg_left (hzero.upper Q)
          (threeBlockTranslationFactor_pos (w := w) z).le
      _ = (K * threeBlockTranslationFactor (w := w) z) *
          gramVolume Q := by ring

end ShiftedTerminalComparison

end BernoulliLinearAlgebra
