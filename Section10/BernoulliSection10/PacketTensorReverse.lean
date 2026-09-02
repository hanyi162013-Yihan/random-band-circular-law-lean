import BernoulliSection10.PacketTensorScaling
import BernoulliSection10.TensorCornerBound

/-!
# Reverse comparison for the normalized packet tensor

The packet coefficient theorem uses the raw squarefree coefficient norm,
whereas Corollary 10.3 uses the canonical tensor after the random atoms have
been grouped into normalized physical rows.  This module proves the missing
reverse comparison with only `exp (O(W log(eW)))` loss.
-/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliSection10

open MvPolynomial
open BernoulliLinearAlgebra

set_option maxHeartbeats 800000

/-- A squarefree polynomial evaluated on a vector supported on `A`, with
all active coordinates in the unit disk, is bounded by `2^|A|` times its
complete Euclidean squarefree coefficient norm. -/
theorem norm_eval_squarefree_le_pow_card_support_mul_coeffNorm
    {v : Type*} [Fintype v] [DecidableEq v]
    (P : MvPolynomial v ℂ) (hP : HasSquarefreeSupport P)
    (x : v → ℂ) (A : Finset v)
    (hxzero : ∀ i, i ∉ A → x i = 0)
    (hxnorm : ∀ i, ‖x i‖ ≤ 1) :
    ‖eval x P‖ ≤ (2 : ℝ) ^ A.card *
      ‖(WithLp.toLp 2 (fun S : Finset v ↦
        coeff (squarefreeExponent S) P) : CoeffSpace v)‖ := by
  classical
  let C : ℝ := ‖(WithLp.toLp 2 (fun S : Finset v ↦
    coeff (squarefreeExponent S) P) : CoeffSpace v)‖
  let term : Finset v → ℂ := fun S ↦
    coeff (squarefreeExponent S) P * ∏ i : S, x i
  have htermzero (S : Finset v) (hSA : ¬ S ⊆ A) : term S = 0 := by
    obtain ⟨i, hiS, hiA⟩ := Finset.not_subset.mp hSA
    have hp : (∏ j : S, x j) = 0 := by
      refine Finset.prod_eq_zero (s := Finset.univ)
        (i := ⟨i, hiS⟩) (Finset.mem_univ _) ?_
      exact hxzero i hiA
    simp only [term, hp, mul_zero]
  have hrestrict : (∑ S : Finset v, ‖term S‖) =
      (∑ S ∈ A.powerset, ‖term S‖) := by
    symm
    apply Finset.sum_subset (by simp)
    intro S hSuniv hSpower
    rw [norm_eq_zero]
    exact htermzero S (by simpa only [Finset.mem_powerset] using hSpower)
  have hterm (S : Finset v) (hSA : S ⊆ A) : ‖term S‖ ≤ C := by
    have hc : ‖coeff (squarefreeExponent S) P‖ ≤ C := by
      simpa only [C] using PiLp.norm_apply_le
        (WithLp.toLp 2 (fun T : Finset v ↦
          coeff (squarefreeExponent T) P) : CoeffSpace v) S
    have hp : ‖∏ i : S, x i‖ ≤ 1 := by
      change ‖Finset.univ.prod (fun i : S ↦ x i)‖ ≤ 1
      rw [norm_prod]
      apply Finset.prod_le_one
      · intro i hi
        exact norm_nonneg _
      · intro i hi
        exact hxnorm i
    calc
      ‖term S‖ = ‖coeff (squarefreeExponent S) P‖ *
          ‖∏ i : S, x i‖ := by simp only [term, norm_mul]
      _ ≤ C * 1 := mul_le_mul hc hp (norm_nonneg _) (by positivity)
      _ = C := mul_one C
  rw [eval_eq_sum_squarefree_coeff P hP]
  calc
    ‖∑ S : Finset v,
        coeff (squarefreeExponent S) P * ∏ i : S, x i‖ ≤
        ∑ S : Finset v, ‖term S‖ := by
      simpa only [term] using
        (norm_sum_le Finset.univ term)
    _ = ∑ S ∈ A.powerset, ‖term S‖ := hrestrict
    _ ≤ ∑ _S ∈ A.powerset, C := by
      apply Finset.sum_le_sum
      intro S hS
      exact hterm S (Finset.mem_powerset.mp hS)
    _ = (2 : ℝ) ^ A.card * C := by
      simp [Finset.card_powerset, nsmul_eq_mul]
    _ = _ := by rfl

/-- Every row of a replicated zero/one-hot corner is itself zero or a
single standard coordinate after flattening. -/
theorem multiAffineRowsToFinRows_eq_zero_or_single_of_corner
    (p : ℕ) : ∀ (n : ℕ)
    (y : MultiAffineRows (List.replicate n p)),
    IsReplicatedCorner p n y →
    ∀ i : Fin n,
      multiAffineRowsToFinRows p n y i = 0 ∨
        ∃ s : Fin p,
          multiAffineRowsToFinRows p n y i = Pi.single s 1 := by
  intro n
  induction n with
  | zero =>
      intro y hy i
      exact Fin.elim0 i
  | succ n ih =>
      intro y hy i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · change y.1 = 0 ∨ ∃ s, y.1 = Pi.single s 1
        exact hy.1
      · change multiAffineRowsToFinRows p n y.2 j = 0 ∨
          ∃ s, multiAffineRowsToFinRows p n y.2 j = Pi.single s 1
        exact ih y.2 hy.2 j

/-- At a physical-row corner at most one fresh atom per row is active. -/
theorem card_packetCornerActiveSupport_le
    (W : ℕ)
    (y : MultiAffineRows (List.replicate
      (PacketAtomRowCount W) (PacketAtomRowCount W)))
    (hy : IsReplicatedCorner (PacketAtomRowCount W)
      (PacketAtomRowCount W) y) :
    (Finset.univ.filter (fun e : ThreeBlockVariable (Fin W) ↦
      packetAtomAssignment W
        (multiAffineRowsToFinRows (PacketAtomRowCount W)
          (PacketAtomRowCount W) y) e ≠ 0)).card ≤
      PacketAtomRowCount W := by
  classical
  let rows := multiAffineRowsToFinRows (PacketAtomRowCount W)
    (PacketAtomRowCount W) y
  let A := Finset.univ.filter (fun e : ThreeBlockVariable (Fin W) ↦
    packetAtomAssignment W rows e ≠ 0)
  let f : A → Fin (PacketAtomRowCount W) := fun e ↦
    packetIndexEquiv W e.1.1.1
  have hf : Function.Injective f := by
    intro a b hab
    have haActive : packetAtomAssignment W rows a.1 ≠ 0 :=
      (Finset.mem_filter.mp a.2).2
    have hbActive : packetAtomAssignment W rows b.1 ≠ 0 :=
      (Finset.mem_filter.mp b.2).2
    have haRow : rows (packetIndexEquiv W a.1.1.1)
        (packetIndexEquiv W a.1.1.2) ≠ 0 := by
      intro hz
      apply haActive
      simp [packetAtomAssignment, rows, hz]
    have hbRow : rows (packetIndexEquiv W b.1.1.1)
        (packetIndexEquiv W b.1.1.2) ≠ 0 := by
      intro hz
      apply hbActive
      simp [packetAtomAssignment, rows, hz]
    have hshape := multiAffineRowsToFinRows_eq_zero_or_single_of_corner
      (PacketAtomRowCount W) (PacketAtomRowCount W) y hy
        (packetIndexEquiv W a.1.1.1)
    rcases hshape with hzero | ⟨q, hsingle⟩
    · apply (haRow ?_).elim
      change multiAffineRowsToFinRows (PacketAtomRowCount W)
        (PacketAtomRowCount W) y (packetIndexEquiv W a.1.1.1)
          (packetIndexEquiv W a.1.1.2) = 0
      rw [hzero]
      rfl
    · have haCol : packetIndexEquiv W a.1.1.2 = q := by
        by_contra hne
        apply haRow
        change multiAffineRowsToFinRows (PacketAtomRowCount W)
          (PacketAtomRowCount W) y (packetIndexEquiv W a.1.1.1)
            (packetIndexEquiv W a.1.1.2) = 0
        rw [hsingle]
        simp [Pi.single_apply, hne]
      have hrowEq : a.1.1.1 = b.1.1.1 :=
        (packetIndexEquiv W).injective hab
      have hbCol : packetIndexEquiv W b.1.1.2 = q := by
        by_contra hne
        apply hbRow
        change multiAffineRowsToFinRows (PacketAtomRowCount W)
          (PacketAtomRowCount W) y (packetIndexEquiv W b.1.1.1)
            (packetIndexEquiv W b.1.1.2) = 0
        rw [← hrowEq, hsingle]
        simp [Pi.single_apply, hne]
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext hrowEq
      exact (packetIndexEquiv W).injective (haCol.trans hbCol.symm)
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fin, A] using hcard

/-- Uniform corner bound for the literal packet boundary polynomial in
terms of its raw squarefree coefficient norm. -/
theorem packetBoundaryEvalRecursive_corner_le_rawCoefficientNorm
    (W : ℕ) (hW : 0 < W) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (y : MultiAffineRows (List.replicate
      (PacketAtomRowCount W) (PacketAtomRowCount W)))
    (hy : IsReplicatedCorner (PacketAtomRowCount W)
      (PacketAtomRowCount W) y) :
    ‖packetBoundaryEvalRecursive W z CL BR Theta y‖ ≤
      (2 : ℝ) ^ PacketAtomRowCount W *
        packetBoundaryCoefficientNorm z CL BR Theta := by
  let rows := multiAffineRowsToFinRows (PacketAtomRowCount W)
    (PacketAtomRowCount W) y
  let A := Finset.univ.filter (fun e : ThreeBlockVariable (Fin W) ↦
    packetAtomAssignment W rows e ≠ 0)
  have hzero : ∀ e, e ∉ A → packetAtomAssignment W rows e = 0 := by
    intro e he
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact Classical.not_not.mp he
  have hnorm : ∀ e, ‖packetAtomAssignment W rows e‖ ≤ 1 := by
    intro e
    simp only [packetAtomAssignment, Complex.norm_real, Real.norm_eq_abs,
      abs_mul]
    calc
      |blockNormalization W| *
          |rows (packetIndexEquiv W e.1.1)
            (packetIndexEquiv W e.1.2)| ≤ 1 * 1 :=
        mul_le_mul (abs_blockNormalization_le_one W hW)
          (abs_multiAffineRowsToFinRows_le_one_of_corner
            (PacketAtomRowCount W) (PacketAtomRowCount W) y hy
              (packetIndexEquiv W e.1.1) (packetIndexEquiv W e.1.2))
          (abs_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hgeneric := norm_eval_squarefree_le_pow_card_support_mul_coeffNorm
    (packetBoundaryPolynomial z CL BR Theta)
    (hasSquarefreeSupport_globalBoundaryDetPolynomial z CL BR Theta)
    (packetAtomAssignment W rows) A hzero hnorm
  have hcoeffEq :
      ‖(WithLp.toLp 2 (fun S : Finset (ThreeBlockVariable (Fin W)) ↦
        coeff (squarefreeExponent S)
          (packetBoundaryPolynomial z CL BR Theta)) :
          CoeffSpace (ThreeBlockVariable (Fin W)))‖ =
        packetBoundaryCoefficientNorm z CL BR Theta := by
    rfl
  rw [hcoeffEq] at hgeneric
  have hcard : A.card ≤ PacketAtomRowCount W := by
    simpa only [A, rows] using card_packetCornerActiveSupport_le W y hy
  calc
    ‖packetBoundaryEvalRecursive W z CL BR Theta y‖ ≤
        (2 : ℝ) ^ A.card * packetBoundaryCoefficientNorm z CL BR Theta := by
      simpa only [packetBoundaryEvalRecursive, packetBoundaryEval, rows,
        packetBoundaryCoefficientNorm, globalBoundaryCoeffVector] using hgeneric
    _ ≤ (2 : ℝ) ^ PacketAtomRowCount W *
        packetBoundaryCoefficientNorm z CL BR Theta := by
      gcongr
      · exact norm_nonneg _
      · norm_num

/-- Explicit reverse-comparison factor between the normalized physical-row
tensor and the raw squarefree coefficient vector. -/
def packetTensorReverseFactor (W : ℕ) : ℝ :=
  (1 + 2 * (PacketAtomRowCount W : ℝ)) ^ PacketAtomRowCount W *
    (2 : ℝ) ^ PacketAtomRowCount W

theorem packetBoundaryCoefficientTensor_le_reverseFactor_mul_raw
    (W : ℕ) (hW : 0 < W) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    ‖packetBoundaryCoefficientTensor W z CL BR Theta‖ ≤
      packetTensorReverseFactor W *
        packetBoundaryCoefficientNorm z CL BR Theta := by
  have hcorner := norm_multiAffineTensorOfFunction_le_of_corner
    (E := ℂ) (PacketAtomRowCount W) (PacketAtomRowCount W)
      (packetBoundaryEvalRecursive W z CL BR Theta)
      ((2 : ℝ) ^ PacketAtomRowCount W *
        packetBoundaryCoefficientNorm z CL BR Theta)
      (mul_nonneg (by positivity) (norm_nonneg _))
      (packetBoundaryEvalRecursive_corner_le_rawCoefficientNorm
        W hW z CL BR Theta)
  simpa only [packetBoundaryCoefficientTensor, packetTensorReverseFactor,
    mul_assoc] using hcorner

theorem packetTensorReverseFactor_eq_pow (W : ℕ) :
    packetTensorReverseFactor W =
      (2 * (1 + 2 * (PacketAtomRowCount W : ℝ))) ^
        PacketAtomRowCount W := by
  unfold packetTensorReverseFactor
  rw [← mul_pow]
  congr 1
  ring

theorem one_le_packetTensorReverseFactor (W : ℕ) :
    1 ≤ packetTensorReverseFactor W := by
  rw [packetTensorReverseFactor_eq_pow]
  apply one_le_pow₀
  have h : 0 ≤ (PacketAtomRowCount W : ℝ) := by positivity
  nlinarith

def packetTensorReverseLogConstant : ℝ :=
  3 * (Real.posLog 14 + 1)

theorem packetTensorReverseLogConstant_nonneg :
    0 ≤ packetTensorReverseLogConstant := by
  unfold packetTensorReverseLogConstant
  exact mul_nonneg (by norm_num)
    (add_nonneg Real.posLog_nonneg (by norm_num))

theorem posLog_packetTensorReverseFactor_le_W_log_eW
    (W : ℕ) (hW : 0 < W) :
    Real.posLog (packetTensorReverseFactor W) ≤
      packetTensorReverseLogConstant * W *
        Real.log (Real.exp 1 * W) := by
  have hcard : PacketAtomRowCount W = 3 * W := by
    simpa only [Fintype.card_fin] using
      (card_threeBlockIndex (W := Fin W))
  have hW1Nat : 1 ≤ W := by omega
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1Nat
  have hW0 : (0 : ℝ) ≤ W := by positivity
  have hbase :
      2 * (1 + 2 * (PacketAtomRowCount W : ℝ)) ≤ 14 * W := by
    rw [hcard]
    push_cast
    nlinarith
  have hbase0 : 0 ≤
      2 * (1 + 2 * (PacketAtomRowCount W : ℝ)) := by positivity
  have hposlog := Real.posLog_le_posLog hbase0 hbase
  rw [hcard] at hposlog
  have hmul : Real.posLog (14 * W : ℝ) ≤
      Real.posLog 14 + Real.posLog (W : ℝ) := Real.posLog_mul
  have ht : 0 ≤ Real.posLog (W : ℝ) := Real.posLog_nonneg
  have h14 : 0 ≤ Real.posLog (14 : ℝ) := Real.posLog_nonneg
  rw [packetTensorReverseFactor_eq_pow, Real.posLog_pow, hcard]
  calc
    (3 * W : ℕ) *
        Real.posLog (2 * (1 + 2 * (3 * W : ℕ))) ≤
        (3 * W : ℕ) * Real.posLog (14 * W : ℝ) := by
      exact mul_le_mul_of_nonneg_left hposlog (by positivity)
    _ ≤ (3 * W : ℝ) *
        (Real.posLog 14 + Real.posLog (W : ℝ)) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (mul_le_mul_of_nonneg_left hmul
          (show 0 ≤ (3 * W : ℝ) by positivity))
    _ ≤ packetTensorReverseLogConstant * W *
        (1 + Real.posLog (W : ℝ)) := by
      unfold packetTensorReverseLogConstant
      push_cast
      nlinarith [mul_nonneg h14 ht]
    _ = packetTensorReverseLogConstant * W *
        Real.log (Real.exp 1 * W) := by
      rw [one_add_posLog_nat_eq_log_e_mul W hW]

/-- The two concrete coefficient norms used by Propositions 10.8 and 10.9
differ by only the two explicit physical-row scaling factors. -/
theorem abs_log_packetBoundaryCoefficientTensor_sub_raw_le
    (W : ℕ) (hW : 0 < W) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (hTheta : IsUnit Theta.det) :
    |Real.log ‖packetBoundaryCoefficientTensor W z CL BR Theta‖ -
        Real.log (packetBoundaryCoefficientNorm z CL BR Theta)| ≤
      Real.posLog (packetTensorEvaluationFactor W) +
        Real.posLog (packetTensorReverseFactor W) := by
  let T := ‖packetBoundaryCoefficientTensor W z CL BR Theta‖
  let C := packetBoundaryCoefficientNorm z CL BR Theta
  let F := packetTensorEvaluationFactor W
  let G := packetTensorReverseFactor W
  have hC : 0 < C := globalBoundaryCoefficientNorm_pos_fullyInstantiated
    z CL BR hCL hBR Theta hTheta
  have hFC := packetBoundaryCoefficientNorm_le_evaluationFactor_mul_tensor
    W hW z CL BR Theta
  have hGC := packetBoundaryCoefficientTensor_le_reverseFactor_mul_raw
    W hW z CL BR Theta
  have hF : 0 < F := by
    unfold F packetTensorEvaluationFactor
    apply pow_pos
    have hinv : 0 ≤ (blockNormalization W)⁻¹ :=
      (inv_pos.mpr (blockNormalization_pos W hW)).le
    have hmul : 0 ≤ (PacketAtomRowCount W : ℝ) *
        (blockNormalization W)⁻¹ := mul_nonneg (by positivity) hinv
    linarith
  have hG : 0 < G := zero_lt_one.trans_le
    (one_le_packetTensorReverseFactor W)
  have hT : 0 < T := by
    by_contra h
    have hz : T = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    have hbound : C ≤ F * T := by simpa only [C, F, T] using hFC
    rw [hz, mul_zero] at hbound
    exact (not_le_of_gt hC) hbound
  have hlowLog : Real.log C ≤ Real.log F + Real.log T := by
    have hbound : C ≤ F * T := by simpa only [C, F, T] using hFC
    have h := Real.log_le_log hC hbound
    rwa [Real.log_mul hF.ne' hT.ne'] at h
  have huppLog : Real.log T ≤ Real.log G + Real.log C := by
    have hbound : T ≤ G * C := by simpa only [C, G, T] using hGC
    have h := Real.log_le_log hT hbound
    rwa [Real.log_mul hG.ne' hC.ne'] at h
  have hFone : 1 ≤ F := by
    unfold F packetTensorEvaluationFactor
    exact one_le_pow₀ (by
      have hinv : 0 ≤ (blockNormalization W)⁻¹ :=
        (inv_pos.mpr (blockNormalization_pos W hW)).le
      exact le_add_of_nonneg_right (mul_nonneg (by positivity) hinv))
  have hGone : 1 ≤ G := one_le_packetTensorReverseFactor W
  have hFp : Real.posLog F = Real.log F := by
    apply Real.posLog_eq_log
    rw [abs_of_nonneg hF.le]
    exact hFone
  have hGp : Real.posLog G = Real.log G := by
    apply Real.posLog_eq_log
    rw [abs_of_nonneg hG.le]
    exact hGone
  have hlogF : 0 ≤ Real.log F := Real.log_nonneg hFone
  have hlogG : 0 ≤ Real.log G := Real.log_nonneg hGone
  rw [hFp, hGp]
  rw [abs_le]
  constructor <;> dsimp only [T, C] at * <;> linarith

end BernoulliSection10
