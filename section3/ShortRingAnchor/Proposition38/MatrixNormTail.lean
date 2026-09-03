import ShortRingAnchor.Proposition38.MaskNorm

/-! # Proposition 3.8: the literal rescaled matrix satisfies Cook's norm guard -/

noncomputable section
open MeasureTheory ProbabilityTheory SubgaussianNorm
open scoped Matrix.Norms.L2Operator BigOperators
namespace ShortRingAnchor.Proposition38

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {A : Atom} {W s : ℕ}

def rawFullBlockMatrix
    (S : AtomArray μ A (Fin ((s + 3) * W) × Fin ((s + 3) * W))) :
    Ω → Matrix (Fin ((s + 3) * W)) (Fin ((s + 3) * W)) ℂ :=
  fun sample => maskedMatrix (fun i => (finProdFinEquiv.symm i).1) siteAdjacent
    (S.subgaussianSquare.rawMatrix sample)

/-- Proposition 3.8, Cook rescaling: multiplying the normalized matrix
by `sqrt(3W)` gives exactly the zero-one masked IID matrix. -/
theorem rescaled_fullBlockMatrix_eq (hW : 0 < W)
    (S : AtomArray μ A (Fin ((s + 3) * W) × Fin ((s + 3) * W))) (sample : Ω) :
    (Real.sqrt (3 * (W : ℝ)) : ℂ) • fullBlockMatrix S sample =
      rawFullBlockMatrix S sample := by
  have hr : (Real.sqrt (3 * (W : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 3 * W)).ne'
  apply Matrix.ext
  intro i j
  change (Real.sqrt (3 * (W : ℝ)) : ℂ) *
      ((coefficient W s i j : ℂ) * (S.entry (i, j) sample : ℂ)) =
    if siteAdjacent (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
      then (S.entry (i, j) sample : ℂ) else 0
  unfold coefficient
  split_ifs
  · rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hr, one_mul]
  · simp

/-- Proposition 3.8, Cook rescaling: the deterministic complex shift is
rescaled as well, with no restriction on the fixed `z`. -/
theorem rescaled_shift_eq (hW : 0 < W)
    (S : AtomArray μ A (Fin ((s + 3) * W) × Fin ((s + 3) * W)))
    (sample : Ω) (z : ℂ) :
    (Real.sqrt (3 * (W : ℝ)) : ℂ) • (fullBlockMatrix S sample - z • 1) =
      rawFullBlockMatrix S sample - ((Real.sqrt (3 * (W : ℝ)) : ℂ) * z) • 1 := by
  rw [smul_sub, rescaled_fullBlockMatrix_eq hW, smul_smul]

/-- Proposition 3.8, bounded-block Cook branch: a fixed uniform norm
constant, allowed to depend on the atom, block-count cutoff, and `z`. -/
def cookNormConstant (A : Atom) (sStar : ℕ) (z : ℂ) : ℝ :=
  ((sStar + 3 : ℕ) : ℝ) ^ 2 * (40 * Real.sqrt (A.parameter + 1)) +
    Real.sqrt 3 * ‖z‖ + 1

/-- Proposition 3.8 / Cook 1.12: the norm constant meets Cook's `K ≥ 1`. -/
theorem one_le_cookNormConstant (A : Atom) (sStar : ℕ) (z : ℂ) :
    1 ≤ cookNormConstant A sStar z := by
  unfold cookNormConstant
  have h : 0 ≤ ((sStar + 3 : ℕ) : ℝ) ^ 2 * (40 * Real.sqrt (A.parameter + 1)) +
      Real.sqrt 3 * ‖z‖ := by positivity
  linarith

/-- Proposition 3.8, norm event between (3.21) and (3.22): the genuine
masked and shifted matrix has an exponentially vanishing norm exception.
The estimate is internal; only Cook's joint LSV/norm estimate is external. -/
theorem fullBlock_cook_norm_tail (hW : 0 < W) (sStar : ℕ) (hs : s ≤ sStar)
    (S : AtomArray μ A (Fin ((s + 3) * W) × Fin ((s + 3) * W))) (z : ℂ) :
    μ.real {sample | cookNormConstant A sStar z * Real.sqrt ((s + 3) * W : ℕ) <
      ‖rawFullBlockMatrix S sample - ((Real.sqrt (3 * (W : ℝ)) : ℂ) * z) • 1‖} ≤
      Real.exp (-(((s + 3) * W : ℕ) : ℝ)) := by
  let N := (s + 3) * W
  have hN : 0 < N := Nat.mul_pos (by omega) hW
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  let C : ℝ := 40 * Real.sqrt (A.parameter + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm : (((s + 3 : ℕ) : ℝ) ^ 2) ≤ ((sStar + 3 : ℕ) : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast (show s + 3 ≤ sStar + 3 by omega)
  have hshift : ‖((Real.sqrt (3 * (W : ℝ)) : ℂ) * z) •
      (1 : Matrix (Fin N) (Fin N) ℂ)‖ ≤ Real.sqrt 3 * ‖z‖ * Real.sqrt N := by
    rw [norm_smul, norm_one, mul_one, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hWN : (W : ℝ) ≤ N := by
      exact_mod_cast (show W ≤ (s + 3) * W from
        (Nat.one_mul W).symm.trans_le (Nat.mul_le_mul_right W (by omega)))
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hWN) (Real.sqrt_nonneg 3)
    nlinarith [mul_le_mul_of_nonneg_right hh (norm_nonneg z)]
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _))
    (rawComplexMatrix_opNorm_tail S.subgaussianSquare hN)
  intro sample hsample
  change C * Real.sqrt N < ‖S.subgaussianSquare.rawMatrix sample‖
  by_contra hn
  have hraw := norm_block_mask_le
    (fun i : Fin N => (finProdFinEquiv.symm i).1) siteAdjacent
    (S.subgaussianSquare.rawMatrix sample)
  simp only [Fintype.card_fin] at hraw
  change ‖rawFullBlockMatrix S sample‖ ≤ ((s + 3 : ℕ) : ℝ) ^ 2 *
    ‖S.subgaussianSquare.rawMatrix sample‖ at hraw
  have hbound : ‖rawFullBlockMatrix S sample‖ ≤
      ((sStar + 3 : ℕ) : ℝ) ^ 2 * (C * Real.sqrt N) :=
    hraw.trans (mul_le_mul hm (le_of_not_gt hn) (norm_nonneg _)
      (sq_nonneg _))
  have hsub := norm_sub_le (rawFullBlockMatrix S sample)
    (((Real.sqrt (3 * (W : ℝ)) : ℂ) * z) • (1 : Matrix (Fin N) (Fin N) ℂ))
  change cookNormConstant A sStar z * Real.sqrt N < _ at hsample
  dsimp [cookNormConstant, C] at hbound hsample
  nlinarith [Real.sqrt_nonneg (N : ℝ)]

end ShortRingAnchor.Proposition38
