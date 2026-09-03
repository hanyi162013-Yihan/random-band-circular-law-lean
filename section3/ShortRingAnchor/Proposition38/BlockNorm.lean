import ShortRingAnchor.Proposition38.BlockEmbedding
import Vendor.SubgaussianNorm.OperatorNorm

/-!
# Reusing the proved IID norm tail for Proposition 3.8

The Cook step between (3.21) and (3.22) only needs bounded block counts.
Embed each IID block as an operator, sum the blocks, and use a finite union
bound. This avoids a new masked-matrix norm theorem and introduces no
external probability premise. Arbitrary deterministic shifts are included.
-/

open MeasureTheory Filter SubgaussianNorm
open scoped Matrix.Norms.L2Operator BigOperators Topology
noncomputable section
namespace ShortRingAnchor.Proposition38

variable {Ω B J : Type*} [MeasurableSpace Ω]
  [Fintype B] [DecidableEq B] [Fintype J]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {W : ℕ}

/-- Proposition 3.8's block assembly, as an operator on the actual direct
sum of the block coordinate spaces. Cyclic placement is a specialization
of `row` and `col`; no independence between different blocks is needed
for this particular norm estimate. -/
def rawBlockSum (S : J → IidSubgaussianSquare Ω μ W) (row col : J → B)
    (sample : Ω) : EuclideanSpace ℂ (B × Fin W) →L[ℂ] EuclideanSpace ℂ (B × Fin W) :=
  ∑ j, embeddedBlock (row j) (col j)
    (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) ((S j).rawMatrix sample))

/-- Proposition 3.8's norm event: union bound over the embedded IID blocks.
For the ring, `card J = 3m`; this estimate is sufficient when `m < m_*`. -/
theorem rawBlockSum_norm_tail
    (S : J → IidSubgaussianSquare Ω μ W) (row col : J → B)
    (hW : 0 < W) (C : ℝ)
    (hC : ∀ j, subgaussianOpNormConstant (S j) ≤ C) :
    μ.real {sample | (Fintype.card J : ℝ) * C * Real.sqrt W <
        ‖rawBlockSum S row col sample‖} ≤
      (Fintype.card J : ℝ) * Real.exp (-(W : ℝ)) := by
  classical
  let bad : J → Set Ω := fun j => {sample |
    subgaussianOpNormConstant (S j) * Real.sqrt W < ‖(S j).rawMatrix sample‖}
  have hsubset : {sample | (Fintype.card J : ℝ) * C * Real.sqrt W <
      ‖rawBlockSum S row col sample‖} ⊆ ⋃ j, bad j := by
    intro sample hs
    by_contra hn
    have hb : ∀ j, ‖(S j).rawMatrix sample‖ ≤ C * Real.sqrt W := by
      intro j
      have hj : ¬ sample ∈ bad j := fun h => hn (Set.mem_iUnion.mpr ⟨j, h⟩)
      exact (le_of_not_gt hj).trans
        (mul_le_mul_of_nonneg_right (hC j) (Real.sqrt_nonneg _))
    have hsum : ‖rawBlockSum S row col sample‖ ≤
        (Fintype.card J : ℝ) * C * Real.sqrt W := by
      calc
        _ ≤ ∑ j, ‖Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ)
              ((S j).rawMatrix sample)‖ := norm_sum_embeddedBlock_le row col _
        _ ≤ ∑ _j : J, C * Real.sqrt W := by
          apply Finset.sum_le_sum
          intro j _
          simpa only [Matrix.l2_opNorm_toEuclideanCLM] using hb j
        _ = _ := by simp [mul_assoc]
    exact (not_lt_of_ge hsum) hs
  calc
    _ ≤ μ.real (⋃ j, bad j) := measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ ∑ j, μ.real (bad j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : J, Real.exp (-(W : ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      exact rawComplexMatrix_opNorm_tail (S j) hW
    _ = _ := by simp

/-- Proposition 3.8's Cook norm event after the deterministic complex shift.
The same exponentially small exceptional set suffices; no restriction on
the fixed shift's size is imposed. -/
theorem shifted_rawBlockSum_norm_tail
    (S : J → IidSubgaussianSquare Ω μ W) (row col : J → B)
    (hW : 0 < W) (C : ℝ)
    (hC : ∀ j, subgaussianOpNormConstant (S j) ≤ C)
    (D : EuclideanSpace ℂ (B × Fin W) →L[ℂ] EuclideanSpace ℂ (B × Fin W)) :
    μ.real {sample | (Fintype.card J : ℝ) * C * Real.sqrt W + ‖D‖ <
        ‖rawBlockSum S row col sample - D‖} ≤
      (Fintype.card J : ℝ) * Real.exp (-(W : ℝ)) := by
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _))
    (rawBlockSum_norm_tail S row col hW C hC)
  intro sample hs
  have ht := norm_sub_le (rawBlockSum S row col sample) D
  change (Fintype.card J : ℝ) * C * Real.sqrt W < ‖rawBlockSum S row col sample‖
  change (Fintype.card J : ℝ) * C * Real.sqrt W + ‖D‖ <
    ‖rawBlockSum S row col sample - D‖ at hs
  linarith

/-- Proposition 3.8's Cook guard, uniformly over a bounded number of
blocks. For cyclic rings set `L = 3 m_*`, `N = m W`, and bound the
deterministic shift by a constant times `sqrt N`. This supplies exactly
the norm event required by Cook 1.12, not a bound on matrix entries. -/
theorem cook_norm_guard_tail
    (S : J → IidSubgaussianSquare Ω μ W) (row col : J → B)
    (hW : 0 < W) (C D0 L : ℝ) (hC0 : 0 ≤ C) (hL0 : 0 ≤ L)
    (hC : ∀ j, subgaussianOpNormConstant (S j) ≤ C)
    (hcard : (Fintype.card J : ℝ) ≤ L) (N : ℕ) (hWN : W ≤ N)
    (D : EuclideanSpace ℂ (B × Fin W) →L[ℂ] EuclideanSpace ℂ (B × Fin W))
    (hD : ‖D‖ ≤ D0 * Real.sqrt N) :
    μ.real {sample | (L * C + D0) * Real.sqrt N <
        ‖rawBlockSum S row col sample - D‖} ≤ L * Real.exp (-(W : ℝ)) := by
  have hthreshold : (Fintype.card J : ℝ) * C * Real.sqrt W + ‖D‖ ≤
      (L * C + D0) * Real.sqrt N := by
    have hroot : Real.sqrt W ≤ Real.sqrt N := Real.sqrt_le_sqrt (by exact_mod_cast hWN)
    have hfirst : (Fintype.card J : ℝ) * C * Real.sqrt W ≤ L * C * Real.sqrt N :=
      mul_le_mul (mul_le_mul_of_nonneg_right hcard hC0) hroot
        (Real.sqrt_nonneg _) (mul_nonneg hL0 hC0)
    nlinarith
  calc
    _ ≤ μ.real {sample | (Fintype.card J : ℝ) * C * Real.sqrt W + ‖D‖ <
        ‖rawBlockSum S row col sample - D‖} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro sample hs
      exact hthreshold.trans_lt hs
    _ ≤ (Fintype.card J : ℝ) * Real.exp (-(W : ℝ)) :=
      shifted_rawBlockSum_norm_tail S row col hW C hC D
    _ ≤ L * Real.exp (-(W : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le

/-- Proposition 3.8's actual rescaled shift: multiplying `X-zI` by
`sqrt(3W)` costs at most `sqrt(3) |z| sqrt(N)` in operator norm. -/
theorem norm_rescaled_shift_le (N : ℕ) (hWN : W ≤ N) (z : ℂ) :
    ‖((Real.sqrt (3 * (W : ℝ)) : ℂ) * z) •
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (B × Fin W))‖ ≤
      (Real.sqrt 3 * ‖z‖) * Real.sqrt N := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hs : Real.sqrt (3 * (W : ℝ)) ≤ Real.sqrt 3 * Real.sqrt N := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by exact_mod_cast hWN)) (Real.sqrt_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hs (norm_nonneg z)) (norm_nonneg x)]

/-- Proposition 3.8: the finite-block union-bound error tends to zero.
Thus no extra norm-tail literature assumption is needed for bounded `m`. -/
theorem bounded_block_norm_failure_tendsto_zero
    {W : ℕ → ℕ} (hW : Tendsto W atTop atTop) (mStar : ℝ) :
    Tendsto (fun k => 3 * mStar * Real.exp (-(W k : ℝ))) atTop (nhds 0) := by
  have hreal : Tendsto (fun k => (W k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hW
  simpa using (Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp hreal)).const_mul (3 * mStar)

end ShortRingAnchor.Proposition38
