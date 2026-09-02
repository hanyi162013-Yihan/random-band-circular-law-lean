import BernoulliSection10.HodgeFamilyGrowth

/-! Cleared compound bounds from normalized block entries; no atom support bound. -/
open scoped BigOperators Matrix Matrix.Norms.Frobenius
noncomputable section
namespace SubgaussianSection8
open BernoulliSection10 BernoulliLinearAlgebra Matrix Set Set.powersetCard

local instance growthSumOrder (W : ℕ) : LinearOrder (Fin W ⊕ Fin W) :=
  LinearOrder.lift' (fun x : Fin W ⊕ Fin W => (toLex x : Fin W ⊕ₗ Fin W))
    (fun _ _ h => toLex.injective h)

theorem norm_clearedInverseCompound_stepL_le
    {W : ℕ} (B D C : Matrix (Fin W) (Fin W) ℂ) (q : ℂ)
    (hL : ∀ i j, ‖stepL B i j‖ ≤ 1 + ‖q‖)
    (hK : ∀ i j, ‖stepK D C i j‖ ≤ 1 + ‖q‖) (k : ℕ) (hk : k ≤ 2 * W)
    (s t : powersetCard (Fin W ⊕ Fin W) k) :
    ‖clearedInverseCompound k (stepL B) s t‖ ≤
      oneSiteLeftMinorBound W k q := by
  have hk' : k ≤ Fintype.card (Fin W ⊕ Fin W) := by
    simpa [Fintype.card_sum, two_mul] using hk
  rw [clearedInverseCompound_apply_of_le k _ hk', norm_mul]
  have hsign : ‖jacobiReindexSign (Nat.sub_add_cancel hk') s t‖ = 1 := by
    have hs := congrArg norm
      (jacobiReindexSign_sq (Nat.sub_add_cancel hk') s t)
    rw [norm_mul, norm_one] at hs
    nlinarith [norm_nonneg
      (jacobiReindexSign (Nat.sub_add_cancel hk') s t)]
  rw [hsign, one_mul]
  unfold oneSiteLeftMinorBound
  simpa [Fintype.card_sum, two_mul] using
    (norm_minor_le_factorial_mul_pow
      (Fintype.card (Fin W ⊕ Fin W) - k)
      (stepL B)
      (powersetCard.compl (Nat.sub_add_cancel hk') t)
      (powersetCard.compl (Nat.sub_add_cancel hk') s)
      (1 + ‖q‖)
      hL)


theorem norm_compound_stepK_le
    {W : ℕ} (B D C : Matrix (Fin W) (Fin W) ℂ) (q : ℂ)
    (hL : ∀ i j, ‖stepL B i j‖ ≤ 1 + ‖q‖)
    (hK : ∀ i j, ‖stepK D C i j‖ ≤ 1 + ‖q‖) (k : ℕ)
    (s t : powersetCard (Fin W ⊕ Fin W) k) :
    ‖compound k (stepK D
        C) s t‖ ≤
      oneSiteRightMinorBound k q := by
  rw [compound_apply]
  exact norm_minor_le_factorial_mul_pow k _ s t (1 + ‖q‖)
    hK


theorem norm_clearedStepCompound_entry_le
    {W : ℕ} (B D C : Matrix (Fin W) (Fin W) ℂ) (q : ℂ)
    (hL : ∀ i j, ‖stepL B i j‖ ≤ 1 + ‖q‖)
    (hK : ∀ i j, ‖stepK D C i j‖ ≤ 1 + ‖q‖) (k : ℕ) (hk : k ≤ 2 * W)
    (s t : powersetCard (Fin W ⊕ Fin W) k) :
    ‖clearedStepCompound k B
        D
        C s t‖ ≤
      oneSiteClearedEntryBound W k q := by
  rw [clearedStepCompound_apply, norm_mul]
  simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul, Matrix.mul_apply]
  calc
    ‖∑ u, clearedInverseCompound k
          (stepL B) s u *
        compound k (stepK D
          C) u t‖ ≤
        ∑ u, ‖clearedInverseCompound k
          (stepL B) s u *
        compound k (stepK D
          C) u t‖ := norm_sum_le _ _
    _ ≤ ∑ _u : powersetCard (Fin W ⊕ Fin W) k,
        oneSiteLeftMinorBound W k q * oneSiteRightMinorBound k q := by
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul]
      exact mul_le_mul
        (norm_clearedInverseCompound_stepL_le B D C q hL hK k hk s u)
        (norm_compound_stepK_le B D C q hL hK k u t)
        (norm_nonneg _) (by
          unfold oneSiteLeftMinorBound
          positivity)
    _ = oneSiteClearedEntryBound W k q := by
      unfold oneSiteClearedEntryBound
      have hcard : Fintype.card (powersetCard (Fin W ⊕ Fin W) k) =
          Nat.choose (2 * W) k := by
        rw [← Nat.card_eq_fintype_card, powersetCard.card,
          Nat.card_eq_fintype_card]
        simp [Fintype.card_sum, two_mul]
      simp [hcard]


theorem norm_clearedStepCompound_le_degreeBound
    {W : ℕ} (B D C : Matrix (Fin W) (Fin W) ℂ) (q : ℂ)
    (hL : ∀ i j, ‖stepL B i j‖ ≤ 1 + ‖q‖)
    (hK : ∀ i j, ‖stepK D C i j‖ ≤ 1 + ‖q‖) (k : ℕ) (hk : k ≤ 2 * W) :
    ‖clearedStepCompound k B
        D
        C‖ ≤
      oneSiteDegreeFrobeniusBound W k q := by
  have hcard : Fintype.card (powersetCard (Fin W ⊕ Fin W) k) =
      Nat.choose (2 * W) k := by
    rw [← Nat.card_eq_fintype_card, powersetCard.card,
      Nat.card_eq_fintype_card]
    simp [Fintype.card_sum, two_mul]
  have h := frobenius_norm_le_card_mul_of_entry_norm_le
    (clearedStepCompound k B
      D C)
    (oneSiteClearedEntryBound W k q)
    (oneSiteClearedEntryBound_nonneg W k q)
    (norm_clearedStepCompound_entry_le B D C q hL hK k hk)
  simpa only [oneSiteDegreeFrobeniusBound, hcard, pow_two] using h


end SubgaussianSection8
