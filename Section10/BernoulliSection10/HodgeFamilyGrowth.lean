import BernoulliSection10.HodgeFamily
import BernoulliSection10.IntervalHodge
import BernoulliSection10.TensorCornerBound
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Deterministic growth of the simultaneous Hodge tensor

This module bounds the concrete coefficient tensor used in Lemma 10.6.  The
argument evaluates the separately affine family only at zero/one-hot row
corners, bounds the resulting minors by the standard Leibniz estimate, and
then applies `norm_multiAffineTensorOfFunction_le_of_corner`.
-/

open scoped BigOperators Matrix ENNReal NNReal Matrix.Norms.Frobenius
open MeasureTheory

noncomputable section

namespace BernoulliSection10

open Matrix Set Set.powersetCard
open BernoulliLinearAlgebra

set_option maxHeartbeats 800000

local instance hodgeFamilyGrowthSumLinearOrder (W : ℕ) :
    LinearOrder (Fin W ⊕ Fin W) :=
  LinearOrder.lift' (fun x : Fin W ⊕ Fin W ↦ (toLex x : Fin W ⊕ₗ Fin W))
    (fun _ _ h ↦ toLex.injective h)

/-- Every scalar atom in a flat one-site configuration has modulus at most
one. -/
def OneSiteAtomsBound (W : ℕ) (x : IntervalRows W 1) : Prop :=
  ∀ i a, |x i a| ≤ 1

theorem oneSiteAtomsBound_of_corner (W : ℕ)
    (y : MultiAffineRows (List.replicate (1 * W) (3 * W)))
    (hy : IsReplicatedCorner (3 * W) (1 * W) y) :
    OneSiteAtomsBound W
      (multiAffineRowsToFinRows (3 * W) (1 * W) y) := by
  intro i a
  exact abs_multiAffineRowsToFinRows_le_one_of_corner
    (3 * W) (1 * W) y hy i a

theorem abs_blockNormalization_le_one (W : ℕ) (hW : 0 < W) :
    |blockNormalization W| ≤ 1 := by
  have hone : (1 : ℝ) ≤ 3 * W := by
    norm_cast
    omega
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (3 * W : ℝ) := by
    simpa only [Real.one_le_sqrt] using hone
  have hnonneg : 0 ≤ blockNormalization W := by
    unfold blockNormalization
    positivity
  rw [abs_of_nonneg hnonneg]
  exact inv_le_one_of_one_le₀ hsqrt

theorem norm_normalizedPhysicalAtom_le_one
    {W : ℕ} (hW : 0 < W) (x : PhysicalRowAtoms W)
    (b : Fin 3) (c : Fin W)
    (hx : |x (physicalAtomIndex b c)| ≤ 1) :
    ‖normalizedPhysicalAtom x b c‖ ≤ 1 := by
  rw [normalizedPhysicalAtom]
  norm_cast
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |blockNormalization W| * |x (physicalAtomIndex b c)| ≤ 1 * 1 :=
      mul_le_mul (abs_blockNormalization_le_one W hW) hx
        (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

theorem norm_intervalSiteBlocks_B_le_one
    {W : ℕ} (hW : 0 < W) (z : ℂ) (x : IntervalRows W 1)
    (hx : OneSiteAtomsBound W x) (a c : Fin W) :
    ‖(intervalSiteBlocks z x 0).B a c‖ ≤ 1 := by
  exact norm_normalizedPhysicalAtom_le_one hW _ 0 c
    (hx (intervalRowIndex 0 a) (physicalAtomIndex 0 c))

theorem norm_intervalSiteBlocks_C_le_one
    {W : ℕ} (hW : 0 < W) (z : ℂ) (x : IntervalRows W 1)
    (hx : OneSiteAtomsBound W x) (a c : Fin W) :
    ‖(intervalSiteBlocks z x 0).C a c‖ ≤ 1 := by
  exact norm_normalizedPhysicalAtom_le_one hW _ 2 c
    (hx (intervalRowIndex 0 a) (physicalAtomIndex 2 c))

theorem norm_intervalSiteBlocks_D_le
    {W : ℕ} (hW : 0 < W) (z : ℂ) (x : IntervalRows W 1)
    (hx : OneSiteAtomsBound W x) (a c : Fin W) :
    ‖(intervalSiteBlocks z x 0).D a c‖ ≤ 1 + ‖z‖ := by
  change ‖normalizedPhysicalAtom (x (intervalRowIndex 0 a)) 1 c -
      (if a = c then z else 0)‖ ≤ _
  calc
    _ ≤ ‖normalizedPhysicalAtom (x (intervalRowIndex 0 a)) 1 c‖ +
        ‖if a = c then z else 0‖ := norm_sub_le _ _
    _ ≤ 1 + ‖z‖ := by
      gcongr
      · exact norm_normalizedPhysicalAtom_le_one hW _ 1 c
          (hx (intervalRowIndex 0 a) (physicalAtomIndex 1 c))
      · split <;> simp

theorem norm_stepL_intervalSiteBlocks_le
    {W : ℕ} (hW : 0 < W) (z : ℂ) (x : IntervalRows W 1)
    (hx : OneSiteAtomsBound W x) (i j : Fin W ⊕ Fin W) :
    ‖stepL (intervalSiteBlocks z x 0).B i j‖ ≤ 1 + ‖z‖ := by
  cases i with
  | inl a =>
      cases j with
      | inl c =>
          exact (norm_intervalSiteBlocks_B_le_one hW z x hx a c).trans
            (le_add_of_nonneg_right (norm_nonneg z))
      | inr c =>
          simp [stepL]
          positivity
  | inr a =>
      cases j with
      | inl c =>
          simp [stepL]
          positivity
      | inr c =>
          by_cases hac : a = c <;>
            simp [stepL, Matrix.one_apply, hac] <;> positivity

theorem norm_stepK_intervalSiteBlocks_le
    {W : ℕ} (hW : 0 < W) (z : ℂ) (x : IntervalRows W 1)
    (hx : OneSiteAtomsBound W x) (i j : Fin W ⊕ Fin W) :
    ‖stepK (intervalSiteBlocks z x 0).D
        (intervalSiteBlocks z x 0).C i j‖ ≤ 1 + ‖z‖ := by
  cases i with
  | inl a =>
      cases j with
      | inl c => exact norm_intervalSiteBlocks_D_le hW z x hx a c
      | inr c =>
          exact (norm_intervalSiteBlocks_C_le_one hW z x hx a c).trans
            (le_add_of_nonneg_right (norm_nonneg z))
  | inr a =>
      cases j with
      | inl c =>
          by_cases hac : a = c <;>
            simp [stepK, Matrix.one_apply, hac] <;> positivity
      | inr c =>
          simp [stepK]
          positivity

/-! ## Minor and cleared-step bounds -/

def oneSiteLeftMinorBound (W k : ℕ) (z : ℂ) : ℝ :=
  (2 * W - k).factorial * (1 + ‖z‖) ^ (2 * W - k)

def oneSiteRightMinorBound (k : ℕ) (z : ℂ) : ℝ :=
  k.factorial * (1 + ‖z‖) ^ k

theorem norm_clearedInverseCompound_stepL_le
    {W : ℕ} (hW : 0 < W) (z : ℂ) (x : IntervalRows W 1)
    (hx : OneSiteAtomsBound W x) (k : ℕ) (hk : k ≤ 2 * W)
    (s t : powersetCard (Fin W ⊕ Fin W) k) :
    ‖clearedInverseCompound k (stepL (intervalSiteBlocks z x 0).B) s t‖ ≤
      oneSiteLeftMinorBound W k z := by
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
      (stepL (intervalSiteBlocks z x 0).B)
      (powersetCard.compl (Nat.sub_add_cancel hk') t)
      (powersetCard.compl (Nat.sub_add_cancel hk') s)
      (1 + ‖z‖)
      (norm_stepL_intervalSiteBlocks_le hW z x hx))

theorem norm_compound_stepK_le
    {W : ℕ} (hW : 0 < W) (z : ℂ) (x : IntervalRows W 1)
    (hx : OneSiteAtomsBound W x) (k : ℕ)
    (s t : powersetCard (Fin W ⊕ Fin W) k) :
    ‖compound k (stepK (intervalSiteBlocks z x 0).D
        (intervalSiteBlocks z x 0).C) s t‖ ≤
      oneSiteRightMinorBound k z := by
  rw [compound_apply]
  exact norm_minor_le_factorial_mul_pow k _ s t (1 + ‖z‖)
    (norm_stepK_intervalSiteBlocks_le hW z x hx)

def oneSiteClearedEntryBound (W k : ℕ) (z : ℂ) : ℝ :=
  Nat.choose (2 * W) k *
    (oneSiteLeftMinorBound W k z * oneSiteRightMinorBound k z)

theorem oneSiteClearedEntryBound_nonneg (W k : ℕ) (z : ℂ) :
    0 ≤ oneSiteClearedEntryBound W k z := by
  unfold oneSiteClearedEntryBound oneSiteLeftMinorBound
    oneSiteRightMinorBound
  positivity

theorem norm_clearedStepCompound_entry_le
    {W : ℕ} (hW : 0 < W) (z : ℂ) (x : IntervalRows W 1)
    (hx : OneSiteAtomsBound W x) (k : ℕ) (hk : k ≤ 2 * W)
    (s t : powersetCard (Fin W ⊕ Fin W) k) :
    ‖clearedStepCompound k (intervalSiteBlocks z x 0).B
        (intervalSiteBlocks z x 0).D
        (intervalSiteBlocks z x 0).C s t‖ ≤
      oneSiteClearedEntryBound W k z := by
  rw [clearedStepCompound_apply, norm_mul]
  simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul, Matrix.mul_apply]
  calc
    ‖∑ u, clearedInverseCompound k
          (stepL (intervalSiteBlocks z x 0).B) s u *
        compound k (stepK (intervalSiteBlocks z x 0).D
          (intervalSiteBlocks z x 0).C) u t‖ ≤
        ∑ u, ‖clearedInverseCompound k
          (stepL (intervalSiteBlocks z x 0).B) s u *
        compound k (stepK (intervalSiteBlocks z x 0).D
          (intervalSiteBlocks z x 0).C) u t‖ := norm_sum_le _ _
    _ ≤ ∑ _u : powersetCard (Fin W ⊕ Fin W) k,
        oneSiteLeftMinorBound W k z * oneSiteRightMinorBound k z := by
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul]
      exact mul_le_mul
        (norm_clearedInverseCompound_stepL_le hW z x hx k hk s u)
        (norm_compound_stepK_le hW z x hx k u t)
        (norm_nonneg _) (by
          unfold oneSiteLeftMinorBound
          positivity)
    _ = oneSiteClearedEntryBound W k z := by
      unfold oneSiteClearedEntryBound
      have hcard : Fintype.card (powersetCard (Fin W ⊕ Fin W) k) =
          Nat.choose (2 * W) k := by
        rw [← Nat.card_eq_fintype_card, powersetCard.card,
          Nat.card_eq_fintype_card]
        simp [Fintype.card_sum, two_mul]
      simp [hcard]

def oneSiteDegreeFrobeniusBound (W k : ℕ) (z : ℂ) : ℝ :=
  (Nat.choose (2 * W) k : ℝ) ^ 2 *
    oneSiteClearedEntryBound W k z

theorem oneSiteDegreeFrobeniusBound_nonneg (W k : ℕ) (z : ℂ) :
    0 ≤ oneSiteDegreeFrobeniusBound W k z := by
  unfold oneSiteDegreeFrobeniusBound
  exact mul_nonneg (sq_nonneg _) (oneSiteClearedEntryBound_nonneg W k z)

theorem oneSiteDegreeFrobeniusBound_eq
    (W k : ℕ) (hk : k ≤ 2 * W) (z : ℂ) :
    oneSiteDegreeFrobeniusBound W k z =
      (Nat.choose (2 * W) k : ℝ) ^ 2 *
        ((2 * W).factorial : ℝ) * (1 + ‖z‖) ^ (2 * W) := by
  have hfac : (Nat.choose (2 * W) k : ℝ) * k.factorial *
      (2 * W - k).factorial = (2 * W).factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  unfold oneSiteDegreeFrobeniusBound oneSiteClearedEntryBound
    oneSiteLeftMinorBound oneSiteRightMinorBound
  calc
    (Nat.choose (2 * W) k : ℝ) ^ 2 *
        ((Nat.choose (2 * W) k : ℝ) *
          (((2 * W - k).factorial : ℝ) *
            (1 + ‖z‖) ^ (2 * W - k) *
          ((k.factorial : ℝ) * (1 + ‖z‖) ^ k))) =
        (Nat.choose (2 * W) k : ℝ) ^ 2 *
          ((Nat.choose (2 * W) k : ℝ) * k.factorial *
            (2 * W - k).factorial) *
          ((1 + ‖z‖) ^ (2 * W - k) * (1 + ‖z‖) ^ k) := by ring
    _ = (Nat.choose (2 * W) k : ℝ) ^ 2 *
        ((2 * W).factorial : ℝ) * (1 + ‖z‖) ^ (2 * W) := by
      rw [hfac, ← pow_add, Nat.sub_add_cancel hk]

def oneSiteCommonDegreeBound (W : ℕ) (z : ℂ) : ℝ :=
  ((2 ^ (2 * W) : ℕ) : ℝ) ^ 2 *
    ((2 * W).factorial : ℝ) * (1 + ‖z‖) ^ (2 * W)

theorem oneSiteCommonDegreeBound_nonneg (W : ℕ) (z : ℂ) :
    0 ≤ oneSiteCommonDegreeBound W z := by
  unfold oneSiteCommonDegreeBound
  positivity

theorem oneSiteDegreeFrobeniusBound_le_common
    (W k : ℕ) (hk : k ≤ 2 * W) (z : ℂ) :
    oneSiteDegreeFrobeniusBound W k z ≤
      oneSiteCommonDegreeBound W z := by
  rw [oneSiteDegreeFrobeniusBound_eq W k hk z]
  unfold oneSiteCommonDegreeBound
  gcongr
  exact_mod_cast Nat.choose_le_two_pow (2 * W) k

theorem norm_clearedStepCompound_le_degreeBound
    {W : ℕ} (hW : 0 < W) (z : ℂ) (x : IntervalRows W 1)
    (hx : OneSiteAtomsBound W x) (k : ℕ) (hk : k ≤ 2 * W) :
    ‖clearedStepCompound k (intervalSiteBlocks z x 0).B
        (intervalSiteBlocks z x 0).D
        (intervalSiteBlocks z x 0).C‖ ≤
      oneSiteDegreeFrobeniusBound W k z := by
  have hcard : Fintype.card (powersetCard (Fin W ⊕ Fin W) k) =
      Nat.choose (2 * W) k := by
    rw [← Nat.card_eq_fintype_card, powersetCard.card,
      Nat.card_eq_fintype_card]
    simp [Fintype.card_sum, two_mul]
  have h := frobenius_norm_le_card_mul_of_entry_norm_le
    (clearedStepCompound k (intervalSiteBlocks z x 0).B
      (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C)
    (oneSiteClearedEntryBound W k z)
    (oneSiteClearedEntryBound_nonneg W k z)
    (norm_clearedStepCompound_entry_le hW z x hx k hk)
  simpa only [oneSiteDegreeFrobeniusBound, hcard, pow_two] using h

/-! ## Simultaneous degree family and coefficient tensor -/

def oneSiteFamilyCornerBound (W : ℕ) (z : ℂ) : ℝ :=
  ∑ r : Fin (2 * W + 1), oneSiteDegreeFrobeniusBound W r.1 z

theorem oneSiteFamilyCornerBound_nonneg (W : ℕ) (z : ℂ) :
    0 ≤ oneSiteFamilyCornerBound W z := by
  unfold oneSiteFamilyCornerBound
  exact Finset.sum_nonneg fun r hr ↦
    oneSiteDegreeFrobeniusBound_nonneg W r.1 z

theorem oneSiteDegreeFrobeniusBound_le_familyCornerBound
    (W : ℕ) (z : ℂ) (r : Fin (2 * W + 1)) :
    oneSiteDegreeFrobeniusBound W r.1 z ≤
      oneSiteFamilyCornerBound W z := by
  unfold oneSiteFamilyCornerBound
  exact Finset.single_le_sum
    (fun j hj ↦ oneSiteDegreeFrobeniusBound_nonneg W j.1 z)
    (Finset.mem_univ r)

theorem oneSiteFamilyCornerBound_le_common
    (W : ℕ) (z : ℂ) :
    oneSiteFamilyCornerBound W z ≤
      (2 * W + 1 : ℝ) * oneSiteCommonDegreeBound W z := by
  unfold oneSiteFamilyCornerBound
  calc
    ∑ r : Fin (2 * W + 1), oneSiteDegreeFrobeniusBound W r.1 z ≤
        ∑ _r : Fin (2 * W + 1), oneSiteCommonDegreeBound W z := by
      apply Finset.sum_le_sum
      intro r hr
      exact oneSiteDegreeFrobeniusBound_le_common W r.1
        (Nat.le_of_lt_succ r.2) z
    _ = (2 * W + 1 : ℝ) * oneSiteCommonDegreeBound W z := by
      simp

def oneSiteTensorCoarseBound (W : ℕ) (z : ℂ) : ℝ :=
  (1 + 2 * (3 * W : ℝ)) ^ W *
    ((2 * W + 1 : ℝ) * oneSiteCommonDegreeBound W z)

theorem oneSiteTensorCoarseBound_nonneg (W : ℕ) (z : ℂ) :
    0 ≤ oneSiteTensorCoarseBound W z := by
  unfold oneSiteTensorCoarseBound
  exact mul_nonneg (pow_nonneg (by positivity) W)
    (mul_nonneg (by positivity) (oneSiteCommonDegreeBound_nonneg W z))

theorem norm_oneSiteClearedFamilyRecursiveFunction_le_cornerBound
    (W : ℕ) (hW : 0 < W) (z : ℂ)
    (y : MultiAffineRows (List.replicate (1 * W) (3 * W)))
    (hy : IsReplicatedCorner (3 * W) (1 * W) y) :
    ‖oneSiteClearedFamilyRecursiveFunction W z y‖ ≤
      oneSiteFamilyCornerBound W z := by
  rw [pi_norm_le_iff_of_nonneg
    (oneSiteFamilyCornerBound_nonneg W z)]
  intro r
  let x : IntervalRows W 1 :=
    multiAffineRowsToFinRows (3 * W) (1 * W) y
  have hx : OneSiteAtomsBound W x :=
    oneSiteAtomsBound_of_corner W y hy
  change ‖intervalClearedProduct W 1 z x r‖ ≤
    oneSiteFamilyCornerBound W z
  rw [intervalClearedProduct_one]
  exact (norm_clearedStepCompound_le_degreeBound hW z x hx r.1
    (Nat.le_of_lt_succ r.2)).trans
      (oneSiteDegreeFrobeniusBound_le_familyCornerBound W z r)

/-- Fully concrete deterministic coefficient-tensor estimate for the
simultaneous family in Lemma 10.6.  No coefficient certificate remains in the
statement. -/
theorem norm_oneSiteClearedFamilyTensor_le
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    ‖oneSiteClearedFamilyTensor W z‖ ≤
      (1 + 2 * (3 * W : ℝ)) ^ W * oneSiteFamilyCornerBound W z := by
  unfold oneSiteClearedFamilyTensor
  simpa only [one_mul, Nat.cast_mul, Nat.cast_ofNat] using
    (norm_multiAffineTensorOfFunction_le_of_corner
      (E := OneSiteClearedFamily W) (3 * W) (1 * W)
      (oneSiteClearedFamilyRecursiveFunction W z)
      (oneSiteFamilyCornerBound W z)
      (oneSiteFamilyCornerBound_nonneg W z)
      (norm_oneSiteClearedFamilyRecursiveFunction_le_cornerBound W hW z))

theorem norm_oneSiteClearedFamilyTensor_le_coarse
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    ‖oneSiteClearedFamilyTensor W z‖ ≤
      oneSiteTensorCoarseBound W z := by
  calc
    ‖oneSiteClearedFamilyTensor W z‖ ≤
        (1 + 2 * (3 * W : ℝ)) ^ W *
          oneSiteFamilyCornerBound W z :=
      norm_oneSiteClearedFamilyTensor_le W hW z
    _ ≤ oneSiteTensorCoarseBound W z := by
      unfold oneSiteTensorCoarseBound
      gcongr
      exact oneSiteFamilyCornerBound_le_common W z

theorem posLog_norm_oneSiteClearedFamilyTensor_le
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    Real.posLog ‖oneSiteClearedFamilyTensor W z‖ ≤
      Real.posLog ((1 + 2 * (3 * W : ℝ)) ^ W *
        oneSiteFamilyCornerBound W z) := by
  exact Real.posLog_le_posLog (norm_nonneg _)
    (norm_oneSiteClearedFamilyTensor_le W hW z)

theorem posLog_norm_oneSiteClearedFamilyTensor_le_coarse
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    Real.posLog ‖oneSiteClearedFamilyTensor W z‖ ≤
      Real.posLog (oneSiteTensorCoarseBound W z) := by
  exact Real.posLog_le_posLog (norm_nonneg _)
    (norm_oneSiteClearedFamilyTensor_le_coarse W hW z)

def oneSiteTensorLogBound (W : ℕ) (z : ℂ) : ℝ :=
  (W : ℝ) * Real.posLog (1 + 2 * (3 * W : ℝ)) +
    Real.log (2 * W + 1 : ℝ) +
    4 * W * Real.posLog 2 +
    2 * W * Real.posLog (2 * W : ℝ) +
    2 * W * Real.posLog (1 + ‖z‖)

theorem posLog_oneSiteCommonDegreeBound_le
    (W : ℕ) (z : ℂ) :
    Real.posLog (oneSiteCommonDegreeBound W z) ≤
      4 * W * Real.posLog 2 +
        2 * W * Real.posLog (2 * W : ℝ) +
        2 * W * Real.posLog (1 + ‖z‖) := by
  let n : ℕ := 2 * W
  let q : ℝ := 1 + ‖z‖
  have hfactNat := Nat.factorial_le_pow n
  have hfact : ((n.factorial : ℕ) : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast hfactNat
  have hfactLog : Real.posLog ((n.factorial : ℕ) : ℝ) ≤
      n * Real.posLog (n : ℝ) := by
    calc
      Real.posLog ((n.factorial : ℕ) : ℝ) ≤
          Real.posLog ((n : ℝ) ^ n) :=
        Real.posLog_le_posLog (by positivity) hfact
      _ = n * Real.posLog (n : ℝ) := Real.posLog_pow n _
  have htwo :
      Real.posLog ((((2 ^ n : ℕ) : ℝ) ^ 2)) =
        2 * n * Real.posLog 2 := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.posLog_pow]
    ring
  unfold oneSiteCommonDegreeBound
  change Real.posLog (((((2 ^ n : ℕ) : ℝ) ^ 2) *
      ((n.factorial : ℕ) : ℝ)) * q ^ n) ≤ _
  calc
    Real.posLog (((((2 ^ n : ℕ) : ℝ) ^ 2) *
        ((n.factorial : ℕ) : ℝ)) * q ^ n) ≤
        Real.posLog ((((2 ^ n : ℕ) : ℝ) ^ 2) *
          ((n.factorial : ℕ) : ℝ)) + Real.posLog (q ^ n) :=
      Real.posLog_mul
    _ ≤ (Real.posLog ((((2 ^ n : ℕ) : ℝ) ^ 2)) +
        Real.posLog ((n.factorial : ℕ) : ℝ)) +
          Real.posLog (q ^ n) := by
      gcongr
      exact Real.posLog_mul
    _ ≤ (2 * n * Real.posLog 2 +
        n * Real.posLog (n : ℝ)) + n * Real.posLog q := by
      rw [htwo, Real.posLog_pow]
      gcongr
    _ = 4 * W * Real.posLog 2 +
        2 * W * Real.posLog (2 * W : ℝ) +
        2 * W * Real.posLog (1 + ‖z‖) := by
      simp only [n, q]
      push_cast
      ring

theorem posLog_oneSiteTensorCoarseBound_le_logBound
    (W : ℕ) (z : ℂ) :
    Real.posLog (oneSiteTensorCoarseBound W z) ≤
      oneSiteTensorLogBound W z := by
  unfold oneSiteTensorCoarseBound oneSiteTensorLogBound
  calc
    Real.posLog ((1 + 2 * (3 * W : ℝ)) ^ W *
        ((2 * W + 1 : ℝ) * oneSiteCommonDegreeBound W z)) ≤
        Real.posLog ((1 + 2 * (3 * W : ℝ)) ^ W) +
          Real.posLog ((2 * W + 1 : ℝ) *
            oneSiteCommonDegreeBound W z) := Real.posLog_mul
    _ ≤ W * Real.posLog (1 + 2 * (3 * W : ℝ)) +
        (Real.log (2 * W + 1 : ℝ) +
          Real.posLog (oneSiteCommonDegreeBound W z)) := by
      rw [Real.posLog_pow]
      gcongr
      simpa using
        (Real.posLog_nat_mul
          (x := oneSiteCommonDegreeBound W z) (n := 2 * W + 1))
    _ ≤ (W : ℝ) * Real.posLog (1 + 2 * (3 * W : ℝ)) +
        Real.log (2 * W + 1 : ℝ) +
        4 * W * Real.posLog 2 +
        2 * W * Real.posLog (2 * W : ℝ) +
        2 * W * Real.posLog (1 + ‖z‖) := by
      have hc := posLog_oneSiteCommonDegreeBound_le W z
      push_cast
      linarith

theorem posLog_norm_oneSiteClearedFamilyTensor_le_logBound
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    Real.posLog ‖oneSiteClearedFamilyTensor W z‖ ≤
      oneSiteTensorLogBound W z :=
  (posLog_norm_oneSiteClearedFamilyTensor_le_coarse W hW z).trans
    (posLog_oneSiteTensorCoarseBound_le_logBound W z)

def oneSiteTensorLogConstant (z : ℂ) : ℝ :=
  4 + Real.posLog 7 + Real.posLog 3 + 6 * Real.posLog 2 +
    2 * Real.posLog (1 + ‖z‖)

theorem oneSiteTensorLogConstant_nonneg (z : ℂ) :
    0 ≤ oneSiteTensorLogConstant z := by
  unfold oneSiteTensorLogConstant
  nlinarith [Real.posLog_nonneg (x := (7 : ℝ)),
    Real.posLog_nonneg (x := (3 : ℝ)),
    Real.posLog_nonneg (x := (2 : ℝ)),
    Real.posLog_nonneg (x := 1 + ‖z‖)]

theorem oneSiteTensorLogBound_le_scale
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    oneSiteTensorLogBound W z ≤
      oneSiteTensorLogConstant z * W *
        (1 + Real.posLog (W : ℝ)) := by
  have hW1Nat : 1 ≤ W := by omega
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1Nat
  have hW0 : (0 : ℝ) ≤ W := hW1.trans' (by norm_num)
  let t : ℝ := Real.posLog (W : ℝ)
  let A : ℝ := Real.posLog 7 + Real.posLog 3 +
    6 * Real.posLog 2 + 2 * Real.posLog (1 + ‖z‖)
  have ht : 0 ≤ t := Real.posLog_nonneg
  have hA : 0 ≤ A := by
    unfold A
    nlinarith [Real.posLog_nonneg (x := (7 : ℝ)),
      Real.posLog_nonneg (x := (3 : ℝ)),
      Real.posLog_nonneg (x := (2 : ℝ)),
      Real.posLog_nonneg (x := 1 + ‖z‖)]
  have hbase : Real.posLog (1 + 2 * (3 * W : ℝ)) ≤
      Real.posLog 7 + t := by
    have hle : (1 + 2 * (3 * W : ℝ)) ≤ 7 * W := by
      push_cast
      nlinarith
    calc
      Real.posLog (1 + 2 * (3 * W : ℝ)) ≤
          Real.posLog (7 * (W : ℝ)) :=
        Real.posLog_le_posLog (by positivity) hle
      _ ≤ Real.posLog 7 + t := by
        simpa only [t] using (Real.posLog_mul (x := 7) (y := (W : ℝ)))
  have hcount : Real.log (2 * W + 1 : ℝ) ≤
      Real.posLog 3 + t := by
    have hle : (2 * W + 1 : ℝ) ≤ 3 * W := by
      push_cast
      nlinarith
    have hnonneg : (0 : ℝ) ≤ 2 * W + 1 := by positivity
    have hone : (1 : ℝ) ≤ |(2 * W + 1 : ℝ)| := by
      rw [abs_of_nonneg hnonneg]
      nlinarith
    calc
      Real.log (2 * W + 1 : ℝ) =
          Real.posLog (2 * W + 1 : ℝ) :=
        (Real.posLog_eq_log hone).symm
      _ ≤ Real.posLog (3 * (W : ℝ)) :=
        Real.posLog_le_posLog hnonneg hle
      _ ≤ Real.posLog 3 + t := by
        simpa only [t] using (Real.posLog_mul (x := 3) (y := (W : ℝ)))
  have hdouble : Real.posLog (2 * W : ℝ) ≤
      Real.posLog 2 + t := by
    simpa only [t] using (Real.posLog_mul (x := 2) (y := (W : ℝ)))
  have hbaseW : (W : ℝ) * Real.posLog (1 + 2 * (3 * W : ℝ)) ≤
      W * (Real.posLog 7 + t) :=
    mul_le_mul_of_nonneg_left hbase hW0
  have hcountW : Real.log (2 * W + 1 : ℝ) ≤
      W * (Real.posLog 3 + t) := by
    calc
      Real.log (2 * W + 1 : ℝ) ≤ Real.posLog 3 + t := hcount
      _ = 1 * (Real.posLog 3 + t) := by ring
      _ ≤ W * (Real.posLog 3 + t) :=
        mul_le_mul_of_nonneg_right hW1
          (add_nonneg Real.posLog_nonneg ht)
  have hdoubleW : (2 : ℝ) * W * Real.posLog (2 * W : ℝ) ≤
      2 * W * (Real.posLog 2 + t) := by
    exact mul_le_mul_of_nonneg_left hdouble (by positivity)
  have hfirst : oneSiteTensorLogBound W z ≤
      (W : ℝ) * (A + 4 * t) := by
    unfold oneSiteTensorLogBound
    push_cast
    dsimp only [A]
    linarith
  calc
    oneSiteTensorLogBound W z ≤ (W : ℝ) * (A + 4 * t) := hfirst
    _ ≤ (A + 4) * W * (1 + t) := by
      rw [show (A + 4) * (W : ℝ) * (1 + t) =
        (W : ℝ) * ((A + 4) * (1 + t)) by ring]
      apply mul_le_mul_of_nonneg_left _ hW0
      nlinarith [mul_nonneg hA ht]
    _ = oneSiteTensorLogConstant z * W *
        (1 + Real.posLog (W : ℝ)) := by
      simp only [A, t, oneSiteTensorLogConstant]
      ring

theorem one_add_posLog_nat_eq_log_e_mul
    (W : ℕ) (hW : 0 < W) :
    1 + Real.posLog (W : ℝ) =
      Real.log (Real.exp 1 * W) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hWne : (W : ℝ) ≠ 0 := ne_of_gt hW0
  have hposLog : Real.posLog (W : ℝ) = Real.log W := by
    apply Real.posLog_eq_log
    rw [abs_of_pos hW0]
    exact_mod_cast (show 1 ≤ W by omega)
  rw [hposLog, Real.log_mul (Real.exp_ne_zero 1) hWne, Real.log_exp]

/-! ## Common `W log(eW)` scale -/

/-- On a repeated row shape, the telescoping cost is exactly the number of
rows times the single-row cost. -/
theorem multiAffineLogCost_replicate (L : ℝ) (n p : ℕ) :
    multiAffineLogCost L (List.replicate n p) =
      (n : ℝ≥0∞) * ENNReal.ofReal
        (Real.sqrt (lemma10_2Constant L) *
          Real.log (Real.exp 1 * (p : ℝ))) := by
  induction n with
  | zero => simp [multiAffineLogCost]
  | succ n ih =>
      rw [List.replicate_succ, multiAffineLogCost, ih]
      push_cast
      ring

/-- Explicit density-dependent coefficient of the repeated-row term. -/
def oneSiteRowLogConstant (L : ℝ) : ℝ :=
  Real.sqrt (lemma10_2Constant L) * (1 + Real.posLog 3)

theorem oneSiteRowLogConstant_nonneg (L : ℝ) :
    0 ≤ oneSiteRowLogConstant L := by
  unfold oneSiteRowLogConstant
  exact mul_nonneg (Real.sqrt_nonneg _)
    (add_nonneg (by norm_num) Real.posLog_nonneg)

/-- The full Corollary 10.3 row cost has the manuscript's `W log(eW)`
scale, with an explicit coefficient depending only on the density bound. -/
theorem oneSiteRepeatedRowCost_le_W_log_eW
    (L : ℝ) (W : ℕ) (hW : 0 < W) :
    multiAffineLogCost L (List.replicate (1 * W) (3 * W)) ≤
      ENNReal.ofReal (oneSiteRowLogConstant L * W *
        Real.log (Real.exp 1 * W)) := by
  have hrep : multiAffineLogCost L (List.replicate (1 * W) (3 * W)) =
      (W : ℝ≥0∞) * ENNReal.ofReal
        (Real.sqrt (lemma10_2Constant L) *
          Real.log (Real.exp 1 * (3 * W : ℝ))) := by
    simpa using multiAffineLogCost_replicate L W (3 * W)
  rw [hrep]
  have hW0 : (0 : ℝ) ≤ W := by positivity
  rw [← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_mul hW0]
  apply ENNReal.ofReal_le_ofReal
  have hscale : (1 : ℝ) ≤ Real.log (Real.exp 1 * W) := by
    rw [← one_add_posLog_nat_eq_log_e_mul W hW]
    exact le_add_of_nonneg_right Real.posLog_nonneg
  have hlog3 : Real.log (3 : ℝ) = Real.posLog 3 := by
    symm
    apply Real.posLog_eq_log
    norm_num
  have hfactor : Real.log (Real.exp 1 * (3 * W : ℝ)) =
      Real.posLog 3 + Real.log (Real.exp 1 * W) := by
    rw [show Real.exp 1 * (3 * W : ℝ) =
      3 * (Real.exp 1 * W) by push_cast; ring]
    rw [Real.log_mul (by norm_num) (mul_ne_zero (Real.exp_ne_zero 1)
      (by exact_mod_cast (ne_of_gt hW)))]
    rw [hlog3]
  rw [hfactor]
  have hsqrt : 0 ≤ Real.sqrt (lemma10_2Constant L) := Real.sqrt_nonneg _
  have hpos3 : 0 ≤ Real.posLog (3 : ℝ) := Real.posLog_nonneg
  have hmul : Real.posLog 3 ≤ Real.posLog 3 *
      Real.log (Real.exp 1 * W) := by
    nlinarith [mul_nonneg hpos3 (sub_nonneg.mpr hscale)]
  have hsingle : Real.sqrt (lemma10_2Constant L) *
      (Real.posLog 3 + Real.log (Real.exp 1 * W)) ≤
      Real.sqrt (lemma10_2Constant L) * (1 + Real.posLog 3) *
        Real.log (Real.exp 1 * W) := by
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hsqrt
    nlinarith
  calc
    (W : ℝ) * (Real.sqrt (lemma10_2Constant L) *
        (Real.posLog 3 + Real.log (Real.exp 1 * W))) ≤
        W * (Real.sqrt (lemma10_2Constant L) * (1 + Real.posLog 3) *
          Real.log (Real.exp 1 * W)) :=
      mul_le_mul_of_nonneg_left hsingle hW0
    _ = oneSiteRowLogConstant L * W *
        Real.log (Real.exp 1 * W) := by
      unfold oneSiteRowLogConstant
      ring

/-- A numerical coefficient for the two normalized interface determinants. -/
def oneSiteDetLogConstant : ℝ := Real.posLog 10 + 2

theorem oneSiteDetLogConstant_nonneg : 0 ≤ oneSiteDetLogConstant := by
  unfold oneSiteDetLogConstant
  exact add_nonneg Real.posLog_nonneg (by norm_num)

/-- The coefficient-tensor growth used for both interface determinants is
also at most an explicit constant times `W log(eW)`. -/
theorem posLog_oneSiteDetTensorGrowth_le_W_log_eW
    (W : ℕ) (hW : 0 < W) :
    Real.posLog (oneSiteDetTensorGrowth W) ≤
      oneSiteDetLogConstant * W * Real.log (Real.exp 1 * W) := by
  have hW1Nat : 1 ≤ W := by omega
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1Nat
  have hW0 : (0 : ℝ) ≤ W := by positivity
  have hnorm : |(blockNormalization W)⁻¹| = Real.sqrt (3 * W : ℝ) := by
    unfold blockNormalization
    rw [inv_inv]
    exact abs_of_nonneg (Real.sqrt_nonneg _)
  have hsqrt : Real.sqrt (3 * W : ℝ) ≤ 3 * W := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  have hbase : 1 + (3 * W : ℝ) * |(blockNormalization W)⁻¹| ≤
      10 * W ^ 2 := by
    rw [hnorm]
    have hmul := mul_le_mul_of_nonneg_left hsqrt
      (show (0 : ℝ) ≤ 3 * W by positivity)
    nlinarith [sq_nonneg ((W : ℝ) - 1)]
  have hbasepos : 0 ≤ 1 + (3 * W : ℝ) * |(blockNormalization W)⁻¹| := by
    positivity
  calc
    Real.posLog (oneSiteDetTensorGrowth W) =
        W * Real.posLog (1 + (3 * W : ℝ) *
          |(blockNormalization W)⁻¹|) := by
      unfold oneSiteDetTensorGrowth
      rw [Real.posLog_pow]
    _ ≤ W * Real.posLog (10 * W ^ 2) := by
      gcongr
    _ ≤ W * (Real.posLog 10 + 2 * Real.posLog (W : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hW0
      calc
        Real.posLog (10 * W ^ 2) ≤
            Real.posLog 10 + Real.posLog (W ^ 2 : ℝ) := by
          exact Real.posLog_mul
        _ = Real.posLog 10 + 2 * Real.posLog (W : ℝ) := by
          congr 1
          rw [Real.posLog_pow]
          norm_num
    _ ≤ oneSiteDetLogConstant * W *
        (1 + Real.posLog (W : ℝ)) := by
      unfold oneSiteDetLogConstant
      have ht : 0 ≤ Real.posLog (W : ℝ) := Real.posLog_nonneg
      have hc : 0 ≤ Real.posLog (10 : ℝ) := Real.posLog_nonneg
      have hinner : Real.posLog 10 + 2 * Real.posLog (W : ℝ) ≤
          (Real.posLog 10 + 2) * (1 + Real.posLog (W : ℝ)) := by
        nlinarith [mul_nonneg hc ht]
      calc
        (W : ℝ) * (Real.posLog 10 + 2 * Real.posLog (W : ℝ)) ≤
            W * ((Real.posLog 10 + 2) *
              (1 + Real.posLog (W : ℝ))) :=
          mul_le_mul_of_nonneg_left hinner hW0
        _ = (Real.posLog 10 + 2) * W *
            (1 + Real.posLog (W : ℝ)) := by ring
    _ = oneSiteDetLogConstant * W * Real.log (Real.exp 1 * W) := by
      rw [← one_add_posLog_nat_eq_log_e_mul W hW]

theorem posLog_norm_oneSiteClearedFamilyTensor_le_W_log_eW
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    Real.posLog ‖oneSiteClearedFamilyTensor W z‖ ≤
      oneSiteTensorLogConstant z * W *
        Real.log (Real.exp 1 * W) := by
  calc
    Real.posLog ‖oneSiteClearedFamilyTensor W z‖ ≤
        oneSiteTensorLogBound W z :=
      posLog_norm_oneSiteClearedFamilyTensor_le_logBound W hW z
    _ ≤ oneSiteTensorLogConstant z * W *
        (1 + Real.posLog (W : ℝ)) :=
      oneSiteTensorLogBound_le_scale W hW z
    _ = oneSiteTensorLogConstant z * W *
        Real.log (Real.exp 1 * W) := by
      rw [one_add_posLog_nat_eq_log_e_mul W hW]

/-! ## Certificate-free probabilistic bounds -/

def oneSiteExplicitForwardMaxIntegralBound
    (L : ℝ) (W : ℕ) (z : ℂ) : ℝ≥0∞ :=
  multiAffineLogCost L (List.replicate (1 * W) (3 * W)) +
    ENNReal.ofReal (Real.posLog
      ((1 + 2 * (3 * W : ℝ)) ^ W * oneSiteFamilyCornerBound W z))

def oneSiteLogForwardMaxIntegralBound
    (L : ℝ) (W : ℕ) (z : ℂ) : ℝ≥0∞ :=
  multiAffineLogCost L (List.replicate (1 * W) (3 * W)) +
    ENNReal.ofReal (oneSiteTensorLogBound W z)

def oneSiteWLogForwardMaxIntegralBound
    (L : ℝ) (W : ℕ) (z : ℂ) : ℝ≥0∞ :=
  multiAffineLogCost L (List.replicate (1 * W) (3 * W)) +
    ENNReal.ofReal (oneSiteTensorLogConstant z * W *
      Real.log (Real.exp 1 * W))

/-- Lemma 10.6's simultaneous forward first-moment estimate with the concrete
coefficient tensor eliminated from the right-hand side. -/
theorem oneSiteClearedFamily_posLog_lintegral_le_explicit
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal
        (Real.posLog ‖oneSiteClearedFamily W z x‖)
        ∂intervalRowsLaw W 1 μ) ≤
      oneSiteExplicitForwardMaxIntegralBound L W z := by
  calc
    (∫⁻ x, ENNReal.ofReal
        (Real.posLog ‖oneSiteClearedFamily W z x‖)
        ∂intervalRowsLaw W 1 μ) ≤
        oneSiteForwardMaxIntegralBound L W z :=
      oneSiteClearedFamily_posLog_lintegral_le hμ W hW z
    _ ≤ oneSiteExplicitForwardMaxIntegralBound L W z := by
      unfold oneSiteForwardMaxIntegralBound
        oneSiteExplicitForwardMaxIntegralBound
      exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal
        (posLog_norm_oneSiteClearedFamilyTensor_le W hW z))

/-- Factorial-free `W log W`-shaped version of the forward first-moment
bound. -/
theorem oneSiteClearedFamily_posLog_lintegral_le_logBound
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal
        (Real.posLog ‖oneSiteClearedFamily W z x‖)
        ∂intervalRowsLaw W 1 μ) ≤
      oneSiteLogForwardMaxIntegralBound L W z := by
  calc
    (∫⁻ x, ENNReal.ofReal
        (Real.posLog ‖oneSiteClearedFamily W z x‖)
        ∂intervalRowsLaw W 1 μ) ≤
        oneSiteForwardMaxIntegralBound L W z :=
      oneSiteClearedFamily_posLog_lintegral_le hμ W hW z
    _ ≤ oneSiteLogForwardMaxIntegralBound L W z := by
      unfold oneSiteForwardMaxIntegralBound
        oneSiteLogForwardMaxIntegralBound
      exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal
        (posLog_norm_oneSiteClearedFamilyTensor_le_logBound W hW z))

/-- The manuscript-scale `C_z W log(eW)` forward estimate, with an explicit
choice of the constant `oneSiteTensorLogConstant z`. -/
theorem oneSiteClearedFamily_posLog_lintegral_le_W_log_eW
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal
        (Real.posLog ‖oneSiteClearedFamily W z x‖)
        ∂intervalRowsLaw W 1 μ) ≤
      oneSiteWLogForwardMaxIntegralBound L W z := by
  calc
    (∫⁻ x, ENNReal.ofReal
        (Real.posLog ‖oneSiteClearedFamily W z x‖)
        ∂intervalRowsLaw W 1 μ) ≤
        oneSiteForwardMaxIntegralBound L W z :=
      oneSiteClearedFamily_posLog_lintegral_le hμ W hW z
    _ ≤ oneSiteWLogForwardMaxIntegralBound L W z := by
      unfold oneSiteForwardMaxIntegralBound
        oneSiteWLogForwardMaxIntegralBound
      exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal
        (posLog_norm_oneSiteClearedFamilyTensor_le_W_log_eW W hW z))

def oneSiteExplicitMaxHodgeIntegralBound
    (L : ℝ) (W : ℕ) (z : ℂ) : ℝ≥0∞ :=
  2 * oneSiteExplicitForwardMaxIntegralBound L W z +
    2 * oneSiteInterfaceDetIntegralBound L W

def oneSiteLogMaxHodgeIntegralBound
    (L : ℝ) (W : ℕ) (z : ℂ) : ℝ≥0∞ :=
  2 * oneSiteLogForwardMaxIntegralBound L W z +
    2 * oneSiteInterfaceDetIntegralBound L W

theorem oneSiteMaxHodgeIntegralBound_le_explicit
    (L : ℝ) (W : ℕ) (hW : 0 < W) (z : ℂ) :
    oneSiteMaxHodgeIntegralBound L W z ≤
      oneSiteExplicitMaxHodgeIntegralBound L W z := by
  unfold oneSiteMaxHodgeIntegralBound
    oneSiteExplicitMaxHodgeIntegralBound
  gcongr
  unfold oneSiteForwardMaxIntegralBound
    oneSiteExplicitForwardMaxIntegralBound
  exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal
    (posLog_norm_oneSiteClearedFamilyTensor_le W hW z))

theorem oneSiteMaxHodgeIntegralBound_le_logBound
    (L : ℝ) (W : ℕ) (hW : 0 < W) (z : ℂ) :
    oneSiteMaxHodgeIntegralBound L W z ≤
      oneSiteLogMaxHodgeIntegralBound L W z := by
  unfold oneSiteMaxHodgeIntegralBound oneSiteLogMaxHodgeIntegralBound
  gcongr
  unfold oneSiteForwardMaxIntegralBound oneSiteLogForwardMaxIntegralBound
  exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal
    (posLog_norm_oneSiteClearedFamilyTensor_le_logBound W hW z))

/-- The full one-site Hodge envelope bound with every internally
constructible certificate removed. -/
theorem oneSiteMaxHodgeEnvelope_lintegral_le_explicit
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal (oneSiteMaxHodgeEnvelope W z x)
        ∂intervalRowsLaw W 1 μ) ≤
      oneSiteExplicitMaxHodgeIntegralBound L W z := by
  calc
    (∫⁻ x, ENNReal.ofReal (oneSiteMaxHodgeEnvelope W z x)
        ∂intervalRowsLaw W 1 μ) ≤
        oneSiteMaxHodgeIntegralBound L W z :=
      oneSiteMaxHodgeEnvelope_lintegral_le hμ W hW z
    _ ≤ oneSiteExplicitMaxHodgeIntegralBound L W z := by
      exact oneSiteMaxHodgeIntegralBound_le_explicit L W hW z

theorem oneSiteMaxHodgeEnvelope_lintegral_le_logBound
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal (oneSiteMaxHodgeEnvelope W z x)
        ∂intervalRowsLaw W 1 μ) ≤
      oneSiteLogMaxHodgeIntegralBound L W z :=
  (oneSiteMaxHodgeEnvelope_lintegral_le hμ W hW z).trans
    (oneSiteMaxHodgeIntegralBound_le_logBound L W hW z)

/-- The common scale on the right of Lemma 10.6. -/
def oneSiteWLogScale (W : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((W : ℝ) * Real.log (Real.exp 1 * W))

/-- One explicit choice of the manuscript constant `C_{L,z}`.  It includes
the four row-cost copies, the two simultaneous forward-tensor copies, and
the two interface-determinant copies in the Hodge envelope. -/
def oneSiteMaxHodgeWLogConstant (L : ℝ) (z : ℂ) : ℝ≥0∞ :=
  4 * ENNReal.ofReal (oneSiteRowLogConstant L) +
    2 * ENNReal.ofReal (oneSiteTensorLogConstant z) +
    2 * ENNReal.ofReal oneSiteDetLogConstant

theorem oneSiteMaxHodgeIntegralBound_le_W_log_eW
    (L : ℝ) (W : ℕ) (hW : 0 < W) (z : ℂ) :
    oneSiteMaxHodgeIntegralBound L W z ≤
      oneSiteMaxHodgeWLogConstant L z * oneSiteWLogScale W := by
  have hrow : multiAffineLogCost L (List.replicate (1 * W) (3 * W)) ≤
      ENNReal.ofReal (oneSiteRowLogConstant L) * oneSiteWLogScale W := by
    have h := oneSiteRepeatedRowCost_le_W_log_eW L W hW
    rw [show oneSiteRowLogConstant L * (W : ℝ) *
      Real.log (Real.exp 1 * W) = oneSiteRowLogConstant L *
        ((W : ℝ) * Real.log (Real.exp 1 * W)) by ring,
      ENNReal.ofReal_mul (oneSiteRowLogConstant_nonneg L)] at h
    simpa only [oneSiteWLogScale] using h
  have htensor : ENNReal.ofReal
      (Real.posLog ‖oneSiteClearedFamilyTensor W z‖) ≤
      ENNReal.ofReal (oneSiteTensorLogConstant z) * oneSiteWLogScale W := by
    have h := ENNReal.ofReal_le_ofReal
      (posLog_norm_oneSiteClearedFamilyTensor_le_W_log_eW W hW z)
    rw [show oneSiteTensorLogConstant z * (W : ℝ) *
      Real.log (Real.exp 1 * W) = oneSiteTensorLogConstant z *
        ((W : ℝ) * Real.log (Real.exp 1 * W)) by ring,
      ENNReal.ofReal_mul (oneSiteTensorLogConstant_nonneg z)] at h
    simpa only [oneSiteWLogScale] using h
  have hdet : ENNReal.ofReal (Real.posLog (oneSiteDetTensorGrowth W)) ≤
      ENNReal.ofReal oneSiteDetLogConstant * oneSiteWLogScale W := by
    have h := ENNReal.ofReal_le_ofReal
      (posLog_oneSiteDetTensorGrowth_le_W_log_eW W hW)
    rw [show oneSiteDetLogConstant * (W : ℝ) *
      Real.log (Real.exp 1 * W) = oneSiteDetLogConstant *
        ((W : ℝ) * Real.log (Real.exp 1 * W)) by ring,
      ENNReal.ofReal_mul oneSiteDetLogConstant_nonneg] at h
    simpa only [oneSiteWLogScale] using h
  unfold oneSiteMaxHodgeIntegralBound oneSiteForwardMaxIntegralBound
    oneSiteInterfaceDetIntegralBound oneSiteMaxHodgeWLogConstant
  calc
    2 * (multiAffineLogCost L (List.replicate (1 * W) (3 * W)) +
        ENNReal.ofReal (Real.posLog ‖oneSiteClearedFamilyTensor W z‖)) +
        2 * (multiAffineLogCost L (List.replicate (1 * W) (3 * W)) +
          ENNReal.ofReal (Real.posLog (oneSiteDetTensorGrowth W))) ≤
      2 * (ENNReal.ofReal (oneSiteRowLogConstant L) * oneSiteWLogScale W +
        ENNReal.ofReal (oneSiteTensorLogConstant z) * oneSiteWLogScale W) +
      2 * (ENNReal.ofReal (oneSiteRowLogConstant L) * oneSiteWLogScale W +
        ENNReal.ofReal oneSiteDetLogConstant * oneSiteWLogScale W) := by
      gcongr
    _ = (4 * ENNReal.ofReal (oneSiteRowLogConstant L) +
        2 * ENNReal.ofReal (oneSiteTensorLogConstant z) +
        2 * ENNReal.ofReal oneSiteDetLogConstant) * oneSiteWLogScale W := by
      ring

/-- Caller-facing one-site first-moment statement of Lemma 10.6 with the
paper's `C_{L,z} W log(eW)` dependence and no auxiliary certificates. -/
theorem oneSiteMaxHodgeEnvelope_lintegral_le_W_log_eW
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal (oneSiteMaxHodgeEnvelope W z x)
        ∂intervalRowsLaw W 1 μ) ≤
      oneSiteMaxHodgeWLogConstant L z * oneSiteWLogScale W :=
  (oneSiteMaxHodgeEnvelope_lintegral_le hμ W hW z).trans
    (oneSiteMaxHodgeIntegralBound_le_W_log_eW L W hW z)

def intervalExplicitMaxHodgeIntegralBound
    (L : ℝ) (W s : ℕ) (z : ℂ) : ℝ≥0∞ :=
  (s : ℝ≥0∞) * oneSiteExplicitMaxHodgeIntegralBound L W z

def intervalLogMaxHodgeIntegralBound
    (L : ℝ) (W s : ℕ) (z : ℂ) : ℝ≥0∞ :=
  (s : ℝ≥0∞) * oneSiteLogMaxHodgeIntegralBound L W z

/-- Certificate-free interval corollary of the improved one-site Hodge
bound, with exact linear dependence on the number of sites. -/
theorem intervalMaxHodgeEnvelope_lintegral_le_explicit
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal (intervalMaxHodgeEnvelope W s z x)
        ∂intervalRowsLaw W s μ) ≤
      intervalExplicitMaxHodgeIntegralBound L W s z := by
  calc
    (∫⁻ x, ENNReal.ofReal (intervalMaxHodgeEnvelope W s z x)
        ∂intervalRowsLaw W s μ) ≤
        (s : ℝ≥0∞) * oneSiteMaxHodgeIntegralBound L W z :=
      intervalMaxHodgeEnvelope_lintegral_le hμ W s hW z
    _ ≤ intervalExplicitMaxHodgeIntegralBound L W s z := by
      unfold intervalExplicitMaxHodgeIntegralBound
      gcongr
      exact oneSiteMaxHodgeIntegralBound_le_explicit L W hW z

theorem intervalMaxHodgeEnvelope_lintegral_le_logBound
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal (intervalMaxHodgeEnvelope W s z x)
        ∂intervalRowsLaw W s μ) ≤
      intervalLogMaxHodgeIntegralBound L W s z := by
  calc
    (∫⁻ x, ENNReal.ofReal (intervalMaxHodgeEnvelope W s z x)
        ∂intervalRowsLaw W s μ) ≤
        (s : ℝ≥0∞) * oneSiteMaxHodgeIntegralBound L W z :=
      intervalMaxHodgeEnvelope_lintegral_le hμ W s hW z
    _ ≤ intervalLogMaxHodgeIntegralBound L W s z := by
      unfold intervalLogMaxHodgeIntegralBound
      gcongr
      exact oneSiteMaxHodgeIntegralBound_le_logBound L W hW z

/-- Interval form of Lemma 10.6: the same explicit `C_{L,z}` and exact linear
dependence on the number of sites. -/
theorem intervalMaxHodgeEnvelope_lintegral_le_W_log_eW
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal (intervalMaxHodgeEnvelope W s z x)
        ∂intervalRowsLaw W s μ) ≤
      (s : ℝ≥0∞) * oneSiteMaxHodgeWLogConstant L z *
        oneSiteWLogScale W := by
  calc
    (∫⁻ x, ENNReal.ofReal (intervalMaxHodgeEnvelope W s z x)
        ∂intervalRowsLaw W s μ) ≤
        (s : ℝ≥0∞) * oneSiteMaxHodgeIntegralBound L W z :=
      intervalMaxHodgeEnvelope_lintegral_le hμ W s hW z
    _ ≤ (s : ℝ≥0∞) *
        (oneSiteMaxHodgeWLogConstant L z * oneSiteWLogScale W) := by
      gcongr
      exact oneSiteMaxHodgeIntegralBound_le_W_log_eW L W hW z
    _ = (s : ℝ≥0∞) * oneSiteMaxHodgeWLogConstant L z *
        oneSiteWLogScale W := by ring

end BernoulliSection10
