import BernoulliSection8.CellCoordinates
import SubgaussianSection8.IntervalResetLoss
import BernoulliSection8.ResetTelescoping

/-! # Each actual cell-prefix loss has the literal interval reset law -/

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace SubgaussianSection8
open BernoulliSection8

open BernoulliSection9 BernoulliSection10

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

@[simp] theorem flattenCompleteCells_row (Ξ : Atom) (W c K : ℕ)
    (x : Fin K → IntervalRows W c) (k : Fin K) (j : Fin c) (a : Fin W) :
    flattenCompleteCells W c K x (intervalRowIndex (completeCellSite k j) a) =
      x k (intervalRowIndex j a) := by
  simp only [flattenCompleteCells, completeCellRowEquiv_rowIndex]

/-- Restricting a chronological cell interval to an initial group of
cells is exactly flattening the same initial cell array. -/
theorem intervalRestriction_flatten_prefix (Ξ : Atom) (W c K n : ℕ) (hn : n ≤ K)
    (x : Fin K → IntervalRows W c) :
    intervalRestriction (Fin.castLEEmb (Nat.mul_le_mul_right c hn))
      (flattenCompleteCells W c K x) =
      flattenCompleteCells W c n (fun k => x (Fin.castLE hn k)) := by
  funext i
  obtain ⟨⟨j, a⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨k, l⟩, rfl⟩ := finProdFinEquiv.surjective j
  change flattenCompleteCells W c K x
    (intervalRowEmbedding (Fin.castLEEmb (Nat.mul_le_mul_right c hn))
      (intervalRowIndex (completeCellSite k l) a)) = _
  rw [intervalRowEmbedding_rowIndex]
  change flattenCompleteCells W c K x
    (intervalRowIndex (completeCellSite (Fin.castLE hn k) l) a) =
      flattenCompleteCells W c n (fun k => x (Fin.castLE hn k))
        (intervalRowIndex (completeCellSite k l) a)
  simp only [(flattenCompleteCells_row Ξ)]

def cellPastEmbedding (Ξ : Atom) (s K : ℕ) (j : Fin K) :
    Fin (j.val * (3 + s)) ↪ Fin (K * (3 + s)) :=
  Fin.castLEEmb (Nat.mul_le_mul_right (3 + s) j.isLt.le)

/-- The chronological interval through cell `j` is written in the exact
`past + reset + core` type used by `(intervalResetLoss Ξ)`. -/
def cellThroughResetEmbedding (Ξ : Atom) (s K : ℕ) (j : Fin K) :
    Fin (j.val * (3 + s) + 3 + s) ↪ Fin (K * (3 + s)) :=
  Fin.castLEEmb (by
    calc
      j.val * (3 + s) + 3 + s = (j.val + 1) * (3 + s) := by ring
      _ ≤ K * (3 + s) := Nat.mul_le_mul_right _ j.isLt)

def cellPastRows (Ξ : Atom) (W s K : ℕ) (j : Fin K) (x : Fin K → IntervalRows W (3 + s)) :
    IntervalRows W (j.val * (3 + s)) :=
  intervalRestriction ((cellPastEmbedding Ξ) s K j) (flattenCompleteCells W (3 + s) K x)

def cellThroughResetRows (Ξ : Atom) (W s K : ℕ) (j : Fin K)
    (x : Fin K → IntervalRows W (3 + s)) : IntervalRows W (j.val * (3 + s) + 3 + s) :=
  intervalRestriction ((cellThroughResetEmbedding Ξ) s K j)
    (flattenCompleteCells W (3 + s) K x)

theorem intervalLastCore_cellThroughResetRows (Ξ : Atom) (W s K : ℕ) (j : Fin K)
    (x : Fin K → IntervalRows W (3 + s)) :
    (intervalLastCore Ξ) W s (j.val * (3 + s)) ((cellThroughResetRows Ξ) W s K j x) =
      completeCellCore W s (x j) := by
  funext i
  obtain ⟨⟨k, a⟩, rfl⟩ := finProdFinEquiv.surjective i
  change (intervalLastCore Ξ) W s (j.val * (3 + s)) ((cellThroughResetRows Ξ) W s K j x)
      (intervalRowIndex k a) =
    completeCellCore W s (x j) (intervalRowIndex k a)
  simp only [(intervalLastCore Ξ), (cellThroughResetRows Ξ), completeCellCore,
    intervalRestriction, Function.comp_apply, intervalRowEmbedding_rowIndex]
  have hsite : (cellThroughResetEmbedding Ξ) s K j
      ((Fin.natAddEmb (j.val * (3 + s) + 3)) k) =
      completeCellSite j ((Fin.natAddEmb 3) k) := by
    apply Fin.ext
    simp [(cellThroughResetEmbedding Ξ), completeCellSite, finProdFinEquiv]
    ring
  rw [hsite, (flattenCompleteCells_row Ξ)]

theorem intervalPast_cellThroughResetRows (Ξ : Atom) (W s K : ℕ) (j : Fin K)
    (x : Fin K → IntervalRows W (3 + s)) :
    (intervalPastBeforeReset Ξ) W s (j.val * (3 + s))
      ((cellThroughResetRows Ξ) W s K j x) = (cellPastRows Ξ) W s K j x := by
  funext i
  obtain ⟨⟨k, a⟩, rfl⟩ := finProdFinEquiv.surjective i
  change (intervalPastBeforeReset Ξ) W s (j.val * (3 + s))
      ((cellThroughResetRows Ξ) W s K j x) (intervalRowIndex k a) =
    (cellPastRows Ξ) W s K j x (intervalRowIndex k a)
  simp only [(intervalPastBeforeReset Ξ), (cellThroughResetRows Ξ), (cellPastRows Ξ),
    intervalRestriction, Function.comp_apply, intervalRowEmbedding_rowIndex]
  have hsite : (cellThroughResetEmbedding Ξ) s K j
      ((Fin.castAddEmb s) ((Fin.castAddEmb 3) k)) = (cellPastEmbedding Ξ) s K j k := by
    apply Fin.ext
    rfl
  rw [hsite]

theorem intervalResetPacket_cellThroughResetRows (Ξ : Atom) (W s K : ℕ) (j : Fin K)
    (x : Fin K → IntervalRows W (3 + s)) :
    intervalRestriction (Fin.natAddEmb (j.val * (3 + s)))
      (intervalRestriction (Fin.castAddEmb s) ((cellThroughResetRows Ξ) W s K j x)) =
      completeCellReset W s (x j) := by
  funext i
  obtain ⟨⟨k, a⟩, rfl⟩ := finProdFinEquiv.surjective i
  change intervalRestriction (Fin.natAddEmb (j.val * (3 + s)))
      (intervalRestriction (Fin.castAddEmb s) ((cellThroughResetRows Ξ) W s K j x))
      (intervalRowIndex k a) =
    completeCellReset W s (x j) (intervalRowIndex k a)
  simp only [(cellThroughResetRows Ξ), completeCellReset, intervalRestriction,
    Function.comp_apply, intervalRowEmbedding_rowIndex]
  have hsite : (cellThroughResetEmbedding Ξ) s K j
      ((Fin.castAddEmb s) ((Fin.natAddEmb (j.val * (3 + s))) k)) =
      completeCellSite j ((Fin.castAddEmb s) k) := by
    apply Fin.ext
    simp [(cellThroughResetEmbedding Ξ), completeCellSite, finProdFinEquiv]
    ring
  rw [hsite, (flattenCompleteCells_row Ξ)]

theorem intervalClearedProduct_cellThroughResetRows (Ξ : Atom) (W s K : ℕ) (j : Fin K) (z : ℂ)
    (x : Fin K → IntervalRows W (3 + s)) (r : Fin (2 * W + 1)) :
    intervalClearedProduct W (j.val * (3 + s) + 3 + s) z
      ((cellThroughResetRows Ξ) W s K j x) r =
      intervalClearedProduct W s z (completeCellCore W s (x j)) r *
        intervalClearedProduct W 3 z (completeCellReset W s (x j)) r *
          intervalClearedProduct W (j.val * (3 + s)) z ((cellPastRows Ξ) W s K j x) r := by
  rw [intervalClearedProduct_split W (j.val * (3 + s) + 3) s,
    intervalClearedProduct_split W (j.val * (3 + s)) 3]
  change intervalClearedProduct W s z
    ((intervalLastCore Ξ) W s (j.val * (3 + s)) ((cellThroughResetRows Ξ) W s K j x)) r *
    (intervalClearedProduct W 3 z
      (intervalRestriction (Fin.natAddEmb (j.val * (3 + s)))
        (intervalRestriction (Fin.castAddEmb s) ((cellThroughResetRows Ξ) W s K j x))) r *
      intervalClearedProduct W (j.val * (3 + s)) z
        ((intervalPastBeforeReset Ξ) W s (j.val * (3 + s))
          ((cellThroughResetRows Ξ) W s K j x)) r) = _
  rw [(intervalLastCore_cellThroughResetRows Ξ), (intervalPast_cellThroughResetRows Ξ),
    (intervalResetPacket_cellThroughResetRows Ξ), Matrix.mul_assoc]

theorem intervalClearedProduct_cellPastRows (Ξ : Atom) (W s K : ℕ) (j : Fin K) (z : ℂ)
    (x : Fin K → IntervalRows W (3 + s)) (r : Fin (2 * W + 1)) :
    intervalClearedProduct W (j.val * (3 + s)) z ((cellPastRows Ξ) W s K j x) r =
      reverseMatrixProduct (fun k : Fin j.val =>
        intervalClearedProduct W s z (completeCellCore W s (x (k.castLE j.isLt.le))) r *
          intervalClearedProduct W 3 z (completeCellReset W s (x (k.castLE j.isLt.le))) r) := by
  unfold cellPastRows cellPastEmbedding
  rw [(intervalRestriction_flatten_prefix Ξ)]
  exact intervalClearedProduct_flatten_core_reset W s j.val z _ r

/-- The actual core matrices as a natural-indexed array. The extension
by the identity past the finite array is never used by a prefix `≤ K`. -/
def cellCoreProducts (Ξ : Atom) (W s K : ℕ) (z : ℂ) (r : Fin (2 * W + 1))
    (x : Fin K → IntervalRows W (3 + s)) (j : ℕ) :
    Matrix (Set.powersetCard (Fin W ⊕ Fin W) r.val)
      (Set.powersetCard (Fin W ⊕ Fin W) r.val) ℂ :=
  if hj : j < K then intervalClearedProduct W s z
    (completeCellCore W s (x ⟨j, hj⟩)) r else 1

def cellResetProducts (Ξ : Atom) (W s K : ℕ) (z : ℂ) (r : Fin (2 * W + 1))
    (x : Fin K → IntervalRows W (3 + s)) (j : ℕ) :
    Matrix (Set.powersetCard (Fin W ⊕ Fin W) r.val)
      (Set.powersetCard (Fin W ⊕ Fin W) r.val) ℂ :=
  if hj : j < K then intervalClearedProduct W 3 z
    (completeCellReset W s (x ⟨j, hj⟩)) r else 1

@[simp] theorem cellCoreProducts_val (Ξ : Atom) (W s K : ℕ) (z : ℂ) (r : Fin (2 * W + 1))
    (x : Fin K → IntervalRows W (3 + s)) (j : Fin K) :
    (cellCoreProducts Ξ) W s K z r x j.val =
      intervalClearedProduct W s z (completeCellCore W s (x j)) r := by
  simp [(cellCoreProducts Ξ), j.isLt]

@[simp] theorem cellResetProducts_val (Ξ : Atom) (W s K : ℕ) (z : ℂ) (r : Fin (2 * W + 1))
    (x : Fin K → IntervalRows W (3 + s)) (j : Fin K) :
    (cellResetProducts Ξ) W s K z r x j.val =
      intervalClearedProduct W 3 z (completeCellReset W s (x j)) r := by
  simp [(cellResetProducts Ξ), j.isLt]

theorem intervalClearedProduct_flatten_eq_resetPrefixProduct (Ξ : Atom)
    (W s K : ℕ) (z : ℂ) (x : Fin K → IntervalRows W (3 + s)) (r : Fin (2 * W + 1)) :
    intervalClearedProduct W (K * (3 + s)) z (flattenCompleteCells W (3 + s) K x) r =
      resetPrefixProduct ((cellCoreProducts Ξ) W s K z r x)
        ((cellResetProducts Ξ) W s K z r x) K := by
  letI : Nonempty (Set.powersetCard (Fin W ⊕ Fin W) r.val) := by
    rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
    apply Nat.choose_pos
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  rw [intervalClearedProduct_flatten_core_reset, ← reverseMatrixProduct_eq_resetPrefixProduct]
  congr 1
  funext k
  simp only [(cellCoreProducts_val Ξ), (cellResetProducts_val Ξ)]

theorem intervalClearedProduct_cellPastRows_eq_resetPrefixProduct (Ξ : Atom)
    (W s K : ℕ) (j : Fin K) (z : ℂ)
    (x : Fin K → IntervalRows W (3 + s)) (r : Fin (2 * W + 1)) :
    intervalClearedProduct W (j.val * (3 + s)) z ((cellPastRows Ξ) W s K j x) r =
      resetPrefixProduct ((cellCoreProducts Ξ) W s K z r x)
        ((cellResetProducts Ξ) W s K z r x) j.val := by
  letI : Nonempty (Set.powersetCard (Fin W ⊕ Fin W) r.val) := by
    rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
    apply Nat.choose_pos
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  rw [(intervalClearedProduct_cellPastRows Ξ), ← reverseMatrixProduct_eq_resetPrefixProduct]
  congr 1
  funext k
  have hk : k.val < K := lt_of_lt_of_le k.isLt j.isLt.le
  simp [(cellCoreProducts Ξ), (cellResetProducts Ξ), hk, Fin.castLE]

theorem intervalClearedProduct_cellThroughResetRows_eq_resetPrefixProduct (Ξ : Atom)
    (W s K : ℕ) (j : Fin K) (z : ℂ)
    (x : Fin K → IntervalRows W (3 + s)) (r : Fin (2 * W + 1)) :
    intervalClearedProduct W (j.val * (3 + s) + 3 + s) z
      ((cellThroughResetRows Ξ) W s K j x) r =
      resetPrefixProduct ((cellCoreProducts Ξ) W s K z r x)
        ((cellResetProducts Ξ) W s K z r x) (j.val + 1) := by
  rw [(intervalClearedProduct_cellThroughResetRows Ξ),
    (intervalClearedProduct_cellPastRows_eq_resetPrefixProduct Ξ)]
  simp only [resetPrefixProduct, (cellCoreProducts_val Ξ), (cellResetProducts_val Ξ)]

/-- A single actual prefix loss, expressed entirely using its physical
rows. The equality below identifies its full distribution. -/
def cellIntervalResetLoss (Ξ : Atom) (W s K : ℕ) (j : Fin K) (z : ℂ)
    (r : Fin (2 * W + 1)) (T : ℝ) (x : Fin K → IntervalRows W (3 + s)) : ℝ :=
  cappedSpliceLoss T
    ‖intervalClearedProduct W s z (completeCellCore W s (x j)) r‖
    ‖intervalClearedProduct W (j.val * (3 + s)) z ((cellPastRows Ξ) W s K j x) r‖
    ‖intervalClearedProduct W (j.val * (3 + s) + 3 + s) z
      ((cellThroughResetRows Ξ) W s K j x) r‖

theorem cellIntervalResetLoss_eq_intervalResetLoss (Ξ : Atom) (W s K : ℕ) (j : Fin K) (z : ℂ)
    (r : Fin (2 * W + 1)) (T : ℝ) (x : Fin K → IntervalRows W (3 + s)) :
    (cellIntervalResetLoss Ξ) W s K j z r T x =
      (intervalResetLoss Ξ) W s (j.val * (3 + s)) z r T ((cellThroughResetRows Ξ) W s K j x) := by
  simp only [(cellIntervalResetLoss Ξ), (intervalResetLoss Ξ),
    (intervalLastCore_cellThroughResetRows Ξ), (intervalPast_cellThroughResetRows Ξ)]

/-- The precise random variable used by the telescoping theorem is (Ξ : Atom) the
same literal reset loss whose integral was proved on interval rows. -/
theorem prefixResetLoss_eq_cellIntervalResetLoss (Ξ : Atom)
    (W s K : ℕ) (j : Fin K) (z : ℂ) (r : Fin (2 * W + 1)) (T : ℝ)
    (x : Fin K → IntervalRows W (3 + s)) :
    prefixResetLoss ((cellCoreProducts Ξ) W s K z r x) ((cellResetProducts Ξ) W s K z r x) T j.val =
      (cellIntervalResetLoss Ξ) W s K j z r T x := by
  simp only [prefixResetLoss, (cellIntervalResetLoss Ξ), (cellCoreProducts_val Ξ),
    (intervalClearedProduct_cellPastRows_eq_resetPrefixProduct Ξ),
    (intervalClearedProduct_cellThroughResetRows_eq_resetPrefixProduct Ξ)]

theorem cellThroughResetRows_measurePreserving (Ξ : Atom)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (W s K : ℕ) (j : Fin K) :
    MeasurePreserving ((cellThroughResetRows Ξ) W s K j)
      (independentCoreLaw μ W (3 + s) K)
      (intervalRowsLaw W (j.val * (3 + s) + 3 + s) μ) :=
  (physicalRestriction_measurePreserving μ ((cellThroughResetEmbedding Ξ) s K j)).comp
    (flattenCompleteCells_measurePreserving μ W (3 + s) K)

theorem integral_cellIntervalResetLoss_eq (Ξ : Atom)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (W s K : ℕ) (j : Fin K) (z : ℂ)
    (r : Fin (2 * W + 1)) (T : ℝ) :
    (∫ x, (cellIntervalResetLoss Ξ) W s K j z r T x ∂independentCoreLaw μ W (3 + s) K) =
      ∫ y, (intervalResetLoss Ξ) W s (j.val * (3 + s)) z r T y
        ∂intervalRowsLaw W (j.val * (3 + s) + 3 + s) μ := by
  simp only [(cellIntervalResetLoss_eq_intervalResetLoss Ξ)]
  exact real_integral_comp_measurePreserving
    ((cellThroughResetRows_measurePreserving Ξ) μ W s K j)
    ((measurable_intervalResetLoss Ξ) W s (j.val * (3 + s)) z r T)

theorem cellIntervalResetLoss_integral_le (Ξ : Atom)
    (cook : CookInput Ξ) (I : NguyenBottomSingularInput.{0, 0})
    (hI : Ξ.parameter ≤ I.subgaussianBound) (W s K : ℕ) (j : Fin K) (z : ℂ)
    (hW : (subgaussianBoundaryWidthThreshold Ξ) cook z ≤ W)
    (hWI : interfaceCanonicalLargeWThreshold I ≤ W)
    (r : Fin (2 * W + 1)) {T : ℝ} (hT : 0 < T) :
    (∫ x, (cellIntervalResetLoss Ξ) W s K j z r T x
      ∂independentCoreLaw Ξ.law W (3 + s) K) ≤
      (subgaussianBoundaryLogConstant Ξ) I z * W * densityLogScale W +
        (subgaussianBoundaryBaseLoss Ξ) cook W z + T *
          ((subgaussianBoundaryBadProbability Ξ) cook W +
            (9 + 3 * ((s : ℝ) + (j.val * (3 + s) : ℕ))) *
              Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ))) := by
  rw [(integral_cellIntervalResetLoss_eq Ξ)]
  exact (intervalResetLoss_integral_le Ξ) cook I hI W s (j.val * (3 + s)) z hW hWI r hT

end SubgaussianSection8
