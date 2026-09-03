import BernoulliSection10Complex.IntervalRestriction
import BernoulliSection10.FiniteIIDCoordinates

/-! # Independent concatenation of literal physical intervals -/

open MeasureTheory

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

def intervalConcatCoordinate (W p q : ℕ) :
    Fin ((p + q) * W) ≃ Fin (p * W) ⊕ Fin (q * W) :=
  (finCongr (Nat.add_mul p q W)).trans finSumFinEquiv.symm

def intervalConcat (W p q : ℕ) (v : IntervalRows W p × IntervalRows W q) :
    IntervalRows W (p + q) :=
  fun i => Sum.elim v.1 v.2 (intervalConcatCoordinate W p q i)

theorem intervalConcat_measurePreserving
    {μ : Measure ℂ} [IsProbabilityMeasure μ] (W p q : ℕ) :
    MeasurePreserving (intervalConcat W p q)
      ((intervalRowsLaw W p μ).prod (intervalRowsLaw W q μ))
      (intervalRowsLaw W (p + q) μ) := by
  letI : IsProbabilityMeasure (physicalRowLaw W μ) := by
    unfold physicalRowLaw
    infer_instance
  exact (measurePreserving_iid_reindex (physicalRowLaw W μ)
    (intervalConcatCoordinate W p q)).comp
    (measurePreserving_iid_sum_elim (physicalRowLaw W μ))

@[simp]
theorem intervalConcatCoordinate_prefix (W p q : ℕ) (j : Fin p) (a : Fin W) :
    intervalConcatCoordinate W p q (intervalRowIndex (j.castAdd q) a) =
      Sum.inl (intervalRowIndex j a) := by
  apply finSumFinEquiv.injective
  simp only [intervalConcatCoordinate, Equiv.trans_apply, Equiv.apply_symm_apply,
    finSumFinEquiv_apply_left]
  apply Fin.ext
  simp [intervalRowIndex, finProdFinEquiv]

@[simp]
theorem intervalConcatCoordinate_suffix (W p q : ℕ) (j : Fin q) (a : Fin W) :
    intervalConcatCoordinate W p q (intervalRowIndex (j.natAdd p) a) =
      Sum.inr (intervalRowIndex j a) := by
  apply finSumFinEquiv.injective
  simp only [intervalConcatCoordinate, Equiv.trans_apply, Equiv.apply_symm_apply,
    finSumFinEquiv_apply_right]
  apply Fin.ext
  simp [intervalRowIndex, finProdFinEquiv]
  ring

@[simp]
theorem intervalRestriction_concat_prefix (W p q : ℕ)
    (x : IntervalRows W p) (y : IntervalRows W q) :
    intervalRestriction (Fin.castAddEmb q) (intervalConcat W p q (x, y)) = x := by
  funext i
  obtain ⟨⟨j, a⟩, rfl⟩ := finProdFinEquiv.surjective i
  change intervalConcat W p q (x, y)
    (intervalRowEmbedding (Fin.castAddEmb q) (intervalRowIndex j a)) = _
  rw [intervalRowEmbedding_rowIndex]
  simp [intervalConcat] <;> rfl

@[simp]
theorem intervalRestriction_concat_suffix (W p q : ℕ)
    (x : IntervalRows W p) (y : IntervalRows W q) :
    intervalRestriction (Fin.natAddEmb p) (intervalConcat W p q (x, y)) = y := by
  funext i
  obtain ⟨⟨j, a⟩, rfl⟩ := finProdFinEquiv.surjective i
  change intervalConcat W p q (x, y)
    (intervalRowEmbedding (Fin.natAddEmb p) (intervalRowIndex j a)) = _
  rw [intervalRowEmbedding_rowIndex]
  simp [intervalConcat] <;> rfl

theorem intervalClearedProduct_concat (W p q : ℕ) (z : ℂ)
    (x : IntervalRows W p) (y : IntervalRows W q) (r : Fin (2 * W + 1)) :
    intervalClearedProduct W (p + q) z (intervalConcat W p q (x, y)) r =
      intervalClearedProduct W q z y r * intervalClearedProduct W p z x r := by
  rw [intervalClearedProduct_split, intervalRestriction_concat_prefix,
    intervalRestriction_concat_suffix]

end BernoulliSection10Complex
