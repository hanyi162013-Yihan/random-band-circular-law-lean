import BernoulliSection10Complex.IntervalHodge
import Mathlib.Data.List.OfFn

/-!
# Literal restrictions of physical intervals

Restrictions retain their original independent row law. Splitting an
interval produces the suffix product on the left of the prefix product,
in precisely the transfer-matrix order used in the manuscript.
-/

open MeasureTheory
open scoped BigOperators Matrix

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open BernoulliLinearAlgebra

def intervalRowEmbedding {W s t : ℕ} (e : Fin t ↪ Fin s) :
    Fin (t * W) ↪ Fin (s * W) where
  toFun i := intervalRowIndex (e (finProdFinEquiv.symm i).1)
    (finProdFinEquiv.symm i).2
  inj' := by
    intro i j hij
    apply finProdFinEquiv.symm.injective
    have h := finProdFinEquiv.injective hij
    exact Prod.ext (e.injective (Prod.mk.inj h).1) (Prod.mk.inj h).2

def intervalRestriction {W s t : ℕ} (e : Fin t ↪ Fin s)
    (x : IntervalRows W s) : IntervalRows W t :=
  x ∘ intervalRowEmbedding e

@[simp]
theorem intervalRowEmbedding_rowIndex {W s t : ℕ}
    (e : Fin t ↪ Fin s) (j : Fin t) (a : Fin W) :
    intervalRowEmbedding e (intervalRowIndex j a) = intervalRowIndex (e j) a := by
  change finProdFinEquiv
    (e (finProdFinEquiv.symm (finProdFinEquiv (j, a))).1,
      (finProdFinEquiv.symm (finProdFinEquiv (j, a))).2) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem intervalRestriction_measurePreserving
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {W s t : ℕ} (e : Fin t ↪ Fin s) :
    MeasurePreserving (intervalRestriction (W := W) e)
      (intervalRowsLaw W s μ) (intervalRowsLaw W t μ) := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (physicalRowLaw W μ) := by
    unfold physicalRowLaw
    infer_instance
  exact measurePreserving_pi_restrict_embedding
    (physicalRowLaw W μ) (intervalRowEmbedding e)

@[simp]
theorem intervalSiteBlocks_intervalRestriction
    {W s t : ℕ} (e : Fin t ↪ Fin s) (z : ℂ)
    (x : IntervalRows W s) (j : Fin t) :
    intervalSiteBlocks z (intervalRestriction e x) j =
      intervalSiteBlocks z x (e j) := by
  apply PhysicalBlocks.ext <;> ext a c <;>
    simp only [intervalSiteBlocks, intervalPhysicalRow, intervalRestriction,
      Function.comp_apply, intervalRowEmbedding_rowIndex]

theorem list_ofFn_fin_rev {α : Type*} {s : ℕ} (f : Fin s → α) :
    List.ofFn (fun i => f i.rev) = (List.ofFn f).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [Fin.rev, Nat.sub_sub, Nat.add_comm]

theorem reverseMatrixProduct_split {n : Type*} [Fintype n] [DecidableEq n]
    {p q : ℕ} (M : Fin (p + q) → Matrix n n ℂ) :
    reverseMatrixProduct M =
      reverseMatrixProduct (fun j : Fin q => M (j.natAdd p)) *
        reverseMatrixProduct (fun j : Fin p => M (j.castAdd q)) := by
  unfold reverseMatrixProduct
  rw [list_ofFn_fin_rev M, List.ofFn_add, List.reverse_append, List.prod_append]
  congr 1
  · exact (congrArg List.prod (list_ofFn_fin_rev
      (fun j : Fin q => M (j.natAdd p)))).symm
  · exact (congrArg List.prod (list_ofFn_fin_rev
      (fun j : Fin p => M (j.castAdd q)))).symm

/-- Exact factorization of the actual product, including empty pieces. -/
theorem intervalClearedProduct_split
    (W p q : ℕ) (z : ℂ) (x : IntervalRows W (p + q))
    (r : Fin (2 * W + 1)) :
    intervalClearedProduct W (p + q) z x r =
      intervalClearedProduct W q z (intervalRestriction (Fin.natAddEmb p) x) r *
        intervalClearedProduct W p z (intervalRestriction (Fin.castAddEmb q) x) r := by
  have hq : intervalClearedStep W z
      (intervalRestriction (Fin.natAddEmb p) x) r =
      fun j : Fin q => intervalClearedStep W z x r (j.natAdd p) := by
    funext j
    simp only [intervalClearedStep, intervalSiteBlocks_intervalRestriction,
      Fin.natAddEmb_apply]
  have hp : intervalClearedStep W z
      (intervalRestriction (Fin.castAddEmb q) x) r =
      fun j : Fin p => intervalClearedStep W z x r (j.castAdd q) := by
    funext j
    simp only [intervalClearedStep, intervalSiteBlocks_intervalRestriction,
      Fin.castAddEmb_apply]
  simp only [intervalClearedProduct, hq, hp, reverseMatrixProduct_split]

end BernoulliSection10Complex
