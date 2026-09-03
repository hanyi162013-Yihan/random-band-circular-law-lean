import BernoulliSection10Complex.RemainderControl

/-!
# Actual transfer products and their clearing factors

The denominator-free products remain the observables. On the full-measure
invertible-interface event, this module identifies them with the common
scalar clearing factor times the compound of one underlying transfer.
This is the structural fact needed to use decomposable singular wedges.
-/

open MeasureTheory
open scoped BigOperators Matrix

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open BernoulliLinearAlgebra Matrix Set Set.powersetCard

set_option maxHeartbeats 800000

local instance intervalTransferSumOrder (W : ℕ) : LinearOrder (Fin W ⊕ Fin W) :=
  LinearOrder.lift' (fun x : Fin W ⊕ Fin W => (toLex x : Fin W ⊕ₗ Fin W))
    (fun _ _ h => toLex.injective h)

theorem list_prod_smul_compound
    {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (r : ℕ) (l : List (ℂ × Matrix n n ℂ)) :
    (l.map (fun p => p.1 • compound r p.2)).prod =
      (l.map Prod.fst).prod • compound r (l.map Prod.snd).prod := by
  induction l with
  | nil => simp [compound_one]
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, ih, compound_mul]
    rw [smul_mul_smul_comm]

def intervalClearingFactor (W s : ℕ) (z : ℂ) (x : IntervalRows W s) : ℂ :=
  (List.ofFn fun j : Fin s => (intervalSiteBlocks z x j.rev).B.det).prod

def intervalTransferProduct (W s : ℕ) (z : ℂ) (x : IntervalRows W s) :
    Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ :=
  reverseMatrixProduct (fun j => stepTransfer (intervalSiteBlocks z x j).B
    (intervalSiteBlocks z x j).D (intervalSiteBlocks z x j).C)

theorem intervalClearedProduct_eq_clearing_smul_compound
    (W s : ℕ) (z : ℂ) (x : IntervalRows W s)
    (hB : ∀ j, IsUnit (intervalSiteBlocks z x j).B.det)
    (r : Fin (2 * W + 1)) :
    intervalClearedProduct W s z x r =
      intervalClearingFactor W s z x • compound r.1 (intervalTransferProduct W s z x) := by
  let l : List (ℂ × Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :=
    List.ofFn fun j : Fin s =>
      ((intervalSiteBlocks z x j.rev).B.det,
        stepTransfer (intervalSiteBlocks z x j.rev).B
          (intervalSiteBlocks z x j.rev).D (intervalSiteBlocks z x j.rev).C)
  have heq : intervalClearedProduct W s z x r =
      (l.map (fun p => p.1 • compound r.1 p.2)).prod := by
    unfold intervalClearedProduct reverseMatrixProduct
    simp only [l, List.map_ofFn, Function.comp_def]
    congr 1
    apply congrArg List.ofFn
    funext j
    apply clearedStepCompound_eq_det_smul_compound_stepTransfer r.1
    · simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    · exact hB j.rev
  apply heq.trans
  simpa only [l, List.map_ofFn, Function.comp_def, intervalClearingFactor,
    intervalTransferProduct, reverseMatrixProduct] using list_prod_smul_compound r.1 l

theorem intervalClearingFactor_ne_zero
    (W s : ℕ) (z : ℂ) (x : IntervalRows W s)
    (hB : ∀ j, IsUnit (intervalSiteBlocks z x j).B.det) :
    intervalClearingFactor W s z x ≠ 0 := by
  apply List.prod_ne_zero
  intro hc
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hc
  exact isUnit_iff_ne_zero.mp (hB j.rev) hj

theorem intervalTransferProduct_det_isUnit
    (W s : ℕ) (z : ℂ) (x : IntervalRows W s)
    (hB : ∀ j, IsUnit (intervalSiteBlocks z x j).B.det)
    (hC : ∀ j, IsUnit (intervalSiteBlocks z x j).C.det) :
    IsUnit (intervalTransferProduct W s z x).det := by
  apply list_prod_det_isUnit
  intro A hA
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hA
  exact stepTransfer_det_isUnit _ _ _ (hB j.rev) (hC j.rev)

/-- All structural requirements of the transfer representation follow
from the actual independent bounded-density atom law. -/
theorem intervalTransfer_representation_ae
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    ∀ᵐ x ∂intervalRowsLaw W s μ,
      intervalClearingFactor W s z x ≠ 0 ∧
        IsUnit (intervalTransferProduct W s z x).det ∧
        ∀ r : Fin (2 * W + 1), intervalClearedProduct W s z x r =
          intervalClearingFactor W s z x • compound r.1 (intervalTransferProduct W s z x) := by
  filter_upwards [intervalInterfaceDets_isUnit_ae hμ W s hW z] with x hx
  exact ⟨intervalClearingFactor_ne_zero W s z x (fun j => (hx j).1),
    intervalTransferProduct_det_isUnit W s z x (fun j => (hx j).1) (fun j => (hx j).2),
    intervalClearedProduct_eq_clearing_smul_compound W s z x (fun j => (hx j).1)⟩

end BernoulliSection10Complex
