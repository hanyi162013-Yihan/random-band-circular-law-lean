/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/FiniteProbability.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RandomMatrixModel

/-! Finite measure bounds without implicit measurability or independence assumptions. -/

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace HighBandLSV.FiniteProbability

theorem ofReal_prod {I : Type*} (s : Finset I) (b : I → Real)
    (hb : ∀ i ∈ s, 0 ≤ b i) :
    ENNReal.ofReal (∏ i ∈ s, b i) = ∏ i ∈ s, ENNReal.ofReal (b i) := by
  classical
  revert hb
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert i s hi ih =>
    intro hb
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      ENNReal.ofReal_mul (hb i (Finset.mem_insert_self _ _))]
    rw [ih (fun j hj => hb j (Finset.mem_insert_of_mem hj))]

theorem finite_union {Omega Q : Type*} [MeasurableSpace Omega] [Fintype Q]
    (mu : Measure Omega) (E : Q → Set Omega) {B : Real}
    (hE : ∀ q, mu (E q) ≤ ENNReal.ofReal B) :
    mu (⋃ q, E q) ≤ ENNReal.ofReal ((Fintype.card Q : Real) * B) := by
  calc
    mu (⋃ q, E q) ≤ ∑' q, mu (E q) := measure_iUnion_le _
    _ ≤ ∑' _q : Q, ENNReal.ofReal B := ENNReal.tsum_le_tsum hE
    _ = (Fintype.card Q : ENNReal) * ENNReal.ofReal B := by simp
    _ = ENNReal.ofReal ((Fintype.card Q : Real) * B) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp

theorem finite_union_of_card_bound {Omega Q : Type*}
    [MeasurableSpace Omega] [Fintype Q]
    (mu : Measure Omega) (E : Q → Set Omega) {B count : Real}
    (hB : 0 ≤ B) (hcount : (Fintype.card Q : Real) ≤ count)
    (hE : ∀ q, mu (E q) ≤ ENNReal.ofReal B) :
    mu (⋃ q, E q) ≤ ENNReal.ofReal (count * B) := by
  exact (finite_union mu E hE).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcount hB))

theorem product_bound {I : Type*} (s : Finset I) (a : I → ENNReal) (b : I → Real)
    (hb : ∀ i ∈ s, 0 ≤ b i) (hab : ∀ i ∈ s, a i ≤ ENNReal.ofReal (b i)) :
    (∏ i ∈ s, a i) ≤ ENNReal.ofReal (∏ i ∈ s, b i) := by
  rw [ofReal_prod s b hb]
  exact Finset.prod_le_prod' hab

end HighBandLSV.FiniteProbability

#print axioms HighBandLSV.FiniteProbability.finite_union
#print axioms HighBandLSV.FiniteProbability.product_bound

