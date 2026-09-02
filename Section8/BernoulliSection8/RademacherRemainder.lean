import BernoulliSection8.RademacherTransferBounds
import BernoulliSection10.OutsidePressureIdentification

/-!
# Removing the actual incomplete cell

The empty remainder contributes zero because its operator norm is one.
For a nonempty remainder the deterministic Hodge bound is applied on the
same physical interface good event as the complete cells.
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10 BernoulliLinearAlgebra

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem intervalClearedProduct_empty (W : ℕ) (z : ℂ) (x : IntervalRows W 0)
    (r : Fin (2 * W + 1)) : intervalClearedProduct W 0 z x r = 1 := by
  simp [intervalClearedProduct, reverseMatrixProduct]

theorem rademacher_remainder_log_change_le
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W p q : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (z : ℂ) (x : IntervalRows W (p + q))
    (hx : x ∈ rademacherInterfaceGoodEvent I W (p + q)) (r : Fin (2 * W + 1)) :
    |intervalDegreeLog W (p + q) z r x -
      intervalDegreeLog W p z r (intervalRestriction (Fin.castAddEmb q) x)| ≤
      rademacherTransferLogConstant I z * ((q * W : ℕ) : ℝ) * densityLogScale W := by
  rw [intervalDegreeLog, intervalDegreeLog, intervalClearedProduct_split]
  by_cases hq : q = 0
  · subst q
    simp [intervalClearedProduct_empty]
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    have hprefix := rademacherInterfaceGoodEvent_subset_subinterval I (Fin.castAddEmb q) hx
    have htail := rademacherInterfaceGoodEvent_subset_subinterval I (Fin.natAddEmb p) hx
    have hdet := rademacherInterface_dets_isUnit_of_good I hI W q hW
      (intervalRestriction (Fin.natAddEmb p) x) htail.2 z
    have hu := intervalClearedProduct_det_isUnit W q z _
      (fun j => (hdet j).1) (fun j => (hdet j).2) r
    have hprefix0 := (rademacherInterval_norm_pos_of_good I hI W p hW z _ hprefix r).ne'
    have hpne := norm_ne_zero_iff.mp hprefix0
    letI : Nonempty (Set.powersetCard (Fin W ⊕ Fin W) r.1) := by
      rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
      apply Nat.choose_pos
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    have h := abs_matrix_logNorm_mul_sub_le_hodgeLoss
      (intervalClearedProduct W q z (intervalRestriction (Fin.natAddEmb p) x) r)
      (intervalClearedProduct W p z (intervalRestriction (Fin.castAddEmb q) x) r) hu hpne
    apply h.trans
    have hb : ∀ i a, |intervalRestriction (Fin.natAddEmb p) x i a| ≤ 1 := by
      intro i a
      rcases htail.1 i a with hh | hh <;> rw [hh] <;> norm_num
    have hh := rademacherInterval_hodgeLoss_le_of_good I hI W q hW hqpos z _ htail.2 hb r
    rwa [one_add_posLog_nat_eq_log_e_mul W (interfaceCanonicalLargeWConditions I hW).1] at hh

theorem rademacher_remainder_maxPressure_change_le
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W p q : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (z : ℂ) (x : IntervalRows W (p + q))
    (hx : x ∈ rademacherInterfaceGoodEvent I W (p + q)) :
    |intervalMaxDegreeLog W (p + q) z x -
      intervalMaxDegreeLog W p z (intervalRestriction (Fin.castAddEmb q) x)| ≤
      rademacherTransferLogConstant I z * ((q * W : ℕ) : ℝ) * densityLogScale W := by
  apply abs_finitePressureMax_sub_le
  exact rademacher_remainder_log_change_le I hI W p q hW z x hx

end BernoulliSection8
