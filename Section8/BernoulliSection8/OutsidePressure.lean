import BernoulliSection10.OutsidePressureIdentification

/-! # The literal exterior maximum on an invertible-interface event -/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection8

open BernoulliSection10 BernoulliLinearAlgebra

local instance outsidePressureSumOrder (W : ℕ) : LinearOrder (Fin W ⊕ Fin W) :=
  BernoulliLinearAlgebra.clearedStepCompoundSumLinearOrder

theorem intervalMaxDegreeLog_eq_outsidePressure_of_units
    (W s : ℕ) (z : ℂ) (x : IntervalRows W s)
    (hB : ∀ j, IsUnit (intervalSiteBlocks z x j).B.det)
    (hC : ∀ j, IsUnit (intervalSiteBlocks z x j).C.det) :
    intervalMaxDegreeLog W s z x = outsideExteriorPressure
      (intervalClearingFactor W s z x) (intervalTransferProduct W s z x) := by
  have hc := intervalClearingFactor_ne_zero W s z x hB
  have heq := intervalClearedProduct_eq_clearing_smul_compound W s z x hB
  have hu := intervalClearedProduct_det_isUnit W s z x hB hC
  have hcompound (r : Fin (2 * W + 1)) :
      0 < ‖compound r.1 (intervalTransferProduct W s z x)‖ := by
    letI : Nonempty (Set.powersetCard (Fin W ⊕ Fin W) r.1) := by
      rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
      apply Nat.choose_pos
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    apply norm_pos_iff.mpr
    intro hzero
    have hne : intervalClearedProduct W s z x r ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mpr (hu r)).ne_zero
    apply hne
    rw [heq r, hzero, smul_zero]
  have hlog (r : Fin (2 * W + 1)) : intervalDegreeLog W s z r x =
      Real.log ‖compound r.1 (intervalTransferProduct W s z x)‖ +
        Real.log ‖intervalClearingFactor W s z x‖ := by
    rw [intervalDegreeLog, heq r, norm_smul,
      Real.log_mul (norm_ne_zero_iff.mpr hc) (hcompound r).ne']
    ring
  simp only [intervalMaxDegreeLog, hlog, finitePressureMax_add_const,
    finitePressureMax_log _ hcompound, finitePressureMax_compound_norm, outsideExteriorPressure]
  ring

end BernoulliSection8
