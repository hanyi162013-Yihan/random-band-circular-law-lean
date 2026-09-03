import BernoulliSection10Complex.IntervalTransfer
import BernoulliSection10Complex.ConcretePressure
import BernoulliSection10.SeamComparison

/-! # Identifying the outside transfer pressure with the actual degree maximum -/

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open BernoulliLinearAlgebra Matrix Set Set.powersetCard

local instance outsidePressureSumOrder (W : ℕ) : LinearOrder (Fin W ⊕ Fin W) :=
  BernoulliLinearAlgebra.clearedStepCompoundSumLinearOrder

theorem finitePressureMax_log {d : ℕ} (F : Fin (d + 1) → ℝ) (hF : ∀ r, 0 < F r) :
    finitePressureMax (fun r => Real.log (F r)) = Real.log (finitePressureMax F) := by
  apply le_antisymm
  · exact finitePressureMax_le fun r => Real.log_le_log (hF r) (le_finitePressureMax F r)
  · obtain ⟨r, hr⟩ := finitePressureMax_attained F
    rw [← hr]
    exact le_finitePressureMax (fun r => Real.log (F r)) r

theorem finitePressureMax_compound_norm (W : ℕ)
    (R : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    finitePressureMax (fun r : Fin (2 * W + 1) => ‖compound r.1 R‖) =
      maxExteriorOperatorGrowth R := by
  have hcard : Fintype.card (Fin W ⊕ Fin W) = 2 * W := by simp; omega
  apply le_antisymm
  · apply finitePressureMax_le
    intro r
    exact compound_operator_le_maxExteriorOperatorGrowth R (by rw [hcard]; omega)
  · apply Finset.sup'_le
    intro k hk
    have hk' : k < 2 * W + 1 := by simpa only [Finset.mem_range, hcard] using hk
    exact le_finitePressureMax (fun r : Fin (2 * W + 1) => ‖compound r.1 R‖) ⟨k, hk'⟩

theorem intervalMaxDegreeLog_eq_outsidePressure_ae
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    ∀ᵐ x ∂intervalRowsLaw W s μ,
      intervalMaxDegreeLog W s z x = outsideExteriorPressure
        (intervalClearingFactor W s z x) (intervalTransferProduct W s z x) := by
  filter_upwards [intervalTransfer_representation_ae hμ W s hW z,
    intervalClearedProduct_det_isUnit_ae hμ W s hW z] with x hx hu
  have hcompound (r : Fin (2 * W + 1)) :
      0 < ‖compound r.1 (intervalTransferProduct W s z x)‖ := by
    letI : Nonempty (powersetCard (Fin W ⊕ Fin W) r.1) := by
      rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
      apply Nat.choose_pos
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    apply norm_pos_iff.mpr
    intro hzero
    have hne : intervalClearedProduct W s z x r ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mpr (hu r)).ne_zero
    apply hne
    rw [hx.2.2 r, hzero, smul_zero]
  have hlog (r : Fin (2 * W + 1)) : intervalDegreeLog W s z r x =
      Real.log ‖compound r.1 (intervalTransferProduct W s z x)‖ +
        Real.log ‖intervalClearingFactor W s z x‖ := by
    rw [intervalDegreeLog, hx.2.2 r, norm_smul,
      Real.log_mul (norm_ne_zero_iff.mpr hx.1) (hcompound r).ne']
    ring
  simp only [intervalMaxDegreeLog, hlog, finitePressureMax_add_const,
    finitePressureMax_log _ hcompound, finitePressureMax_compound_norm, outsideExteriorPressure]
  ring

end BernoulliSection10Complex

