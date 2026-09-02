import BernoulliSection9.InterfaceEndpointBridge
import Mathlib.Tactic

/-!
# Canonical large-width interface threshold

The Nguyen interface estimates only ask that the packet width dominate two
fixed positive constants.  This module packages those requirements into one
explicit threshold, so the paper-facing result does not ask the caller to
reprove the two scalar inequalities separately.
-/

noncomputable section

namespace BernoulliSection9

open MeasureTheory

universe u

/-- A width depending only on the explicit Nguyen input. -/
def interfaceCanonicalLargeWThreshold
    (I : NguyenBottomSingularInput) : Nat :=
  max 1 <| max
    (Nat.ceil (1 / nguyenInterfaceCutoffRho I ^ 2))
    (Nat.ceil (32 / interfaceCombinedRate I ^ 2))

theorem interfaceCanonicalLargeWConditions
    (I : NguyenBottomSingularInput) {W : Nat}
    (hW : interfaceCanonicalLargeWThreshold I <= W) :
    0 < W /\
      1 <= nguyenInterfaceCutoffRho I ^ 2 * (W : Real) /\
      32 <= interfaceCombinedRate I ^ 2 * (W : Real) := by
  let rho := nguyenInterfaceCutoffRho I
  let rate := interfaceCombinedRate I
  have hrho : 0 < rho := nguyenInterfaceCutoffRho_pos I
  have hrate : 0 < rate := interfaceCombinedRate_pos I
  have hceilRhoNat : Nat.ceil (1 / rho ^ 2) <= W := by
    exact (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hceilRateNat : Nat.ceil (32 / rate ^ 2) <= W := by
    exact (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  have hceilRho : (Nat.ceil (1 / rho ^ 2) : Real) <= W := by
    exact_mod_cast hceilRhoNat
  have hceilRate : (Nat.ceil (32 / rate ^ 2) : Real) <= W := by
    exact_mod_cast hceilRateNat
  have hratioRho : 1 / rho ^ 2 <= (W : Real) :=
    (Nat.le_ceil (1 / rho ^ 2)).trans hceilRho
  have hratioRate : 32 / rate ^ 2 <= (W : Real) :=
    (Nat.le_ceil (32 / rate ^ 2)).trans hceilRate
  have hcutoff : 1 <= rho ^ 2 * (W : Real) := by
    have hsquare : 0 < rho ^ 2 := sq_pos_of_pos hrho
    simpa [mul_comm] using (div_le_iff₀ hsquare).mp hratioRho
  have hlarge : 32 <= rate ^ 2 * (W : Real) := by
    have hsquare : 0 < rate ^ 2 := sq_pos_of_pos hrate
    simpa [mul_comm] using (div_le_iff₀ hsquare).mp hratioRate
  refine ⟨?_, ?_, ?_⟩
  · have : 1 <= W := (le_max_left _ _).trans hW
    omega
  · simpa [rho] using hcutoff
  · simpa [rate] using hlarge

/-- Interface control with only the canonical paper-level width hypothesis. -/
theorem interfacePairProbabilityAndPaperEndpointGoodCanonical
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {W : Nat} (I : NguyenBottomSingularInput.{u, u})
    (SL SR : IidSubgaussianSquare Omega mu W)
    (hSL : SL.subgaussianParameter ≤ I.subgaussianBound)
    (hSR : SR.subgaussianParameter ≤ I.subgaussianBound)
    (hW : interfaceCanonicalLargeWThreshold I <= W) :
    mu.real (interfacePairBadEvent I SL SR) <=
        2 * Real.exp (-(interfaceCombinedRate I / 2) * (W : Real)) ∧
      ∀ omega ∉ interfacePairBadEvent I SL SR,
        PaperEndpointGood
          (normalizedInterfaceMatrix SL omega)
          (normalizedInterfaceMatrix SR omega)
          (interfacePairOpNormBound SL SR)
          (interfaceDeterminantLowerBound I W) := by
  have h := interfaceCanonicalLargeWConditions I hW
  exact interfacePairProbabilityAndPaperEndpointGood
    mu I SL SR hSL hSR h.1 h.2.1 h.2.2

end BernoulliSection9
