import BernoulliSection10.SingularCoefficient
import BernoulliSection10Complex.IntervalTransfer

/-!
# Scalar tests for the actual cleared core and past

The scalar clearing factors are part of the physical products, and cancel
exactly in the relative reset estimate. This is the concrete application
of the singular-frame construction to Section 10.5.
-/

open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open BernoulliLinearAlgebra Matrix Set Set.powersetCard

set_option maxHeartbeats 800000

variable {W : Type*} [Fintype W] [LinearOrder W]

local instance clearedSingularTestSumOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift' (fun x : W ⊕ W => (toLex x : W ⊕ₗ W))
    (fun _ _ h => toLex.injective h)

theorem exists_cleared_exterior_product_scalar_test
    (A B : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (hA : IsUnit A.det) (hB : IsUnit B.det) (c d : ℂ)
    (r : ℕ) (hr : r ≤ Fintype.card (W ⊕ W)) :
    ∃ U V : unitaryGroup (W ⊕ W) ℂ, ∃ s : powersetCard (W ⊕ W) r,
      ∀ Q : Matrix (powersetCard (W ⊕ W) r) (powersetCard (W ⊕ W) r) ℂ,
        ‖c • compound r A‖ * ‖d • compound r B‖ *
          ‖((compound r (U : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ * Q *
            compound r (V : Matrix (W ⊕ W) (W ⊕ W) ℂ)) s s‖ ≤
            ‖(c • compound r A) * Q * (d • compound r B)‖ := by
  obtain ⟨U, V, s, h⟩ := exists_exterior_product_scalar_test A B hA hB r hr
  refine ⟨U, V, s, fun Q => ?_⟩
  have hh := mul_le_mul_of_nonneg_left (h Q) (mul_nonneg (norm_nonneg c) (norm_nonneg d))
  simpa only [smul_mul_assoc, mul_smul_comm, smul_smul, norm_smul, norm_mul,
    mul_assoc, mul_comm, mul_left_comm] using hh

/-- For the actual independent core and past, all singular frames and
their decomposability are proved from the interface laws. -/
theorem interval_product_scalar_test_ae
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W p q : ℕ) (hW : 0 < W) (z : ℂ) :
    ∀ᵐ x ∂intervalRowsLaw W p μ, ∀ᵐ y ∂intervalRowsLaw W q μ,
      ∀ r : Fin (2 * W + 1),
        ∃ U V : unitaryGroup (Fin W ⊕ Fin W) ℂ,
          ∃ s : powersetCard (Fin W ⊕ Fin W) r.1,
            ∀ Q : Matrix (powersetCard (Fin W ⊕ Fin W) r.1)
              (powersetCard (Fin W ⊕ Fin W) r.1) ℂ,
              ‖intervalClearedProduct W p z x r‖ * ‖intervalClearedProduct W q z y r‖ *
                ‖((compound r.1 (U : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ))ᴴ * Q *
                  compound r.1 (V : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)) s s‖ ≤
                ‖intervalClearedProduct W p z x r * Q * intervalClearedProduct W q z y r‖ := by
  filter_upwards [intervalTransfer_representation_ae hμ W p hW z] with x hx
  filter_upwards [intervalTransfer_representation_ae hμ W q hW z] with y hy
  intro r
  have hr : r.1 ≤ Fintype.card (Fin W ⊕ Fin W) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  simpa only [hx.2.2 r, hy.2.2 r] using
    exists_cleared_exterior_product_scalar_test
      (intervalTransferProduct W p z x) (intervalTransferProduct W q z y)
      hx.2.1 hy.2.1 (intervalClearingFactor W p z x) (intervalClearingFactor W q z y) r.1 hr

end BernoulliSection10Complex

