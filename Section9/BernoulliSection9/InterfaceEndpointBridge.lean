import BernoulliSection9.EndpointInterfaceData
import BernoulliSection9.InterfaceOperatorControl

/-!
# From iid interface squares to the paper endpoint data

This module applies the proved interface-control theorem separately to the
two endpoint squares.  The two squares may be dependent: the only operation
combining their exceptional events is the union bound.
-/

open scoped Matrix Matrix.Norms.L2Operator ENNReal NNReal

noncomputable section

namespace BernoulliSection9

open MeasureTheory ProbabilityTheory

universe u

/-- The endpoint matrix with the paper's `(3W)^{-1/2}` normalization. -/
def normalizedInterfaceMatrix
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega} {W : Nat}
    (S : IidSubgaussianSquare Omega mu W) (omega : Omega) :
    Matrix (Fin W) (Fin W) Complex :=
  ((((Real.sqrt (3 * (W : Real)))⁻¹ : Real) : Complex) • S.rawMatrix omega)

/-- The joint endpoint failure event.  No independence between the two
endpoint squares is built into this definition or used below. -/
def interfacePairBadEvent
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega} {W : Nat}
    (I : NguyenBottomSingularInput)
    (SL SR : IidSubgaussianSquare Omega mu W) : Set Omega :=
  interfaceCombinedBadEvent I SL ∪ interfaceCombinedBadEvent I SR

/-- The common deterministic operator-norm bound for the two endpoints. -/
def interfacePairOpNormBound
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega} {W : Nat}
    (SL SR : IidSubgaussianSquare Omega mu W) : Real :=
  max (subgaussianOpNormConstant SL) (subgaussianOpNormConstant SR)

/-- The determinant lower bound supplied by the Nguyen interface input. -/
def interfaceDeterminantLowerBound
    (I : NguyenBottomSingularInput) (W : Nat) : Real :=
  Real.exp
    (-nguyenInterfaceDetLoss I (nguyenInterfaceCutoffRho I) * (W : Real))

lemma interfaceDeterminantLowerBound_pos
    (I : NguyenBottomSingularInput) (W : Nat) :
    0 < interfaceDeterminantLowerBound I W := by
  exact Real.exp_pos _

/-- Applying the complete interface theorem to both endpoint squares gives
the sum of their exponential error bounds.  This theorem deliberately makes
no independence assumption between `SL` and `SR`. -/
theorem interfacePairBadEvent_probability_le
    {Omega : Type u} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu] {W : Nat}
    (I : NguyenBottomSingularInput.{u, u})
    (SL SR : IidSubgaussianSquare Omega mu W)
    (hSL : SL.subgaussianParameter ≤ I.subgaussianBound)
    (hSR : SR.subgaussianParameter ≤ I.subgaussianBound) (hW : 0 < W)
    (hcutoffLarge :
      1 <= nguyenInterfaceCutoffRho I ^ 2 * (W : Real))
    (hlarge : 32 <= interfaceCombinedRate I ^ 2 * (W : Real)) :
    mu.real (interfacePairBadEvent I SL SR) <=
      2 * Real.exp (-(interfaceCombinedRate I / 2) * (W : Real)) := by
  have hL := (interfaceCanonicalDetUpperLowerInverseControl
    mu I SL hSL hW hcutoffLarge hlarge).1
  have hR := (interfaceCanonicalDetUpperLowerInverseControl
    mu I SR hSR hW hcutoffLarge hlarge).1
  calc
    mu.real (interfacePairBadEvent I SL SR) <=
        mu.real (interfaceCombinedBadEvent I SL) +
          mu.real (interfaceCombinedBadEvent I SR) := by
      exact measureReal_union_le _ _
    _ <= Real.exp (-(interfaceCombinedRate I / 2) * (W : Real)) +
          Real.exp (-(interfaceCombinedRate I / 2) * (W : Real)) :=
      add_le_add hL hR
    _ = 2 * Real.exp (-(interfaceCombinedRate I / 2) * (W : Real)) := by
      ring

/-- Outside the joint bad event, the two normalized raw iid matrices satisfy
exactly `PaperEndpointGood`, with no inverse, compound-matrix, elimination,
or RRQR certificate exposed to the caller. -/
theorem paperEndpointGood_of_not_mem_interfacePairBadEvent
    {Omega : Type u} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu] {W : Nat}
    (I : NguyenBottomSingularInput.{u, u})
    (SL SR : IidSubgaussianSquare Omega mu W)
    (hSL : SL.subgaussianParameter ≤ I.subgaussianBound)
    (hSR : SR.subgaussianParameter ≤ I.subgaussianBound) (hW : 0 < W)
    (hcutoffLarge :
      1 <= nguyenInterfaceCutoffRho I ^ 2 * (W : Real))
    (hlarge : 32 <= interfaceCombinedRate I ^ 2 * (W : Real))
    (omega : Omega) (hgood : omega ∉ interfacePairBadEvent I SL SR) :
    PaperEndpointGood
      (normalizedInterfaceMatrix SL omega)
      (normalizedInterfaceMatrix SR omega)
      (interfacePairOpNormBound SL SR)
      (interfaceDeterminantLowerBound I W) := by
  have hsplit :
      omega ∉ interfaceCombinedBadEvent I SL ∧
        omega ∉ interfaceCombinedBadEvent I SR := by
    simpa [interfacePairBadEvent] using hgood
  have hL := (interfaceCanonicalDetUpperLowerInverseControl
    mu I SL hSL hW hcutoffLarge hlarge).2 omega hsplit.1
  have hR := (interfaceCanonicalDetUpperLowerInverseControl
    mu I SR hSR hW hcutoffLarge hlarge).2 omega hsplit.2
  refine
    { norm_CL_le := hL.1.trans (le_max_left _ _)
      norm_BR_le := hR.1.trans (le_max_right _ _)
      delta_pos := interfaceDeterminantLowerBound_pos I W
      delta_le_norm_det_CL := hL.2.1
      delta_le_norm_det_BR := hR.2.1 }

/-- Combined probability-and-good-data form used by the Section 9 caller.
Its only external mathematical input is Nguyen's bottom-singular-value input;
the operator-norm bound is derived internally from the two iid subgaussian
square structures. -/
theorem interfacePairProbabilityAndPaperEndpointGood
    {Omega : Type u} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu] {W : Nat}
    (I : NguyenBottomSingularInput.{u, u})
    (SL SR : IidSubgaussianSquare Omega mu W)
    (hSL : SL.subgaussianParameter ≤ I.subgaussianBound)
    (hSR : SR.subgaussianParameter ≤ I.subgaussianBound) (hW : 0 < W)
    (hcutoffLarge :
      1 <= nguyenInterfaceCutoffRho I ^ 2 * (W : Real))
    (hlarge : 32 <= interfaceCombinedRate I ^ 2 * (W : Real)) :
    mu.real (interfacePairBadEvent I SL SR) <=
        2 * Real.exp (-(interfaceCombinedRate I / 2) * (W : Real)) ∧
      ∀ omega ∉ interfacePairBadEvent I SL SR,
        PaperEndpointGood
          (normalizedInterfaceMatrix SL omega)
          (normalizedInterfaceMatrix SR omega)
          (interfacePairOpNormBound SL SR)
          (interfaceDeterminantLowerBound I W) := by
  exact ⟨interfacePairBadEvent_probability_le mu I SL SR hSL hSR hW
      hcutoffLarge hlarge,
    fun omega hgood => paperEndpointGood_of_not_mem_interfacePairBadEvent
      mu I SL SR hSL hSR hW hcutoffLarge hlarge omega hgood⟩

end BernoulliSection9
