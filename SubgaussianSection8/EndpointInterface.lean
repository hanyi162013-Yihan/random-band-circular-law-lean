import SubgaussianSection8.Inputs
import SubgaussianSection8.Interface
import BernoulliSection10.PacketPhysicalIdentification

/-! # Actual independent endpoint good event

The endpoint pair carries its literal product law. Its exceptional
probability follows by assembling an independent fresh packet into the
physical three-site interval and applying the proved Nguyen event there.
-/

open MeasureTheory Set
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace SubgaussianSection8
open BernoulliSection8

open BernoulliSection9 BernoulliSection10 BernoulliLinearAlgebra

def subgaussianEndpointGoodEvent (Ξ : Atom) (I : NguyenBottomSingularInput.{0, 0}) (W : ℕ) :
    Set (EndpointBlockPair W) :=
  {ep | ‖normalizedBlockMatrix W ep.1‖ ≤ opNormConstant Ξ ∧
    ‖normalizedBlockMatrix W ep.2‖ ≤ opNormConstant Ξ ∧
    interfaceDeterminantLowerBound I W ≤ ‖(normalizedBlockMatrix W ep.1).det‖ ∧
    interfaceDeterminantLowerBound I W ≤ ‖(normalizedBlockMatrix W ep.2).det‖}

theorem measurableSet_subgaussianEndpointGoodEvent (Ξ : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (W : ℕ) :
    MeasurableSet ((subgaussianEndpointGoodEvent Ξ) I W) := by
  have hL : Continuous (fun ep : EndpointBlockPair W => normalizedBlockMatrix W ep.1) := by
    unfold normalizedBlockMatrix
    fun_prop
  have hR : Continuous (fun ep : EndpointBlockPair W => normalizedBlockMatrix W ep.2) := by
    unfold normalizedBlockMatrix
    fun_prop
  exact (measurableSet_le hL.norm.measurable measurable_const).inter
    ((measurableSet_le hR.norm.measurable measurable_const).inter
      ((measurableSet_le measurable_const hL.matrix_det.norm.measurable).inter
        (measurableSet_le measurable_const hR.matrix_det.norm.measurable)))

theorem subgaussianEndpointGoodEvent_spec (Ξ : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (W : ℕ) (ep : EndpointBlockPair W)
    (hep : ep ∈ (subgaussianEndpointGoodEvent Ξ) I W) :
    PaperEndpointGood (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)
      (opNormConstant Ξ) (interfaceDeterminantLowerBound I W) :=
  ⟨hep.1, hep.2.1, interfaceDeterminantLowerBound_pos I W, hep.2.2.1, hep.2.2.2⟩

theorem subgaussianEndpointGoodEvent_of_packet_good (Ξ : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : Ξ.parameter ≤ I.subgaussianBound)
    (W : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (p : EndpointBlockPair W × PacketAtomRows W)
    (hp : packetPhysicalRows W p ∈ (subgaussianInterfaceGoodEvent Ξ) I W 3) :
    p.1 ∈ (subgaussianEndpointGoodEvent Ξ) I W := by
  have h := (subgaussianEndpointGood_of_good Ξ) I hI W 3 hW
    (packetPhysicalRows W p) hp 0 2 0
  simp only [intervalSiteBlocks_packetPhysicalRows, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.cons_val_one] at h
  exact ⟨h.norm_CL_le, h.norm_BR_le, h.delta_le_norm_det_CL, h.delta_le_norm_det_BR⟩

/-- The factor nine comes from the three-block union at three sites.
Only the two endpoint blocks enter the event itself. -/
theorem subgaussianEndpointGoodEvent_compl_probability_le (Ξ : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : Ξ.parameter ≤ I.subgaussianBound)
    (W : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W) :
    (endpointBlockPairLaw W Ξ.law).real ((subgaussianEndpointGoodEvent Ξ) I W)ᶜ ≤
      9 * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
  let epLaw := endpointBlockPairLaw W Ξ.law
  let packetLaw := packetAtomRowsLaw W Ξ.law
  letI : IsProbabilityMeasure epLaw := by
    dsimp [epLaw, endpointBlockPairLaw, blockAtomRowsLaw]
    infer_instance
  letI : IsProbabilityMeasure packetLaw := by
    dsimp [packetLaw, packetAtomRowsLaw]
    infer_instance
  have hfst : MeasurePreserving Prod.fst (epLaw.prod packetLaw) epLaw := measurePreserving_fst
  have hpacket := packetPhysicalRows_measurePreserving (μ := Ξ.law) W
  have hsubset : Prod.fst ⁻¹' ((subgaussianEndpointGoodEvent Ξ) I W)ᶜ ⊆
      packetPhysicalRows W ⁻¹' ((subgaussianInterfaceGoodEvent Ξ) I W 3)ᶜ := by
    intro p hp hgood
    exact hp ((subgaussianEndpointGoodEvent_of_packet_good Ξ) I hI W hW p hgood)
  calc
    epLaw.real ((subgaussianEndpointGoodEvent Ξ) I W)ᶜ =
        (epLaw.prod packetLaw).real (Prod.fst ⁻¹' ((subgaussianEndpointGoodEvent Ξ) I W)ᶜ) :=
      (hfst.measureReal_preimage
        ((measurableSet_subgaussianEndpointGoodEvent Ξ) I W).compl.nullMeasurableSet).symm
    _ ≤ (epLaw.prod packetLaw).real
        (packetPhysicalRows W ⁻¹' ((subgaussianInterfaceGoodEvent Ξ) I W 3)ᶜ) :=
      measureReal_mono hsubset
    _ = (intervalRowsLaw W 3 Ξ.law).real
        ((subgaussianInterfaceGoodEvent Ξ) I W 3)ᶜ :=
      hpacket.measureReal_preimage
        ((measurableSet_subgaussianInterfaceGoodEvent Ξ) I W 3).compl.nullMeasurableSet
    _ ≤ 9 * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
      have h := (subgaussianInterfaceGoodEvent_compl_probability_le Ξ) I hI W 3 hW
      norm_num at h
      simpa using h

end SubgaussianSection8
