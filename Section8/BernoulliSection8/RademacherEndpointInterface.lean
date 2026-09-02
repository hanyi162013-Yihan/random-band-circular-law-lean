import BernoulliSection8.RademacherInterface
import BernoulliSection10.PacketPhysicalIdentification

/-! # Actual independent endpoint good event

The endpoint pair carries its literal product law. Its exceptional
probability follows by assembling an independent fresh packet into the
physical three-site interval and applying the proved Nguyen event there.
-/

open MeasureTheory Set
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10 BernoulliLinearAlgebra

def rademacherEndpointGoodEvent (I : NguyenBottomSingularInput.{0, 0}) (W : ℕ) :
    Set (EndpointBlockPair W) :=
  {ep | ‖normalizedBlockMatrix W ep.1‖ ≤ 40 * Real.sqrt 2 ∧
    ‖normalizedBlockMatrix W ep.2‖ ≤ 40 * Real.sqrt 2 ∧
    interfaceDeterminantLowerBound I W ≤ ‖(normalizedBlockMatrix W ep.1).det‖ ∧
    interfaceDeterminantLowerBound I W ≤ ‖(normalizedBlockMatrix W ep.2).det‖}

theorem measurableSet_rademacherEndpointGoodEvent
    (I : NguyenBottomSingularInput.{0, 0}) (W : ℕ) :
    MeasurableSet (rademacherEndpointGoodEvent I W) := by
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

theorem rademacherEndpointGoodEvent_spec
    (I : NguyenBottomSingularInput.{0, 0}) (W : ℕ) (ep : EndpointBlockPair W)
    (hep : ep ∈ rademacherEndpointGoodEvent I W) :
    PaperEndpointGood (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2)
      (40 * Real.sqrt 2) (interfaceDeterminantLowerBound I W) :=
  ⟨hep.1, hep.2.1, interfaceDeterminantLowerBound_pos I W, hep.2.2.1, hep.2.2.2⟩

theorem rademacherEndpointGoodEvent_of_packet_good
    (I : NguyenBottomSingularInput.{0, 0}) (hI : 1 ≤ I.subgaussianBound)
    (W : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (p : EndpointBlockPair W × PacketAtomRows W)
    (hp : packetPhysicalRows W p ∈ rademacherInterfaceGoodEvent I W 3) :
    p.1 ∈ rademacherEndpointGoodEvent I W := by
  have h := rademacherEndpointGood_of_good I hI W 3 hW
    (packetPhysicalRows W p) hp.2 0 2 0
  simp only [intervalSiteBlocks_packetPhysicalRows, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.cons_val_one] at h
  exact ⟨h.norm_CL_le, h.norm_BR_le, h.delta_le_norm_det_CL, h.delta_le_norm_det_BR⟩

/-- The factor nine comes from the three-block union at three sites.
Only the two endpoint blocks enter the event itself. -/
theorem rademacherEndpointGoodEvent_compl_probability_le
    (I : NguyenBottomSingularInput.{0, 0}) (hI : 1 ≤ I.subgaussianBound)
    (W : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W) :
    (endpointBlockPairLaw W rademacherLaw).real (rademacherEndpointGoodEvent I W)ᶜ ≤
      9 * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
  let epLaw := endpointBlockPairLaw W rademacherLaw
  let packetLaw := packetAtomRowsLaw W rademacherLaw
  letI : IsProbabilityMeasure epLaw := by
    dsimp [epLaw, endpointBlockPairLaw, blockAtomRowsLaw]
    infer_instance
  letI : IsProbabilityMeasure packetLaw := by
    dsimp [packetLaw, packetAtomRowsLaw]
    infer_instance
  have hfst : MeasurePreserving Prod.fst (epLaw.prod packetLaw) epLaw := measurePreserving_fst
  have hpacket := packetPhysicalRows_measurePreserving (μ := rademacherLaw) W
  have hsubset : Prod.fst ⁻¹' (rademacherEndpointGoodEvent I W)ᶜ ⊆
      packetPhysicalRows W ⁻¹' (rademacherInterfaceGoodEvent I W 3)ᶜ := by
    intro p hp hgood
    exact hp (rademacherEndpointGoodEvent_of_packet_good I hI W hW p hgood)
  calc
    epLaw.real (rademacherEndpointGoodEvent I W)ᶜ =
        (epLaw.prod packetLaw).real (Prod.fst ⁻¹' (rademacherEndpointGoodEvent I W)ᶜ) :=
      (hfst.measureReal_preimage
        (measurableSet_rademacherEndpointGoodEvent I W).compl.nullMeasurableSet).symm
    _ ≤ (epLaw.prod packetLaw).real
        (packetPhysicalRows W ⁻¹' (rademacherInterfaceGoodEvent I W 3)ᶜ) :=
      measureReal_mono hsubset
    _ = (intervalRowsLaw W 3 rademacherLaw).real
        (rademacherInterfaceGoodEvent I W 3)ᶜ :=
      hpacket.measureReal_preimage
        (measurableSet_rademacherInterfaceGoodEvent I W 3).compl.nullMeasurableSet
    _ ≤ 9 * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
      simpa using rademacherInterfaceGoodEvent_compl_probability_le I hI W 3 hW

end BernoulliSection8
