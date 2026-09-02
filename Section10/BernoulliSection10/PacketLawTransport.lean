import BernoulliSection10.FiniteIIDCoordinates
import BernoulliSection10.PacketProbability
import BernoulliSection10.EndpointDeterminant

/-!
# The padded packet law generates a literal physical interval

The seven fresh blocks and the two independently integrated endpoint
blocks use nine distinct sets of atoms. The two padded dummy blocks in
the packet are unused. This module constructs the atom selection map and
proves its law, so packet independence is not a model-side certificate.
-/

open MeasureTheory

noncomputable section

namespace BernoulliSection10

open BernoulliLinearAlgebra

set_option maxHeartbeats 1600000

def packetSiteEquiv (W : ℕ) : (Fin 3 × Fin W) ≃ ThreeBlockIndex (Fin W) where
  toFun p := match p.1.val with
    | 0 => packetLeftRow p.2
    | 1 => packetCenterRow p.2
    | _ => packetRightRow p.2
  invFun i := match i with
    | Sum.inl (false, a) => (0, a)
    | Sum.inr a => (1, a)
    | Sum.inl (true, a) => (2, a)
  left_inv p := by rcases p with ⟨j, a⟩; fin_cases j <;> rfl
  right_inv i := by
    rcases i with ⟨b, a⟩ | a
    · cases b <;> rfl
    · rfl

abbrev PacketSourceCoordinate (W : ℕ) :=
  ((Fin W × Fin W) ⊕ (Fin W × Fin W)) ⊕
    (Fin (PacketAtomRowCount W) × Fin (PacketAtomRowCount W))

def endpointAtomsFlatten (W : ℕ) (ep : EndpointBlockPair W) :
    (Fin W × Fin W) ⊕ (Fin W × Fin W) → ℝ :=
  Sum.elim (fun p => ep.1 p.1 p.2) (fun p => ep.2 p.1 p.2)

def packetSourceFlatten (W : ℕ) (p : EndpointBlockPair W × PacketAtomRows W) :
    PacketSourceCoordinate W → ℝ :=
  Sum.elim (endpointAtomsFlatten W p.1) (fun q => p.2 q.1 q.2)

theorem endpointAtomsFlatten_measurePreserving
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (W : ℕ) :
    MeasurePreserving (endpointAtomsFlatten W) (endpointBlockPairLaw W μ)
      (Measure.pi fun _ : (Fin W × Fin W) ⊕ (Fin W × Fin W) => μ) := by
  have hf := measurePreserving_iid_uncurry (ι := Fin W) (κ := Fin W) μ
  exact (measurePreserving_iid_sum_elim μ).comp (hf.prod hf)

theorem packetSourceFlatten_measurePreserving
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (W : ℕ) :
    MeasurePreserving (packetSourceFlatten W)
      ((endpointBlockPairLaw W μ).prod (packetAtomRowsLaw W μ))
      (Measure.pi fun _ : PacketSourceCoordinate W => μ) := by
  letI : IsProbabilityMeasure (endpointBlockPairLaw W μ) := by
    dsimp [endpointBlockPairLaw, blockAtomRowsLaw]
    infer_instance
  have hp := measurePreserving_iid_uncurry
    (ι := Fin (PacketAtomRowCount W)) (κ := Fin (PacketAtomRowCount W)) μ
  exact (measurePreserving_iid_sum_elim μ).comp
    ((endpointAtomsFlatten_measurePreserving W).prod hp)

/-- Block labels in a physical row are `B,A,C`; their packet columns are
right, diagonal, and left respectively. Wrap-around entries are supplied
by the two endpoint blocks instead of by padded packet coordinates. -/
def packetColumnSite (j b : Fin 3) : Fin 3 :=
  ⟨(j.val + 1 + 2 * b.val) % 3, Nat.mod_lt _ (by decide)⟩

def packetSelectedAtom (W : ℕ) (p : (Fin 3 × Fin W) × (Fin 3 × Fin W)) :
    PacketSourceCoordinate W :=
  if p.1.1 = 0 ∧ p.2.1 = 2 then Sum.inl (Sum.inl (p.1.2, p.2.2))
  else if p.1.1 = 2 ∧ p.2.1 = 0 then Sum.inl (Sum.inr (p.1.2, p.2.2))
  else Sum.inr
    (packetIndexEquiv W (packetSiteEquiv W p.1),
      packetIndexEquiv W (packetSiteEquiv W (packetColumnSite p.1.1 p.2.1, p.2.2)))

theorem packetSelectedAtom_injective (W : ℕ) : Function.Injective (packetSelectedAtom W) := by
  rintro ⟨⟨j, a⟩, ⟨b, c⟩⟩ ⟨⟨k, d⟩, ⟨e, f⟩⟩ h
  fin_cases j <;> fin_cases b <;> fin_cases k <;> fin_cases e <;>
    simp_all [packetSelectedAtom, packetColumnSite, packetSiteEquiv,
      packetLeftRow, packetCenterRow, packetRightRow]

def packetPhysicalAtomEmbedding (W : ℕ) :
    (Fin (3 * W) × Fin (3 * W)) ↪ PacketSourceCoordinate W :=
  (Equiv.prodCongr finProdFinEquiv.symm finProdFinEquiv.symm).toEmbedding.trans
    ⟨packetSelectedAtom W, packetSelectedAtom_injective W⟩

def packetPhysicalRows (W : ℕ) (p : EndpointBlockPair W × PacketAtomRows W) :
    IntervalRows W 3 := fun i a =>
  packetSourceFlatten W p (packetPhysicalAtomEmbedding W (i, a))

/-- The assembled nine-block packet has exactly the physical three-site
i.i.d. law, including all row and within-row independence. -/
theorem packetPhysicalRows_measurePreserving
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (W : ℕ) :
    MeasurePreserving (packetPhysicalRows W)
      ((endpointBlockPairLaw W μ).prod (packetAtomRowsLaw W μ))
      (intervalRowsLaw W 3 μ) := by
  have hs := (measurePreserving_pi_restrict_embedding μ (packetPhysicalAtomEmbedding W)).comp
    (packetSourceFlatten_measurePreserving W)
  exact (measurePreserving_iid_curry (ι := Fin (3 * W)) (κ := Fin (3 * W)) μ).comp hs

theorem packetPhysicalRows_apply (W : ℕ) (p : EndpointBlockPair W × PacketAtomRows W)
    (j b : Fin 3) (a c : Fin W) :
    packetPhysicalRows W p (intervalRowIndex j a) (physicalAtomIndex b c) =
      packetSourceFlatten W p (packetSelectedAtom W ((j, a), (b, c))) := by
  change packetSourceFlatten W p (packetSelectedAtom W
    (finProdFinEquiv.symm (finProdFinEquiv (j, a)),
      finProdFinEquiv.symm (finProdFinEquiv (b, c)))) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end BernoulliSection10
