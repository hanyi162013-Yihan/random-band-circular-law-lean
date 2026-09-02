import BernoulliSection8.RademacherEnergy
import BernoulliSection9.ExternalInputs
import BernoulliSection10.PacketProbability
import BernoulliSection10.FiniteIIDCoordinates

/-! # Actual finite IID Bernoulli families for the Section 9 theorem

All independence, identical distribution and moment certificates are built
from the concrete product measure. The padded packet uses the same seven
fresh blocks as the physical three-site matrix; its two unused blocks do
not enter the atom selector.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10 BernoulliLinearAlgebra

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- Build the Section 9 IID certificate from an actual product marginal.
This helper is discharged below by the explicit padded packet selector. -/
def iidRademacherFamilyOfMeasurePreserving
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : Ω → ι → ℝ)
    (hG : MeasurePreserving G μ (Measure.pi fun _ : ι => rademacherLaw)) :
    IidSubgaussianFamily Ω μ ι := by
  have hc (i : ι) : MeasurePreserving (fun ω => G ω i) μ rademacherLaw :=
    (measurePreserving_eval (fun _ : ι => rademacherLaw) i).comp hG
  refine
    { atom := fun i ω => G ω i
      measurable_atom := fun i => (hc i).measurable
      independent := ?_
      identically_distributed := ?_
      centered := ?_
      variance_one := ?_
      subgaussianParameter := 1
      subgaussian := ?_ }
  · apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hc i).measurable.aemeasurable)).2
    change μ.map G = Measure.pi (fun i => μ.map (fun ω => G ω i))
    simp only [(hc _).map_eq, hG.map_eq]
  · intro i j
    exact ⟨(hc i).measurable.aemeasurable, (hc j).measurable.aemeasurable,
      (hc i).map_eq.trans (hc j).map_eq.symm⟩
  · intro i
    exact (real_integral_comp_measurePreserving (hc i) measurable_id).trans
      rademacherLaw_mean_zero
  · intro i
    exact (real_integral_comp_measurePreserving (hc i)
      (by fun_prop : Measurable (fun x : ℝ => x ^ 2))).trans rademacherLaw_second_moment
  · intro i
    apply (HasSubgaussianMGF.id_map_iff (hc i).measurable.aemeasurable).mp
    rw [(hc i).map_eq]
    exact rademacherLaw_subgaussian

def rademacherProductFamily (ι : Type*) [Fintype ι] :
    IidSubgaussianFamily (ι → ℝ) (Measure.pi fun _ : ι => rademacherLaw) ι :=
  iidRademacherFamilyOfMeasurePreserving _ id (MeasurePreserving.id _)

instance rademacherPacketLaw_isProbabilityMeasure (W : ℕ) :
    IsProbabilityMeasure (packetAtomRowsLaw W rademacherLaw) := by
  unfold packetAtomRowsLaw
  infer_instance

/-- Distinct fresh packet entries occupy distinct padded matrix entries. -/
def packetFreshEmbedding (W : ℕ) :
    ThreeBlockVariable (Fin W) ↪
      (Fin (PacketAtomRowCount W) × Fin (PacketAtomRowCount W)) where
  toFun e := (packetIndexEquiv W e.1.1, packetIndexEquiv W e.1.2)
  inj' := by
    intro e f hef
    apply Subtype.ext
    exact Prod.ext ((packetIndexEquiv W).injective (congrArg Prod.fst hef))
      ((packetIndexEquiv W).injective (congrArg Prod.snd hef))

def rawPacketAssignment (W : ℕ) (x : PacketAtomRows W) :
    ThreeBlockVariable (Fin W) → ℝ :=
  fun e => x (packetIndexEquiv W e.1.1) (packetIndexEquiv W e.1.2)

theorem rawPacketAssignment_measurePreserving (W : ℕ) :
    MeasurePreserving (rawPacketAssignment W) (packetAtomRowsLaw W rademacherLaw)
      (Measure.pi fun _ : ThreeBlockVariable (Fin W) => rademacherLaw) :=
  (measurePreserving_pi_restrict_embedding rademacherLaw (packetFreshEmbedding W)).comp
    (measurePreserving_iid_uncurry rademacherLaw)

/-- The literal seven fresh blocks on the padded physical packet law,
with all Section 9 model certificates constructed internally. -/
def rademacherPacketFamily (W : ℕ) :
    IidSubgaussianFamily (PacketAtomRows W) (packetAtomRowsLaw W rademacherLaw)
      (ThreeBlockVariable (Fin W)) :=
  iidRademacherFamilyOfMeasurePreserving _ (rawPacketAssignment W)
    (rawPacketAssignment_measurePreserving W)

@[simp] theorem rademacherPacketFamily_atom (W : ℕ)
    (e : ThreeBlockVariable (Fin W)) (x : PacketAtomRows W) :
    (rademacherPacketFamily W).atom e x = rawPacketAssignment W x e := rfl

@[simp] theorem rademacherPacketFamily_subgaussianParameter (W : ℕ) :
    (rademacherPacketFamily W).subgaussianParameter = 1 := rfl

end BernoulliSection8
