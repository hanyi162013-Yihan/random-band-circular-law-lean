import SubgaussianSection8.Atom
import BernoulliSection8.RademacherIID
import BernoulliSection8.RademacherIntervalIID

/-! Literal packet and interval IID certificates for any fixed atom law. -/
open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator NNReal
noncomputable section
namespace SubgaussianSection8
open BernoulliSection9 BernoulliSection10 BernoulliLinearAlgebra

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

def iidFamilyOfMeasurePreserving (A : Atom)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : Ω → ι → ℝ)
    (hG : MeasurePreserving G μ (Measure.pi fun _ : ι => A.law)) :
    IidSubgaussianFamily Ω μ ι := by
  have hc (i : ι) : MeasurePreserving (fun ω => G ω i) μ A.law :=
    (measurePreserving_eval (fun _ : ι => A.law) i).comp hG
  refine
    { atom := fun i ω => G ω i
      measurable_atom := fun i => (hc i).measurable
      independent := ?_
      identically_distributed := ?_
      centered := ?_
      variance_one := ?_
      subgaussianParameter := A.parameter
      subgaussian := ?_ }
  · apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hc i).measurable.aemeasurable)).2
    change μ.map G = Measure.pi (fun i => μ.map (fun ω => G ω i))
    simp only [(hc _).map_eq, hG.map_eq]
  · intro i j
    exact ⟨(hc i).measurable.aemeasurable, (hc j).measurable.aemeasurable,
      (hc i).map_eq.trans (hc j).map_eq.symm⟩
  · intro i
    exact (real_integral_comp_measurePreserving (hc i) measurable_id).trans A.centered
  · intro i
    exact (real_integral_comp_measurePreserving (hc i)
      (by fun_prop : Measurable (fun x : ℝ => x ^ 2))).trans A.second_moment
  · intro i
    apply (HasSubgaussianMGF.id_map_iff (hc i).measurable.aemeasurable).mp
    rw [(hc i).map_eq]
    exact A.subgaussian

def productFamily (A : Atom) (ι : Type*) [Fintype ι] :
    IidSubgaussianFamily (ι → ℝ) (Measure.pi fun _ : ι => A.law) ι :=
  iidFamilyOfMeasurePreserving A _ id (MeasurePreserving.id _)

def intervalFamily (A : Atom) (W s : ℕ) :
    IidSubgaussianFamily (IntervalRows W s) (intervalRowsLaw W s A.law)
      (Fin (s * W) × Fin (3 * W)) :=
  iidFamilyOfMeasurePreserving A _ (fun x p => x p.1 p.2)
    (measurePreserving_iid_uncurry A.law)

def intervalSquare (A : Atom) (W s : ℕ) (j : Fin s) (b : Fin 3) :
    IidSubgaussianSquare (IntervalRows W s) (intervalRowsLaw W s A.law) W :=
  (intervalFamily A W s).squareRestriction
    (BernoulliSection8.intervalSquareEntryEmbedding j b)

@[simp] theorem intervalSquare_subgaussianParameter
    (A : Atom) (W s : ℕ) (j : Fin s) (b : Fin 3) :
    (intervalSquare A W s j b).subgaussianParameter = A.parameter := rfl

@[simp] theorem intervalSquare_rawMatrix_apply (A : Atom) (W s : ℕ)
    (j : Fin s) (b : Fin 3) (x : IntervalRows W s) (a c : Fin W) :
    (intervalSquare A W s j b).rawMatrix x a c =
      (x (intervalRowIndex j a) (physicalAtomIndex b c) : ℂ) := rfl

def opNormConstant (A : Atom) : ℝ := 40 * Real.sqrt (A.parameter + 1)

@[simp] theorem intervalSquare_opNormConstant
    (A : Atom) (W s : ℕ) (j : Fin s) (b : Fin 3) :
    subgaussianOpNormConstant (intervalSquare A W s j b) = opNormConstant A := rfl

instance (A : Atom) (W : ℕ) : IsProbabilityMeasure (packetAtomRowsLaw W A.law) := by
  unfold packetAtomRowsLaw
  infer_instance

theorem rawPacketAssignment_measurePreserving (A : Atom) (W : ℕ) :
    MeasurePreserving (BernoulliSection8.rawPacketAssignment W) (packetAtomRowsLaw W A.law)
      (Measure.pi fun _ : ThreeBlockVariable (Fin W) => A.law) :=
  (measurePreserving_pi_restrict_embedding A.law (BernoulliSection8.packetFreshEmbedding W)).comp
    (measurePreserving_iid_uncurry A.law)

def packetFamily (A : Atom) (W : ℕ) :
    IidSubgaussianFamily (PacketAtomRows W) (packetAtomRowsLaw W A.law)
      (ThreeBlockVariable (Fin W)) :=
  iidFamilyOfMeasurePreserving A _ (BernoulliSection8.rawPacketAssignment W)
    (rawPacketAssignment_measurePreserving A W)

@[simp] theorem packetFamily_atom (A : Atom) (W : ℕ)
    (e : ThreeBlockVariable (Fin W)) (x : PacketAtomRows W) :
    (packetFamily A W).atom e x = BernoulliSection8.rawPacketAssignment W x e := rfl

@[simp] theorem packetFamily_subgaussianParameter (A : Atom) (W : ℕ) :
    (packetFamily A W).subgaussianParameter = A.parameter := rfl

end SubgaussianSection8
