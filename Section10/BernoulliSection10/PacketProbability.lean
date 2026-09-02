import BernoulliSection10.HodgeIntegrability
import BernoulliSection10.PacketMultiaffine

/-!
# Concrete packet probability law and Proposition 10.9

The seven fresh packet blocks are grouped into the `3W` physical rows used
in the paper.  Each group is uniformly padded to `3W` real atom coordinates;
the unused coordinates do not enter the evaluation.  This module transports
Corollary 10.3 from recursive multiaffine rows to that literal flat packet law.
-/

open scoped BigOperators Matrix ENNReal NNReal
open MeasureTheory

noncomputable section

namespace BernoulliSection10

open Matrix MvPolynomial
open BernoulliLinearAlgebra

abbrev PacketAtomRowCount (W : ℕ) :=
  Fintype.card (ThreeBlockIndex (Fin W))

abbrev PacketAtomRows (W : ℕ) :=
  Fin (PacketAtomRowCount W) → Fin (PacketAtomRowCount W) → ℝ

def packetAtomRowsLaw (W : ℕ) (μ : Measure ℝ) : Measure (PacketAtomRows W) :=
  Measure.pi fun _ : Fin (PacketAtomRowCount W) ↦
    Measure.pi fun _ : Fin (PacketAtomRowCount W) ↦ μ

def packetIndexEquiv (W : ℕ) :
    ThreeBlockIndex (Fin W) ≃ Fin (PacketAtomRowCount W) :=
  Fintype.equivFin _

def packetAtomAssignment (W : ℕ) (x : PacketAtomRows W) :
    ThreeBlockVariable (Fin W) → ℂ := fun e ↦
  (blockNormalization W *
    x (packetIndexEquiv W e.1.1) (packetIndexEquiv W e.1.2) : ℝ)

def packetPhysicalRowValues (W : ℕ) (i : ThreeBlockIndex (Fin W))
    (u : Fin (PacketAtomRowCount W) → ℝ) : PacketPhysicalRow i → ℂ :=
  fun e ↦ (blockNormalization W *
    u (packetIndexEquiv W e.1.1.2) : ℝ)

theorem packetAtomAssignment_update
    (W : ℕ) (x : PacketAtomRows W)
    (i : Fin (PacketAtomRowCount W))
    (u : Fin (PacketAtomRowCount W) → ℝ) :
    packetAtomAssignment W (Function.update x i u) =
      replacePacketPhysicalRow (packetAtomAssignment W x)
        ((packetIndexEquiv W).symm i)
        (packetPhysicalRowValues W ((packetIndexEquiv W).symm i) u) := by
  funext e
  by_cases h : e.1.1 = (packetIndexEquiv W).symm i
  · have hi : packetIndexEquiv W e.1.1 = i := by
      rw [h, Equiv.apply_symm_apply]
    simp [packetAtomAssignment, replacePacketPhysicalRow,
      packetPhysicalRowValues, h, hi]
  · have hi : packetIndexEquiv W e.1.1 ≠ i := by
      intro heq
      apply h
      exact (packetIndexEquiv W).injective
        (heq.trans (Equiv.apply_symm_apply _ _).symm)
    simp [packetAtomAssignment, replacePacketPhysicalRow,
      packetPhysicalRowValues, h, hi]

theorem packetPhysicalRowValues_interpolate
    (W : ℕ) (i : ThreeBlockIndex (Fin W))
    (u v : Fin (PacketAtomRowCount W) → ℝ) (t : ℝ) :
    packetPhysicalRowValues W i ((1 - t) • u + t • v) =
      interpolatePacketPhysicalRow (t : ℂ)
        (packetPhysicalRowValues W i u)
        (packetPhysicalRowValues W i v) := by
  funext e
  simp [packetPhysicalRowValues, interpolatePacketPhysicalRow]
  push_cast
  ring

def packetBoundaryEval (W : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (x : PacketAtomRows W) : ℂ :=
  eval (packetAtomAssignment W x)
    (packetBoundaryPolynomial z CL BR Theta)

theorem packetBoundaryEval_update_line
    (W : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (x : PacketAtomRows W) (i : Fin (PacketAtomRowCount W))
    (u v : Fin (PacketAtomRowCount W) → ℝ) (t : ℝ) :
    packetBoundaryEval W z CL BR Theta
        (Function.update x i ((1 - t) • u + t • v)) =
      (1 - t) • packetBoundaryEval W z CL BR Theta
          (Function.update x i u) +
        t • packetBoundaryEval W z CL BR Theta
          (Function.update x i v) := by
  let j := (packetIndexEquiv W).symm i
  have hP := packetBoundaryPolynomial_isAffineInPhysicalRow
    z CL BR Theta j
  simp only [packetBoundaryEval, packetAtomAssignment_update]
  rw [packetPhysicalRowValues_interpolate]
  have h := hP (packetAtomAssignment W x)
    (packetPhysicalRowValues W j u) (packetPhysicalRowValues W j v) (t : ℂ)
  simpa [j] using h

def packetBoundaryEvalRecursive (W : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    MultiAffineRows
        (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W)) → ℂ :=
  fun y ↦ packetBoundaryEval W z CL BR Theta
    (multiAffineRowsToFinRows (PacketAtomRowCount W)
      (PacketAtomRowCount W) y)

theorem packetBoundaryEval_recursive_isMultiAffine
    (W : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    IsMultiAffine (packetBoundaryEvalRecursive W z CL BR Theta) := by
  apply isMultiAffine_comp_multiAffineRowsToFinRows
  intro x i u v t
  exact packetBoundaryEval_update_line W z CL BR Theta x i u v t

theorem blockNormalization_ne_zero (W : ℕ) (hW : 0 < W) :
    blockNormalization W ≠ 0 := by
  unfold blockNormalization
  exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by positivity)))

def packetAtomRowsOfRealAssignment (W : ℕ)
    (a : ThreeBlockVariable (Fin W) → ℝ) : PacketAtomRows W :=
  fun i j ↦
    if h : threeBlockFresh
        ((packetIndexEquiv W).symm i) ((packetIndexEquiv W).symm j) then
      a ⟨((packetIndexEquiv W).symm i,
        (packetIndexEquiv W).symm j), h⟩ / blockNormalization W
    else 0

theorem packetAtomAssignment_rowsOfRealAssignment
    (W : ℕ) (hW : 0 < W)
    (a : ThreeBlockVariable (Fin W) → ℝ) :
    packetAtomAssignment W (packetAtomRowsOfRealAssignment W a) =
      fun e ↦ (a e : ℂ) := by
  funext e
  change ((blockNormalization W *
      (if h : threeBlockFresh
          ((packetIndexEquiv W).symm (packetIndexEquiv W e.1.1))
          ((packetIndexEquiv W).symm (packetIndexEquiv W e.1.2)) then
        a ⟨((packetIndexEquiv W).symm (packetIndexEquiv W e.1.1),
          (packetIndexEquiv W).symm (packetIndexEquiv W e.1.2)), h⟩ /
            blockNormalization W
       else 0) : ℝ) : ℂ) = (a e : ℂ)
  simp only [Equiv.symm_apply_apply, e.2, dite_true]
  rw [mul_div_cancel₀ _ (blockNormalization_ne_zero W hW)]

theorem exists_packetAtomRows_eval_ne_zero
    (W : ℕ) (hW : 0 < W)
    {P : MvPolynomial (ThreeBlockVariable (Fin W)) ℂ} (hP : P ≠ 0) :
    ∃ x : PacketAtomRows W, eval (packetAtomAssignment W x) P ≠ 0 := by
  by_contra h
  push Not at h
  apply hP
  apply MvPolynomial.funext_set
    (s := fun _ : ThreeBlockVariable (Fin W) ↦
      Set.range ((↑) : ℝ → ℂ))
  · intro i
    exact Set.infinite_range_of_injective Complex.ofReal_injective
  · intro y hy
    choose a ha using fun e ↦ hy e (Set.mem_univ e)
    have hzero := h (packetAtomRowsOfRealAssignment W a)
    rw [packetAtomAssignment_rowsOfRealAssignment W hW a] at hzero
    have hay : (fun e ↦ (a e : ℂ)) = y := funext ha
    rw [← hay]
    exact hzero.trans (map_zero (eval fun e ↦ (a e : ℂ))).symm

theorem packetBoundaryEvalRecursive_ne_zero
    (W : ℕ) (hW : 0 < W) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (hTheta : IsUnit Theta.det) :
    packetBoundaryEvalRecursive W z CL BR Theta ≠ 0 := by
  have hP := packetBoundaryPolynomial_ne_zero
    z CL BR hCL hBR Theta hTheta
  obtain ⟨x, hx⟩ := exists_packetAtomRows_eval_ne_zero W hW hP
  intro hzero
  have hvalue := congrFun hzero
    (finRowsToMultiAffineRows (PacketAtomRowCount W)
      (PacketAtomRowCount W) x)
  apply hx
  simpa only [packetBoundaryEvalRecursive, packetBoundaryEval,
    multiAffineRowsToFinRows_leftInverse, Pi.zero_apply] using hvalue

def packetBoundaryCoefficientTensor (W : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    MultiAffineTensor ℂ
      (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W)) :=
  multiAffineTensorOfFunction
    (packetBoundaryEvalRecursive W z CL BR Theta)

theorem proposition_10_9_recursive
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (hTheta : IsUnit Theta.det) :
    (∫⁻ y, ENNReal.ofReal
        |Real.log ‖packetBoundaryEvalRecursive W z CL BR Theta y‖ -
          Real.log ‖packetBoundaryCoefficientTensor W z CL BR Theta‖|
        ∂multiAffineRowLaw μ
          (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W))) ≤
        multiAffineLogCost L
          (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W)) ∧
      ∀ᵐ y ∂multiAffineRowLaw μ
          (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W)),
        packetBoundaryEvalRecursive W z CL BR Theta y ≠ 0 := by
  have hpos : ∀ p ∈ List.replicate
      (PacketAtomRowCount W) (PacketAtomRowCount W), 0 < p := by
    intro p hp
    simp only [List.mem_replicate] at hp
    have hcard : PacketAtomRowCount W = 3 * W :=
      by simpa only [Fintype.card_fin] using
        (card_threeBlockIndex (W := Fin W))
    omega
  simpa only [packetBoundaryCoefficientTensor] using
    corollary_10_3 hμ
      (packetBoundaryEval_recursive_isMultiAffine W z CL BR Theta)
      hpos
      (packetBoundaryEvalRecursive_ne_zero
        W hW z CL BR hCL hBR Theta hTheta)

theorem proposition_10_9
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (hTheta : IsUnit Theta.det) :
    (∫⁻ x, ENNReal.ofReal
        |Real.log ‖packetBoundaryEval W z CL BR Theta x‖ -
          Real.log ‖packetBoundaryCoefficientTensor W z CL BR Theta‖|
        ∂packetAtomRowsLaw W μ) ≤
        multiAffineLogCost L
          (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W)) ∧
      ∀ᵐ x ∂packetAtomRowsLaw W μ,
        packetBoundaryEval W z CL BR Theta x ≠ 0 := by
  letI := hμ.toIsProbabilityMeasure
  let n := PacketAtomRowCount W
  let e := finRowsMultiAffineRowsMeasurableEquiv n n
  have hmp : MeasurePreserving e (packetAtomRowsLaw W μ)
      (multiAffineRowLaw μ (List.replicate n n)) := by
    simpa only [packetAtomRowsLaw, n] using
      finRowsMultiAffineRows_measurePreserving μ n n
  have hrec := proposition_10_9_recursive
    hμ W hW z CL BR hCL hBR Theta hTheta
  constructor
  · have heq := hmp.lintegral_comp_emb e.measurableEmbedding
      (fun y ↦ ENNReal.ofReal
        |Real.log ‖packetBoundaryEvalRecursive W z CL BR Theta y‖ -
          Real.log ‖packetBoundaryCoefficientTensor W z CL BR Theta‖|)
    calc
      (∫⁻ x, ENNReal.ofReal
          |Real.log ‖packetBoundaryEval W z CL BR Theta x‖ -
            Real.log ‖packetBoundaryCoefficientTensor W z CL BR Theta‖|
          ∂packetAtomRowsLaw W μ) =
          ∫⁻ y, ENNReal.ofReal
            |Real.log ‖packetBoundaryEvalRecursive W z CL BR Theta y‖ -
              Real.log ‖packetBoundaryCoefficientTensor W z CL BR Theta‖|
            ∂multiAffineRowLaw μ (List.replicate n n) := by
        simpa only [packetBoundaryEvalRecursive, e, n,
          finRowsMultiAffineRowsMeasurableEquiv_apply,
          multiAffineRowsToFinRows_leftInverse] using heq
      _ ≤ multiAffineLogCost L (List.replicate n n) := by
        simpa only [n] using hrec.1
  · have hrecMap : ∀ᵐ y ∂Measure.map e (packetAtomRowsLaw W μ),
        packetBoundaryEvalRecursive W z CL BR Theta y ≠ 0 := by
      rw [hmp.map_eq]
      simpa only [n] using hrec.2
    have hflat := e.measurableEmbedding.ae_map_iff.mp hrecMap
    simpa only [packetBoundaryEvalRecursive, e, n,
      finRowsMultiAffineRowsMeasurableEquiv_apply,
      multiAffineRowsToFinRows_leftInverse] using hflat

end BernoulliSection10
