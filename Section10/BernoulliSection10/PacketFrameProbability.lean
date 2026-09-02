import BernoulliSection10.PacketProbability
import BernoulliSection10.PacketFrame
import BernoulliSection10.PositiveLog

/-!
# Probability layer for the packet frame

This module transports physical-row multiaffinity through the concrete
large-frame coefficient limit.  It is the first probability-side bridge
toward Proposition 10.10.
-/

open scoped BigOperators Matrix Topology ENNReal NNReal
open MeasureTheory

noncomputable section

namespace BernoulliSection10

open Filter Matrix MvPolynomial
open BernoulliLinearAlgebra

set_option maxHeartbeats 800000

/-- Evaluation of a squarefree polynomial as the finite sum of all of its
squarefree coefficients. -/
theorem eval_eq_sum_squarefree_coeff
    {v : Type*} [Fintype v] [DecidableEq v]
    (P : MvPolynomial v ℂ) (hP : HasSquarefreeSupport P)
    (x : v → ℂ) :
    eval x P =
      ∑ S : Finset v, coeff (squarefreeExponent S) P * ∏ i : S, x i := by
  calc
    eval x P = eval x (squarefreePolynomial
        (WithLp.toLp 2
          (fun S => coeff (squarefreeExponent S) P))) := by
      rw [squarefreePolynomial_coefficients_eq P hP]
    _ = _ := by
      simp [squarefreePolynomial, eval_monomial, squarefreeExponent,
        Finsupp.prod_indicator_index]

/-- Squarefree support is independent of the computational choice of
decidable equality. -/
theorem hasSquarefreeSupport_classical_to_infer
    {v : Type*} [Fintype v] [DecidableEq v]
    {P : MvPolynomial v ℂ}
    (hP : @HasSquarefreeSupport v (Classical.decEq v) P) :
    HasSquarefreeSupport P := by
  have hinst : (Classical.decEq v) = (inferInstance : DecidableEq v) :=
    Subsingleton.elim _ _
  cases hinst
  exact hP

/-! ## Passing physical-row affinity through the frame limit -/

/-- Coefficientwise frame convergence may be evaluated at every fixed packet
assignment because all polynomials involved live in the same finite
squarefree coefficient space. -/
theorem tendsto_packetBoundaryPolynomial_frame_eval
    (W r : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r)
    (x : ThreeBlockVariable (Fin W) → ℂ) :
    Tendsto
      (fun q => packetFrameComplexNormalization r q *
        eval x (packetBoundaryPolynomial z CL BR
          (packetFrameTheta U V s q)))
      atTop
      (nhds ((-1 : ℂ) ^ r *
        eval x
          (packetScalarMatrixCoefficientPolynomial r z CL BR U V s))) := by
  let Z := packetScalarMatrixCoefficientPolynomial r z CL BR U V s
  have hsum : Tendsto
      (fun q => ∑ S : Finset (ThreeBlockVariable (Fin W)),
        (packetFrameComplexNormalization r q *
          coeff (squarefreeExponent S)
            (packetBoundaryPolynomial z CL BR
              (packetFrameTheta U V s q))) *
          ∏ i : S, x i)
      atTop
      (nhds (∑ S : Finset (ThreeBlockVariable (Fin W)),
        (((-1 : ℂ) ^ r * coeff (squarefreeExponent S) Z) *
          ∏ i : S, x i))) := by
    refine tendsto_finsetSum Finset.univ ?_
    intro S hS
    exact (tendsto_packetBoundaryPolynomial_frame_coefficient
      (squarefreeExponent S) r z CL BR U V s).mul_const (∏ i : S, x i)
  have hleft :
      (fun q => packetFrameComplexNormalization r q *
        eval x (packetBoundaryPolynomial z CL BR
          (packetFrameTheta U V s q))) =
        fun q => ∑ S : Finset (ThreeBlockVariable (Fin W)),
          (packetFrameComplexNormalization r q *
            coeff (squarefreeExponent S)
              (packetBoundaryPolynomial z CL BR
                (packetFrameTheta U V s q))) *
            ∏ i : S, x i := by
    funext q
    rw [eval_eq_sum_squarefree_coeff
      (packetBoundaryPolynomial z CL BR (packetFrameTheta U V s q))
      (hasSquarefreeSupport_globalBoundaryDetPolynomial
        z CL BR (packetFrameTheta U V s q)) x,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    ring
  have hright :
      ((-1 : ℂ) ^ r * eval x Z) =
        ∑ S : Finset (ThreeBlockVariable (Fin W)),
          (((-1 : ℂ) ^ r * coeff (squarefreeExponent S) Z) *
            ∏ i : S, x i) := by
    have hZ : HasSquarefreeSupport Z :=
      hasSquarefreeSupport_classical_to_infer (by
        simpa only [Z] using
          (hasSquarefreeSupport_packetScalarMatrixCoefficientPolynomial
            r z CL BR U V s))
    rw [eval_eq_sum_squarefree_coeff Z
      hZ x,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    ring
  rw [hleft, hright]
  exact hsum

/-- The concrete scalar matrix-coefficient polynomial used in Proposition
10.10 is affine separately in every physical packet row.  The proof passes the
already checked determinant-row identity through the literal frame limit;
no affinity certificate is requested from the caller. -/
theorem packetScalarMatrixCoefficientPolynomial_isAffineInPhysicalRow
    (W r : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r)
    (i : ThreeBlockIndex (Fin W)) :
    IsAffineInPacketPhysicalRow i
      (packetScalarMatrixCoefficientPolynomial r z CL BR U V s) := by
  intro x u v t
  let xi := replacePacketPhysicalRow x i
    (interpolatePacketPhysicalRow t u v)
  let xu := replacePacketPhysicalRow x i u
  let xv := replacePacketPhysicalRow x i v
  let Z := packetScalarMatrixCoefficientPolynomial r z CL BR U V s
  have hinterp := tendsto_packetBoundaryPolynomial_frame_eval
    W r z CL BR U V s xi
  have hu := tendsto_packetBoundaryPolynomial_frame_eval
    W r z CL BR U V s xu
  have hv := tendsto_packetBoundaryPolynomial_frame_eval
    W r z CL BR U V s xv
  have hright := (hu.const_mul (1 - t)).add (hv.const_mul t)
  have hscaled (q : ℕ) :
      packetFrameComplexNormalization r q *
          eval xi (packetBoundaryPolynomial z CL BR
            (packetFrameTheta U V s q)) =
        (1 - t) *
            (packetFrameComplexNormalization r q *
              eval xu (packetBoundaryPolynomial z CL BR
                (packetFrameTheta U V s q))) +
          t *
            (packetFrameComplexNormalization r q *
              eval xv (packetBoundaryPolynomial z CL BR
                (packetFrameTheta U V s q))) := by
    have hrow := packetBoundaryPolynomial_isAffineInPhysicalRow
      z CL BR (packetFrameTheta U V s q) i x u v t
    simp only [xi, xu, xv]
    rw [hrow]
    ring
  have hleftAsRight : Tendsto
      (fun q =>
        (1 - t) *
            (packetFrameComplexNormalization r q *
              eval xu (packetBoundaryPolynomial z CL BR
                (packetFrameTheta U V s q))) +
          t *
            (packetFrameComplexNormalization r q *
              eval xv (packetBoundaryPolynomial z CL BR
                (packetFrameTheta U V s q))))
      atTop (nhds ((-1 : ℂ) ^ r * eval xi Z)) :=
    hinterp.congr' (Filter.Eventually.of_forall hscaled)
  have hlimit :
      ((-1 : ℂ) ^ r * eval xi Z) =
        (1 - t) * ((-1 : ℂ) ^ r * eval xu Z) +
          t * ((-1 : ℂ) ^ r * eval xv Z) :=
    tendsto_nhds_unique hleftAsRight hright
  have hsign : (-1 : ℂ) ^ r ≠ 0 := pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ hsign
  change (-1 : ℂ) ^ r * eval xi Z =
    (-1 : ℂ) ^ r * ((1 - t) * eval xu Z + t * eval xv Z)
  calc
    (-1 : ℂ) ^ r * eval xi Z =
        (1 - t) * ((-1 : ℂ) ^ r * eval xu Z) +
          t * ((-1 : ℂ) ^ r * eval xv Z) := hlimit
    _ = _ := by ring

/-! ## Corollary 10.3 for the scalar frame coefficient -/

/-- Evaluation of the literal scalar wedge coefficient on the normalized
flat packet atom rows. -/
def packetScalarCoefficientEval
    (W r : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r)
    (x : PacketAtomRows W) : ℂ :=
  eval (packetAtomAssignment W x)
    (packetScalarMatrixCoefficientPolynomial r z CL BR U V s)

theorem packetScalarCoefficientEval_update_line
    (W r : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r)
    (x : PacketAtomRows W) (i : Fin (PacketAtomRowCount W))
    (u v : Fin (PacketAtomRowCount W) → ℝ) (t : ℝ) :
    packetScalarCoefficientEval W r z CL BR U V s
        (Function.update x i ((1 - t) • u + t • v)) =
      (1 - t) • packetScalarCoefficientEval W r z CL BR U V s
          (Function.update x i u) +
        t • packetScalarCoefficientEval W r z CL BR U V s
          (Function.update x i v) := by
  let j := (packetIndexEquiv W).symm i
  have hP := packetScalarMatrixCoefficientPolynomial_isAffineInPhysicalRow
    W r z CL BR U V s j
  simp only [packetScalarCoefficientEval, packetAtomAssignment_update]
  rw [packetPhysicalRowValues_interpolate]
  have h := hP (packetAtomAssignment W x)
    (packetPhysicalRowValues W j u) (packetPhysicalRowValues W j v) (t : ℂ)
  simpa [j] using h

/-- Recursive row form required by `MultiAffineTensor`. -/
def packetScalarCoefficientEvalRecursive
    (W r : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) :
    MultiAffineRows
        (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W)) → ℂ :=
  fun y ↦ packetScalarCoefficientEval W r z CL BR U V s
    (multiAffineRowsToFinRows (PacketAtomRowCount W)
      (PacketAtomRowCount W) y)

theorem packetScalarCoefficientEval_recursive_isMultiAffine
    (W r : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) :
    IsMultiAffine
      (packetScalarCoefficientEvalRecursive W r z CL BR U V s) := by
  apply isMultiAffine_comp_multiAffineRowsToFinRows
  intro x i u v t
  exact packetScalarCoefficientEval_update_line
    W r z CL BR U V s x i u v t

theorem packetScalarCoefficientEvalRecursive_ne_zero
    (W : ℕ) (hW : 0 < W) (r : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) :
    packetScalarCoefficientEvalRecursive W r z CL BR U V s ≠ 0 := by
  have hP := packetScalarMatrixCoefficientPolynomial_ne_zero
    r z CL BR hCL hBR U V s
  obtain ⟨x, hx⟩ := exists_packetAtomRows_eval_ne_zero W hW hP
  intro hzero
  have hvalue := congrFun hzero
    (finRowsToMultiAffineRows (PacketAtomRowCount W)
      (PacketAtomRowCount W) x)
  apply hx
  simpa only [packetScalarCoefficientEvalRecursive,
    packetScalarCoefficientEval, multiAffineRowsToFinRows_leftInverse,
    Pi.zero_apply] using hvalue

/-- The actual normalized-atom coefficient tensor for the scalar wedge
coefficient. -/
def packetScalarCoefficientTensor
    (W r : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) :
    MultiAffineTensor ℂ
      (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W)) :=
  multiAffineTensorOfFunction
    (packetScalarCoefficientEvalRecursive W r z CL BR U V s)

/-- Concrete Corollary 10.3 input for Proposition 10.10.  It gives the packet
expectation relative to the normalized scalar coefficient tensor, together
with almost-sure nonvanishing. -/
theorem proposition_10_10_scalar_evaluation_recursive
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (r : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) :
    (∫⁻ y, ENNReal.ofReal
        |Real.log ‖packetScalarCoefficientEvalRecursive
            W r z CL BR U V s y‖ -
          Real.log ‖packetScalarCoefficientTensor W r z CL BR U V s‖|
        ∂multiAffineRowLaw μ
          (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W))) ≤
        multiAffineLogCost L
          (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W)) ∧
      ∀ᵐ y ∂multiAffineRowLaw μ
          (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W)),
        packetScalarCoefficientEvalRecursive W r z CL BR U V s y ≠ 0 := by
  have hpos : ∀ p ∈ List.replicate
      (PacketAtomRowCount W) (PacketAtomRowCount W), 0 < p := by
    intro p hp
    simp only [List.mem_replicate] at hp
    have hcard : PacketAtomRowCount W = 3 * W :=
      by simpa only [Fintype.card_fin] using
        (card_threeBlockIndex (W := Fin W))
    omega
  simpa only [packetScalarCoefficientTensor] using
    corollary_10_3 hμ
      (packetScalarCoefficientEval_recursive_isMultiAffine
        W r z CL BR U V s)
      hpos
      (packetScalarCoefficientEvalRecursive_ne_zero
        W hW r z CL BR hCL hBR U V s)

/-- Flat product-law form of the scalar coefficient evaluation estimate. -/
theorem proposition_10_10_scalar_evaluation
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (r : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) :
    (∫⁻ x, ENNReal.ofReal
        |Real.log ‖packetScalarCoefficientEval W r z CL BR U V s x‖ -
          Real.log ‖packetScalarCoefficientTensor W r z CL BR U V s‖|
        ∂packetAtomRowsLaw W μ) ≤
        multiAffineLogCost L
          (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W)) ∧
      ∀ᵐ x ∂packetAtomRowsLaw W μ,
        packetScalarCoefficientEval W r z CL BR U V s x ≠ 0 := by
  letI := hμ.toIsProbabilityMeasure
  let n := PacketAtomRowCount W
  let e := finRowsMultiAffineRowsMeasurableEquiv n n
  have hmp : MeasurePreserving e (packetAtomRowsLaw W μ)
      (multiAffineRowLaw μ (List.replicate n n)) := by
    simpa only [packetAtomRowsLaw, n] using
      finRowsMultiAffineRows_measurePreserving μ n n
  have hrec := proposition_10_10_scalar_evaluation_recursive
    hμ W hW r z CL BR hCL hBR U V s
  constructor
  · have heq := hmp.lintegral_comp_emb e.measurableEmbedding
      (fun y ↦ ENNReal.ofReal
        |Real.log ‖packetScalarCoefficientEvalRecursive
            W r z CL BR U V s y‖ -
          Real.log ‖packetScalarCoefficientTensor W r z CL BR U V s‖|)
    calc
      (∫⁻ x, ENNReal.ofReal
          |Real.log ‖packetScalarCoefficientEval W r z CL BR U V s x‖ -
            Real.log ‖packetScalarCoefficientTensor W r z CL BR U V s‖|
          ∂packetAtomRowsLaw W μ) =
          ∫⁻ y, ENNReal.ofReal
            |Real.log ‖packetScalarCoefficientEvalRecursive
                W r z CL BR U V s y‖ -
              Real.log ‖packetScalarCoefficientTensor W r z CL BR U V s‖|
            ∂multiAffineRowLaw μ (List.replicate n n) := by
        simpa only [packetScalarCoefficientEvalRecursive, e, n,
          finRowsMultiAffineRowsMeasurableEquiv_apply,
          multiAffineRowsToFinRows_leftInverse] using heq
      _ ≤ multiAffineLogCost L (List.replicate n n) := by
        simpa only [n] using hrec.1
  · have hrecMap : ∀ᵐ y ∂Measure.map e (packetAtomRowsLaw W μ),
        packetScalarCoefficientEvalRecursive W r z CL BR U V s y ≠ 0 := by
      rw [hmp.map_eq]
      simpa only [n] using hrec.2
    have hflat := e.measurableEmbedding.ae_map_iff.mp hrecMap
    simpa only [packetScalarCoefficientEvalRecursive, e, n,
      finRowsMultiAffineRowsMeasurableEquiv_apply,
      multiAffineRowsToFinRows_leftInverse] using hflat

/-- The 10.10 scalar evaluation theorem already implies the desired positive
inverse-log estimate up to the single deterministic term measuring the
normalized coefficient tensor.  This isolates exactly the remaining
endpoint/norm-comparison obligation. -/
theorem proposition_10_10_log_inv_le_tensor_loss
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (r : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) :
    (∫⁻ x, ENNReal.ofReal
        (Real.posLog ‖packetScalarCoefficientEval
          W r z CL BR U V s x‖⁻¹) ∂packetAtomRowsLaw W μ) ≤
      multiAffineLogCost L
          (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W)) +
        ENNReal.ofReal (Real.posLog
          ‖packetScalarCoefficientTensor W r z CL BR U V s‖⁻¹) := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (packetAtomRowsLaw W μ) := by
    unfold packetAtomRowsLaw
    infer_instance
  have heval := proposition_10_10_scalar_evaluation
    hμ W hW r z CL BR hCL hBR U V s
  let Γ : ℝ := ‖packetScalarCoefficientTensor W r z CL BR U V s‖
  have hpoint (x : PacketAtomRows W) :
      ENNReal.ofReal
          (Real.posLog ‖packetScalarCoefficientEval
            W r z CL BR U V s x‖⁻¹) ≤
        ENNReal.ofReal
            |Real.log ‖packetScalarCoefficientEval
                W r z CL BR U V s x‖ - Real.log Γ| +
          ENNReal.ofReal (Real.posLog Γ⁻¹) := by
    calc
      ENNReal.ofReal
          (Real.posLog ‖packetScalarCoefficientEval
            W r z CL BR U V s x‖⁻¹) ≤
          ENNReal.ofReal
            (|Real.log ‖packetScalarCoefficientEval
                W r z CL BR U V s x‖ - Real.log Γ| +
              Real.posLog Γ⁻¹) :=
        ENNReal.ofReal_le_ofReal
          (posLog_inv_le_abs_log_sub_log_add_posLog_inv
            ‖packetScalarCoefficientEval W r z CL BR U V s x‖ Γ)
      _ = _ := ENNReal.ofReal_add (abs_nonneg _)
        (Real.posLog_nonneg (x := Γ⁻¹))
  calc
    (∫⁻ x, ENNReal.ofReal
        (Real.posLog ‖packetScalarCoefficientEval
          W r z CL BR U V s x‖⁻¹) ∂packetAtomRowsLaw W μ) ≤
        ∫⁻ x, (ENNReal.ofReal
            |Real.log ‖packetScalarCoefficientEval
                W r z CL BR U V s x‖ - Real.log Γ| +
          ENNReal.ofReal (Real.posLog Γ⁻¹))
          ∂packetAtomRowsLaw W μ := lintegral_mono hpoint
    _ = (∫⁻ x, ENNReal.ofReal
            |Real.log ‖packetScalarCoefficientEval
                W r z CL BR U V s x‖ - Real.log Γ|
          ∂packetAtomRowsLaw W μ) +
        ENNReal.ofReal (Real.posLog Γ⁻¹) := by
      rw [lintegral_add_right _ measurable_const]
      simp
    _ ≤ multiAffineLogCost L
          (List.replicate (PacketAtomRowCount W) (PacketAtomRowCount W)) +
        ENNReal.ofReal (Real.posLog Γ⁻¹) := by
      have h := add_le_add_left heval.1
        (ENNReal.ofReal (Real.posLog Γ⁻¹))
      simpa only [Γ, add_comm] using h

end BernoulliSection10
