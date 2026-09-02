import BernoulliSection9.RandomQConditional
import BernoulliSection9.Section9DeductionFromTerminal

set_option maxHeartbeats 1000000

/-!
# Conditional arbitrary-frame small ball with a random outside frame

The deterministic arbitrary-frame theorem is uniform in its frame and
endpoint data.  This file performs the measure-theoretic last step when that
data is measurable with respect to an outside sigma-field and the complete
fresh iid packet is independent of that sigma-field.

There are two deliberately separate layers.

* `RandomFrame.conditionalResult_of_fiberwise` is the reusable conditional
  theorem.  Its parameter is represented by the *final finite coefficient
  vector*.  Joint measurability of the value is proved directly from the
  finite squarefree sum; no measurable choice of a unitary completion is
  used.
* `literalRandomFrameConditionalResult_of_packetConcrete` instantiates every
  deterministic fiber with
  `literalArbitraryFrameSmallBall_of_packetConcrete`.  Consequently no RRQR,
  CUR, mask, elimination, square-selection, or completion certificate occurs
  in this theorem signature.

For the literal wrapper, measurability of the final limiting coefficients is
proved from measurable endpoint matrices and measurable prescribed frame
columns.  The proof first eliminates the internal unitary completions by an
exact leading-minor identity.

The main package states Parseval fiberwise against the law of the fresh
vector, and hence requires no second-moment hypothesis on the random outside
parameter.  A final, separate theorem gives the Bochner conditional-
expectation form when the resulting random second moment is integrable.
-/

open scoped BigOperators ProbabilityTheory Matrix.Norms.L2Operator Topology
  ComplexConjugate

noncomputable section

namespace BernoulliSection9

open MeasureTheory ProbabilityTheory BernoulliLinearAlgebra Matrix Set
  Set.powersetCard

universe u v w

namespace RandomFrame

local instance randomFrameSumLinearOrder {W : Type*} [LinearOrder W] :
    LinearOrder (W ⊕ W) :=
  LinearOrder.lift'
    (fun x : W ⊕ W => (toLex x : W ⊕ₗ W))
    toLex.injective

/- Endpoint matrices carry their finite-dimensional Borel structure.  Frame
minor measurability below is proved directly from the determinant expansion,
so no conversion to an iterated Pi measurable space is needed. -/
local instance randomFrameMatrixMeasurableSpace {m n : Type*} :
    MeasurableSpace (Matrix m n Complex) := borel _

local instance randomFrameMatrixBorelSpace {m n : Type*} :
    BorelSpace (Matrix m n Complex) := ⟨rfl⟩

/-! ## Completion-free exterior contraction

The next lemmas isolate the algebraic fact which makes random frames
measurable.  Although `literalFrameCoefficient` was originally defined using
an internally chosen unitary completion, the selected rank-one exterior
operator uses only the prescribed leading columns. -/

private theorem continuous_compound_matrix
    {X κ ι : Type*} [TopologicalSpace X]
    [Fintype κ] [DecidableEq κ] [LinearOrder κ]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (k : Nat) {A : X -> Matrix κ ι Complex} (hA : Continuous A) :
    Continuous (fun x => compound k (A x)) := by
  apply continuous_matrix
  intro s t
  simpa only [compound_apply, minor] using
    (hA.matrix_submatrix (ofFinEmbEquiv.symm s)
      (ofFinEmbEquiv.symm t)).matrix_det

private theorem continuous_clearedInverseCompound_matrix
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (k : Nat) :
    Continuous (fun A : Matrix ι ι Complex => clearedInverseCompound k A) := by
  exact continuous_clearedInverseCompound_of_continuous k continuous_id

private theorem continuous_clearedStepCompound_matrix
    {X W : Type*} [TopologicalSpace X]
    [Fintype W] [LinearOrder W]
    (k : Nat) {B D C : X -> Matrix W W Complex}
    (hB : Continuous B) (hD : Continuous D) (hC : Continuous C) :
    Continuous (fun x => clearedStepCompound k (B x) (D x) (C x)) := by
  have hstepL : Continuous (fun x => stepL (B x)) := by
    unfold stepL
    exact hB.matrix_fromBlocks continuous_const continuous_const continuous_const
  have hstepK : Continuous (fun x => stepK (D x) (C x)) := by
    unfold stepK
    exact hD.matrix_fromBlocks hC continuous_const continuous_const
  have hleft : Continuous (fun x =>
      clearedInverseCompound k (stepL (B x))) :=
    (continuous_clearedInverseCompound_matrix k).comp hstepL
  have hright : Continuous (fun x => compound k (stepK (D x) (C x))) :=
    continuous_compound_matrix k hstepK
  unfold clearedStepCompound
  have hscalar : Continuous (fun _ : X => (-1 : Complex) ^ k) :=
    continuous_const
  apply continuous_matrix
  intro i j
  refine (hscalar.mul
    ((hleft.matrix_mul hright).matrix_elem i j)).congr ?_
  intro x
  simp only [Pi.mul_apply, Matrix.smul_apply, smul_eq_mul]

private theorem continuous_literalClearedProduct
    {W : Nat} (z : Complex) (k : Nat)
    (x : ThreeBlockVariable (Fin W) -> Complex) :
    Continuous (fun p :
      Matrix (Fin W) (Fin W) Complex × Matrix (Fin W) (Fin W) Complex =>
      polynomialClearedCompoundProduct k
        (literalBoundaryCompanionSteps z p.1 p.2 x)) := by
  have hleft := continuous_clearedStepCompound_matrix (W := Fin W) k
    (X := Matrix (Fin W) (Fin W) Complex ×
      Matrix (Fin W) (Fin W) Complex)
    (B := fun _ => threeBlockBL x)
    (D := fun _ => threeBlockAL x - z • 1)
    (C := fun p => p.1)
    continuous_const continuous_const continuous_fst
  have hcenter := continuous_clearedStepCompound_matrix (W := Fin W) k
    (X := Matrix (Fin W) (Fin W) Complex ×
      Matrix (Fin W) (Fin W) Complex)
    (B := fun _ => threeBlockBC x)
    (D := fun _ => threeBlockAC x - z • 1)
    (C := fun _ => threeBlockCC x)
    continuous_const continuous_const continuous_const
  have hright := continuous_clearedStepCompound_matrix (W := Fin W) k
    (X := Matrix (Fin W) (Fin W) Complex ×
      Matrix (Fin W) (Fin W) Complex)
    (B := fun p => p.2)
    (D := fun _ => threeBlockAR x - z • 1)
    (C := fun _ => threeBlockCR x)
    continuous_snd continuous_const continuous_const
  simpa [literalBoundaryCompanionSteps, boundaryCompanionSteps,
    polynomialClearedCompoundProduct] using
    (((continuous_const.matrix_mul hright).matrix_mul hcenter).matrix_mul hleft)

/-- Every entry of the inverse-free literal exterior tensor is continuous in
the two endpoint matrices. -/
theorem continuous_literalBoundaryFrameTensor_entry
    {W : Nat} (z : Complex) (k : Nat)
    (S : Finset (ThreeBlockVariable (Fin W)))
    (i j : powersetCard (Fin W ⊕ Fin W) k) :
    Continuous (fun p :
      Matrix (Fin W) (Fin W) Complex × Matrix (Fin W) (Fin W) Complex =>
      literalBoundaryFrameTensor W z p.1 p.2 k S i j) := by
  unfold literalBoundaryFrameTensor literalBoundaryExteriorTensor
    booleanCoefficient
  apply continuous_const.mul
  apply continuous_finsetSum
  intro T _
  exact continuous_const.mul
    ((continuous_literalClearedProduct z k (booleanCubePoint T)).matrix_elem i j)

/-- The frame index selected by the `j`th column of the reindexed leading
exterior coordinate. -/
def boundaryLeadingFrameIndex {W r : Nat} (h : r <= 2 * W)
    (j : Fin r) : Fin r :=
  ⟨(boundaryCoordinateEquiv W
      (ofFinEmbEquiv.symm (boundaryLeadingPowerset h) j)).val, by
    have hj : ofFinEmbEquiv.symm (boundaryLeadingPowerset h) j ∈
        (boundaryLeadingPowerset h).val := by
      simpa [ofFinEmbEquiv_symm_apply] using
        (Finset.orderEmbOfFin_mem (boundaryLeadingPowerset h).val
          (boundaryLeadingPowerset h).prop j)
    simpa [boundaryLeadingPowerset, powersetCard.map,
      leadingPowerset] using hj⟩

/-- Determinant of the prescribed frame columns on an exterior row
coordinate.  No completion is present in this definition. -/
def directBoundaryFrameMinor {W r : Nat}
    (U : ComplexFrame r (2 * W)) (h : r <= 2 * W)
    (s : powersetCard (Fin W ⊕ Fin W) r) : Complex :=
  Matrix.det (Matrix.of (fun i j : Fin r =>
    frameColumn U (boundaryLeadingFrameIndex h j)
      (boundaryCoordinateEquiv W (ofFinEmbEquiv.symm s i))))

/-- A leading minor of the internally completed frame is literally the
direct determinant of prescribed frame columns. -/
theorem compound_boundaryCompletedFrameMatrix_leading
    {W r : Nat} (U : ComplexFrame r (2 * W)) (h : r <= 2 * W)
    (s : powersetCard (Fin W ⊕ Fin W) r) :
    compound r (boundaryCompletedFrameMatrix U h) s
        (boundaryLeadingPowerset h) =
      directBoundaryFrameMinor U h s := by
  rw [compound_apply]
  unfold minor directBoundaryFrameMinor
  apply congrArg (fun M : Matrix (Fin r) (Fin r) Complex => M.det)
  ext i j
  simp only [Matrix.submatrix_apply, boundaryCompletedFrameMatrix,
    Matrix.reindex_apply, Equiv.symm_symm_apply, Matrix.of_apply]
  have hcolumn :
      boundaryCoordinateEquiv W
          (ofFinEmbEquiv.symm (boundaryLeadingPowerset h) j) =
        leadingEmbedding h (boundaryLeadingFrameIndex h j) := by
    apply Fin.ext
    rfl
  rw [hcolumn, completedFrameMatrix_leading]

/-- The completion-free rank-one exterior matrix
`|wedge V><wedge U|`. -/
def directBoundaryFrameExteriorRankOne {W r : Nat}
    (U V : ComplexFrame r (2 * W)) (h : r <= 2 * W) :
    Matrix (powersetCard (Fin W ⊕ Fin W) r)
      (powersetCard (Fin W ⊕ Fin W) r) Complex :=
  fun s t => directBoundaryFrameMinor V h s *
    star (directBoundaryFrameMinor U h t)

private theorem selectedArtificialExteriorRankOne_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {r : Nat} (L : powersetCard ι r) (A B : Matrix ι ι Complex)
    (s t : powersetCard ι r) :
    selectedArtificialExteriorRankOne L A B s t =
      compound r A s L * compound r B L t := by
  have hmul (x : powersetCard ι r) :
      (compound r A * selectedExteriorProjection L) s x =
        if x = L then compound r A s L else 0 := by
    by_cases hx : x = L
    · subst x
      simp [Matrix.mul_apply, selectedExteriorProjection]
    · simp [Matrix.mul_apply, selectedExteriorProjection, hx]
  rw [selectedArtificialExteriorRankOne, Matrix.mul_apply]
  simp_rw [hmul]
  simp

/-- The selected rank-one exterior matrix is independent of every column in
the internal unitary completions except the prescribed frame columns. -/
theorem selectedBoundaryFrameExteriorRankOne_eq_direct
    {W r : Nat} (U V : ComplexFrame r (2 * W)) (h : r <= 2 * W) :
    selectedArtificialExteriorRankOne
        (boundaryLeadingPowerset h)
        (boundaryCompletedFrameMatrix V h)
        ((boundaryCompletedFrameMatrix U h)ᴴ) =
      directBoundaryFrameExteriorRankOne U V h := by
  ext s t
  rw [selectedArtificialExteriorRankOne_apply,
    compound_boundaryCompletedFrameMatrix_leading]
  rw [compound_apply, minor_conjTranspose, ← compound_apply,
    compound_boundaryCompletedFrameMatrix_leading]
  rfl

/-- The actual limiting literal coefficient written as a finite contraction
of the inverse-free boundary tensor with prescribed frame-column minors. -/
def directLiteralFrameCoefficient {W r : Nat}
    (z : Complex) (CL BR : Matrix (Fin W) (Fin W) Complex)
    (U V : ComplexFrame r (2 * W)) (h : r <= 2 * W)
    (S : Finset (ThreeBlockVariable (Fin W))) : Complex :=
  (-1 : Complex) ^ r * Matrix.trace
    (literalBoundaryFrameTensor W z CL BR r S *
      directBoundaryFrameExteriorRankOne U V h)

/-- The completion-based definition used by the deterministic development is
equal to the direct exterior contraction. -/
theorem literalFrameCoefficient_eq_direct {W r : Nat}
    (z : Complex) (CL BR : Matrix (Fin W) (Fin W) Complex)
    (U V : ComplexFrame r (2 * W)) (h : r <= 2 * W)
    (S : Finset (ThreeBlockVariable (Fin W))) :
    literalFrameCoefficient z CL BR U V h S =
      directLiteralFrameCoefficient z CL BR U V h S := by
  unfold literalFrameCoefficient selectedLimitingFrameCoefficient
    directLiteralFrameCoefficient
  rw [selectedBoundaryFrameExteriorRankOne_eq_direct]

/-- Coordinate-generated measurability of a random complex frame. -/
def FrameCoordinateMeasurable
    {Param : Type*} [MeasurableSpace Param] {r n : Nat}
    (U : Param -> ComplexFrame r n) : Prop :=
  forall j i, Measurable (fun p => frameColumn (U p) j i)

theorem measurable_directBoundaryFrameMinor
    {Param : Type*} [MeasurableSpace Param] {W r : Nat}
    (U : Param -> ComplexFrame r (2 * W)) (h : r <= 2 * W)
    (hU : FrameCoordinateMeasurable U)
    (s : powersetCard (Fin W ⊕ Fin W) r) :
    Measurable (fun p => directBoundaryFrameMinor (U p) h s) := by
  let F : Param -> (Fin r -> Fin r -> Complex) := fun p i j =>
    frameColumn (U p) (boundaryLeadingFrameIndex h j)
      (boundaryCoordinateEquiv W (ofFinEmbEquiv.symm s i))
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact hU (boundaryLeadingFrameIndex h j)
      (boundaryCoordinateEquiv W (ofFinEmbEquiv.symm s i))
  have hdet : Measurable (fun f : Fin r -> Fin r -> Complex =>
      Matrix.det (Matrix.of f)) := by
    have hc : Continuous (fun f : Fin r -> Fin r -> Complex =>
        Matrix.det (Matrix.of f)) := by
      change Continuous (fun M : Matrix (Fin r) (Fin r) Complex => M.det)
      exact continuous_id.matrix_det
    exact hc.measurable
  change Measurable ((fun f : Fin r -> Fin r -> Complex =>
    Matrix.det (Matrix.of f)) ∘ F)
  exact hdet.comp hF

private theorem measurable_literalBoundaryFrameTensor_entry_endpoints
    {W r : Nat} (z : Complex)
    (S : Finset (ThreeBlockVariable (Fin W)))
    (i j : powersetCard (Fin W ⊕ Fin W) r) :
    Measurable (fun p :
      Matrix (Fin W) (Fin W) Complex × Matrix (Fin W) (Fin W) Complex =>
      literalBoundaryFrameTensor W z p.1 p.2 r S i j) := by
  exact (continuous_literalBoundaryFrameTensor_entry z r S i j).measurable

private theorem measurable_literalBoundaryFrameTensor_entry_comp
    {Param : Type*} [MeasurableSpace Param] {W r : Nat}
    (z : Complex)
    (CL BR : Param -> Matrix (Fin W) (Fin W) Complex)
    (hCL : Measurable CL) (hBR : Measurable BR)
    (S : Finset (ThreeBlockVariable (Fin W)))
    (i j : powersetCard (Fin W ⊕ Fin W) r) :
    Measurable (fun p =>
      literalBoundaryFrameTensor W z (CL p) (BR p) r S i j) := by
  change Measurable
    ((fun q : Matrix (Fin W) (Fin W) Complex ×
        Matrix (Fin W) (Fin W) Complex =>
      literalBoundaryFrameTensor W z q.1 q.2 r S i j) ∘
        (fun p => (CL p, BR p)))
  exact (measurable_literalBoundaryFrameTensor_entry_endpoints z S i j).comp
    (hCL.prodMk hBR)

private theorem measurable_directBoundaryFrameExteriorRankOne_entry
    {Param : Type*} [MeasurableSpace Param] {W r : Nat}
    (U V : Param -> ComplexFrame r (2 * W)) (h : r <= 2 * W)
    (hU : FrameCoordinateMeasurable U)
    (hV : FrameCoordinateMeasurable V)
    (i j : powersetCard (Fin W ⊕ Fin W) r) :
    Measurable (fun p =>
      directBoundaryFrameExteriorRankOne (U p) (V p) h j i) := by
  exact (measurable_directBoundaryFrameMinor V h hV j).mul
    (continuous_star.measurable.comp
      (measurable_directBoundaryFrameMinor U h hU i))

private theorem measurable_directLiteralFrameSummand
    {Param : Type*} [MeasurableSpace Param] {W r : Nat}
    (z : Complex)
    (CL BR : Param -> Matrix (Fin W) (Fin W) Complex)
    (hCL : Measurable CL) (hBR : Measurable BR)
    (U V : Param -> ComplexFrame r (2 * W)) (h : r <= 2 * W)
    (hU : FrameCoordinateMeasurable U)
    (hV : FrameCoordinateMeasurable V)
    (S : Finset (ThreeBlockVariable (Fin W)))
    (i j : powersetCard (Fin W ⊕ Fin W) r) :
    Measurable (fun p =>
      literalBoundaryFrameTensor W z (CL p) (BR p) r S i j *
        directBoundaryFrameExteriorRankOne (U p) (V p) h j i) := by
  exact (measurable_literalBoundaryFrameTensor_entry_comp
      z CL BR hCL hBR S i j).mul
    (measurable_directBoundaryFrameExteriorRankOne_entry
      U V h hU hV i j)

private theorem measurable_directLiteralFrameRow
    {Param : Type*} [MeasurableSpace Param] {W r : Nat}
    (z : Complex)
    (CL BR : Param -> Matrix (Fin W) (Fin W) Complex)
    (hCL : Measurable CL) (hBR : Measurable BR)
    (U V : Param -> ComplexFrame r (2 * W)) (h : r <= 2 * W)
    (hU : FrameCoordinateMeasurable U)
    (hV : FrameCoordinateMeasurable V)
    (S : Finset (ThreeBlockVariable (Fin W)))
    (i : powersetCard (Fin W ⊕ Fin W) r) :
    Measurable (fun p => ∑ j,
      literalBoundaryFrameTensor W z (CL p) (BR p) r S i j *
        directBoundaryFrameExteriorRankOne (U p) (V p) h j i) := by
  apply Finset.measurable_fun_sum
  intro j _
  exact measurable_directLiteralFrameSummand
    z CL BR hCL hBR U V h hU hV S i j

theorem measurable_directLiteralFrameCoefficient
    {Param : Type*} [MeasurableSpace Param] {W r : Nat}
    (z : Complex)
    (CL BR : Param -> Matrix (Fin W) (Fin W) Complex)
    (hCL : Measurable CL) (hBR : Measurable BR)
    (U V : Param -> ComplexFrame r (2 * W)) (h : r <= 2 * W)
    (hU : FrameCoordinateMeasurable U)
    (hV : FrameCoordinateMeasurable V)
    (S : Finset (ThreeBlockVariable (Fin W))) :
    Measurable (fun p => directLiteralFrameCoefficient z (CL p) (BR p)
      (U p) (V p) h S) := by
  unfold directLiteralFrameCoefficient Matrix.trace
  apply measurable_const.mul
  apply Finset.measurable_fun_sum
  intro i _
  change Measurable (fun p => ∑ j,
    literalBoundaryFrameTensor W z (CL p) (BR p) r S i j *
      directBoundaryFrameExteriorRankOne (U p) (V p) h j i)
  exact measurable_directLiteralFrameRow
    z CL BR hCL hBR U V h hU hV S i

/-- Coordinatewise measurable endpoint matrices and prescribed frame columns
make every final literal coefficient measurable. -/
theorem measurable_literalFrameCoefficient
    {Param : Type*} [MeasurableSpace Param] {W r : Nat}
    (z : Complex)
    (CL BR : Param -> Matrix (Fin W) (Fin W) Complex)
    (hCL : Measurable CL) (hBR : Measurable BR)
    (U V : Param -> ComplexFrame r (2 * W)) (h : r <= 2 * W)
    (hU : FrameCoordinateMeasurable U)
    (hV : FrameCoordinateMeasurable V)
    (S : Finset (ThreeBlockVariable (Fin W))) :
    Measurable (fun p => literalFrameCoefficient z (CL p) (BR p)
      (U p) (V p) h S) := by
  have hdirect := measurable_directLiteralFrameCoefficient
    z CL BR hCL hBR U V h hU hV S
  rw [show (fun p => literalFrameCoefficient z (CL p) (BR p)
      (U p) (V p) h S) =
      (fun p => directLiteralFrameCoefficient z (CL p) (BR p)
        (U p) (V p) h S) by
    funext p
    exact literalFrameCoefficient_eq_direct
      z (CL p) (BR p) (U p) (V p) h S]
  exact hdirect

/-! ## Direct finite squarefree evaluator -/

/-- The complete iid vector, regarded as one finite-dimensional fresh random
variable. -/
def freshSample
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {mu : Measure Omega} (X : IidSubgaussianFamily Omega mu ι) :
    Omega -> (ι -> Real) :=
  fun omega i => X.atom i omega

theorem measurable_freshSample
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {mu : Measure Omega} (X : IidSubgaussianFamily Omega mu ι) :
    Measurable (freshSample X) := by
  exact measurable_pi_lambda _ fun i => X.measurable_atom i

/-- Euclidean norm of a parameterized finite squarefree coefficient vector. -/
def coefficientNorm
    {Param ι : Type*} [Fintype ι]
    (coefficient : Param -> Finset ι -> Complex) (p : Param) : Real :=
  ‖(WithLp.toLp 2 (coefficient p) :
    EuclideanSpace Complex (Finset ι))‖

/-- Evaluate the final finite squarefree polynomial at a deterministic fresh
sample.  This definition mentions only the final coefficient vector and a
finite sum. -/
def valueFromSample
    {Param ι : Type*} [Fintype ι]
    (coefficient : Param -> Finset ι -> Complex)
    (p : Param × (ι -> Real)) : Complex :=
  evalSquarefree (coefficient p.1) (fun i x => x i) p.2

def cappedLoss
    {Param ι : Type*} [Fintype ι]
    (T : Real) (coefficient : Param -> Finset ι -> Complex)
    (p : Param × (ι -> Real)) : Real :=
  cappedLogLoss T (coefficientNorm coefficient p.1)
    (valueFromSample coefficient p)

def zeroIndicator
    {Param ι : Type*} [Fintype ι]
    (coefficient : Param -> Finset ι -> Complex)
    (p : Param × (ι -> Real)) : Real :=
  if valueFromSample coefficient p = 0 then 1 else 0

def secondMoment
    {Param ι : Type*} [Fintype ι]
    (coefficient : Param -> Finset ι -> Complex)
    (p : Param × (ι -> Real)) : Real :=
  ‖valueFromSample coefficient p‖ ^ 2

theorem measurable_coefficientNorm
    {Param ι : Type*} [MeasurableSpace Param] [Fintype ι]
    (coefficient : Param -> Finset ι -> Complex)
    (hcoefficient : forall S, Measurable (fun p => coefficient p S)) :
    Measurable (coefficientNorm coefficient) := by
  rw [show coefficientNorm coefficient = fun p =>
      Real.sqrt (∑ S, ‖coefficient p S‖ ^ 2) by
    funext p
    exact EuclideanSpace.norm_eq _]
  apply Real.continuous_sqrt.measurable.comp
  apply Finset.measurable_fun_sum
  intro S _
  exact (hcoefficient S).norm.pow_const 2

/-- Joint measurability is proved directly from the displayed finite
squarefree sum.  In particular, this proof never unfolds a frame completion. -/
theorem measurable_valueFromSample
    {Param ι : Type*} [MeasurableSpace Param] [Fintype ι]
    (coefficient : Param -> Finset ι -> Complex)
    (hcoefficient : forall S, Measurable (fun p => coefficient p S)) :
    Measurable (valueFromSample coefficient) := by
  unfold valueFromSample evalSquarefree
  apply Finset.measurable_fun_sum
  intro S _
  have hmonomial : Measurable (fun x : ι -> Real =>
      squarefreeMonomial (fun i y => y i) S x) :=
    TerminalAssembly.measurable_squarefreeMonomial
      (fun i (x : ι -> Real) => x i) (fun i => measurable_pi_apply i) S
  exact ((hcoefficient S).comp measurable_fst).mul
    ((hmonomial.complex_ofReal).comp measurable_snd)

theorem measurable_cappedLoss
    {Param ι : Type*} [MeasurableSpace Param] [Fintype ι]
    (T : Real) (coefficient : Param -> Finset ι -> Complex)
    (hcoefficient : forall S, Measurable (fun p => coefficient p S)) :
    Measurable (cappedLoss T coefficient) := by
  unfold cappedLoss cappedLogLoss
  have hvalue := measurable_valueFromSample coefficient hcoefficient
  have hnorm : Measurable (fun p : Param × (ι -> Real) =>
      coefficientNorm coefficient p.1) :=
    (measurable_coefficientNorm coefficient hcoefficient).comp measurable_fst
  apply Measurable.ite
  · exact hvalue (measurableSet_singleton 0)
  · exact measurable_const
  · exact Measurable.min measurable_const
      (Real.continuous_posLog.measurable.comp (hnorm.div hvalue.norm))

theorem measurable_zeroIndicator
    {Param ι : Type*} [MeasurableSpace Param] [Fintype ι]
    (coefficient : Param -> Finset ι -> Complex)
    (hcoefficient : forall S, Measurable (fun p => coefficient p S)) :
    Measurable (zeroIndicator coefficient) := by
  unfold zeroIndicator
  apply Measurable.ite
  · exact (measurable_valueFromSample coefficient hcoefficient)
      (measurableSet_singleton 0)
  · exact measurable_const
  · exact measurable_const

theorem measurable_secondMoment
    {Param ι : Type*} [MeasurableSpace Param] [Fintype ι]
    (coefficient : Param -> Finset ι -> Complex)
    (hcoefficient : forall S, Measurable (fun p => coefficient p S)) :
    Measurable (secondMoment coefficient) := by
  exact (measurable_valueFromSample coefficient hcoefficient).norm.pow_const 2

@[simp] theorem valueFromSample_freshSample
    {Omega Param ι : Type*} [MeasurableSpace Omega]
    [Fintype ι]
    {mu : Measure Omega} (X : IidSubgaussianFamily Omega mu ι)
    (coefficient : Param -> Finset ι -> Complex) (p : Param)
    (omega : Omega) :
    valueFromSample coefficient (p, freshSample X omega) =
      evalSquarefree (coefficient p) X.atom omega := by
  rfl

/-! ## Conditional conclusion -/

/-- Conditional arbitrary-frame output.  Conditional probabilities are
represented by conditional expectations of their `0/1` indicators. -/
structure ConditionalResult
    {Omega Param ι : Type*} [mOmega : MeasurableSpace Omega]
    [MeasurableSpace Param]
    [Fintype ι]
    (outside : TerminalAssembly.OutsideSigmaField Omega) (mu : Measure Omega)
    (X : IidSubgaussianFamily Omega mu ι) (parameter : Omega -> Param)
    (coefficient : Param -> Finset ι -> Complex)
    (baseLoss badProbability : Real) where
  coefficientNorm_pos : forall omega,
    0 < coefficientNorm coefficient (parameter omega)
  coefficientNorm_stronglyMeasurable : StronglyMeasurable
    (fun omega => coefficientNorm coefficient (parameter omega))
  value_stronglyMeasurable : StronglyMeasurable
    (fun omega => valueFromSample coefficient
      (parameter omega, freshSample X omega))
  capped : forall T : Real, 0 < T ->
    ∀ᵐ omega ∂mu,
      mu[fun eta => cappedLogLoss T
          (coefficientNorm coefficient (parameter eta))
          (valueFromSample coefficient
            (parameter eta, freshSample X eta)) | outside.space] omega <=
        baseLoss + badProbability * T
  zero_probability : ∀ᵐ omega ∂mu,
    mu[fun eta => if valueFromSample coefficient
          (parameter eta, freshSample X eta) = 0
        then (1 : Real) else 0 | outside.space] omega <= badProbability
  parseval_fiber : forall omega,
    coefficientNorm coefficient (parameter omega) ^ 2 =
      ∫ x,
        ‖valueFromSample coefficient (parameter omega, x)‖ ^ 2
        ∂(@Measure.map Omega (ι -> Real) mOmega inferInstance
          (freshSample X) mu)

/-- Lift a deterministic arbitrary-frame conclusion in every parameter fiber
to an almost-sure conditional conclusion for an outside-measurable random
parameter independent of the full fresh iid vector.

The deterministic input is precisely `ArbitraryFrameDeductionConclusion`.
Its artificial sequence and coefficient limits stay inside each fiber and
do not become new caller-facing certificates. -/
noncomputable def conditionalResult_of_fiberwise
    {Omega : Type u} {Param : Type v} {ι : Type w}
    [mOmega : MeasurableSpace Omega] [MeasurableSpace Param] [Fintype ι]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : IidSubgaussianFamily Omega mu ι)
    (mOutside : MeasurableSpace Omega) (hmOutside : mOutside <= mOmega)
    (parameter : Omega -> Param)
    (hparameter : @Measurable Omega Param mOutside inferInstance parameter)
    (h_indep : @Indep Omega mOutside
      (MeasurableSpace.comap
        (@freshSample Omega ι mOmega inferInstance mu X) inferInstance)
      mOmega mu)
    (coefficient : Param -> Finset ι -> Complex)
    (hcoefficient : forall S, Measurable (fun p => coefficient p S))
    (artificialCoefficientNorm : Param -> Nat -> Real)
    (artificialValue : Param -> Nat -> Omega -> Complex)
    (lower upper : Param -> Real) (baseLoss badProbability : Real)
    (fiber : forall p,
      @ArbitraryFrameDeductionConclusion Omega mOmega mu
        (artificialCoefficientNorm p) (coefficientNorm coefficient p)
        (artificialValue p)
        (fun omega => valueFromSample coefficient
          (p, @freshSample Omega ι mOmega inferInstance mu X omega))
        (lower p) (upper p) baseLoss badProbability) :
    @ConditionalResult Omega Param ι mOmega inferInstance inferInstance
      ⟨mOutside⟩ mu X parameter coefficient
      baseLoss badProbability := by
  classical
  letI : MeasurableSpace Omega := mOmega
  let fresh := freshSample X
  have hfresh : Measurable fresh := measurable_freshSample X
  have hparameterAmbient : Measurable parameter :=
    hparameter.mono hmOutside le_rfl
  have hpair : Measurable (fun omega => (parameter omega, fresh omega)) :=
    hparameterAmbient.prodMk hfresh
  have hnormStrong : StronglyMeasurable
      (fun omega => coefficientNorm coefficient (parameter omega)) :=
    ((measurable_coefficientNorm coefficient hcoefficient).comp
      hparameterAmbient).stronglyMeasurable
  have hvalueStrong : StronglyMeasurable
      (fun omega => valueFromSample coefficient
        (parameter omega, fresh omega)) :=
    ((measurable_valueFromSample coefficient hcoefficient).comp
      hpair).stronglyMeasurable
  refine
    { coefficientNorm_pos := fun omega =>
        (fiber (parameter omega)).coefficientNorm_pos
      coefficientNorm_stronglyMeasurable := hnormStrong
      value_stronglyMeasurable := hvalueStrong
      capped := ?_
      zero_probability := ?_
      parseval_fiber := ?_ }
  · intro T hT
    let loss := cappedLoss T coefficient
    have hloss : StronglyMeasurable loss :=
      (measurable_cappedLoss T coefficient hcoefficient).stronglyMeasurable
    have hlossRandom : Integrable
        (fun omega => loss (parameter omega, fresh omega)) mu := by
      apply (integrable_const T).mono'
      · exact (hloss.comp_measurable hpair).aestronglyMeasurable
      · filter_upwards [] with omega
        dsimp [loss, cappedLoss]
        rw [abs_of_nonneg (cappedLogLoss_nonneg hT.le)]
        exact cappedLogLoss_le_cap
    have heq := condExp_parameterized_ae_eq_integral_map_of_indepSigma
      mu mOutside hmOutside parameter fresh hparameter hfresh.aemeasurable
      h_indep loss hloss hlossRandom
    filter_upwards [heq] with omega homega
    change mu[fun eta => loss (parameter eta, fresh eta) |
      mOutside] omega <= _
    rw [homega]
    rw [integral_map hfresh.aemeasurable]
    · simpa [loss, cappedLoss, fresh] using
        (fiber (parameter omega)).capped T hT
    · exact (hloss.comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · let indicator := zeroIndicator coefficient
    have hindicator : StronglyMeasurable indicator :=
      (measurable_zeroIndicator coefficient hcoefficient).stronglyMeasurable
    have hindicatorRandom : Integrable
        (fun omega => indicator (parameter omega, fresh omega)) mu := by
      apply (integrable_const (1 : Real)).mono'
      · exact (hindicator.comp_measurable hpair).aestronglyMeasurable
      · filter_upwards [] with omega
        dsimp [indicator, zeroIndicator]
        split <;> norm_num
    have heq := condExp_parameterized_ae_eq_integral_map_of_indepSigma
      mu mOutside hmOutside parameter fresh hparameter hfresh.aemeasurable
      h_indep indicator hindicator hindicatorRandom
    filter_upwards [heq] with omega homega
    change mu[fun eta => indicator (parameter eta, fresh eta) |
      mOutside] omega <= _
    rw [homega]
    rw [integral_map hfresh.aemeasurable]
    · let zeroSet : Set Omega :=
        {eta | valueFromSample coefficient
          (parameter omega, fresh eta) = 0}
      have hzeroSet : MeasurableSet zeroSet := by
        exact ((measurable_valueFromSample coefficient hcoefficient).comp
          (measurable_const.prodMk hfresh)) (measurableSet_singleton 0)
      have hintegral :
          (∫ eta, indicator (parameter omega, fresh eta) ∂mu) =
            mu.real zeroSet := by
        have hfun : (fun eta => indicator (parameter omega, fresh eta)) =
            zeroSet.indicator (fun _ => (1 : Real)) := by
          funext eta
          by_cases heta : valueFromSample coefficient
              (parameter omega, fresh eta) = 0
          · simp [indicator, zeroIndicator, zeroSet, heta]
          · simp [indicator, zeroIndicator, zeroSet, heta]
        rw [hfun]
        simpa using (integral_indicator_const
          (μ := mu) (1 : Real) hzeroSet)
      rw [hintegral]
      exact (fiber (parameter omega)).zero_probability
    · exact (hindicator.comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · intro omega
    rw [integral_map hfresh.aemeasurable]
    · simpa only [coefficientNorm, fresh,
        valueFromSample_freshSample] using
        (integral_norm_evalSquarefree_sq_eq_coeffNorm X
          (WithLp.toLp 2 (coefficient (parameter omega)))).symm
    · exact ((measurable_secondMoment coefficient hcoefficient).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable

/-! ## Literal arbitrary-frame instantiation -/

/-- Instantiate the conditional lift with the certificate-free literal
arbitrary-frame theorem.  All endpoint and frame objects are deterministic
functions of the outside parameter; every fixed parameter is discharged by
`literalArbitraryFrameSmallBall_of_packetConcrete` internally.

No measurability or continuity of an internally selected unitary completion
is assumed. -/
noncomputable def literalRandomFrameConditionalResult_of_packetConcrete
    {Omega : Type u} {Param : Type v}
    [mOmega : MeasurableSpace Omega] [MeasurableSpace Param]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {W Kz r : Nat}
    (cook : CookDeformedSquareInput) (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W)))
    (t : Real)
    (C : TerminalAssembly.PacketTerminalConcreteConclusion
      cook mu W Kz z X t)
    (mOutside : MeasurableSpace Omega) (hmOutside : mOutside <= mOmega)
    (parameter : Omega -> Param)
    (hparameter : @Measurable Omega Param mOutside inferInstance parameter)
    (h_indep : @Indep Omega mOutside
      (MeasurableSpace.comap
        (@freshSample Omega (ThreeBlockVariable (Fin W)) mOmega
          inferInstance mu X) inferInstance) mOmega mu)
    (CL BR : Param -> Matrix (Fin W) (Fin W) Complex)
    (B delta : Param -> Real)
    (endpoint : forall p, PaperEndpointGood (CL p) (BR p) (B p) (delta p))
    (U V : Param -> ComplexFrame r (2 * W)) (h : r <= 2 * W)
    (hCL : Measurable CL) (hBR : Measurable BR)
    (hU : FrameCoordinateMeasurable U)
    (hV : FrameCoordinateMeasurable V) :
    @ConditionalResult Omega Param (ThreeBlockVariable (Fin W))
      mOmega inferInstance inferInstance ⟨mOutside⟩ mu X parameter
      (fun p => literalFrameCoefficient z (CL p) (BR p)
        (U p) (V p) h)
      (@TerminalAssembly.terminalUniformBaseLoss Omega mOmega mu W
        cook Kz z X t)
      (TerminalAssembly.terminalUniformBadProbability cook W Kz t) := by
  letI : MeasurableSpace Omega := mOmega
  let coefficient := fun p =>
    literalFrameCoefficient z (CL p) (BR p) (U p) (V p) h
  have hcoefficient : forall S, Measurable (fun p => coefficient p S) :=
    fun S => measurable_literalFrameCoefficient
      z CL BR hCL hBR U V h hU hV S
  apply conditionalResult_of_fiberwise mu X mOutside hmOutside parameter
    hparameter h_indep coefficient hcoefficient
    (fun p => literalArtificialCoefficientNorm z (CL p) (BR p)
      (U p) (V p) h)
    (fun p => literalArtificialRandomValue z (CL p) (BR p)
      (U p) (V p) h X)
    (fun p =>
      (literalBoundaryHodgeComparisonConstant W z (B p)
        ((delta p)⁻¹ ^ 2))⁻¹)
    (fun p => literalBoundaryHodgeComparisonConstant W z (B p)
      ((delta p)⁻¹ ^ 2))
    (TerminalAssembly.terminalUniformBaseLoss cook Kz z X t)
    (TerminalAssembly.terminalUniformBadProbability cook W Kz t)
  intro p
  have hvalue :
      (fun omega => valueFromSample coefficient
        (p, freshSample X omega)) =
        literalFrameRandomValue z (CL p) (BR p)
          (U p) (V p) h X := by
    funext omega
    simpa [coefficient] using
      (literalFrameRandomValue_eq_evalSquarefree
        z (CL p) (BR p) (U p) (V p) h X omega).symm
  change ArbitraryFrameDeductionConclusion mu
    (literalArtificialCoefficientNorm z (CL p) (BR p)
      (U p) (V p) h)
    (literalFrameCoefficientNorm z (CL p) (BR p) (U p) (V p) h)
    (literalArtificialRandomValue z (CL p) (BR p) (U p) (V p) h X)
    (fun omega => valueFromSample coefficient (p, freshSample X omega))
    ((literalBoundaryHodgeComparisonConstant W z (B p)
      ((delta p)⁻¹ ^ 2))⁻¹)
    (literalBoundaryHodgeComparisonConstant W z (B p)
      ((delta p)⁻¹ ^ 2))
    (TerminalAssembly.terminalUniformBaseLoss cook Kz z X t)
    (TerminalAssembly.terminalUniformBadProbability cook W Kz t)
  rw [hvalue]
  exact literalArbitraryFrameSmallBall_of_packetConcrete
    cook z X t C (CL p) (BR p) (B p) (delta p) (endpoint p)
      (U p) (V p) h

/-! ## Optional conditional Parseval -/

/-- With an explicit integrability hypothesis, fiberwise Parseval becomes a
Bochner conditional-expectation identity.  Keeping this separate prevents a
global random-frame second moment from entering the small-ball package. -/
theorem condExp_parseval
    {Omega : Type u} {Param : Type v} {ι : Type w}
    [mOmega : MeasurableSpace Omega] [MeasurableSpace Param]
    [Fintype ι] [DecidableEq ι]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : IidSubgaussianFamily Omega mu ι)
    (mOutside : MeasurableSpace Omega) (hmOutside : mOutside <= mOmega)
    (parameter : Omega -> Param)
    (hparameter : @Measurable Omega Param mOutside inferInstance parameter)
    (h_indep : @Indep Omega mOutside
      (MeasurableSpace.comap
        (@freshSample Omega ι mOmega inferInstance mu X) inferInstance)
      mOmega mu)
    (coefficient : Param -> Finset ι -> Complex)
    (hcoefficient : forall S, Measurable (fun p => coefficient p S))
    (hsecondMoment : Integrable (fun omega =>
      ‖valueFromSample coefficient
        (parameter omega,
          @freshSample Omega ι mOmega inferInstance mu X omega)‖ ^ 2) mu) :
    mu[fun eta => ‖valueFromSample coefficient
          (parameter eta,
            @freshSample Omega ι mOmega inferInstance mu X eta)‖ ^ 2 |
        mOutside] =ᵐ[mu]
      fun omega => coefficientNorm coefficient (parameter omega) ^ 2 := by
  letI : MeasurableSpace Omega := mOmega
  let fresh := freshSample X
  let second := secondMoment coefficient
  have hfresh : Measurable fresh := measurable_freshSample X
  have hsecond : StronglyMeasurable second :=
    (measurable_secondMoment coefficient hcoefficient).stronglyMeasurable
  have heq := condExp_parameterized_ae_eq_integral_map_of_indepSigma
    mu mOutside hmOutside parameter fresh hparameter hfresh.aemeasurable
    h_indep second hsecond (by
      simpa [second, secondMoment, fresh] using hsecondMoment)
  refine heq.trans (ae_of_all mu fun omega => ?_)
  change (∫ x, second (parameter omega, x) ∂Measure.map fresh mu) = _
  rw [integral_map hfresh.aemeasurable]
  · have hvalue : (fun x => valueFromSample coefficient
        (parameter omega, fresh x)) =
        fun x => evalSquarefree (coefficient (parameter omega)) X.atom x := by
      funext x
      simpa [fresh] using
        (valueFromSample_freshSample X coefficient (parameter omega) x)
    simp only [second, secondMoment]
    have hnorm := congrArg
      (fun f : Omega -> Complex => fun x => ‖f x‖ ^ 2) hvalue
    rw [hnorm]
    simpa only [coefficientNorm] using
      (integral_norm_evalSquarefree_sq_eq_coeffNorm X
        (WithLp.toLp 2 (coefficient (parameter omega))))
  · exact (hsecond.comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable

end RandomFrame

end BernoulliSection9
