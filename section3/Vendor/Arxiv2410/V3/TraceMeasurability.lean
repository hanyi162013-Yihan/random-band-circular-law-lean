/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/TraceMeasurability.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.Proposition34RowMcDiarmid
import Vendor.Arxiv2410.V3.RandomModel
import Vendor.Arxiv2410.V3.ResolventPerturbation
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Instances.Matrix

/-!
# Measurability and integrability of the random normalized resolvent trace

This file discharges two routine analytic side conditions that formerly appeared as explicit
inputs to the row-McDiarmid reconstruction of arXiv:2410.16457v3, Proposition 3.4.  Matrix
inversion is handled from its definition `det⁻¹ • adjugate`; no probabilistic or random-matrix
estimate is used here.
-/

namespace Arxiv2410V3

open Matrix Complex MeasureTheory ProbabilityTheory

noncomputable section

/-- The coordinate product sigma-algebra on complex matrices.  `Matrix` is a definition rather
than an abbreviation, so this local instance makes its underlying twofold Pi structure explicit
to typeclass synthesis. -/
local instance matrixMeasurableSpace {m n : Type*} :
    MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

/-- For countable index types the preceding product sigma-algebra is the Borel sigma-algebra of
the usual coordinatewise matrix topology. -/
local instance matrixBorelSpace {m n : Type*} [Countable m] [Countable n] :
    BorelSpace (Matrix m n ℂ) :=
  inferInstanceAs (BorelSpace (m → n → ℂ))

section FiniteMatrixMeasurability

variable {Omega : Type*} [MeasurableSpace Omega]
variable {iota : Type*}

/-- A finite complex matrix with measurable entries is a measurable matrix-valued map. -/
theorem measurable_matrix_of_apply
    {A : Omega → Matrix iota iota ℂ}
    (hA : ∀ i j, Measurable (fun omega ↦ A omega i j)) :
    Measurable A := by
  exact measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ hA i j

variable [Fintype iota] [DecidableEq iota]

/-- Matrix inversion preserves measurability in finite complex dimension.

The proof deliberately expands the nonsingular inverse as `det⁻¹ • adjugate`.  Both the
determinant and adjugate are polynomial in the entries, while scalar inversion on `ℂ` is
measurable (including at zero). -/
theorem measurable_matrix_inv
    {A : Omega → Matrix iota iota ℂ} (hA : Measurable A) :
    Measurable (fun omega ↦ (A omega)⁻¹) := by
  have hdet : Measurable (fun omega ↦ (A omega).det) :=
    continuous_id.matrix_det.measurable.comp hA
  have hadj : Measurable (fun omega ↦ (A omega).adjugate) :=
    continuous_id.matrix_adjugate.measurable.comp hA
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  exact hdet.inv.mul <|
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hadj)

end FiniteMatrixMeasurability

section ResolventTraceMeasurability

variable {Omega : Type*} [MeasurableSpace Omega]
variable {n : ℕ}

/-- The shifted matrix `X - zI` in v3 formula (3.1) has measurable entries. -/
theorem measurable_shiftedMatrix
    {X : Omega → Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i j, Measurable (fun omega ↦ X omega i j)) (z : ℂ) :
    Measurable (fun omega ↦ shiftedMatrix (X omega) z) := by
  apply measurable_matrix_of_apply
  intro i j
  simp only [shiftedMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  exact (hX i j).sub measurable_const

/-- The Hermitian dilation in v3 formula (3.1) is measurable whenever the original matrix
entries are measurable. -/
theorem measurable_hermitization
    {X : Omega → Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i j, Measurable (fun omega ↦ X omega i j)) (z : ℂ) :
    Measurable (fun omega ↦ hermitization (X omega) z) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  rcases i with i | i <;> rcases j with j | j
  · simp [hermitization]
  · simp only [hermitization, Matrix.fromBlocks_apply₁₂, shiftedMatrix, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply]
    exact (hX i j).sub measurable_const
  · simp only [hermitization, Matrix.fromBlocks_apply₂₁, conjTranspose_apply,
      shiftedMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    exact continuous_star.measurable.comp <|
      (hX j i).sub measurable_const
  · simp [hermitization]

/-- The Green matrix `𝒢_z(η)` from v3 Section 3 is measurable entrywise.  This is the
finite-dimensional `det⁻¹ · adjugate` argument, independent of the upper-half-plane bound. -/
theorem measurable_greenFunction
    {X : Omega → Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i j, Measurable (fun omega ↦ X omega i j)) (z eta : ℂ) :
    Measurable (fun omega ↦ greenFunction (X omega) z eta) := by
  unfold greenFunction
  apply measurable_matrix_inv
  apply measurable_matrix_of_apply
  intro i j
  simp only [Matrix.sub_apply, Matrix.smul_apply]
  exact ((measurable_pi_apply j).comp
    ((measurable_pi_apply i).comp (measurable_hermitization hX z))).sub measurable_const

/-- The scalar normalized resolvent trace `m_z(η)` in v3 Proposition 3.4 is measurable. -/
theorem measurable_stieltjesTrace
    {X : Omega → Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i j, Measurable (fun omega ↦ X omega i j)) (z eta : ℂ) :
    Measurable (fun omega ↦ stieltjesTrace (X omega) z eta) := by
  unfold stieltjesTrace normalizedTrace
  exact (continuous_id.matrix_trace.measurable.comp
    (measurable_greenFunction hX z eta)).div measurable_const

end ResolventTraceMeasurability

section ResolventTraceIntegrability

variable {n : ℕ} [NeZero n]

/-- The deterministic domination used to integrate `m_z(η)`:
`|m_z(η)| ≤ ‖𝒢_z(η)‖ ≤ (Im η)⁻¹`.

This is the standard Hermitian resolvent bound appearing in the proof of v3 (3.8), now also
used to remove the separate integrability hypothesis from the McDiarmid wrapper. -/
theorem norm_stieltjesTrace_le_inv_im
    (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) {eta : ℂ} (heta : 0 < eta.im) :
    ‖stieltjesTrace X z eta‖ ≤ (eta.im)⁻¹ := by
  exact (norm_normalizedTrace_le_l2Operator _).trans <|
    norm_shiftedHermitian_inv_le_inv_im
      (hermitization X z) (hermitization_isHermitian X z) heta

variable {Omega : Type*} [MeasurableSpace Omega]

/-- On any finite measure space (in particular, a probability space), the random normalized
resolvent trace is integrable for every upper-half-plane `η`. -/
theorem integrable_stieltjesTrace
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {X : Omega → Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i j, Measurable (fun omega ↦ X omega i j)) (z : ℂ)
    {eta : ℂ} (heta : 0 < eta.im) :
    Integrable (fun omega ↦ stieltjesTrace (X omega) z eta) mu := by
  apply Integrable.of_bound (measurable_stieltjesTrace hX z eta).aestronglyMeasurable
    (eta.im)⁻¹
  exact ae_of_all _ fun omega ↦ norm_stieltjesTrace_le_inv_im (X omega) z heta

end ResolventTraceIntegrability

namespace RandomMatrixModelV3

variable {n : ℕ}
variable {Omega OmegaXi : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
variable {mu : Measure Omega} {nu : Measure OmegaXi}
variable [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]

/-- Model method: entry measurability in `RandomMatrixModelV3` implies measurability of the
observable used in v3 Proposition 3.4. -/
theorem stieltjesTrace_measurable
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (z eta : ℂ) :
    Measurable (fun omega ↦ stieltjesTrace (model.matrix omega) z eta) :=
  measurable_stieltjesTrace model.entry_measurable z eta

/-- Model method: for `Im η > 0`, the observable used in v3 Proposition 3.4 is automatically
integrable under the model's probability measure. -/
theorem stieltjesTrace_integrable [NeZero n]
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (z : ℂ)
    {eta : ℂ} (heta : 0 < eta.im) :
    Integrable (fun omega ↦ stieltjesTrace (model.matrix omega) z eta) mu :=
  integrable_stieltjesTrace model.entry_measurable z heta

end RandomMatrixModelV3

section ActualModelMcDiarmidWrapper

open scoped BigOperators ENNReal NNReal ProbabilityTheory

/-- v3 Proposition 3.4, proof step (3), for the actual normalized resolvent trace of a
`RandomMatrixModelV3`.

Compared with `proposition34_formula39_from_row_doobIntervalCertificates`, this theorem no
longer asks the caller to prove measurability or integrability of the trace: both follow from
`entry_measurable` and the deterministic upper-half-plane resolvent estimate.  The two Doob
certificates remain the genuinely model-specific row-exposure input. -/
theorem proposition34_formula39_from_randomMatrixModel_row_doobIntervalCertificates
    {Omega OmegaXi : Type*}
    {mOmega : MeasurableSpace Omega} {mOmegaXi : MeasurableSpace OmegaXi}
    [StandardBorelSpace Omega]
    {mu : Measure Omega} {nu : Measure OmegaXi}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {n : ℕ} (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    {filtration : Filtration ℕ mOmega}
    (z : ℂ) {eta : ℂ} (heta : 0 < eta.im)
    (hn : 2 ≤ n)
    {sensitivity : ℕ → ℝ≥0}
    (hsensitivity : ∀ i < n,
      (sensitivity i : ℝ) ≤ 2 / ((n : ℝ) * eta.im))
    (hsensitivityPos : ∃ i < n, 0 < sensitivity i)
    (hre : DoobIntervalCertificate (filtration := filtration) (mu := mu)
      (fun omega ↦ (stieltjesTrace (model.matrix omega) z eta).re) n sensitivity)
    (him : DoobIntervalCertificate (filtration := filtration) (mu := mu)
      (fun omega ↦ (stieltjesTrace (model.matrix omega) z eta).im) n sensitivity)
    {expectedGaussianTrace expectedCircularGaussianTrace freeTrace : ℂ}
    {B C : ℝ}
    (comparisons : Formula311ExactComparisonInputs
      (∫ omega, stieltjesTrace (model.matrix omega) z eta ∂mu)
      expectedGaussianTrace expectedCircularGaussianTrace freeTrace (n : ℝ) B eta.im C)
    (rate : PolynomialRateCertificate (n : ℝ)
      (formula311Error (n : ℝ) B eta.im C 16)) :
    Proposition34Formula39Conclusion mu
      (ComplexConcentrationGood
        (fun omega ↦ stieltjesTrace (model.matrix omega) z eta)
        (∫ omega, stieltjesTrace (model.matrix omega) z eta ∂mu)
        (16 * Real.sqrt (Real.log (n : ℝ)) /
          (Real.sqrt (n : ℝ) * eta.im)))
      (fun omega ↦ stieltjesTrace (model.matrix omega) z eta)
      freeTrace (n : ℝ) := by
  let _ : NeZero n := ⟨by omega⟩
  exact proposition34_formula39_from_row_doobIntervalCertificates
    (model.stieltjesTrace_measurable z eta)
    (model.stieltjesTrace_integrable z heta)
    hn heta hsensitivity hsensitivityPos hre him comparisons rate

end ActualModelMcDiarmidWrapper

end

end Arxiv2410V3

