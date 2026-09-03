import ShortRingAnchor.SingularValues
import ShortRingAnchor.ShortRingModel
import ShortRingAnchor.PolynomialZeroSets
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Map

/-!
# Almost-sure nonsingularity from an absolutely continuous matrix law

The determinant of `A - z I` is a nonzero polynomial in the entries of `A`.
This file proves that algebraic assertion completely.  The geometric fact
is now proved in `PolynomialZeroSets`: a nonzero polynomial has a null zero
set for every finite product of sigma-finite nonatomic complex measures.
In particular finite-dimensional complex Lebesgue measure satisfies the
predicate `HasNullMatrixPolynomialZeroSets` without any external input.
Absolute continuity of the matrix law then gives almost-sure nonsingularity
without an independence assumption.
-/

open Filter Set
open scoped ENNReal Topology

noncomputable section

namespace ShortRingAnchor

open MeasureTheory

variable {Omega ι : Type*} [MeasurableSpace Omega]
variable [Fintype ι] [DecidableEq ι]

/-- Evaluation of a polynomial in matrix-entry variables at a concrete matrix. -/
def matrixPolynomialEvaluation
    (p : MvPolynomial (ι × ι) ℂ)
    (A : Matrix ι ι ℂ) : ℂ :=
  MvPolynomial.eval (fun ij => A ij.1 ij.2) p

omit [Fintype ι] [DecidableEq ι] in
/-- Matrix-entry polynomial evaluation is continuous. -/
theorem continuous_matrixPolynomialEvaluation
    (p : MvPolynomial (ι × ι) ℂ) :
    Continuous (matrixPolynomialEvaluation p : Matrix ι ι ℂ → ℂ) := by
  apply p.continuous_eval.comp
  exact continuous_pi fun ij =>
    (continuous_apply ij.2).comp (continuous_apply ij.1)

/--
The zero-set property for an arbitrary reference measure.  The next two
theorems prove it for product nonatomic measures and for Lebesgue measure,
so it is no longer an external geometric input in those applications.
-/
def HasNullMvPolynomialZeroSets {sigma : Type*}
    (nu : Measure (sigma → ℂ)) : Prop :=
  ∀ p : MvPolynomial sigma ℂ, p ≠ 0 →
    nu {x | MvPolynomial.eval x p = 0} = 0

/-- Matrix-coordinate spelling of `HasNullMvPolynomialZeroSets`. -/
abbrev HasNullMatrixPolynomialZeroSets
    (nu : Measure ((ι × ι) → ℂ)) : Prop :=
  HasNullMvPolynomialZeroSets nu

/-- The geometric step preceding Proposition 3.6, proved for arbitrary
finite products of sigma-finite nonatomic complex coordinate measures. -/
theorem hasNullMvPolynomialZeroSets_pi
    {sigma : Type*} [Fintype sigma]
    (nu : sigma → Measure ℂ) [∀ i, SigmaFinite (nu i)]
    [∀ i, NullSingletonClass (nu i)] :
    HasNullMvPolynomialZeroSets (Measure.pi nu) :=
  mvPolynomial_zeroSet_measure_pi nu

/-- Finite-dimensional complex Lebesgue measure needs no geometric
hypothesis in the Proposition 3.6 determinant adapter. -/
theorem hasNullMvPolynomialZeroSets_volume
    {sigma : Type*} [Fintype sigma] :
    HasNullMvPolynomialZeroSets (volume : Measure (sigma → ℂ)) :=
  mvPolynomial_zeroSet_volume

/-- Absolute continuity transfers polynomial-zero nullity to random coordinates. -/
theorem mvPolynomial_ne_zero_ae_of_law_absolutelyContinuous
    {sigma : Type*} [Fintype sigma]
    {mu : Measure Omega} {nu : Measure (sigma → ℂ)}
    (X : Omega → sigma → ℂ)
    (hX : AEMeasurable X mu)
    (hLaw : Measure.map X mu ≪ nu)
    (hnull : HasNullMvPolynomialZeroSets nu)
    (p : MvPolynomial sigma ℂ) (hp : p ≠ 0) :
    ∀ᵐ sample ∂mu, MvPolynomial.eval (X sample) p ≠ 0 := by
  rw [ae_iff]
  simp only [not_ne_iff]
  have hs : MeasurableSet {x : sigma → ℂ |
      MvPolynomial.eval x p = 0} :=
    (measurableSet_singleton 0).preimage p.continuous_eval.measurable
  have hmap : (Measure.map X mu)
      {x : sigma → ℂ | MvPolynomial.eval x p = 0} = 0 :=
    hLaw (hnull p hp)
  rw [Measure.map_apply_of_aemeasurable hX hs] at hmap
  exact hmap

omit [DecidableEq ι] in
/-- Absolute continuity transfers polynomial-zero nullity to a random matrix. -/
theorem matrixPolynomial_ne_zero_ae_of_law_absolutelyContinuous
    {mu : Measure Omega} {nu : Measure ((ι × ι) → ℂ)}
    (A : Omega → Matrix ι ι ℂ)
    (hA : AEMeasurable
      (fun sample (ij : ι × ι) => A sample ij.1 ij.2) mu)
    (hLaw : Measure.map
      (fun sample (ij : ι × ι) => A sample ij.1 ij.2) mu ≪ nu)
    (hnull : HasNullMatrixPolynomialZeroSets nu)
    (p : MvPolynomial (ι × ι) ℂ) (hp : p ≠ 0) :
    ∀ᵐ sample ∂mu, matrixPolynomialEvaluation p (A sample) ≠ 0 := by
  simpa only [matrixPolynomialEvaluation] using
    mvPolynomial_ne_zero_ae_of_law_absolutelyContinuous
      (fun sample (ij : ι × ι) => A sample ij.1 ij.2)
      hA hLaw hnull p hp

/-- The polynomial in the entries of `A` whose value is `det (A - z I)`. -/
def shiftedDetPolynomial (z : ℂ) : MvPolynomial (ι × ι) ℂ :=
  (Matrix.mvPolynomialX ι ι ℂ -
    (MvPolynomial.C z : MvPolynomial (ι × ι) ℂ) •
      (1 : Matrix ι ι (MvPolynomial (ι × ι) ℂ))).det

/-- Evaluation of `shiftedDetPolynomial z` is exactly the shifted determinant. -/
theorem matrixPolynomialEvaluation_shiftedDetPolynomial
    (z : ℂ) (A : Matrix ι ι ℂ) :
    matrixPolynomialEvaluation (shiftedDetPolynomial (ι := ι) z) A =
      (A - z • (1 : Matrix ι ι ℂ)).det := by
  simp only [matrixPolynomialEvaluation, shiftedDetPolynomial]
  rw [RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.mvPolynomialX]
  · simp [Matrix.mvPolynomialX, hij]

/--
The shifted determinant polynomial is genuinely nonzero.  The witness is
`A = (z + 1) I`, at which the polynomial evaluates to `det I = 1`.
-/
theorem shiftedDetPolynomial_ne_zero (z : ℂ) :
    shiftedDetPolynomial (ι := ι) z ≠ 0 := by
  intro hp
  have heval := matrixPolynomialEvaluation_shiftedDetPolynomial
    (ι := ι) z ((z + 1) • (1 : Matrix ι ι ℂ))
  rw [hp] at heval
  simp only [matrixPolynomialEvaluation] at heval
  have hmatrix :
      (z + 1) • (1 : Matrix ι ι ℂ) - z • 1 = 1 := by
    module
  rw [hmatrix, Matrix.det_one] at heval
  exact zero_ne_one heval

/--
An absolutely continuous random matrix is almost surely nonsingular after
subtracting any fixed scalar matrix.
-/
theorem shifted_det_ne_zero_ae_of_law_absolutelyContinuous
    {mu : Measure Omega} {nu : Measure ((ι × ι) → ℂ)}
    (A : Omega → Matrix ι ι ℂ)
    (hA : AEMeasurable
      (fun sample (ij : ι × ι) => A sample ij.1 ij.2) mu)
    (hLaw : Measure.map
      (fun sample (ij : ι × ι) => A sample ij.1 ij.2) mu ≪ nu)
    (hnull : HasNullMatrixPolynomialZeroSets nu)
    (z : ℂ) :
    ∀ᵐ sample ∂mu,
      (A sample - z • (1 : Matrix ι ι ℂ)).det ≠ 0 := by
  filter_upwards [matrixPolynomial_ne_zero_ae_of_law_absolutelyContinuous
      A hA hLaw hnull (shiftedDetPolynomial (ι := ι) z)
      (shiftedDetPolynomial_ne_zero (ι := ι) z)] with sample hsample
  simpa [matrixPolynomialEvaluation_shiftedDetPolynomial] using hsample

/-- Proposition 3.6's a.e. invertibility step for any matrix law absolutely
continuous with respect to complex Lebesgue measure.  The geometric zero-set
claim and the determinant-polynomial nonvanishing are both proved inside Lean. -/
theorem shifted_det_ne_zero_ae_of_law_absolutelyContinuous_volume
    {mu : Measure Omega}
    (A : Omega → Matrix ι ι ℂ)
    (hA : AEMeasurable
      (fun sample (ij : ι × ι) => A sample ij.1 ij.2) mu)
    (hLaw : Measure.map
      (fun sample (ij : ι × ι) => A sample ij.1 ij.2) mu ≪
        (volume : Measure ((ι × ι) → ℂ)))
    (z : ℂ) :
    ∀ᵐ sample ∂mu, (A sample - z • (1 : Matrix ι ι ℂ)).det ≠ 0 :=
  shifted_det_ne_zero_ae_of_law_absolutelyContinuous A hA hLaw
    hasNullMvPolynomialZeroSets_volume z

/-- The zero signed offset, represented by the middle element of `BandOffset W`. -/
def centralBandOffset (W : Nat) : BandOffset W :=
  ⟨W, by omega⟩

/-- The central band offset leaves a column unchanged. -/
theorem cyclicColumn_centralBandOffset {M W : Nat}
    (hfit : 2 * W + 1 ≤ M) (i : Fin M) :
    cyclicColumn hfit i (centralBandOffset W) = i := by
  apply Fin.ext
  simp only [cyclicColumn, centralBandOffset]
  have harith : i.val + W + M - W = i.val + M := by omega
  rw [harith]
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

/-- The cyclic short-ring matrix (3.1), with its atoms replaced by variables. -/
def cyclicShortRingPolynomialMatrix
    {M W : Nat} {c0 C0 : Real}
    (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 ≤ M) :
    Matrix (Fin M) (Fin M)
      (MvPolynomial (Fin M × BandOffset W) ℂ) :=
  fun i j => ∑ s : BandOffset W,
    if cyclicColumn hfit i s = j then
      MvPolynomial.C (Real.sqrt (weights.q s) : ℂ) *
        MvPolynomial.X (i, s)
    else 0

/-- The cyclic-model polynomial whose value is `det (H - z I)`. -/
def cyclicShortRingShiftedDetPolynomial
    {M W : Nat} {c0 C0 : Real}
    (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 ≤ M) (z : ℂ) :
    MvPolynomial (Fin M × BandOffset W) ℂ :=
  (cyclicShortRingPolynomialMatrix weights hfit -
    (MvPolynomial.C z : MvPolynomial (Fin M × BandOffset W) ℂ) •
      (1 : Matrix (Fin M) (Fin M)
        (MvPolynomial (Fin M × BandOffset W) ℂ))).det

/-- Evaluation of the cyclic-model polynomial is the desired determinant. -/
theorem eval_cyclicShortRingShiftedDetPolynomial
    {M W : Nat} {c0 C0 : Real}
    (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 ≤ M) (z : ℂ)
    (entry : Fin M → BandOffset W → ℂ) :
    MvPolynomial.eval (fun is => entry is.1 is.2)
        (cyclicShortRingShiftedDetPolynomial weights hfit z) =
      (cyclicShortRingMatrix weights hfit entry -
        z • (1 : Matrix (Fin M) (Fin M) ℂ)).det := by
  simp only [cyclicShortRingShiftedDetPolynomial]
  rw [RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [cyclicShortRingPolynomialMatrix, cyclicShortRingMatrix]
    apply Finset.sum_congr rfl
    intro s _hs
    by_cases hcol : cyclicColumn hfit i s = i <;> simp [hcol]
  · simp [cyclicShortRingPolynomialMatrix, cyclicShortRingMatrix, hij]
    apply Finset.sum_congr rfl
    intro s _hs
    by_cases hcol : cyclicColumn hfit i s = j <;> simp [hcol]

/-- Atoms which make the cyclic matrix equal to `(z+1) I`. -/
def cyclicDiagonalWitness
    {M W : Nat} {c0 C0 : Real}
    (weights : AdmissibleWeights W c0 C0) (z : ℂ) :
    Fin M → BandOffset W → ℂ :=
  fun _ s => if s = centralBandOffset W then
    (z + 1) / (Real.sqrt (weights.q (centralBandOffset W)) : ℂ)
  else 0

/-- The preceding atom assignment really produces `(z+1) I`. -/
theorem cyclicShortRingMatrix_cyclicDiagonalWitness
    {M W : Nat} {c0 C0 : Real}
    (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 ≤ M) (z : ℂ) :
    cyclicShortRingMatrix weights hfit
        (cyclicDiagonalWitness weights z) =
      (z + 1) • (1 : Matrix (Fin M) (Fin M) ℂ) := by
  classical
  have hsqrt :
      (Real.sqrt (weights.q (centralBandOffset W)) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.2 (weights.q_pos (centralBandOffset W))).ne'
  ext i j
  rw [cyclicShortRingMatrix_apply]
  rw [Finset.sum_eq_single (centralBandOffset W)]
  · by_cases hij : i = j
    · subst j
      simp [cyclicDiagonalWitness, cyclicColumn_centralBandOffset]
      exact mul_div_cancel₀ (z + 1) hsqrt
    · simp [cyclicColumn_centralBandOffset, hij]
  · intro s _hs hne
    simp [cyclicDiagonalWitness, hne]
  · simp

/--
The determinant polynomial remains nonzero after restricting to the genuine
cyclic band variables.  Thus sparsity of the matrix causes no algebraic
degeneracy at any fixed finite `z`.
-/
theorem cyclicShortRingShiftedDetPolynomial_ne_zero
    {M W : Nat} {c0 C0 : Real}
    (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 ≤ M) (z : ℂ) :
    cyclicShortRingShiftedDetPolynomial weights hfit z ≠ 0 := by
  intro hp
  have heval := eval_cyclicShortRingShiftedDetPolynomial
    weights hfit z (cyclicDiagonalWitness weights z)
  rw [hp] at heval
  rw [cyclicShortRingMatrix_cyclicDiagonalWitness] at heval
  have hmatrix :
      (z + 1) • (1 : Matrix (Fin M) (Fin M) ℂ) - z • 1 = 1 := by
    module
  rw [hmatrix, Matrix.det_one] at heval
  exact zero_ne_one heval

/--
Almost-sure nonsingularity of the cyclic model from absolute continuity of
the joint law of its active atom coordinates.
-/
theorem cyclicShortRing_shifted_det_ne_zero_ae
    {M W : Nat} {c0 C0 : Real}
    {mu : Measure Omega}
    {nu : Measure ((Fin M × BandOffset W) → ℂ)}
    (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 ≤ M)
    (entry : Omega → Fin M → BandOffset W → ℂ)
    (hentry : AEMeasurable
      (fun sample (is : Fin M × BandOffset W) =>
        entry sample is.1 is.2) mu)
    (hLaw : Measure.map
      (fun sample (is : Fin M × BandOffset W) =>
        entry sample is.1 is.2) mu ≪ nu)
    (hnull : HasNullMvPolynomialZeroSets nu)
    (z : ℂ) :
    ∀ᵐ sample ∂mu,
      (cyclicShortRingRandomMatrix weights hfit entry sample -
        z • (1 : Matrix (Fin M) (Fin M) ℂ)).det ≠ 0 := by
  filter_upwards [mvPolynomial_ne_zero_ae_of_law_absolutelyContinuous
      (fun sample (is : Fin M × BandOffset W) =>
        entry sample is.1 is.2)
      hentry hLaw hnull
      (cyclicShortRingShiftedDetPolynomial weights hfit z)
      (cyclicShortRingShiftedDetPolynomial_ne_zero weights hfit z)]
      with sample hsample
  simpa only [cyclicShortRingRandomMatrix,
    eval_cyclicShortRingShiftedDetPolynomial] using hsample

end ShortRingAnchor
