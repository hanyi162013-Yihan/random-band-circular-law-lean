/- Source snapshot: upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/GeometricBrascampLieb.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The geometric Brascamp--Lieb input behind the projection-density theorem

This file isolates the analytic inequality used in Lemma 6.7 of Yi Han,
*Brown measure convergence for the spectrum of polynomials in Ginibre matrices*.
It records both the real and complex geometric Brascamp--Lieb statements and
fully proves the entropy calculation which turns the fiber estimate into a
dimension-free density bound.

The two geometric Brascamp--Lieb propositions are deliberately data passed to
the downstream theorems.  This accurately identifies the analytic ingredient
which is not currently supplied by Mathlib.
-/

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LivshytsProjectionFormalization

/-- The real rank-one geometric Brascamp--Lieb inequality. -/
def RealGeometricBrascampLieb : Prop :=
  ∀ (n m : ℕ)
    (B : Fin n → ((Fin m → ℝ) →L[ℝ] ℝ))
    (c : Fin n → ℝ),
    (∀ i, 0 ≤ c i) →
    (∀ i, c i ≤ 1) →
    (∀ i, ‖B i‖ = 1) →
    (∀ x, ∑ i, c i * ‖B i x‖ ^ 2 = ‖x‖ ^ 2) →
    ∀ (f : Fin n → ℝ → ℝ≥0∞),
      (∀ i, Measurable (f i)) →
      (∫⁻ x, ∏ i, (f i (B i x)).rpow (c i) ∂volume) ≤
        ∏ i, (∫⁻ t, f i t ∂volume).rpow (c i)

/-- The complex geometric Brascamp--Lieb inequality, with one-dimensional
complex target maps.  Its exponents are the same as in the real statement;
the different final constant comes from two-dimensional Lebesgue scaling. -/
def ComplexGeometricBrascampLieb : Prop :=
  ∀ (n m : ℕ)
    (B : Fin n → ((Fin m → ℂ) →L[ℂ] ℂ))
    (c : Fin n → ℝ),
    (∀ i, 0 ≤ c i) →
    (∀ i, c i ≤ 1) →
    (∀ i, ‖B i‖ = 1) →
    (∀ x, ∑ i, c i * ‖B i x‖ ^ 2 = ‖x‖ ^ 2) →
    ∀ (f : Fin n → ℂ → ℝ≥0∞),
      (∀ i, Measurable (f i)) →
      (∫⁻ x, ∏ i, (f i (B i x)).rpow (c i) ∂volume) ≤
        ∏ i, (∫⁻ z, f i z ∂volume).rpow (c i)

/-- The exact pair of standard analytic inequalities needed for the real and
complex versions of the fiber argument. -/
structure GeometricBrascampLiebInput : Prop where
  real : RealGeometricBrascampLieb
  complex : ComplexGeometricBrascampLieb

/-- The entropy term appearing after the density functions are rescaled on a
fiber.  Mathlib defines `log 0 = 0`, so this formula also handles zero weights. -/
noncomputable def projectionEntropy (c : ℝ) : ℝ := -c * Real.log c

theorem projectionEntropy_le_one_sub {c : ℝ} (hc : 0 ≤ c) :
    projectionEntropy c ≤ 1 - c := by
  have h := Real.self_sub_one_le_mul_log hc
  dsimp [projectionEntropy]
  linarith

theorem sum_projectionEntropy_le_codimension
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (d : ℝ) (hcodim : ∑ i, (1 - c i) = d) :
    ∑ i, projectionEntropy (c i) ≤ d := by
  calc
    ∑ i, projectionEntropy (c i) ≤ ∑ i, (1 - c i) :=
      Finset.sum_le_sum fun i _ => projectionEntropy_le_one_sub (hc i)
    _ = d := hcodim

theorem exp_weighted_projectionEntropy_le
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (d q : ℝ) (hcodim : ∑ i, (1 - c i) = d) (hq : 0 ≤ q) :
    Real.exp (q * ∑ i, projectionEntropy (c i)) ≤ Real.exp (q * d) := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left
    (sum_projectionEntropy_le_codimension c hc d hcodim) hq

/-- A coarea/fiber formula for a pushed-forward measure.  The density is
`ℝ≥0∞`-valued so it can be used directly with `Measure.withDensity`. -/
structure FiberDensityFormula {E : Type*} [MeasurableSpace E]
    (projected reference : Measure E) where
  density : E → ℝ≥0∞
  measurable_density : Measurable density
  map_eq_withDensity : projected = reference.withDensity density

/-- A bounded-density conclusion, including the actual Radon--Nikodym density
and not merely a small-ball estimate. -/
structure HasBoundedDensity {E : Type*} [MeasurableSpace E]
    (projected reference : Measure E) (M : ℝ) where
  density : E → ℝ≥0∞
  measurable_density : Measurable density
  map_eq_withDensity : projected = reference.withDensity density
  density_le : ∀ y, density y ≤ ENNReal.ofReal M

/-- Data produced by the real fiber formula and real geometric
Brascamp--Lieb inequality before the elementary entropy estimate is applied. -/
structure RealFiberBLBound {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    {projected reference : Measure E} (formula : FiberDensityFormula projected reference)
    (K : ℝ) (d : ℕ) where
  weights : ι → ℝ
  weights_nonnegative : ∀ i, 0 ≤ weights i
  codimension_identity : ∑ i, (1 - weights i) = (d : ℝ)
  fiber_bound : ∀ y,
    formula.density y ≤ ENNReal.ofReal
      (K ^ d * Real.exp ((1 / 2 : ℝ) * ∑ i, projectionEntropy (weights i)))

/-- Data produced by the complex fiber formula and complex geometric
Brascamp--Lieb inequality before the elementary entropy estimate is applied. -/
structure ComplexFiberBLBound {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    {projected reference : Measure E} (formula : FiberDensityFormula projected reference)
    (K : ℝ) (d : ℕ) where
  weights : ι → ℝ
  weights_nonnegative : ∀ i, 0 ≤ weights i
  codimension_identity : ∑ i, (1 - weights i) = (d : ℝ)
  fiber_bound : ∀ y,
    formula.density y ≤ ENNReal.ofReal
      (K ^ d * Real.exp (∑ i, projectionEntropy (weights i)))

/-- The real fiber representation immediately before geometric
Brascamp--Lieb is applied.  `fiber_le_integral` is the coarea/fiber step and
`product_integrals_le` is the one-dimensional change-of-variables step. -/
structure RealFiberBLSetup {E : Type*} [MeasurableSpace E]
    {projected reference : Measure E} (formula : FiberDensityFormula projected reference)
    (K : ℝ) (d n m : ℕ) where
  weights : Fin n → ℝ
  weights_nonnegative : ∀ i, 0 ≤ weights i
  weights_le_one : ∀ i, weights i ≤ 1
  codimension_identity : ∑ i, (1 - weights i) = (d : ℝ)
  maps : E → Fin n → ((Fin m → ℝ) →L[ℝ] ℝ)
  map_norm : ∀ y i, ‖maps y i‖ = 1
  frame_identity : ∀ y x, ∑ i, weights i * ‖maps y i x‖ ^ 2 = ‖x‖ ^ 2
  functions : E → Fin n → ℝ → ℝ≥0∞
  measurable_functions : ∀ y i, Measurable (functions y i)
  fiber_le_integral : ∀ y,
    formula.density y ≤
      ∫⁻ x, ∏ i, (functions y i (maps y i x)).rpow (weights i) ∂volume
  product_integrals_le : ∀ y,
    (∏ i, (∫⁻ t, functions y i t ∂volume).rpow (weights i)) ≤
      ENNReal.ofReal
        (K ^ d * Real.exp ((1 / 2 : ℝ) * ∑ i, projectionEntropy (weights i)))

/-- The complex fiber representation immediately before geometric
Brascamp--Lieb is applied.  Planar scaling changes the factor `1 / 2` in the
real setup to `1`. -/
structure ComplexFiberBLSetup {E : Type*} [MeasurableSpace E]
    {projected reference : Measure E} (formula : FiberDensityFormula projected reference)
    (K : ℝ) (d n m : ℕ) where
  weights : Fin n → ℝ
  weights_nonnegative : ∀ i, 0 ≤ weights i
  weights_le_one : ∀ i, weights i ≤ 1
  codimension_identity : ∑ i, (1 - weights i) = (d : ℝ)
  maps : E → Fin n → ((Fin m → ℂ) →L[ℂ] ℂ)
  map_norm : ∀ y i, ‖maps y i‖ = 1
  frame_identity : ∀ y x, ∑ i, weights i * ‖maps y i x‖ ^ 2 = ‖x‖ ^ 2
  functions : E → Fin n → ℂ → ℝ≥0∞
  measurable_functions : ∀ y i, Measurable (functions y i)
  fiber_le_integral : ∀ y,
    formula.density y ≤
      ∫⁻ x, ∏ i, (functions y i (maps y i x)).rpow (weights i) ∂volume
  product_integrals_le : ∀ y,
    (∏ i, (∫⁻ z, functions y i z ∂volume).rpow (weights i)) ≤
      ENNReal.ofReal
        (K ^ d * Real.exp (∑ i, projectionEntropy (weights i)))

def realFiberBLBoundOfGeometric
    {E : Type*} [MeasurableSpace E] {projected reference : Measure E}
    {K : ℝ} {d n m : ℕ} (formula : FiberDensityFormula projected reference)
    (hGBL : RealGeometricBrascampLieb)
    (setup : RealFiberBLSetup formula K d n m) :
    RealFiberBLBound (ι := Fin n) formula K d where
  weights := setup.weights
  weights_nonnegative := setup.weights_nonnegative
  codimension_identity := setup.codimension_identity
  fiber_bound y := calc
    formula.density y ≤
        ∫⁻ x, ∏ i, (setup.functions y i (setup.maps y i x)).rpow (setup.weights i) ∂volume :=
      setup.fiber_le_integral y
    _ ≤ ∏ i, (∫⁻ t, setup.functions y i t ∂volume).rpow (setup.weights i) :=
      hGBL n m (setup.maps y) setup.weights setup.weights_nonnegative setup.weights_le_one
        (setup.map_norm y) (setup.frame_identity y) (setup.functions y)
        (setup.measurable_functions y)
    _ ≤ ENNReal.ofReal
        (K ^ d * Real.exp ((1 / 2 : ℝ) * ∑ i, projectionEntropy (setup.weights i))) :=
      setup.product_integrals_le y

def complexFiberBLBoundOfGeometric
    {E : Type*} [MeasurableSpace E] {projected reference : Measure E}
    {K : ℝ} {d n m : ℕ} (formula : FiberDensityFormula projected reference)
    (hGBL : ComplexGeometricBrascampLieb)
    (setup : ComplexFiberBLSetup formula K d n m) :
    ComplexFiberBLBound (ι := Fin n) formula K d where
  weights := setup.weights
  weights_nonnegative := setup.weights_nonnegative
  codimension_identity := setup.codimension_identity
  fiber_bound y := calc
    formula.density y ≤
        ∫⁻ x, ∏ i, (setup.functions y i (setup.maps y i x)).rpow (setup.weights i) ∂volume :=
      setup.fiber_le_integral y
    _ ≤ ∏ i, (∫⁻ z, setup.functions y i z ∂volume).rpow (setup.weights i) :=
      hGBL n m (setup.maps y) setup.weights setup.weights_nonnegative setup.weights_le_one
        (setup.map_norm y) (setup.frame_identity y) (setup.functions y)
        (setup.measurable_functions y)
    _ ≤ ENNReal.ofReal
        (K ^ d * Real.exp (∑ i, projectionEntropy (setup.weights i))) :=
      setup.product_integrals_le y

theorem real_projection_density_from_fiber_BL
    {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    {projected reference : Measure E} {K : ℝ} {d : ℕ}
    (formula : FiberDensityFormula projected reference)
    (hBL : RealFiberBLBound (ι := ι) formula K d) (hK : 0 ≤ K) :
    Nonempty (HasBoundedDensity projected reference
      (K ^ d * Real.exp ((1 / 2 : ℝ) * (d : ℝ)))) := by
  refine ⟨
    { density := formula.density
      measurable_density := formula.measurable_density
      map_eq_withDensity := formula.map_eq_withDensity
      density_le := ?_ }⟩
  intro y
  refine (hBL.fiber_bound y).trans ?_
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hK d)
  exact exp_weighted_projectionEntropy_le hBL.weights hBL.weights_nonnegative
    (d : ℝ) (1 / 2 : ℝ) hBL.codimension_identity (by norm_num)

theorem complex_projection_density_from_fiber_BL
    {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    {projected reference : Measure E} {K : ℝ} {d : ℕ}
    (formula : FiberDensityFormula projected reference)
    (hBL : ComplexFiberBLBound (ι := ι) formula K d) (hK : 0 ≤ K) :
    Nonempty (HasBoundedDensity projected reference
      (K ^ d * Real.exp (d : ℝ))) := by
  refine ⟨
    { density := formula.density
      measurable_density := formula.measurable_density
      map_eq_withDensity := formula.map_eq_withDensity
      density_le := ?_ }⟩
  intro y
  refine (hBL.fiber_bound y).trans ?_
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hK d)
  simpa only [one_mul] using
    exp_weighted_projectionEntropy_le hBL.weights hBL.weights_nonnegative
      (d : ℝ) 1 hBL.codimension_identity zero_le_one

theorem real_projection_density_from_geometric_BL
    {E : Type*} [MeasurableSpace E] {projected reference : Measure E}
    {K : ℝ} {d n m : ℕ} (formula : FiberDensityFormula projected reference)
    (hGBL : RealGeometricBrascampLieb)
    (setup : RealFiberBLSetup formula K d n m) (hK : 0 ≤ K) :
    Nonempty (HasBoundedDensity projected reference
      (K ^ d * Real.exp ((1 / 2 : ℝ) * (d : ℝ)))) :=
  real_projection_density_from_fiber_BL formula
    (realFiberBLBoundOfGeometric formula hGBL setup) hK

theorem complex_projection_density_from_geometric_BL
    {E : Type*} [MeasurableSpace E] {projected reference : Measure E}
    {K : ℝ} {d n m : ℕ} (formula : FiberDensityFormula projected reference)
    (hGBL : ComplexGeometricBrascampLieb)
    (setup : ComplexFiberBLSetup formula K d n m) (hK : 0 ≤ K) :
    Nonempty (HasBoundedDensity projected reference
      (K ^ d * Real.exp (d : ℝ))) :=
  complex_projection_density_from_fiber_BL formula
    (complexFiberBLBoundOfGeometric formula hGBL setup) hK

theorem real_projection_density_dim_one
    {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    {projected reference : Measure E} {K : ℝ}
    (formula : FiberDensityFormula projected reference)
    (hBL : RealFiberBLBound (ι := ι) formula K 1) (hK : 0 ≤ K) :
    Nonempty (HasBoundedDensity projected reference (Real.exp 1 * K)) := by
  rcases real_projection_density_from_fiber_BL formula hBL hK with ⟨h⟩
  refine ⟨
    { density := h.density
      measurable_density := h.measurable_density
      map_eq_withDensity := h.map_eq_withDensity
      density_le := ?_ }⟩
  intro y
  refine (h.density_le y).trans ?_
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)]
  norm_num only [pow_one, Nat.cast_one]
  have hexp : Real.exp ((1 : ℝ) / 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
  nlinarith [Real.exp_pos ((1 : ℝ) / 2), Real.exp_pos 1]

theorem real_projection_density_dim_two
    {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    {projected reference : Measure E} {K : ℝ}
    (formula : FiberDensityFormula projected reference)
    (hBL : RealFiberBLBound (ι := ι) formula K 2) (hK : 0 ≤ K) :
    Nonempty (HasBoundedDensity projected reference (Real.exp 1 * K ^ 2)) := by
  simpa [show (2 : ℝ) / 2 = 1 by norm_num, mul_comm] using
    (real_projection_density_from_fiber_BL formula hBL hK)

end LivshytsProjectionFormalization

