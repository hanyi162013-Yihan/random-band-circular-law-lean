import BernoulliSection10.EfronStein
import BernoulliSection10.HodgeIntegrability
import BernoulliSection10.PhysicalAffinity

set_option maxHeartbeats 800000

/-!
# Concentration by physical rows

This is the probability-combination layer of Lemma 10.5.  The concrete
physical-row affine normal form is supplied by `PhysicalAffinity`; this
module applies Lemma 10.2 and finite-product Efron--Stein.
-/

open scoped BigOperators Matrix ENNReal NNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory

noncomputable section

namespace BernoulliSection10

open Matrix Set Set.powersetCard
open BernoulliLinearAlgebra
/-! ## Concrete one-row resampling energy -/

/-- The explicit Lemma 10.2 energy paid when one complete physical row,
containing `3W` independent real atoms, is resampled. -/
def physicalRowResamplingEnergy (W : ℕ) (L : ℝ) : ℝ :=
  lemma10_2Constant L *
    Real.log (Real.exp 1 * (((3 * W : ℕ) : ℝ))) ^ 2

theorem physicalRowResamplingEnergy_nonneg (W : ℕ) (L : ℝ) :
    0 ≤ physicalRowResamplingEnergy W L := by
  have hlog : 0 ≤
      Real.log (Real.exp 1 * (((3 * W : ℕ) : ℝ))) ^ 2 := sq_nonneg _
  have hconst : 0 ≤ lemma10_2Constant L := by
    unfold lemma10_2Constant affineLogConstant
    positivity
  exact mul_nonneg hconst hlog

/-- For fixed values of all other rows, the squared change caused by two
independent values of one physical row is integrable.  This is the concrete
`3W`-atom specialization of Lemma 10.2. -/
theorem intervalDegreeLog_resampling_integrable
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ)
    (r : Fin (2 * W + 1)) (x : IntervalRows W s)
    (j : Fin s) (a : Fin W) :
    Integrable
      (fun p : PhysicalRowAtoms W × PhysicalRowAtoms W ↦
        (intervalDegreeLog W s z r
              (Function.update x (intervalRowIndex j a) p.1) -
            intervalDegreeLog W s z r
              (Function.update x (intervalRowIndex j a) p.2)) ^ 2)
      ((physicalRowLaw W μ).prod (physicalRowLaw W μ)) := by
  have hp : 0 < 3 * W := by omega
  have h := lemma_10_2_resampling_integrable_of_pos hμ hp
    (conditionedAffineCenter W s z x r j a)
    (conditionedAffineCoefficient W s z x r j a)
  simpa only [physicalRowLaw, intervalDegreeLog,
    intervalClearedProduct_update_eq_affineValue, sq_abs] using h

/-- Lemma 10.2 bounds the conditional resampling energy of every concrete
physical-row coordinate, uniformly in all conditioned rows. -/
theorem intervalDegreeLog_conditionalCoordinateEnergy_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ)
    (r : Fin (2 * W + 1)) (x : IntervalRows W s)
    (j : Fin s) (a : Fin W) :
    conditionalCoordinateEnergy (μ := physicalRowLaw W μ)
        (intervalDegreeLog W s z r) (intervalRowIndex j a) x ≤
      physicalRowResamplingEnergy W L := by
  letI := hμ.toIsProbabilityMeasure
  letI : SFinite (physicalRowLaw W μ) := by
    unfold physicalRowLaw
    infer_instance
  let F : PhysicalRowAtoms W × PhysicalRowAtoms W → ℝ := fun p ↦
    (intervalDegreeLog W s z r
          (Function.update x (intervalRowIndex j a) p.1) -
        intervalDegreeLog W s z r
          (Function.update x (intervalRowIndex j a) p.2)) ^ 2
  have hFint : Integrable F
      ((physicalRowLaw W μ).prod (physicalRowLaw W μ)) := by
    simpa only [F] using
      intervalDegreeLog_resampling_integrable hμ W s hW z r x j a
  have hp : 0 < 3 * W := by omega
  change (∫ p, F p ∂(physicalRowLaw W μ).prod (physicalRowLaw W μ)) ≤ _
  rw [MeasureTheory.integral_prod F hFint]
  simpa only [F, physicalRowLaw, intervalDegreeLog,
    intervalClearedProduct_update_eq_affineValue, sq_abs,
    physicalRowResamplingEnergy] using
    lemma_10_2_resampling_integral_le_of_pos hμ hp
      (conditionedAffineCenter W s z x r j a)
      (conditionedAffineCoefficient W s z x r j a)

/-! ## Efron--Stein on the `sW` physical-row coordinates -/

/-- Coordinate-free form of the concrete row-resampling integrability
statement.  The product equivalence decodes an arbitrary Efron--Stein
coordinate into its site and within-site row. -/
theorem intervalDegreeLog_resampling_integrable_at_coordinate
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ)
    (r : Fin (2 * W + 1)) (i : Fin (s * W)) (x : IntervalRows W s) :
    Integrable
      (fun p : PhysicalRowAtoms W × PhysicalRowAtoms W ↦
        (intervalDegreeLog W s z r (Function.update x i p.1) -
          intervalDegreeLog W s z r (Function.update x i p.2)) ^ 2)
      ((physicalRowLaw W μ).prod (physicalRowLaw W μ)) := by
  let e : Fin s × Fin W ≃ Fin (s * W) := finProdFinEquiv
  let ja : Fin s × Fin W := e.symm i
  let j : Fin s := ja.1
  let a : Fin W := ja.2
  have hi : intervalRowIndex j a = i := by
    simpa [intervalRowIndex, e, ja, j, a] using e.apply_symm_apply i
  simpa only [hi] using
    intervalDegreeLog_resampling_integrable hμ W s hW z r x j a

/-- Coordinate-free form of the uniform conditional energy estimate. -/
theorem intervalDegreeLog_conditionalCoordinateEnergy_le_at_coordinate
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ)
    (r : Fin (2 * W + 1)) (i : Fin (s * W)) (x : IntervalRows W s) :
    conditionalCoordinateEnergy (μ := physicalRowLaw W μ)
        (intervalDegreeLog W s z r) i x ≤
      physicalRowResamplingEnergy W L := by
  let e : Fin s × Fin W ≃ Fin (s * W) := finProdFinEquiv
  let ja : Fin s × Fin W := e.symm i
  let j : Fin s := ja.1
  let a : Fin W := ja.2
  have hi : intervalRowIndex j a = i := by
    simpa [intervalRowIndex, e, ja, j, a] using e.apply_symm_apply i
  simpa only [hi] using
    intervalDegreeLog_conditionalCoordinateEnergy_le
      hμ W s hW z r x j a

/-- The degree-`r` variance bound with its reusable analytic input exposed. -/
theorem intervalDegreeLog_variance_le_of_memLp
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ)
    (r : Fin (2 * W + 1))
    (hY2 : MemLp (intervalDegreeLog W s z r) 2
      (intervalRowsLaw W s μ)) :
    Var[intervalDegreeLog W s z r; intervalRowsLaw W s μ] ≤
      (1 / 2 : ℝ) *
        ∑ _i : Fin (s * W), physicalRowResamplingEnergy W L := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (physicalRowLaw W μ) := by
    unfold physicalRowLaw
    infer_instance
  have h := efronStein_fin_product (μ := physicalRowLaw W μ) (s * W)
    (measurable_intervalDegreeLog W s z r)
    (by simpa only [intervalRowsLaw] using hY2)
    (fun _i ↦ physicalRowResamplingEnergy W L)
    (fun _i ↦ physicalRowResamplingEnergy_nonneg W L)
    (fun i x ↦
      intervalDegreeLog_resampling_integrable_at_coordinate
        hμ W s hW z r i x)
    (fun i x ↦
      intervalDegreeLog_conditionalCoordinateEnergy_le_at_coordinate
        hμ W s hW z r i x)
  simpa only [intervalRowsLaw] using h

/-- The complete probabilistic composition for Lemma 10.5.  It combines the
concrete row affinity and Lemma 10.2 resampling estimate with Efron--Stein and
the finite-family Cauchy--Schwarz bound.  The remaining hypothesis is exactly
the concrete Hodge `L²` theorem, not an affinity or resampling certificate. -/
theorem intervalDegreeLogs_maxCenteredDeviation_le_of_memLp
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ)
    (hY2 : ∀ r : Fin (2 * W + 1),
      MemLp (intervalDegreeLog W s z r) 2 (intervalRowsLaw W s μ)) :
    (∫ x, maxCenteredDeviation (intervalDegreeLogs W s z)
          (intervalRowsLaw W s μ) x ∂intervalRowsLaw W s μ) ≤
      Real.sqrt
        (∑ _r : Fin (2 * W + 1), (1 / 2 : ℝ) *
          ∑ _i : Fin (s * W), physicalRowResamplingEnergy W L) := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (physicalRowLaw W μ) := by
    unfold physicalRowLaw
    infer_instance
  have h := efronStein_maxCenteredDeviation
    (μ := physicalRowLaw W μ) (s * W) (2 * W)
    (Y := intervalDegreeLogs W s z)
    (fun r ↦ measurable_intervalDegreeLog W s z r)
    (fun r ↦ by
      simpa only [intervalRowsLaw, intervalDegreeLogs] using hY2 r)
    (fun _r _i ↦ physicalRowResamplingEnergy W L)
    (fun _r _i ↦ physicalRowResamplingEnergy_nonneg W L)
    (fun r i x ↦
      intervalDegreeLog_resampling_integrable_at_coordinate
        hμ W s hW z r i x)
    (fun r i x ↦
      intervalDegreeLog_conditionalCoordinateEnergy_le_at_coordinate
        hμ W s hW z r i x)
  simpa only [intervalRowsLaw] using h

/-- The degree-`r` part of Lemma 10.5 with the concrete `L²` input discharged
from bounded density and the interval product itself. -/
theorem intervalDegreeLog_variance_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ)
    (r : Fin (2 * W + 1)) :
    Var[intervalDegreeLog W s z r; intervalRowsLaw W s μ] ≤
      (1 / 2 : ℝ) *
        ∑ _i : Fin (s * W), physicalRowResamplingEnergy W L := by
  exact intervalDegreeLog_variance_le_of_memLp hμ W s hW z r
    (intervalDegreeLog_memLp_two hμ W s hW z r)

/-- Caller-facing Lemma 10.5.  All measurability, row-affinity,
resampling-integrability, and `L²` facts are constructed internally. -/
theorem lemma_10_5
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫ x, maxCenteredDeviation (intervalDegreeLogs W s z)
          (intervalRowsLaw W s μ) x ∂intervalRowsLaw W s μ) ≤
      Real.sqrt
        (∑ _r : Fin (2 * W + 1), (1 / 2 : ℝ) *
          ∑ _i : Fin (s * W), physicalRowResamplingEnergy W L) := by
  apply intervalDegreeLogs_maxCenteredDeviation_le_of_memLp
    hμ W s hW z
  intro r
  exact intervalDegreeLog_memLp_two hμ W s hW z r

end BernoulliSection10
