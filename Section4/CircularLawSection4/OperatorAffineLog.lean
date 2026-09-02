import CircularLawSection4.ProductSmallBall
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Deterministic and one-coordinate core of the operator-affine logarithm lemma

The manuscript chooses a coefficient operator at the natural scale, tests it
with almost norming vectors, freezes all other coordinates, and applies a
scalar bounded-density small-ball estimate.  This file formalizes those
steps for continuous linear maps over `ℝ` and `ℂ`.

It also records the deterministic positive-log reduction and abstract
positive/negative logarithmic second-moment closure.  The analytic
integration of the small-ball tail and the moment bound for the random sum
remain explicit upstream hypotheses.
-/

open scoped BigOperators ENNReal Real
open MeasureTheory Set

namespace CircularLawSection4

universe u v w x

section Scale

variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
variable {E : Type w} {F : Type x}
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- Largest weighted coefficient-operator norm. -/
noncomputable def operatorCoefficientMax (b : ι → 𝕜)
    (M : ι → E →L[𝕜] F) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => ‖b i‖ * ‖M i‖

/-- Natural scale in the operator-affine logarithm lemma. -/
noncomputable def operatorAffineScale (i₀ : ι) (b : ι → 𝕜)
    (M : ι → E →L[𝕜] F) : ℝ :=
  max ‖M i₀‖ (operatorCoefficientMax b M)

theorem weighted_operator_norm_le_coefficientMax
    (b : ι → 𝕜) (M : ι → E →L[𝕜] F) (i : ι) :
    ‖b i‖ * ‖M i‖ ≤ operatorCoefficientMax b M := by
  exact Finset.le_sup' (fun j => ‖b j‖ * ‖M j‖) (Finset.mem_univ i)

theorem weighted_operator_norm_le_scale
    (i₀ : ι) (b : ι → 𝕜) (M : ι → E →L[𝕜] F) (i : ι) :
    ‖b i‖ * ‖M i‖ ≤ operatorAffineScale i₀ b M :=
  (weighted_operator_norm_le_coefficientMax b M i).trans (le_max_right _ _)

theorem distinguished_operator_norm_le_scale
    (i₀ : ι) (b : ι → 𝕜) (M : ι → E →L[𝕜] F) :
    ‖M i₀‖ ≤ operatorAffineScale i₀ b M :=
  le_max_left _ _

/-- The scale is attained either by a weighted coefficient or by the
distinguished operator.  A lower bound on the distinguished scalar
coefficient therefore produces a large affine slope in both cases. -/
theorem exists_weighted_operator_ge_fraction_scale
    (i₀ : ι) (b : ι → 𝕜) (M : ι → E →L[𝕜] F)
    {q : ℝ} (hq1 : q ≤ 1) (hb₀ : q ≤ ‖b i₀‖) :
    ∃ i : ι, q * operatorAffineScale i₀ b M ≤ ‖b i‖ * ‖M i‖ := by
  classical
  by_cases hdom : operatorCoefficientMax b M ≤ ‖M i₀‖
  · refine ⟨i₀, ?_⟩
    rw [operatorAffineScale, max_eq_left hdom]
    exact mul_le_mul_of_nonneg_right hb₀ (norm_nonneg _)
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup'
      (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty)
      (fun j => ‖b j‖ * ‖M j‖)
    refine ⟨i, ?_⟩
    have hi' : operatorCoefficientMax b M = ‖b i‖ * ‖M i‖ := by
      simpa only [operatorCoefficientMax] using hi
    rw [operatorAffineScale, max_eq_right (le_of_not_ge hdom), hi']
    nlinarith [mul_nonneg (norm_nonneg (b i)) (norm_nonneg (M i))]

end Scale

section NormingTest

variable {𝕜 : Type v} [RCLike 𝕜]
variable {E : Type u} {F : Type w}
variable [NormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- A scalar functional tested on a vector of norm at most one is bounded by
the operator norm. -/
theorem scalar_test_le_operator_norm
    (T : E →L[𝕜] F) (x : E) (ell : StrongDual 𝕜 F)
    (hx : ‖x‖ ≤ 1) (hell : ‖ell‖ ≤ 1) :
    ‖ell (T x)‖ ≤ ‖T‖ := by
  calc
    ‖ell (T x)‖ ≤ ‖ell‖ * ‖T x‖ := ell.le_opNorm _
    _ ≤ 1 * (‖T‖ * ‖x‖) := by
      gcongr
      exact T.le_opNorm x
    _ ≤ ‖T‖ := by
      simp only [one_mul]
      nlinarith [norm_nonneg T, norm_nonneg x]

/-- Continuous operators over `ℝ` or `ℂ` have an arbitrarily close scalar
norming test. -/
theorem exists_approx_operator_norming_test
    (T : E →L[𝕜] F) {κ : ℝ} (_hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hT : 0 < ‖T‖) :
    ∃ x : E, ∃ ell : StrongDual 𝕜 F,
      ‖x‖ < 1 ∧ ‖ell‖ ≤ 1 ∧ κ * ‖T‖ < ‖ell (T x)‖ := by
  have hr : κ * ‖T‖ < ‖T‖ := by nlinarith
  obtain ⟨x, hx, hTx⟩ := T.exists_lt_apply_of_lt_opNorm hr
  obtain ⟨ell, hell, hv⟩ := exists_dual_vector'' 𝕜 (T x)
  refine ⟨x, ell, hx, hell, ?_⟩
  rw [hv]
  simpa using hTx

end NormingTest

section LargeSlope

variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable {𝕜 : Type v} [RCLike 𝕜]
variable {E : Type w} {F : Type x}
variable [NormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- Maximum-coefficient selection followed by approximate operator-norm
testing produces a genuinely large scalar affine slope. -/
theorem exists_large_scalarized_slope
    (i₀ : ι) (b : ι → 𝕜) (M : ι → E →L[𝕜] F)
    {q κ : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hb₀ : q ≤ ‖b i₀‖)
    (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hscale : 0 < operatorAffineScale i₀ b M) :
    ∃ s : ι, ∃ x : E, ∃ ell : StrongDual 𝕜 F,
      ‖x‖ < 1 ∧ ‖ell‖ ≤ 1 ∧
        κ * q * operatorAffineScale i₀ b M < ‖b s * ell (M s x)‖ := by
  obtain ⟨s, hs⟩ :=
    exists_weighted_operator_ge_fraction_scale i₀ b M hq1 hb₀
  have hcoeff : 0 < ‖b s‖ * ‖M s‖ :=
    (mul_pos hq0 hscale).trans_le hs
  have hb : 0 < ‖b s‖ := by
    nlinarith [norm_nonneg (b s), norm_nonneg (M s)]
  have hM : 0 < ‖M s‖ := by
    nlinarith [norm_nonneg (b s), norm_nonneg (M s)]
  obtain ⟨x, ell, hx, hell, htest⟩ :=
    exists_approx_operator_norming_test (M s) hκ0.le hκ1 hM
  refine ⟨s, x, ell, hx, hell, ?_⟩
  calc
    κ * q * operatorAffineScale i₀ b M =
        κ * (q * operatorAffineScale i₀ b M) := by ring
    _ ≤ κ * (‖b s‖ * ‖M s‖) :=
      mul_le_mul_of_nonneg_left hs hκ0.le
    _ = ‖b s‖ * (κ * ‖M s‖) := by ring
    _ < ‖b s‖ * ‖ell (M s x)‖ := mul_lt_mul_of_pos_left htest hb
    _ = ‖b s * ell (M s x)‖ := (norm_mul _ _).symm

end LargeSlope

section OperatorAffine

variable {ι : Type u} [Fintype ι]
variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
variable {E : Type w} {F : Type x}
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- Finite operator-valued affine expression. -/
noncomputable def operatorAffine
    (b ξ : ι → 𝕜) (M : ι → E →L[𝕜] F) (z : 𝕜) (M₀ : E →L[𝕜] F) :
    E →L[𝕜] F :=
  (∑ i, (b i * ξ i) • M i) - z • M₀

/-- The part left after freezing all coordinates except `s`. -/
noncomputable def operatorAffineRest [DecidableEq ι]
    (s : ι) (b ξ : ι → 𝕜) (M : ι → E →L[𝕜] F)
    (z : 𝕜) (M₀ : E →L[𝕜] F) : E →L[𝕜] F :=
  (∑ i ∈ Finset.univ.erase s, (b i * ξ i) • M i) - z • M₀

theorem operatorAffine_eq_rest_add [DecidableEq ι]
    (s : ι) (b ξ : ι → 𝕜) (M : ι → E →L[𝕜] F)
    (z : 𝕜) (M₀ : E →L[𝕜] F) :
    operatorAffine b ξ M z M₀ =
      operatorAffineRest s b ξ M z M₀ + (b s * ξ s) • M s := by
  rw [operatorAffine, operatorAffineRest]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ s)]
  abel

/-- Scalarization of the single unfrozen coordinate. -/
theorem scalarize_operatorAffine_oneCoordinate
    (R M : E →L[𝕜] F) (b u : 𝕜) (x : E) (ell : F →L[𝕜] 𝕜) :
    ell ((R + (b * u) • M) x) = ell (R x) + u * (b * ell (M x)) := by
  simp only [add_apply, smul_apply, map_add, map_smul]
  ring

/-- Deterministic positive-tail reduction used in the manuscript. -/
theorem operatorAffine_norm_le_scale_mul_sum
    [Nonempty ι] (i₀ : ι) (b ξ : ι → 𝕜)
    (M : ι → E →L[𝕜] F) (z : 𝕜) :
    ‖operatorAffine b ξ M z (M i₀)‖ ≤
      operatorAffineScale i₀ b M * (∑ i, ‖ξ i‖ + ‖z‖) := by
  classical
  calc
    ‖operatorAffine b ξ M z (M i₀)‖ ≤
        ‖∑ i, (b i * ξ i) • M i‖ + ‖z • M i₀‖ := by
      exact norm_sub_le _ _
    _ ≤ (∑ i, ‖(b i * ξ i) • M i‖) + ‖z • M i₀‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (∑ i, operatorAffineScale i₀ b M * ‖ξ i‖) +
        operatorAffineScale i₀ b M * ‖z‖ := by
      gcongr with i
      · rw [norm_smul, norm_mul]
        calc
          ‖b i‖ * ‖ξ i‖ * ‖M i‖ = (‖b i‖ * ‖M i‖) * ‖ξ i‖ := by ring
          _ ≤ operatorAffineScale i₀ b M * ‖ξ i‖ := by
            gcongr
            exact weighted_operator_norm_le_scale i₀ b M i
      · rw [norm_smul]
        calc
          ‖z‖ * ‖M i₀‖ ≤ ‖z‖ * operatorAffineScale i₀ b M := by
            gcongr
            exact distinguished_operator_norm_le_scale i₀ b M
          _ = operatorAffineScale i₀ b M * ‖z‖ := mul_comm _ _
    _ = operatorAffineScale i₀ b M * (∑ i, ‖ξ i‖ + ‖z‖) := by
      rw [mul_add, Finset.mul_sum]

end OperatorAffine

section OneCoordinateSmallBall

variable {E : Type w} {F : Type x}

/-- Testing a real operator-affine expression by fixed almost-norming vectors
reduces its lower tail to the scalar affine interval estimate. -/
theorem real_operatorAffine_oneCoordinate_smallBall
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    {ν : Measure ℝ} {L : ℝ≥0∞} (hν : RealIntervalBound ν L)
    (R M : E →L[ℝ] F) (b : ℝ) (x : E) (ell : StrongDual ℝ F)
    (hx : ‖x‖ ≤ 1) (hell : ‖ell‖ ≤ 1)
    {ε ρ : ℝ} (hρ : 0 ≤ ρ) (hε : 0 < ε)
    (hslope : ε ≤ |b * ell (M x)|) :
    ν {u | ‖R + (b * u) • M‖ ≤ ε * ρ} ≤
      (2 : ℝ≥0∞) * L * ENNReal.ofReal ρ := by
  have hsub :
      {u | ‖R + (b * u) • M‖ ≤ ε * ρ} ⊆
        {u | |ell (R x) + u * (b * ell (M x))| ≤ ε * ρ} := by
    intro u hu
    have htest := scalar_test_le_operator_norm (R + (b * u) • M) x ell hx hell
    have hscalar :
        ell ((R + (b * u) • M) x) =
          ell (R x) + u * (b * ell (M x)) :=
      scalarize_operatorAffine_oneCoordinate R M b u x ell
    change |ell (R x) + u * (b * ell (M x))| ≤ ε * ρ
    rw [← hscalar, ← Real.norm_eq_abs]
    exact htest.trans hu
  calc
    ν {u | ‖R + (b * u) • M‖ ≤ ε * ρ} ≤
        ν {u | |ell (R x) + u * (b * ell (M x))| ≤ ε * ρ} :=
      measure_mono hsub
    _ ≤ (2 : ℝ≥0∞) * L * ENNReal.ofReal ρ :=
      real_affine_smallBall_of_intervalBound hν hρ hε hslope

/-- Complex analogue using the planar disk estimate. -/
theorem complex_operatorAffine_oneCoordinate_smallBall
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    {ν : Measure ℂ} {L : ℝ≥0∞} (hν : ComplexBallBound ν L)
    (R M : E →L[ℂ] F) (b : ℂ) (x : E) (ell : StrongDual ℂ F)
    (hx : ‖x‖ ≤ 1) (hell : ‖ell‖ ≤ 1)
    {ε ρ : ℝ} (hρ : 0 ≤ ρ) (hε : 0 < ε)
    (hslope : ε ≤ ‖b * ell (M x)‖) :
    ν {u | ‖R + (b * u) • M‖ ≤ ε * ρ} ≤
      ENNReal.ofReal Real.pi * L * ENNReal.ofReal ρ ^ 2 := by
  have hsub :
      {u | ‖R + (b * u) • M‖ ≤ ε * ρ} ⊆
        {u | ‖ell (R x) + u * (b * ell (M x))‖ ≤ ε * ρ} := by
    intro u hu
    have htest := scalar_test_le_operator_norm (R + (b * u) • M) x ell hx hell
    have hscalar :
        ell ((R + (b * u) • M) x) =
          ell (R x) + u * (b * ell (M x)) :=
      scalarize_operatorAffine_oneCoordinate R M b u x ell
    change ‖ell (R x) + u * (b * ell (M x))‖ ≤ ε * ρ
    rw [← hscalar]
    exact htest.trans hu
  calc
    ν {u | ‖R + (b * u) • M‖ ≤ ε * ρ} ≤
        ν {u | ‖ell (R x) + u * (b * ell (M x))‖ ≤ ε * ρ} :=
      measure_mono hsub
    _ ≤ ENNReal.ofReal Real.pi * L * ENNReal.ofReal ρ ^ 2 :=
      complex_affine_smallBall_of_ballBound hν hρ hε hslope

end OneCoordinateSmallBall

end CircularLawSection4
