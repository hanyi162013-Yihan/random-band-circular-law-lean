import CircularLawSection6.PublishedLimitingHardEdge
import CircularLawSection6.SingularValueMeasurability
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Finite-matrix regularized logarithmic calculus

The regularization is the actual squared-singular-value average
`(1 / (2 N)) ∑ log (sᵢ² + t²)`.  Its height derivative is the imaginary
part of the actual Hermitized Stieltjes trace.  At large height its excess
over `log t` is nonnegative and is bounded by the normalized matrix energy
divided by `2 t²`.

All statements include singular matrices.  No limiting singular law,
eigenvalue correlation formula, raw logarithmic limit, or BBV comparison
is assumed.  The last integrability lemma only uses finite expected energy.
-/

open MeasureTheory Module InnerProductSpace Arxiv2410V3 TaoVuReplacement
open scoped BigOperators InnerProductSpace

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

/-- The continuous test of the squared singular values at positive height.
The `max` extends the test to all real inputs without changing its value
on the squared singular values. -/
def regularizedSquaredLog (t x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (max x 0 + t ^ 2)

/-- The actual regularized logarithmic potential of a finite matrix. -/
def matrixRegularizedPotential {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (t : ℝ) : ℝ :=
  matrixSquaredSingularAverage A (regularizedSquaredLog t)

theorem regularizedSquaredLog_sq (t s : ℝ) :
    regularizedSquaredLog t (s ^ 2) =
      (1 / 2 : ℝ) * Real.log (s ^ 2 + t ^ 2) := by
  simp only [regularizedSquaredLog, max_eq_left (sq_nonneg s)]

theorem continuous_regularizedSquaredLog {t : ℝ} (ht : 0 < t) :
    Continuous (regularizedSquaredLog t) := by
  apply Continuous.const_mul
  apply Continuous.log (by fun_prop)
  intro x
  exact (add_pos_of_nonneg_of_pos (le_max_right x 0) (sq_pos_of_pos ht)).ne'

/-- Differentiation of the scalar regularization gives the squared
Poisson test used by the existing Stieltjes interface. -/
theorem hasDerivAt_regularizedSquaredLog (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => regularizedSquaredLog u x) (squaredPoissonTest t x) t := by
  have hq : HasDerivAt (fun u : ℝ => max x 0 + u ^ 2) (2 * t) t := by
    simpa using ((hasDerivAt_id t).pow 2).const_add (max x 0)
  have hpos : 0 < max x 0 + t ^ 2 :=
    add_pos_of_nonneg_of_pos (le_max_right x 0) (sq_pos_of_pos ht)
  refine ((hq.log hpos.ne').const_mul (1 / 2 : ℝ)).congr_deriv ?_
  dsimp [squaredPoissonTest]
  ring

theorem regularizedSquaredLog_sub_log_eq (x : ℝ) {t : ℝ} (ht : 0 < t) :
    regularizedSquaredLog t x - Real.log t =
      (1 / 2 : ℝ) * Real.log ((max x 0 + t ^ 2) / t ^ 2) := by
  have hpos : 0 < max x 0 + t ^ 2 :=
    add_pos_of_nonneg_of_pos (le_max_right x 0) (sq_pos_of_pos ht)
  rw [regularizedSquaredLog, Real.log_div hpos.ne' (pow_ne_zero 2 ht.ne'),
    Real.log_pow]
  ring

/-- The scalar upper bound follows from `log (1 + y) ≤ y`; there is no
lower bound on the singular value. -/
theorem regularizedSquaredLog_highHeight (x : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ regularizedSquaredLog t x - Real.log t ∧
      regularizedSquaredLog t x - Real.log t ≤ max x 0 / (2 * t ^ 2) := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hx : 0 ≤ max x 0 := le_max_right x 0
  have hpos : 0 < max x 0 + t ^ 2 := add_pos_of_nonneg_of_pos hx ht2
  have hratio : 1 ≤ (max x 0 + t ^ 2) / t ^ 2 := by
    apply (le_div_iff₀ ht2).2
    linarith
  rw [regularizedSquaredLog_sub_log_eq x ht]
  constructor
  · exact mul_nonneg (by norm_num) (Real.log_nonneg hratio)
  · calc
      (1 / 2 : ℝ) * Real.log ((max x 0 + t ^ 2) / t ^ 2) ≤
          (1 / 2 : ℝ) * ((max x 0 + t ^ 2) / t ^ 2 - 1) :=
        mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hpos ht2))
          (by norm_num)
      _ = max x 0 / (2 * t ^ 2) := by
        field_simp [ht.ne'] <;> ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An unconditional energy identity, proved from the trace of `A* A`.
Unlike a construction of positive singular bases, this includes zero
singular values and needs no nonsingularity premise. -/
theorem sum_sq_singularValues_eq_hilbertSchmidtSq (A : Matrix ι ι ℂ) :
    (∑ i : Fin (finrank ℂ (EuclideanSpace ℂ ι)),
      A.toEuclideanLin.singularValues i ^ 2) = hilbertSchmidtSq A := by
  let T := A.toEuclideanLin
  have heig :
      (∑ i : Fin (finrank ℂ (EuclideanSpace ℂ ι)), T.singularValues i ^ 2) =
        ∑ i : Fin (finrank ℂ (EuclideanSpace ℂ ι)),
          T.isSymmetric_adjoint_comp_self.eigenvalues rfl i := by
    apply Finset.sum_congr rfl
    intro i _
    exact T.sq_singularValues_fin rfl i
  change (∑ i : Fin (finrank ℂ (EuclideanSpace ℂ ι)), T.singularValues i ^ 2) = _
  rw [heig, ← T.isSymmetric_adjoint_comp_self.re_trace_eq_sum_eigenvalues rfl]
  have htrace :
      RCLike.re ((T.adjoint ∘ₗ T).trace ℂ (EuclideanSpace ℂ ι)) =
        ∑ j : ι, ‖T (EuclideanSpace.basisFun ι ℂ j)‖ ^ 2 := by
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun ι ℂ), map_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [LinearMap.adjoint_inner_right, inner_self_eq_norm_sq]
  rw [htrace]
  have hcol : ∀ j : ι, ‖T (EuclideanSpace.basisFun ι ℂ j)‖ ^ 2 =
      ∑ i : ι, ‖A i j‖ ^ 2 := by
    intro j
    rw [EuclideanSpace.norm_sq_eq]
    simp [T, Matrix.toLpLin_apply]
  rw [Finset.sum_congr rfl (fun j _ => hcol j)]
  unfold hilbertSchmidtSq
  exact Finset.sum_comm

/-- The derivative with respect to positive height, in the existing
averaged squared-singular-value normalization. -/
theorem hasDerivAt_matrixRegularizedPotential (A : Matrix ι ι ℂ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (matrixRegularizedPotential A)
      (matrixSquaredSingularAverage A (squaredPoissonTest t)) t := by
  unfold matrixRegularizedPotential matrixSquaredSingularAverage
  apply HasDerivAt.div_const
  exact HasDerivAt.fun_sum fun i _ =>
    hasDerivAt_regularizedSquaredLog (A.toEuclideanLin.singularValues i ^ 2) ht

/-- Exact derivative-to-Stieltjes bridge for the actual shifted matrix. -/
theorem hasDerivAt_shifted_matrixRegularizedPotential {N : ℕ} [NeZero N]
    (X : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (matrixRegularizedPotential (X - z • 1))
      (stieltjesTrace X z (spectralParameter 0 t)).im t := by
  rw [matrix_stieltjes_im_eq_squaredPoissonAverage X z ht]
  exact hasDerivAt_matrixRegularizedPotential (X - z • 1) ht

/-- The same derivative with the `i t` spelling used by the Ginibre
Dyson module. -/
theorem hasDerivAt_shifted_matrixRegularizedPotential_I_mul {N : ℕ} [NeZero N]
    (X : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (matrixRegularizedPotential (X - z • 1))
      (stieltjesTrace X z (Complex.I * (t : ℂ))).im t := by
  simpa only [spectralParameter, Complex.ofReal_zero, zero_add, mul_comm] using
    hasDerivAt_shifted_matrixRegularizedPotential X z ht

theorem continuousOn_matrixRegularizedPotential_height (A : Matrix ι ι ℂ) :
    ContinuousOn (matrixRegularizedPotential A) (Set.Ioi 0) := by
  intro t ht
  exact (hasDerivAt_matrixRegularizedPotential A ht).continuousAt.continuousWithinAt

/-- For positive height the regularized potential is continuous in the
actual entries, even where a singular value vanishes. -/
theorem continuous_matrixRegularizedPotential {t : ℝ} (ht : 0 < t) :
    Continuous (fun A : Matrix ι ι ℂ => matrixRegularizedPotential A t) := by
  unfold matrixRegularizedPotential matrixSquaredSingularAverage
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  have hi : i.val < Fintype.card ι := by
    simpa only [finrank_euclideanSpace] using i.isLt
  exact (continuous_regularizedSquaredLog ht).comp
    ((continuous_matrix_singularValue (ι := ι) ⟨i.val, hi⟩).pow 2)

theorem measurable_matrixRegularizedPotential {t : ℝ} (ht : 0 < t) :
    Measurable (fun A : Matrix ι ι ℂ => matrixRegularizedPotential A t) :=
  (continuous_matrixRegularizedPotential ht).measurable

theorem matrixRegularizedPotential_sub_log_eq [Nonempty ι]
    (A : Matrix ι ι ℂ) (t : ℝ) :
    matrixRegularizedPotential A t - Real.log t =
      (∑ i : Fin (finrank ℂ (EuclideanSpace ℂ ι)),
        (regularizedSquaredLog t (A.toEuclideanLin.singularValues i ^ 2) - Real.log t)) /
          (finrank ℂ (EuclideanSpace ℂ ι) : ℝ) := by
  have hn : (finrank ℂ (EuclideanSpace ℂ ι) : ℝ) ≠ 0 := by
    simp only [finrank_euclideanSpace]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold matrixRegularizedPotential matrixSquaredSingularAverage
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [sub_div, mul_div_cancel_left₀ _ hn]

/-- The large-height anchor of the actual finite matrix.  The error is
controlled solely by its normalized Hilbert--Schmidt energy. -/
theorem matrixRegularizedPotential_highHeight [Nonempty ι]
    (A : Matrix ι ι ℂ) {t : ℝ} (ht : 0 < t) :
    0 ≤ matrixRegularizedPotential A t - Real.log t ∧
      matrixRegularizedPotential A t - Real.log t ≤
        hilbertSchmidtSq A / (2 * (Fintype.card ι : ℝ) * t ^ 2) := by
  rw [matrixRegularizedPotential_sub_log_eq]
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ =>
      (regularizedSquaredLog_highHeight (A.toEuclideanLin.singularValues i ^ 2) ht).1)
      (Nat.cast_nonneg _)
  · calc
      _ ≤ (∑ i : Fin (finrank ℂ (EuclideanSpace ℂ ι)),
          A.toEuclideanLin.singularValues i ^ 2 / (2 * t ^ 2)) /
            (finrank ℂ (EuclideanSpace ℂ ι) : ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro i _
        simpa only [max_eq_left (sq_nonneg _)] using
          (regularizedSquaredLog_highHeight (A.toEuclideanLin.singularValues i ^ 2) ht).2
      _ = hilbertSchmidtSq A / (2 * (Fintype.card ι : ℝ) * t ^ 2) := by
        rw [← Finset.sum_div, sum_sq_singularValues_eq_hilbertSchmidtSq]
        simp only [finrank_euclideanSpace]
        ring

theorem abs_matrixRegularizedPotential_sub_log_le [Nonempty ι]
    (A : Matrix ι ι ℂ) {t : ℝ} (ht : 0 < t) :
    |matrixRegularizedPotential A t - Real.log t| ≤
      hilbertSchmidtSq A / (2 * (Fintype.card ι : ℝ) * t ^ 2) := by
  rw [abs_of_nonneg (matrixRegularizedPotential_highHeight A ht).1]
  exact (matrixRegularizedPotential_highHeight A ht).2

/-- Finite expected entrywise energy suffices to integrate the actual
regularized potential.  This is not a raw-log integrability premise. -/
theorem integrable_matrixRegularizedPotential [Nonempty ι]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {A : Ω → Matrix ι ι ℂ} (hA : Measurable A)
    (hE : Integrable (fun ω => hilbertSchmidtSq (A ω)) μ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun ω => matrixRegularizedPotential (A ω) t) μ := by
  have henv : Integrable (fun ω => |Real.log t| +
      hilbertSchmidtSq (A ω) / (2 * (Fintype.card ι : ℝ) * t ^ 2)) μ :=
    (integrable_const |Real.log t|).add (hE.div_const _)
  apply henv.mono' ((measurable_matrixRegularizedPotential ht).comp hA).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  calc
    |matrixRegularizedPotential (A ω) t| =
        |(matrixRegularizedPotential (A ω) t - Real.log t) + Real.log t| := by
      congr 1
      ring
    _ ≤ |matrixRegularizedPotential (A ω) t - Real.log t| + |Real.log t| :=
      abs_add _ _
    _ ≤ hilbertSchmidtSq (A ω) / (2 * (Fintype.card ι : ℝ) * t ^ 2) + |Real.log t| :=
      add_le_add_right (abs_matrixRegularizedPotential_sub_log_le (A ω) ht) _
    _ = _ := add_comm _ _

end CircularLawSection6
