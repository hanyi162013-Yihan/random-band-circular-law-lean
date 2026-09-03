import CircularLawSection6.GinibreRegularizedCalculus
import CircularLawSection6.RegularizedLogCutoff
import CircularLawSection6.TightApproximation

/-! # Removing the actual matrix regularization in probability

This bridge uses tight negative moments, not an expected negative-moment
bound. A separate regularized-limit theorem is still needed to apply it.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixRegularizedPotential_eq_sum_card (A : Matrix ι ι ℂ) (t : ℝ) :
    matrixRegularizedPotential A t =
      (∑ i : Fin (Fintype.card ι),
        (1 / 2 : ℝ) * Real.log (A.toEuclideanLin.singularValues i ^ 2 + t ^ 2)) /
          (Fintype.card ι : ℝ) := by
  unfold matrixRegularizedPotential matrixSquaredSingularAverage
  simp_rw [regularizedSquaredLog_sq]
  apply congrArg₂ (fun x y : ℝ => x / y)
  · exact Fintype.sum_equiv
      (finCongr (finrank_euclideanSpace (𝕜 := ℂ) (ι := ι))) _ _ (fun _ => rfl)
  · rw [finrank_euclideanSpace]

theorem matrixRawPotential_le_regularized (A : Matrix ι ι ℂ) (hA : A.det ≠ 0) (t : ℝ) :
    matrixRawPotential A ≤ matrixRegularizedPotential A t := by
  rw [matrixRegularizedPotential_eq_sum_card, matrixRawPotential,
    matrix_log_norm_det_eq_sum_log_singularValues A hA]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  exact regularized_log_ge_log
    (A.toEuclideanLin.injective_iff_forall_lt_finrank_singularValues_pos.mp
      (toEuclideanLin_injective_of_det_ne_zero A hA) i
      (by simpa only [finrank_euclideanSpace] using i.isLt))

theorem matrixRegularizedPotential_le_cutoff [Nonempty ι]
    (A : Matrix ι ι ℂ) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    matrixRegularizedPotential A t ≤ matrixCutoffPotential A a + t ^ 2 / (2 * a ^ 2) := by
  have hn : (Module.finrank ℂ (EuclideanSpace ℂ ι) : ℝ) ≠ 0 := by
    simp only [finrank_euclideanSpace]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold matrixRegularizedPotential matrixSquaredSingularAverage
    matrixCutoffPotential operatorCutoffPotential
  simp_rw [regularizedSquaredLog_sq]
  calc
    _ ≤ (∑ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ ι)),
        (Real.log (max (A.toEuclideanLin.singularValues i) a) + t ^ 2 / (2 * a ^ 2))) / _ := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum fun i _ =>
        regularized_log_le_cutoff (A.toEuclideanLin.singularValues_nonneg i) ha ht
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [add_div, mul_div_cancel_left₀ _ hn]

theorem matrixRegularized_raw_error_le_negativeMoment [Nonempty ι]
    (A : Matrix ι ι ℂ) (hA : A.det ≠ 0) {a t p : ℝ}
    (ha : 0 < a) (ht : 0 < t) (hp : 0 < p) :
    |matrixRegularizedPotential A t - matrixRawPotential A| ≤
      (a ^ p / p) * matrixNegativeMoment A p + t ^ 2 / (2 * a ^ 2) := by
  rw [abs_of_nonneg (sub_nonneg.2 (matrixRawPotential_le_regularized A hA t))]
  have hcut := matrixRegularizedPotential_le_cutoff A ha ht
  have hneg := matrixLowerCutoff_le_negativeMoment A hA ha hp
  have hle := le_abs_self (matrixCutoffPotential A a - matrixRawPotential A)
  linarith

theorem matrixRaw_probability_of_regularized_limits
    {Ω ι : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Nonempty (ι n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, Ω n → Matrix (ι n) (ι n) ℂ)
    (hdet : ∀ n, ∀ᵐ ω ∂μ n, (A n ω).det ≠ 0)
    {p : ℝ} (hp : 0 < p)
    (hneg : BoundedInProbabilityTri μ (fun n ω => matrixNegativeMoment (A n ω) p))
    (a t c : ℕ → ℝ) (target : ℝ)
    (ha : ∀ k, 0 < a k) (ht : ∀ k, 0 < t k)
    (ha0 : Tendsto a atTop (𝓝 0))
    (hscale : Tendsto (fun k => t k ^ 2 / (2 * a k ^ 2)) atTop (𝓝 0))
    (hc : Tendsto c atTop (𝓝 target))
    (hreg : ∀ k, TendstoInProbabilityTri μ
      (fun n ω => matrixRegularizedPotential (A n ω) (t k)) (c k)) :
    TendstoInProbabilityTri μ (fun n ω => matrixRawPotential (A n ω)) target := by
  apply tendstoInProbabilityTri_of_tight_approximations μ
    (fun n ω => matrixRawPotential (A n ω))
    (fun n ω => matrixNegativeMoment (A n ω) p)
    (fun k n ω => matrixRegularizedPotential (A n ω) (t k))
    c (fun k => a k ^ p / p) (fun k => t k ^ 2 / (2 * a k ^ 2)) target
    hneg (ShortRingAnchor.rpow_div_tendsto_zero ha0 hp) hscale hc hreg
  intro k n
  filter_upwards [hdet n] with ω hω
  have hcoef : 0 ≤ a k ^ p / p :=
    div_nonneg (Real.rpow_nonneg (ha k).le p) hp.le
  have hb : 0 ≤ t k ^ 2 / (2 * a k ^ 2) := by positivity
  rw [abs_of_nonneg hcoef, abs_of_nonneg hb, abs_sub_comm]
  exact (matrixRegularized_raw_error_le_negativeMoment (A n ω) hω (ha k) (ht k) hp).trans
    (add_le_add (mul_le_mul_of_nonneg_left (le_abs_self _) hcoef) le_rfl)

end CircularLawSection6
