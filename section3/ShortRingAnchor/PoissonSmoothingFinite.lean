import ShortRingAnchor.PoissonSmoothingKernel
import ShortRingAnchor.ClippedLog

/-!
# Lemma 3.5: finite empirical laws and exact Poisson smoothing

These are finite sums, so the spectral measure, all integrability facts,
and interchange of smoothing and averaging are proved rather than assumed.
-/

open Set MeasureTheory
open scoped BigOperators Interval

noncomputable section
namespace ShortRingAnchor
open Arxiv2410V3

/-- Lemma 3.5: mass of a closed interval under the finite empirical law. -/
def empiricalIntervalMass {I : Type*} [Fintype I] (s : I → ℝ) (a b : ℝ) : ℝ :=
  empiricalAverage s (closedIntervalIndicator a b)

/-- Lemma 3.5: the corresponding Poisson-smoothed interval mass. -/
def empiricalSmoothedMass {I : Type*} [Fintype I] (s : I → ℝ) (v a b : ℝ) : ℝ :=
  empiricalAverage s (poissonWindow v a b)

/-- Lemma 3.5: finite averaging preserves pointwise inequalities. -/
theorem smoothing_empiricalAverage_mono {I : Type*} [Fintype I]
    (s : I → ℝ) {f g : ℝ → ℝ} (h : ∀ x, f x ≤ g x) :
    empiricalAverage s f ≤ empiricalAverage s g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => h (s i)))
    (Nat.cast_nonneg _)

/-- Lemma 3.5: the finite empirical law has total mass one. -/
theorem smoothing_empiricalAverage_add_const {I : Type*} [Fintype I] [Nonempty I]
    (s : I → ℝ) (f : ℝ → ℝ) (c : ℝ) :
    empiricalAverage s (fun x => f x + c) = empiricalAverage s f + c := by
  have hn : (Fintype.card I : ℝ) ≠ 0 := by positivity
  simp [empiricalAverage, Finset.sum_add_distrib, add_div, hn]

/-- Lemma 3.5, empirical upper smoothing inequality, with endpoint atoms included. -/
theorem empiricalIntervalMass_le_smoothed_enlarged {I : Type*}
    [Fintype I] [Nonempty I] (s : I → ℝ) {v delta a b : ℝ}
    (hv : 0 < v) (hd : 0 < delta) (hab : a ≤ b) :
    empiricalIntervalMass s a b ≤ empiricalSmoothedMass s v (a - delta) (b + delta) +
      2 * (v / delta) / Real.pi := by
  exact (smoothing_empiricalAverage_mono s
    (closedIntervalIndicator_le_poissonWindow_enlarged_add_tail hv hd hab)).trans_eq
      (smoothing_empiricalAverage_add_const _ _ _)

/-- Lemma 3.5, empirical lower smoothing inequality. -/
theorem empiricalSmoothedMass_le_interval_enlarged {I : Type*}
    [Fintype I] [Nonempty I] (s : I → ℝ) {v delta a b : ℝ}
    (hv : 0 < v) (hd : 0 < delta) :
    empiricalSmoothedMass s v a b ≤ empiricalIntervalMass s (a - delta) (b + delta) +
      2 * (v / delta) / Real.pi := by
  exact (smoothing_empiricalAverage_mono s
    (poissonWindow_le_closedIntervalIndicator_enlarged_add_tail hv hd)).trans_eq
      (smoothing_empiricalAverage_add_const _ _ _)

/-- Lemma 3.5: imaginary Stieltjes transforms of finite spectra are continuous at fixed height. -/
theorem continuous_empiricalStieltjes_im {I : Type*} [Fintype I]
    (s : I → ℝ) {v : ℝ} (hv : 0 < v) :
    Continuous (fun u => (empiricalStieltjes s (spectralParameter u v)).im) := by
  simp_rw [empiricalStieltjes_im]
  exact (continuous_finsetSum _ (fun i _ => continuous_poissonKernel_shift hv (s i))).div_const _

/-- Lemma 3.5: smoothing equals the compact integral of the actual empirical Stieltjes transform. -/
theorem empiricalSmoothedMass_eq_integral_im {I : Type*} [Fintype I]
    (s : I → ℝ) {v : ℝ} (hv : 0 < v) (a b : ℝ) :
    empiricalSmoothedMass s v a b =
      (∫ u in a..b, (empiricalStieltjes s (spectralParameter u v)).im) / Real.pi := by
  unfold empiricalSmoothedMass empiricalAverage
  simp_rw [poissonWindow_eq_integral hv]
  rw [← Finset.sum_div, ← intervalIntegral.integral_finsetSum
    (fun i _ => (continuous_poissonKernel_shift hv (s i)).intervalIntegrable a b)]
  rw [div_right_comm, ← intervalIntegral.integral_div]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  exact (empiricalStieltjes_im s u v).symm

/-- Lemma 3.5: a compact imaginary Stieltjes bound controls smoothed mass by interval length. -/
theorem empiricalSmoothedMass_le_length_mul {I : Type*} [Fintype I]
    (s : I → ℝ) {v a b C : ℝ} (hv : 0 < v) (hab : a ≤ b)
    (hbound : ∀ u ∈ Icc a b, (empiricalStieltjes s (spectralParameter u v)).im ≤ C) :
    empiricalSmoothedMass s v a b ≤ (b - a) * C / Real.pi := by
  rw [empiricalSmoothedMass_eq_integral_im s hv]
  have h := intervalIntegral.integral_mono_on hab
    ((continuous_empiricalStieltjes_im s hv).intervalIntegrable (μ := volume) a b)
    (intervalIntegrable_const (c := C)) hbound
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using
    div_le_div_of_nonneg_right h Real.pi_pos.le

/-- Lemma 3.5: compact Stieltjes comparison controls the difference of smoothed interval masses. -/
theorem empiricalSmoothedMass_le_comparison {I J : Type*} [Fintype I] [Fintype J]
    (s : I → ℝ) (t : J → ℝ) {v a b E : ℝ} (hv : 0 < v) (hab : a ≤ b)
    (hcompare : ∀ u ∈ Icc a b,
      ‖empiricalStieltjes s (spectralParameter u v) -
        empiricalStieltjes t (spectralParameter u v)‖ ≤ E) :
    empiricalSmoothedMass s v a b ≤ empiricalSmoothedMass t v a b +
      (b - a) * E / Real.pi := by
  have hs := (continuous_empiricalStieltjes_im s hv).intervalIntegrable (μ := volume) a b
  have ht := (continuous_empiricalStieltjes_im t hv).intervalIntegrable (μ := volume) a b
  have he := intervalIntegrable_const (c := E) (μ := volume) (a := a) (b := b)
  have h := intervalIntegral.integral_mono_on hab hs (ht.add he) (fun u hu => by
    have hi := (Complex.im_le_norm
      (empiricalStieltjes s (spectralParameter u v) -
        empiricalStieltjes t (spectralParameter u v))).trans (hcompare u hu)
    rw [Complex.sub_im] at hi
    linarith)
  rw [intervalIntegral.integral_add ht he, intervalIntegral.integral_const] at h
  rw [empiricalSmoothedMass_eq_integral_im s hv, empiricalSmoothedMass_eq_integral_im t hv]
  exact (div_le_div_of_nonneg_right h Real.pi_pos.le).trans_eq (by simp [add_div])

/-- Lemma 3.5: interval enlargement adds only the two endpoint windows.
This inequality is valid even when there are atoms at an endpoint. -/
theorem empiricalIntervalMass_enlarged_le {I : Type*} [Fintype I]
    (s : I → ℝ) (a b delta : ℝ) :
    empiricalIntervalMass s (a - 2 * delta) (b + 2 * delta) ≤
      empiricalIntervalMass s a b + empiricalIntervalMass s (a - 2 * delta) a +
        empiricalIntervalMass s b (b + 2 * delta) := by
  have hnonneg (a b x : ℝ) : 0 ≤ closedIntervalIndicator a b x := by
    unfold closedIntervalIndicator
    split_ifs <;> norm_num
  have hpoint (x : ℝ) :
      closedIntervalIndicator (a - 2 * delta) (b + 2 * delta) x ≤
        closedIntervalIndicator a b x + closedIntervalIndicator (a - 2 * delta) a x +
          closedIntervalIndicator b (b + 2 * delta) x := by
    by_cases hout : a - 2 * delta ≤ x ∧ x ≤ b + 2 * delta
    · rw [closedIntervalIndicator, if_pos hout]
      by_cases hin : a ≤ x ∧ x ≤ b
      · rw [show closedIntervalIndicator a b x = 1 from if_pos hin]
        linarith [hnonneg (a - 2 * delta) a x, hnonneg b (b + 2 * delta) x]
      · by_cases hax : a ≤ x
        · have hbx : b ≤ x := le_of_lt (lt_of_not_ge (fun h => hin ⟨hax, h⟩))
          rw [show closedIntervalIndicator b (b + 2 * delta) x = 1 from if_pos ⟨hbx, hout.2⟩]
          linarith [hnonneg a b x, hnonneg (a - 2 * delta) a x]
        · have hxa : x ≤ a := (lt_of_not_ge hax).le
          rw [show closedIntervalIndicator (a - 2 * delta) a x = 1 from if_pos ⟨hout.1, hxa⟩]
          linarith [hnonneg a b x, hnonneg b (b + 2 * delta) x]
    · rw [closedIntervalIndicator, if_neg hout]
      positivity [hnonneg a b x, hnonneg (a - 2 * delta) a x, hnonneg b (b + 2 * delta) x]
  have h := smoothing_empiricalAverage_mono s hpoint
  simpa only [empiricalIntervalMass, empiricalAverage, Finset.sum_add_distrib, add_div] using h

end ShortRingAnchor
