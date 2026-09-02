import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Radial Jensen expressions, hard-edge cutoffs, and the mean squeeze

This file contains the deterministic analytic closure used in Section 6.  The genuinely
random-matrix or analytic inputs enter through ordinary hypotheses: a Jensen formula
identifies a circle mean with `jensenRootExpression`; integrability and the
truncated-potential identity identify a cutoff error with `cdfCutoffIntegral`; and the
shifted-Ginibre hard-edge theorem supplies the linear CDF bound.  The tail Jensen/Mirsky
comparisons consumed by the final squeeze are likewise explicit premises.  Everything
after those inputs is proved here.

As elsewhere, `Real.log 0` is totalized.  Analytic use of the Jensen wrappers must supply
the nonzero polynomial/leading/constant-term facts stated by the relevant theorem.
-/

open Filter MeasureTheory Set Topology
open scoped Interval

namespace CircularLawSections56.Section6

section JensenRoots

variable {ι : Type*} [Fintype ι]

/-- The root-side expression in Jensen's formula for
`p(w) = leading * ∏ i, (w - roots i)` at radius `r`.

It is useful to keep this finite expression separate from the analytic theorem equating it
to the circle average: its radial monotonicity is entirely elementary. -/
noncomputable def jensenRootExpression
    (leading : ℂ) (roots : ι → ℂ) (r : ℝ) : ℝ :=
  Real.log ‖leading‖ + ∑ i, Real.log (max r ‖roots i‖)

/-- Each root contribution in Jensen's expression increases with the radius. -/
theorem jensenRootExpression_mono
    (leading : ℂ) (roots : ι → ℂ) {r s : ℝ}
    (hr : 0 < r) (hrs : r ≤ s) :
    jensenRootExpression leading roots r ≤
      jensenRootExpression leading roots s := by
  unfold jensenRootExpression
  apply add_le_add (le_refl _)
  apply Finset.sum_le_sum
  intro i hi
  have hrmax : 0 < max r ‖roots i‖ :=
    hr.trans_le (le_max_left _ _)
  exact Real.log_le_log hrmax (max_le_max hrs le_rfl)

/-- The root-side Jensen expression is nondecreasing on positive radii. -/
theorem jensenRootExpression_monotoneOn
    (leading : ℂ) (roots : ι → ℂ) :
    MonotoneOn (jensenRootExpression leading roots) (Ioi 0) := by
  intro r hr s hs hrs
  exact jensenRootExpression_mono leading roots hr hrs

/-- At radius one, the root-side Jensen expression dominates the logarithmic norm of the
constant term.  The nonvanishing hypotheses are exactly what is needed to use the
real-valued logarithm without treating `log 0` as minus infinity. -/
theorem jensenRootExpression_one_ge_log_norm_constantTerm
    (leading : ℂ) (roots : ι → ℂ)
    (hleading : leading ≠ 0) (hroots : ∀ i, roots i ≠ 0) :
    Real.log ‖leading * ∏ i, (-roots i)‖ ≤
      jensenRootExpression leading roots 1 := by
  have hprod : (∏ i, (-roots i)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i hi => neg_ne_zero.mpr (hroots i)
  have hnormRoots :
      ∀ i ∈ (Finset.univ : Finset ι), ‖-roots i‖ ≠ 0 := by
    intro i hi
    exact norm_ne_zero_iff.mpr (neg_ne_zero.mpr (hroots i))
  have hlogConstant :
      Real.log ‖leading * ∏ i, (-roots i)‖ =
        Real.log ‖leading‖ + ∑ i, Real.log ‖roots i‖ := by
    rw [norm_mul, Real.log_mul
      (norm_ne_zero_iff.mpr hleading) (norm_ne_zero_iff.mpr hprod)]
    congr 1
    rw [norm_prod, Real.log_prod hnormRoots]
    simp
  rw [hlogConstant]
  unfold jensenRootExpression
  apply add_le_add (le_refl _)
  apply Finset.sum_le_sum
  intro i hi
  exact Real.log_le_log (norm_pos_iff.mpr (hroots i)) (le_max_right _ _)

/-- A convenient wrapper for applying the preceding root calculation to any circle mean
for which a Jensen factorization identity has already been established. -/
theorem circleMean_radial_monotone_of_eq_jensenRootExpression
    (circleMean : ℝ → ℝ) (leading : ℂ) (roots : ι → ℂ)
    (hJensen : ∀ r, 0 < r →
      circleMean r = jensenRootExpression leading roots r) :
    MonotoneOn circleMean (Ioi 0) := by
  intro r hr s hs hrs
  rw [hJensen r hr, hJensen s hs]
  exact jensenRootExpression_mono leading roots hr hrs

/-- Jensen's root formula at radius one yields the usual lower bound by the value at zero. -/
theorem circleMean_one_ge_log_norm_constantTerm_of_eq_jensenRootExpression
    (circleMean : ℝ → ℝ) (leading : ℂ) (roots : ι → ℂ)
    (hleading : leading ≠ 0) (hroots : ∀ i, roots i ≠ 0)
    (hJensenOne : circleMean 1 = jensenRootExpression leading roots 1) :
    Real.log ‖leading * ∏ i, (-roots i)‖ ≤ circleMean 1 := by
  rw [hJensenOne]
  exact jensenRootExpression_one_ge_log_norm_constantTerm
    leading roots hleading hroots

end JensenRoots

section HardEdgeCutoff

/-- The layer-cake expression for a logarithmic cutoff error.  For a singular-value CDF
`F`, the usual truncated-potential identity reads
`cutoffPotential - rawPotential = cdfCutoffIntegral F a`. -/
noncomputable def cdfCutoffIntegral (F : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ t in 0..a, F t / t

/-- A linear hard-edge mass bound `F(t) ≤ C t` gives the quantitative cutoff estimate
`0 ≤ ∫₀ᵃ F(t)/t dt ≤ C a`.

Integrability is stated explicitly because, in applications, it comes from the CDF
measurability (or directly from the truncated-potential identity). -/
theorem cdfCutoffIntegral_nonneg_and_le_of_linear
    (F : ℝ → ℝ) {a C : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hIntegrable : IntervalIntegrable (fun t => F t / t) volume 0 a)
    (hNonneg : ∀ t ∈ Icc 0 a, 0 ≤ F t)
    (hLinear : ∀ t ∈ Ioc 0 a, F t ≤ C * t) :
    0 ≤ cdfCutoffIntegral F a ∧ cdfCutoffIntegral F a ≤ C * a := by
  constructor
  · unfold cdfCutoffIntegral
    exact intervalIntegral.integral_nonneg ha fun t ht =>
      div_nonneg (hNonneg t ht) ht.1
  · unfold cdfCutoffIntegral
    calc
      (∫ t in 0..a, F t / t) ≤ ∫ _t in 0..a, C := by
        apply intervalIntegral.integral_mono_on ha hIntegrable (by simp)
        intro t ht
        by_cases ht0 : t = 0
        · subst t
          simpa using hC
        · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
          exact (div_le_iff₀ htpos).2 (hLinear t ⟨htpos, ht.2⟩)
      _ = C * a := by simp [mul_comm]

/-- The hard-edge estimate in the form consumed by the Section 6 potential argument. -/
theorem cutoffError_nonneg_and_le_of_linear_mass
    (F : ℝ → ℝ) {a C rawPotential cutoffPotential : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hIntegrable : IntervalIntegrable (fun t => F t / t) volume 0 a)
    (hNonneg : ∀ t ∈ Icc 0 a, 0 ≤ F t)
    (hLinear : ∀ t ∈ Ioc 0 a, F t ≤ C * t)
    (hCutoffIdentity :
      cutoffPotential - rawPotential = cdfCutoffIntegral F a) :
    0 ≤ cutoffPotential - rawPotential ∧
      cutoffPotential - rawPotential ≤ C * a := by
  rw [hCutoffIdentity]
  exact cdfCutoffIntegral_nonneg_and_le_of_linear
    F ha hC hIntegrable hNonneg hLinear

/-- One-sided `O(a)` form of `cutoffError_nonneg_and_le_of_linear_mass`. -/
theorem cutoffError_le_of_linear_cdf
    (F : ℝ → ℝ) {a C rawPotential cutoffPotential : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hIntegrable : IntervalIntegrable (fun t => F t / t) volume 0 a)
    (hNonneg : ∀ t ∈ Icc 0 a, 0 ≤ F t)
    (hLinear : ∀ t ∈ Ioc 0 a, F t ≤ C * t)
    (hCutoffIdentity :
      cutoffPotential - rawPotential = cdfCutoffIntegral F a) :
    cutoffPotential - rawPotential ≤ C * a :=
  (cutoffError_nonneg_and_le_of_linear_mass
    F ha hC hIntegrable hNonneg hLinear hCutoffIdentity).2

end HardEdgeCutoff

section MeanSqueeze

/-- A nonnegative fourth-root cutoff, written as two square roots so its elementary
algebra and continuity can use the standard `Real.sqrt` API. -/
noncomputable def fourthRoot (t : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt t)

@[simp]
theorem fourthRoot_nonneg (t : ℝ) : 0 ≤ fourthRoot t := by
  exact Real.sqrt_nonneg _

theorem fourthRoot_pos {t : ℝ} (ht : 0 < t) : 0 < fourthRoot t := by
  exact Real.sqrt_pos.2 (Real.sqrt_pos.2 ht)

theorem fourthRoot_sq (t : ℝ) :
    fourthRoot t ^ 2 = Real.sqrt t := by
  unfold fourthRoot
  exact Real.sq_sqrt (Real.sqrt_nonneg t)

/-- With the fourth-root cutoff, the Mirsky tail term `√t / a` equals `a`. -/
theorem sqrt_div_fourthRoot {t : ℝ} (ht : 0 < t) :
    Real.sqrt t / fourthRoot t = fourthRoot t := by
  apply (div_eq_iff (fourthRoot_pos ht).ne').2
  calc
    Real.sqrt t = fourthRoot t ^ 2 := (fourthRoot_sq t).symm
    _ = fourthRoot t * fourthRoot t := pow_two _

/-- Quantitative mean squeeze.  The lower Jensen comparison, the upper cutoff comparison,
the cutoff error, and the limiting-potential error are kept as separate hypotheses so the
bound records every contribution. -/
theorem meanSqueeze_error_bound
    (mean rawPotential cutoffPotential target cutoffError tailError
      potentialError : ℝ)
    (hLower : rawPotential ≤ mean)
    (hUpper : mean ≤ cutoffPotential + tailError)
    (hCutoff : cutoffPotential - rawPotential ≤ cutoffError)
    (hPotential : |rawPotential - target| ≤ potentialError)
    (hCutoffError : 0 ≤ cutoffError) (hTailError : 0 ≤ tailError) :
    |mean - target| ≤ potentialError + cutoffError + tailError := by
  apply abs_le.2
  constructor
  · have hPotentialBounds := abs_le.1 hPotential
    have hPotential_le_total :
        potentialError ≤ potentialError + cutoffError + tailError := by
      exact (le_add_of_nonneg_right hCutoffError).trans
        (le_add_of_nonneg_right hTailError)
    calc
      -(potentialError + cutoffError + tailError) ≤ -potentialError :=
        neg_le_neg hPotential_le_total
      _ ≤ rawPotential - target := hPotentialBounds.1
      _ ≤ mean - target := sub_le_sub_right hLower target
  · have hPotentialBounds := abs_le.1 hPotential
    have hCutoffLe : cutoffPotential ≤ rawPotential + cutoffError := by
      rw [add_comm]
      exact (sub_le_iff_le_add).1 hCutoff
    have hRawLe : rawPotential ≤ target + potentialError := by
      rw [add_comm]
      exact (sub_le_iff_le_add).1 hPotentialBounds.2
    apply (sub_le_iff_le_add).2
    calc
      mean ≤ cutoffPotential + tailError := hUpper
      _ ≤ (rawPotential + cutoffError) + tailError :=
        add_le_add_left hCutoffLe tailError
      _ ≤ ((target + potentialError) + cutoffError) + tailError :=
        add_le_add_left (add_le_add_left hRawLe cutoffError) tailError
      _ = (potentialError + cutoffError + tailError) + target := by
        ac_rfl

/-- Quantitative Section 6 closure with the optimized cutoff
`a = t^(1/4)`: a linear hard-edge error costs `C a`, while the tail comparison costs
`√t/a = a`. -/
theorem meanSqueeze_fourthRoot_bound
    (mean rawPotential cutoffPotential target potentialError t C : ℝ)
    (ht : 0 < t) (hC : 0 ≤ C)
    (hLower : rawPotential ≤ mean)
    (hUpper : mean ≤ cutoffPotential + Real.sqrt t / fourthRoot t)
    (hCutoff : cutoffPotential - rawPotential ≤ C * fourthRoot t)
    (hPotential : |rawPotential - target| ≤ potentialError) :
    |mean - target| ≤ potentialError + (C + 1) * fourthRoot t := by
  have hUpper' : mean ≤ cutoffPotential + fourthRoot t := by
    simpa [sqrt_div_fourthRoot ht] using hUpper
  have hbound := meanSqueeze_error_bound
    mean rawPotential cutoffPotential target
    (C * fourthRoot t) (fourthRoot t) potentialError
    hLower hUpper' hCutoff hPotential
    (mul_nonneg hC (fourthRoot_nonneg t)) (fourthRoot_nonneg t)
  simpa [add_mul, add_assoc] using hbound

/-- Fourth roots preserve convergence to zero. -/
theorem tendsto_fourthRoot_zero
    {α : Type*} {l : Filter α} {t : α → ℝ}
    (ht : Tendsto t l (𝓝 0)) :
    Tendsto (fun n => fourthRoot (t n)) l (𝓝 0) := by
  have hsqrt : Tendsto (fun n => Real.sqrt (t n)) l (𝓝 0) := by
    have hcomp :
        Tendsto ((fun x : ℝ => Real.sqrt x) ∘ t) l (𝓝 0) := by
      simpa only [Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto 0).comp ht
    exact hcomp.congr' (Eventually.of_forall fun _ => rfl)
  have hcomp :
      Tendsto
        ((fun x : ℝ => Real.sqrt x) ∘ (fun n => Real.sqrt (t n)))
        l (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsqrt
  exact hcomp.congr' (Eventually.of_forall fun _ => rfl)

/-- Asymptotic mean-squeeze closure.  This is the direct scalar interface used after the
fixed-`R` core and tail bounds have been converted to deterministic expectations. -/
theorem meanSqueeze_fourthRoot_tendsto
    (mean rawPotential cutoffPotential potentialError tailMass : ℕ → ℝ)
    (target C : ℝ)
    (hC : 0 ≤ C)
    (hTailMass : ∀ n, 0 < tailMass n)
    (hLower : ∀ n, rawPotential n ≤ mean n)
    (hUpper : ∀ n,
      mean n ≤ cutoffPotential n +
        Real.sqrt (tailMass n) / fourthRoot (tailMass n))
    (hCutoff : ∀ n,
      cutoffPotential n - rawPotential n ≤
        C * fourthRoot (tailMass n))
    (hPotential : ∀ n,
      |rawPotential n - target| ≤ potentialError n)
    (hTailMassZero : Tendsto tailMass atTop (𝓝 0))
    (hPotentialErrorZero : Tendsto potentialError atTop (𝓝 0)) :
    Tendsto mean atTop (𝓝 target) := by
  have hFourthRootZero :
      Tendsto (fun n => fourthRoot (tailMass n)) atTop (𝓝 0) :=
    tendsto_fourthRoot_zero hTailMassZero
  have hTotalError :
      Tendsto
        (fun n => potentialError n + (C + 1) * fourthRoot (tailMass n))
        atTop (𝓝 0) := by
    have hConstant :
        Tendsto (fun _n : ℕ => C + 1) atTop (𝓝 (C + 1)) :=
      tendsto_const_nhds
    simpa using hPotentialErrorZero.add (hConstant.mul hFourthRootZero)
  have hAbs : Tendsto (fun n => |mean n - target|) atTop (𝓝 0) :=
    squeeze_zero
      (fun n => abs_nonneg (mean n - target))
      (fun n => meanSqueeze_fourthRoot_bound
        (mean n) (rawPotential n) (cutoffPotential n) target
        (potentialError n) (tailMass n) C
        (hTailMass n) hC
        (hLower n) (hUpper n) (hCutoff n) (hPotential n))
      hTotalError
  exact tendsto_iff_dist_tendsto_zero.2 (by
    simpa [Real.dist_eq] using hAbs)

end MeanSqueeze

end CircularLawSections56.Section6
