import BernoulliSection9.ExternalInputs
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Terminal small-ball bookkeeping

This module contains the parts of Proposition 7.3 that do not depend on the
RRQR construction: the capped loss (with the paper's special value at zero),
its scaling invariance, and the limiting argument which turns estimates for
all caps into a zero-probability bound.
-/

open scoped Real

noncomputable section

namespace BernoulliSection9

open MeasureTheory

/-- Equation (7.48), including the essential convention `L_T(c, 0) = T`.
Using ordinary division here would be wrong because division by zero is total
in Lean. -/
def cappedLogLoss (T c : ℝ) (w : ℂ) : ℝ :=
  if w = 0 then T else min T (Real.posLog (c / ‖w‖))

@[simp] theorem cappedLogLoss_zero (T c : ℝ) :
    cappedLogLoss T c 0 = T := by
  simp [cappedLogLoss]

theorem cappedLogLoss_of_ne_zero {T c : ℝ} {w : ℂ} (hw : w ≠ 0) :
    cappedLogLoss T c w = min T (Real.posLog (c / ‖w‖)) := by
  simp [cappedLogLoss, hw]

/-- The capped coefficient-to-value loss is unchanged when both the value
and coefficient norm are multiplied by the same nonzero scalar.  This is the
formal content of (9.13). -/
theorem cappedLogLoss_common_scale (T c : ℝ) (w a : ℂ) (ha : a ≠ 0) :
    cappedLogLoss T (‖a‖ * c) (a * w) = cappedLogLoss T c w := by
  by_cases hw : w = 0
  · simp [hw, cappedLogLoss]
  · have haw : a * w ≠ 0 := mul_ne_zero ha hw
    rw [cappedLogLoss_of_ne_zero haw, cappedLogLoss_of_ne_zero hw,
      norm_mul]
    have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    congr 2
    field_simp

/-- Zero events are likewise invariant under a nonzero common scale. -/
theorem common_scale_eq_zero_iff (w a : ℂ) (ha : a ≠ 0) :
    a * w = 0 ↔ w = 0 := by
  exact mul_eq_zero.trans (or_iff_right ha)

/-- The special value at zero is essential for this uniform cap bound. -/
theorem cappedLogLoss_le_cap {T c : ℝ} {w : ℂ} :
    cappedLogLoss T c w ≤ T := by
  by_cases hw : w = 0
  · simp [cappedLogLoss, hw]
  · simp [cappedLogLoss, hw]

theorem cappedLogLoss_nonneg {T c : ℝ} {w : ℂ} (hT : 0 ≤ T) :
    0 ≤ cappedLogLoss T c w := by
  by_cases hw : w = 0
  · simp [cappedLogLoss, hw, hT]
  · simp only [cappedLogLoss, if_neg hw]
    exact le_min hT (Real.posLog_nonneg (x := c / ‖w‖))

/-- Charge the exceptional event at height `T`.  This is the measure-theoretic
bookkeeping used after the determinant lower bound: a pointwise loss `A` off
`bad`, together with `P(bad) ≤ p`, gives the paper's `A + pT` bound. -/
theorem integral_cappedLogLoss_le_good_add_bad
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [IsProbabilityMeasure μ]
    (T c A p : ℝ) (value : Ω → ℂ) (bad : Set Ω)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hbad : MeasurableSet bad)
    (hint : MeasureTheory.Integrable
      (fun ω ↦ cappedLogLoss T c (value ω)) μ)
    (hprob : μ.real bad ≤ p)
    (hgood : ∀ ω ∉ bad, cappedLogLoss T c (value ω) ≤ A) :
    ∫ ω, cappedLogLoss T c (value ω) ∂μ ≤ A + p * T := by
  let indicator : Ω → ℝ := bad.indicator (1 : Ω → ℝ)
  have hind : MeasureTheory.Integrable indicator μ := by
    exact (MeasureTheory.integrable_const (1 : ℝ)).indicator hbad
  have hmajorant : MeasureTheory.Integrable (fun ω ↦ A + T * indicator ω) μ :=
    (MeasureTheory.integrable_const A).add (hind.const_mul T)
  have hpoint : ∀ ω, cappedLogLoss T c (value ω) ≤ A + T * indicator ω := by
    intro ω
    by_cases hω : ω ∈ bad
    · have hcap := cappedLogLoss_le_cap (T := T) (c := c) (w := value ω)
      simp [indicator, Set.indicator_of_mem hω]
      linarith
    · simpa [indicator, hω] using hgood ω hω
  calc
    ∫ ω, cappedLogLoss T c (value ω) ∂μ ≤
        ∫ ω, (A + T * indicator ω) ∂μ :=
      MeasureTheory.integral_mono hint hmajorant hpoint
    _ = A + T * μ.real bad := by
      have hi : ∫ ω, indicator ω ∂μ = μ.real bad := by
        simpa [indicator] using
          (MeasureTheory.integral_indicator_one (μ := μ) hbad)
      rw [MeasureTheory.integral_add
        (MeasureTheory.integrable_const A) (hind.const_mul T)]
      rw [MeasureTheory.integral_const_mul]
      simp [hi]
    _ ≤ A + p * T := by
      have hmul : T * μ.real bad ≤ T * p :=
        mul_le_mul_of_nonneg_left hprob hT
      simpa [add_comm, mul_comm] using add_le_add_left hmul A

/-- Turn an almost-sure conditional Cook bound back into an unconditional
probability bound.  This is the law-of-total-probability step used after each
of the two conditional applications. -/
theorem probability_le_of_condExp_indicator_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (bad : Set Ω) (p : ℝ) (hbad : @MeasurableSet Ω mΩ bad)
    (hcond : ∀ᵐ ω ∂μ,
      @MeasureTheory.condExp Ω ℝ m (m₀ := mΩ) _ _ μ
        (bad.indicator (1 : Ω → ℝ)) ω ≤ p) :
    μ.real bad ≤ p := by
  let f : Ω → ℝ := bad.indicator (1 : Ω → ℝ)
  let ce : Ω → ℝ :=
    @MeasureTheory.condExp Ω ℝ m (m₀ := mΩ) _ _ μ f
  have hf : Integrable f μ :=
    (MeasureTheory.integrable_const (1 : ℝ)).indicator hbad
  have hce : Integrable ce μ := by
    exact MeasureTheory.integrable_condExp
  have hpint : Integrable (fun _ : Ω ↦ p) μ :=
    MeasureTheory.integrable_const p
  have hle : (∫ ω, ce ω ∂μ) ≤ ∫ _ : Ω, p ∂μ := by
    apply MeasureTheory.integral_mono_ae hce hpint
    filter_upwards [hcond] with ω hω
    simpa [ce, f] using hω
  calc
    μ.real bad = ∫ ω, f ω ∂μ := by
      simpa [f] using
        (MeasureTheory.integral_indicator_one (μ := μ) hbad).symm
    _ = ∫ ω, ce ω ∂μ := by
      symm
      simpa [ce] using
        (MeasureTheory.integral_condExp (μ := μ) (f := f) hm)
    _ ≤ ∫ _ : Ω, p ∂μ := hle
    _ = p := by simp

/-- Union-bound bookkeeping for the two Cook failures. -/
theorem probability_union_le_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (bad₁ bad₂ : Set Ω) (p₁ p₂ : ℝ)
    (h₁ : μ.real bad₁ ≤ p₁) (h₂ : μ.real bad₂ ≤ p₂) :
    μ.real (bad₁ ∪ bad₂) ≤ p₁ + p₂ :=
  (MeasureTheory.measureReal_union_le bad₁ bad₂).trans
    (add_le_add h₁ h₂)

/-- Purely numerical limiting lemma used after dividing the capped estimate
by `T` and sending `T` to infinity. -/
theorem le_of_forall_cap_bound
    {q p A : ℝ} (hA : 0 ≤ A)
    (h : ∀ T : ℝ, 0 < T → T * q ≤ A + p * T) : q ≤ p := by
  by_contra hqp
  have hdiff : 0 < q - p := sub_pos.mpr (lt_of_not_ge hqp)
  let T : ℝ := (A + 1) / (q - p)
  have hT : 0 < T := div_pos (by linarith) hdiff
  have hbound := h T hT
  have hmul : T * (q - p) ≤ A := by
    dsimp [T] at hbound ⊢
    linarith
  have hidentity : T * (q - p) = A + 1 := by
    dsimp [T]
    exact div_mul_cancel₀ (A + 1) hdiff.ne'
  rw [hidentity] at hmul
  linarith

/-- Abstract form of the last line proving (7.20): once the integral estimate
has supplied `T * P{p=0} ≤ A + p T` for every positive cap, the atom at zero
is at most `p`. -/
theorem zeroProbability_of_all_capped_bounds
    {zeroProbability baseLoss badProbability : ℝ}
    (hbase : 0 ≤ baseLoss)
    (hcap : ∀ T : ℝ, 0 < T →
      T * zeroProbability ≤ baseLoss + badProbability * T) :
    zeroProbability ≤ badProbability :=
  le_of_forall_cap_bound hbase hcap

/-- A compact record for the four conclusions of Proposition 7.3.  It is an
output package, not an assumption used to hide RRQR or Cook. -/
structure TerminalSmallBallConclusion
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (coefficientNorm : ℝ) (value : Ω → ℂ)
    (baseLoss badProbability : ℝ) where
  coefficientNorm_pos : 0 < coefficientNorm
  capped : ∀ T : ℝ, 0 < T →
    ∫ ω, cappedLogLoss T coefficientNorm (value ω) ∂μ ≤
      baseLoss + badProbability * T
  zero_probability : μ.real {ω | value ω = 0} ≤ badProbability
  reverse_event : Set Ω
  reverse : ∀ ω ∈ reverse_event,
    Real.posLog (‖value ω‖ / coefficientNorm) ≤ baseLoss
  parseval : coefficientNorm ^ 2 = ∫ ω, ‖value ω‖ ^ 2 ∂μ

end BernoulliSection9
