import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# The bandwidth hypothesis and the global interface probability ledger

The Section 8 all-interface-good event loses a factor equal to the number
of sites. The hypothesis `log N / W → 0` makes that factor negligible
against any fixed exponential `exp (-cW)`. Under `N ≥ 4W` and `W → ∞`,
this is equivalent to the source's `W / log N → ∞`.

The finite union estimates below are measure-theoretic lemmas, with no
independence assumption. Their model-specific local estimates are
instantiated in the interface module.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

noncomputable section

namespace BernoulliSection8

/-- The two standard forms of the bandwidth assumption are equivalent in
the paper's dimension range. -/
theorem bandwidth_div_log_tendsto_iff
    (N W : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hNW : ∀ᶠ n in atTop, 4 * W n ≤ N n) :
    Tendsto (fun n => (W n : ℝ) / Real.log (N n : ℝ)) atTop atTop ↔
      Tendsto (fun n => Real.log (N n : ℝ) / (W n : ℝ)) atTop (𝓝 0) := by
  constructor
  · intro h
    simpa only [Function.comp_def, inv_div] using
      tendsto_inv_atTop_zero.comp h
  · intro h
    have hpos : ∀ᶠ n in atTop,
        0 < Real.log (N n : ℝ) / (W n : ℝ) := by
      filter_upwards [hNW, hW.eventually (eventually_ge_atTop 1)] with n hn hWn
      have hWpos : 0 < (W n : ℝ) := by exact_mod_cast (show 0 < W n by omega)
      have hNgt : (1 : ℝ) < N n := by exact_mod_cast (show 1 < N n by omega)
      exact div_pos (Real.log_pos hNgt) hWpos
    have hright : Tendsto (fun n => Real.log (N n : ℝ) / (W n : ℝ))
        atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨h, hpos⟩
    simpa only [Function.comp_def, inv_div] using
      tendsto_inv_nhdsGT_zero.comp hright

/-- Exponential decay along a diverging block width. -/
theorem tendsto_exp_neg_width
    (W : ℕ → ℕ) (hW : Tendsto W atTop atTop) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n => Real.exp (-c * (W n : ℝ))) atTop (𝓝 0) := by
  have hcast : Tendsto (fun n => (W n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hW
  have hscaled := Filter.Tendsto.const_mul_atTop hc hcast
  simpa only [Function.comp_def, neg_mul] using
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hscaled)

/-- The dimension itself can be absorbed into an exponential under the
logarithmic bandwidth hypothesis. -/
theorem tendsto_dimension_mul_exp_neg_width
    (N W : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log (N n : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n => (N n : ℝ) * Real.exp (-c * (W n : ℝ)))
      atTop (𝓝 0) := by
  have hhalf : 0 < c / 2 := half_pos hc
  have hratio : ∀ᶠ n in atTop,
      Real.log (N n : ℝ) / (W n : ℝ) < c / 2 :=
    hlog.eventually (Iio_mem_nhds hhalf)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (tendsto_exp_neg_width W hW hhalf)
    (Eventually.of_forall fun n => mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
  filter_upwards [hratio, hW.eventually (eventually_ge_atTop 1)] with n hn hWn
  have hWpos : 0 < (W n : ℝ) := by exact_mod_cast (show 0 < W n by omega)
  by_cases hN : N n = 0
  · simp only [hN, Nat.cast_zero, zero_mul]
    exact (Real.exp_pos _).le
  · have hNpos : 0 < (N n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hN)
    have hlogBound : Real.log (N n : ℝ) ≤ c / 2 * (W n : ℝ) :=
      ((div_lt_iff₀ hWpos).mp hn).le
    calc
      (N n : ℝ) * Real.exp (-c * (W n : ℝ)) =
          Real.exp (Real.log (N n : ℝ) - c * (W n : ℝ)) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hNpos]
        congr 2
        ring
      _ ≤ Real.exp (-(c / 2) * (W n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        linarith

/-- The exact scalar rate in the Section 8 global union bound. The
constant `C` is arbitrary because multiplying a null sequence by a fixed
real constant preserves its limit. -/
theorem tendsto_siteRatio_mul_exp_neg_width
    (N W : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log (N n : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) (C : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n => C * ((N n : ℝ) / (W n : ℝ)) *
      Real.exp (-c * (W n : ℝ))) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n => ((N n : ℝ) / (W n : ℝ)) *
      Real.exp (-c * (W n : ℝ))) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds (tendsto_dimension_mul_exp_neg_width N W hW hlog hc)
      (Eventually.of_forall fun n =>
        mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (Real.exp_pos _).le)
    filter_upwards [hW.eventually (eventually_ge_atTop 1)] with n hWn
    have hWone : (1 : ℝ) ≤ W n := by exact_mod_cast hWn
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact div_le_self (Nat.cast_nonneg _) hWone
  simpa only [mul_zero, mul_assoc] using hbase.const_mul C

/-- Write the dimension literally as `mW`, so the remaining prefactor is
the actual number of block sites. -/
theorem tendsto_siteCount_mul_exp_neg_width
    (m W : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log ((m n * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) (C : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n => C * (m n : ℝ) * Real.exp (-c * (W n : ℝ)))
      atTop (𝓝 0) := by
  have h := tendsto_siteRatio_mul_exp_neg_width
    (fun n => m n * W n) W hW hlog C hc
  apply h.congr'
  filter_upwards [hW.eventually (eventually_ge_atTop 1)] with n hWn
  have hWne : (W n : ℝ) ≠ 0 := by exact_mod_cast (show W n ≠ 0 by omega)
  simp only [Nat.cast_mul, mul_div_cancel_right₀ _ hWne]

/-- A finite union costs exactly its number of sites; no independence or
measurability of the events is needed for this upper bound. -/
theorem measureReal_siteUnion_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {m : ℕ}
    (bad : Fin m → Set Ω) (p : ℝ) (hbad : ∀ j, μ.real (bad j) ≤ p) :
    μ.real (⋃ j, bad j) ≤ (m : ℝ) * p := by
  calc
    μ.real (⋃ j, bad j) ≤ ∑ j, μ.real (bad j) :=
      measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _j : Fin m, p := Finset.sum_le_sum fun j _ => hbad j
    _ = (m : ℝ) * p := by simp

/-- Global failure tends to zero when the supplied one-site event has the
local exponential estimate. The probability spaces may vary with `n`. -/
theorem tendsto_measureReal_siteUnion_zero
    (m W : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log ((m n * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0))
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) (bad : ∀ n, Fin (m n) → Set (Ω n))
    (C : ℝ) {c : ℝ} (hc : 0 < c)
    (hbad : ∀ᶠ n in atTop, ∀ j,
      (μ n).real (bad n j) ≤ C * Real.exp (-c * (W n : ℝ))) :
    Tendsto (fun n => (μ n).real (⋃ j, bad n j)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (tendsto_siteCount_mul_exp_neg_width m W hW hlog C hc)
    (Eventually.of_forall fun n => measureReal_nonneg)
  filter_upwards [hbad] with n hn
  simpa only [mul_left_comm, mul_assoc] using
    measureReal_siteUnion_le (μ n) (bad n)
      (C * Real.exp (-c * (W n : ℝ))) hn

end BernoulliSection8

