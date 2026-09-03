import ShortRingAnchor.SourceStatement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# The cyclic short-ring model

This file encodes manuscript formulas (2.2) and (3.1).  The random entries
are supplied as a family indexed by the row and the signed band offset; no
infinite product probability space is postulated or constructed here.

The deterministic quantity `bandwidthParameter` is exactly
`(max_s q_s)⁻¹`.  The final comparison theorem proves uniformly that it is
comparable with `W`, as asserted immediately after (3.1).
-/

open scoped BigOperators

noncomputable section

namespace ShortRingAnchor

/-- The offsets `{-W,...,W}`, encoded in increasing order.  The element with
value `r` represents the signed offset `r-W`. -/
abbrev BandOffset (W : ℕ) := Fin (2 * W + 1)

/-- The zero element witnesses that every band-offset type is nonempty. -/
def firstBandOffset (W : ℕ) : BandOffset W := ⟨0, by omega⟩

/-- Formula (2.2): a positive normalized weight vector on `[-W,W]`, with
constants independent of the matrix size.

The paper permits the weights to depend on the ambient target pair.  Thus a
sequence of short rings may use a different value of this structure at each
size, while sharing the same parameters `c0,C0`. -/
structure AdmissibleWeights (W : ℕ) (c0 C0 : ℝ) where
  q : BandOffset W → ℝ
  c0_pos : 0 < c0
  c0_le_C0 : c0 ≤ C0
  sum_q : ∑ s, q s = 1
  lower : ∀ s, c0 / (2 * W + 1 : ℕ) ≤ q s
  upper : ∀ s, q s ≤ C0 / (2 * W + 1 : ℕ)

namespace AdmissibleWeights

variable {W : ℕ} {c0 C0 : ℝ} (weights : AdmissibleWeights W c0 C0)

include weights in
theorem C0_pos : 0 < C0 := by
  exact lt_of_lt_of_le weights.c0_pos weights.c0_le_C0

theorem q_pos (s : BandOffset W) : 0 < weights.q s := by
  have hcount : (0 : ℝ) < (2 * W + 1 : ℕ) := by positivity
  exact (div_pos weights.c0_pos hcount).trans_le (weights.lower s)

theorem q_nonneg (s : BandOffset W) : 0 ≤ weights.q s :=
  (weights.q_pos s).le

/-- The largest entry variance `max_s q_s`. -/
def maxWeight : ℝ :=
  (Finset.univ : Finset (BandOffset W)).sup'
    ⟨firstBandOffset W, Finset.mem_univ _⟩ weights.q

theorem le_maxWeight (s : BandOffset W) : weights.q s ≤ weights.maxWeight := by
  exact Finset.le_sup' weights.q (Finset.mem_univ s)

theorem maxWeight_le :
    weights.maxWeight ≤ C0 / (2 * W + 1 : ℕ) := by
  apply Finset.sup'_le
  intro s _hs
  exact weights.upper s

theorem lower_le_maxWeight :
    c0 / (2 * W + 1 : ℕ) ≤ weights.maxWeight := by
  exact (weights.lower (firstBandOffset W)).trans
    (weights.le_maxWeight (firstBandOffset W))

theorem maxWeight_pos : 0 < weights.maxWeight := by
  have hcount : (0 : ℝ) < (2 * W + 1 : ℕ) := by positivity
  exact (div_pos weights.c0_pos hcount).trans_le weights.lower_le_maxWeight

/-- The manuscript parameter `b(H_{M,W})=(max_ij E|H_ij|²)⁻¹`.
For the cyclic model its deterministic value is `(max_s q_s)⁻¹`. -/
def bandwidthParameter : ℝ := weights.maxWeight⁻¹

theorem bandwidthParameter_pos : 0 < weights.bandwidthParameter := by
  exact inv_pos.mpr weights.maxWeight_pos

/-- Exact lower comparison in `b(H_{M,W}) ≍ W`. -/
theorem activeCount_div_C0_le_bandwidthParameter :
    (2 * W + 1 : ℕ) / C0 ≤ weights.bandwidthParameter := by
  have hcount : (0 : ℝ) < (2 * W + 1 : ℕ) := by positivity
  have hupper := weights.maxWeight_le
  have hinv := one_div_le_one_div_of_le weights.maxWeight_pos hupper
  calc
    (2 * W + 1 : ℕ) / C0 = 1 / (C0 / (2 * W + 1 : ℕ)) := by
      field_simp
    _ ≤ 1 / weights.maxWeight := hinv
    _ = weights.bandwidthParameter := by simp [bandwidthParameter]

/-- Exact upper comparison in `b(H_{M,W}) ≍ W`. -/
theorem bandwidthParameter_le_activeCount_div_c0 :
    weights.bandwidthParameter ≤ (2 * W + 1 : ℕ) / c0 := by
  have hcount : (0 : ℝ) < (2 * W + 1 : ℕ) := by positivity
  have hlower := weights.lower_le_maxWeight
  have hinv := one_div_le_one_div_of_le (div_pos weights.c0_pos hcount) hlower
  calc
    weights.bandwidthParameter = 1 / weights.maxWeight := by
      simp [bandwidthParameter]
    _ ≤ 1 / (c0 / (2 * W + 1 : ℕ)) := hinv
    _ = (2 * W + 1 : ℕ) / c0 := by field_simp

/-- A convenient coarse form of the lower comparison, linear in `W`. -/
theorem bandwidthParameter_linear_lower :
    (W : ℝ) / C0 ≤ weights.bandwidthParameter := by
  refine le_trans ?_ weights.activeCount_div_C0_le_bandwidthParameter
  apply div_le_div_of_nonneg_right _ weights.C0_pos.le
  norm_num
  nlinarith

/-- A convenient coarse form of the upper comparison, linear in `W+1`. -/
theorem bandwidthParameter_linear_upper :
    weights.bandwidthParameter ≤ 2 * (W + 1 : ℕ) / c0 := by
  refine weights.bandwidthParameter_le_activeCount_div_c0.trans ?_
  apply div_le_div_of_nonneg_right _ weights.c0_pos.le
  norm_num
  nlinarith

/-- The two-sided form of the assertion `b(H_{M,W}) ≍ W` below (3.1). -/
theorem bandwidthParameter_comparable :
    (W : ℝ) / C0 ≤ weights.bandwidthParameter ∧
      weights.bandwidthParameter ≤ 2 * (W + 1 : ℕ) / c0 :=
  ⟨weights.bandwidthParameter_linear_lower,
    weights.bandwidthParameter_linear_upper⟩

end AdmissibleWeights

/-- Addition of a signed offset modulo `M`.  Under `2W+1≤M`, the natural
number `i+s+M-W` is a nonnegative representative of `i+(s-W)` before taking
the remainder modulo `M`. -/
def cyclicColumn {M W : ℕ} (hfit : 2 * W + 1 ≤ M)
    (i : Fin M) (s : BandOffset W) : Fin M :=
  ⟨(i.val + s.val + M - W) % M, by
    apply Nat.mod_lt
    exact lt_of_lt_of_le (by positivity : 0 < 2 * W + 1) hfit⟩

/-- Formula (3.1), with deterministic entries `ξ_{i,s}` supplied by the
caller.  The finite sum is an exact coordinate-free way to place the
`2W+1` active entries in row `i` at the cyclic columns `i+s`.

The assumption `2W+1≤M` ensures distinct offsets occupy distinct columns;
the definition itself remains transparent and needs no choice of an inverse
offset map. -/
def cyclicShortRingMatrix {M W : ℕ} {c0 C0 : ℝ}
    (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 ≤ M)
    (entry : Fin M → BandOffset W → ℂ) :
    Matrix (Fin M) (Fin M) ℂ :=
  fun i j => ∑ s : BandOffset W,
    if cyclicColumn hfit i s = j then
      (Real.sqrt (weights.q s) : ℂ) * entry i s
    else 0

@[simp]
theorem cyclicShortRingMatrix_apply {M W : ℕ} {c0 C0 : ℝ}
    (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 ≤ M)
    (entry : Fin M → BandOffset W → ℂ) (i j : Fin M) :
    cyclicShortRingMatrix weights hfit entry i j =
      ∑ s : BandOffset W,
        if cyclicColumn hfit i s = j then
          (Real.sqrt (weights.q s) : ℂ) * entry i s
        else 0 := rfl

/-- The random version of formula (3.1), obtained by evaluating a supplied
family of random entries.  This is not an assertion that such a family
exists on any particular probability space. -/
def cyclicShortRingRandomMatrix
    {Omega : Type*} {M W : ℕ} {c0 C0 : ℝ}
    (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 ≤ M)
    (entry : Omega → Fin M → BandOffset W → ℂ)
    (omega : Omega) : Matrix (Fin M) (Fin M) ℂ :=
  cyclicShortRingMatrix weights hfit (entry omega)

/-- Entrywise measurability of the short-ring matrix follows from
measurability of the supplied atom copies. -/
theorem cyclicShortRingRandomMatrix_entry_measurable
    {Omega : Type*} [MeasurableSpace Omega]
    {M W : ℕ} {c0 C0 : ℝ}
    (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 ≤ M)
    (entry : Omega → Fin M → BandOffset W → ℂ)
    (hentry : ∀ i s, Measurable (fun omega => entry omega i s))
    (i j : Fin M) :
    Measurable (fun omega =>
      cyclicShortRingRandomMatrix weights hfit entry omega i j) := by
  unfold cyclicShortRingRandomMatrix cyclicShortRingMatrix
  apply Finset.measurable_sum
  intro s _hs
  by_cases hsj : cyclicColumn hfit i s = j
  · simp only [hsj, if_true]
    exact measurable_const.mul (hentry i s)
  · simp only [hsj, if_false]
    exact measurable_const

end ShortRingAnchor
