import ShortRingAnchor.CyclicVarianceProfile
import ShortRingAnchor.AtomAssumption21
import Mathlib.Data.Nat.Dist

/-!
# Profile and density adapters for the copied Theorem 3.1

The high-band project uses cyclic distance and a lower profile bound `c/W`.
The manuscript uses signed offsets and `c0/(2W+1)`. For positive integer
bandwidth these agree with constants `c=c0/3` and `C=C0`.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace ShortRingAnchor

/-- Manuscript (3.1): every pair at cyclic distance at most `W` is an active offset. -/
theorem exists_cyclicColumn_of_cyclicDist_le {M W : ℕ}
    (hfit : 2 * W + 1 ≤ M) (i j : Fin M)
    (h : min (Nat.dist i.val j.val) (M - Nat.dist i.val j.val) ≤ W) :
    ∃ s : BandOffset W, cyclicColumn hfit i s = j := by
  by_cases hij : i.val ≤ j.val
  · rw [Nat.dist_eq_sub_of_le hij] at h
    rcases min_le_iff.mp h with hd | hd
    · let s : BandOffset W := ⟨W + (j.val - i.val), by omega⟩
      refine ⟨s, Fin.ext ?_⟩
      have he : i.val + s.val + M - W = j.val + M := by dsimp [s]; omega
      change (i.val + s.val + M - W) % M = j.val
      simp [he, Nat.mod_eq_of_lt j.isLt]
    · let s : BandOffset W := ⟨W - (M - (j.val - i.val)), by omega⟩
      refine ⟨s, Fin.ext ?_⟩
      have he : i.val + s.val + M - W = j.val := by dsimp [s]; omega
      change (i.val + s.val + M - W) % M = j.val
      rw [he, Nat.mod_eq_of_lt j.isLt]
  · have hji : j.val ≤ i.val := by omega
    rw [Nat.dist_eq_sub_of_le_right hji] at h
    rcases min_le_iff.mp h with hd | hd
    · let s : BandOffset W := ⟨W - (i.val - j.val), by omega⟩
      refine ⟨s, Fin.ext ?_⟩
      have he : i.val + s.val + M - W = j.val + M := by dsimp [s]; omega
      change (i.val + s.val + M - W) % M = j.val
      simp [he, Nat.mod_eq_of_lt j.isLt]
    · let s : BandOffset W := ⟨W + (M - (i.val - j.val)), by omega⟩
      refine ⟨s, Fin.ext ?_⟩
      have he : i.val + s.val + M - W = j.val + M + M := by dsimp [s]; omega
      change (i.val + s.val + M - W) % M = j.val
      simp [he, Nat.mod_eq_of_lt j.isLt]

/-- Theorem 3.1 profile lower bound, with the exact harmless change `c=c0/3`. -/
theorem cyclicVarianceCoefficient_local_floor {M W : ℕ} {c0 C0 : ℝ}
    (weights : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ M) (hW : 0 < W)
    (i j : Fin M) (h : min (Nat.dist i.val j.val) (M - Nat.dist i.val j.val) ≤ W) :
    (c0 / 3) / (W : ℝ) ≤ cyclicVarianceCoefficient weights hfit i j ^ 2 := by
  obtain ⟨s, rfl⟩ := exists_cyclicColumn_of_cyclicDist_le hfit i j h
  rw [cyclicVarianceCoefficient_at, Real.sq_sqrt (weights.q_nonneg s)]
  apply le_trans ?_ (weights.lower s)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  rw [div_div]
  exact div_le_div_of_nonneg_left weights.c0_pos.le (by positivity)
    (by push_cast; linarith)

/-- Theorem 3.1 profile upper bound, retaining the manuscript's `C0`. -/
theorem cyclicVarianceCoefficient_upper {M W : ℕ} {c0 C0 : ℝ}
    (weights : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ M) (hW : 0 < W)
    (i j : Fin M) : cyclicVarianceCoefficient weights hfit i j ^ 2 ≤ C0 / (W : ℝ) := by
  by_cases h : ∃ s, cyclicColumn hfit i s = j
  · obtain ⟨s, rfl⟩ := h
    rw [cyclicVarianceCoefficient_at, Real.sq_sqrt (weights.q_nonneg s)]
    apply (weights.upper s).trans
    exact div_le_div_of_nonneg_left weights.C0_pos.le (by exact_mod_cast hW)
      (by push_cast; linarith [show (0 : ℝ) ≤ W from Nat.cast_nonneg W])
  · rw [cyclicVarianceCoefficient_off_band weights hfit i j h]
    simpa using div_nonneg weights.C0_pos.le (Nat.cast_nonneg W)

/-- Assumption 2.1: convert a bounded density witness to the measure bound
used by the high-band project. The bound is finite and strictly positive. -/
theorem HasBoundedDensityWithRespectTo.exists_pos_measure_le
    {E : Type*} [MeasurableSpace E] {mu lambda : Measure E}
    (h : HasBoundedDensityWithRespectTo mu lambda) :
    ∃ L : ℝ, 0 < L ∧ mu ≤ ENNReal.ofReal L • lambda := by
  refine ⟨h.bound.toReal + 1, by positivity, ?_⟩
  calc
    mu = lambda.withDensity h.density := h.law_eq_withDensity
    _ ≤ lambda.withDensity (fun _ => ENNReal.ofReal (h.bound.toReal + 1)) := by
      apply withDensity_mono
      filter_upwards [h.density_le_bound] with x hx
      apply hx.trans
      calc
        h.bound = ENNReal.ofReal h.bound.toReal := (ENNReal.ofReal_toReal h.bound_lt_top.ne).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
    _ = _ := withDensity_const _

end ShortRingAnchor
