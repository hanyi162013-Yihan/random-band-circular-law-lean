import CircularLawSection4.OrderedIsolatedMaxEntry
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Indicator-profile weights from the manuscript

The scalar indicator model uses deterministic variances `q_s` on one cyclic
band row, normalized by `sum q_s = 1` and bounded above and below by constant
multiples of the reciprocal row width.  This file records that hypothesis in
the exact finite-coordinate form used by the Lean transfer matrices.

The amplitude attached to a row atom is `b_s = sqrt q_s`.  The lower profile
bound therefore supplies both the almost-sure nondegeneracy coefficient used
by the companion transfer and the uniform weight loss used by the reset-word
isolation theorem.
-/

open scoped BigOperators

noncomputable section

namespace CircularLawSection4

/-- Deterministic indicator variance profile on `d + 1` consecutive offsets.

For the manuscript's symmetric width `W`, use `d = 2 * W`; the coordinates
then represent `-W, ..., W`. -/
structure PaperIndicatorWeights (d : ℕ) (c₀ C₀ : ℝ) where
  q : Fin (d + 1) → ℝ
  normalized : (∑ s, q s) = 1
  lower : ∀ s, c₀ / (d + 1 : ℝ) ≤ q s
  upper : ∀ s, q s ≤ C₀ / (d + 1 : ℝ)

namespace PaperIndicatorWeights

variable {d : ℕ} {c₀ C₀ : ℝ}

/-- Deterministic atom amplitudes `b_s = sqrt(q_s)`, embedded in `ℂ`. -/
def b (profile : PaperIndicatorWeights d c₀ C₀) : Fin (d + 1) → ℂ :=
  fun s ↦ (Real.sqrt (profile.q s) : ℂ)

/-- A positive lower profile constant makes every variance weight positive. -/
theorem q_pos (profile : PaperIndicatorWeights d c₀ C₀)
    (hc₀ : 0 < c₀) (s : Fin (d + 1)) : 0 < profile.q s := by
  have hden : 0 < (d + 1 : ℝ) := by positivity
  exact (div_pos hc₀ hden).trans_le (profile.lower s)

/-- Exact norm of the complex amplitude. -/
@[simp] theorem norm_b (profile : PaperIndicatorWeights d c₀ C₀)
    (s : Fin (d + 1)) : ‖profile.b s‖ = Real.sqrt (profile.q s) := by
  simp [b, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Every amplitude is nonzero under the manuscript's positive lower bound. -/
theorem b_ne_zero (profile : PaperIndicatorWeights d c₀ C₀)
    (hc₀ : 0 < c₀) (s : Fin (d + 1)) : profile.b s ≠ 0 := by
  have hnorm : 0 < ‖profile.b s‖ := by
    rw [profile.norm_b]
    exact Real.sqrt_pos.2 (profile.q_pos hc₀ s)
  exact norm_pos_iff.mp hnorm

/-- The profile lower bound transfers exactly to the amplitude scale. -/
theorem sqrt_lower_le_norm_b (profile : PaperIndicatorWeights d c₀ C₀)
    (s : Fin (d + 1)) :
    Real.sqrt (c₀ / (d + 1 : ℝ)) ≤ ‖profile.b s‖ := by
  rw [profile.norm_b]
  exact Real.sqrt_le_sqrt (profile.lower s)

/-- Coefficient weight in the ordered reset/star notation.

For a state of dimension `d + 1`, `none` is the right-edge coefficient and
`some j` is the interior coefficient numbered by `j`. -/
def orderedResetWeight (profile : PaperIndicatorWeights (d + 1) c₀ C₀) :
    ResetLabel (d + 1) → ℂ
  | none => profile.b (Fin.last (d + 1))
  | some j => profile.b j.castSucc

/-- Every reset/star label inherits the same explicit square-root lower
bound from the indicator profile. -/
theorem sqrt_lower_le_norm_orderedResetWeight
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (ell : ResetLabel (d + 1)) :
    Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ ‖profile.orderedResetWeight ell‖ := by
  have hr : ((d + 1 : ℕ) : ℝ) + 1 = (d + 2 : ℝ) := by
    push_cast
    ring
  cases ell with
  | none =>
      have h := profile.sqrt_lower_le_norm_b (Fin.last (d + 1))
      rw [hr] at h
      simpa only [orderedResetWeight] using h
  | some j =>
      have h := profile.sqrt_lower_le_norm_b j.castSucc
      rw [hr] at h
      simpa only [orderedResetWeight] using h

/-- Paper-specific isolated-coefficient lower bound with the indicator
profile substituted for the abstract reset weights. -/
theorem exists_indicator_isolated_orderedCoefficient_maxEntry_lower_bound
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        (Real.sqrt (c₀ / (d + 2 : ℝ))) ^ (d + 1) *
            exteriorFamilyMaxEntryNorm B ≤
          ‖weightedFullMonomialCoefficient profile.orderedResetWeight B
            (orderedCoefficient d) (arbitrarySupportWord I J)‖ := by
  apply exists_isolated_orderedCoefficient_maxEntry_lower_bound
  · exact Real.sqrt_nonneg _
  · intro ell
    exact profile.sqrt_lower_le_norm_orderedResetWeight ell

/-- Euclidean operator-norm version of the indicator-profile isolation
bound.  The explicit finite family-cardinality loss is inherited from the
coordinate extraction theorem. -/
theorem exists_indicator_isolated_orderedCoefficient_maxL2OpNorm_lower_bound
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        (Real.sqrt (c₀ / (d + 2 : ℝ))) ^ (d + 1) *
            (exteriorFamilyMaxL2OpNorm B /
              (Fintype.card (ExteriorFamilyEntry (d + 1)) : ℝ)) ≤
          ‖weightedFullMonomialCoefficient profile.orderedResetWeight B
            (orderedCoefficient d) (arbitrarySupportWord I J)‖ := by
  apply exists_isolated_orderedCoefficient_maxL2OpNorm_lower_bound
  · exact Real.sqrt_nonneg _
  · intro ell
    exact profile.sqrt_lower_le_norm_orderedResetWeight ell

end PaperIndicatorWeights

end CircularLawSection4
