import CircularLawSection4.PaperFreshPolynomial
import CircularLawSection4.PaperIndicatorWeights

/-!
# The manuscript's fresh random rows as an explicit multiaffine polynomial

This module substitutes the scalar indicator coefficients into the generic
fresh-polynomial construction.  A fresh block contains `d + 1` rows.  In row
`t`, `atoms t ell` is the atom attached to the ordered reset/star label
`ell`; the deterministic amplitude is supplied by `PaperIndicatorWeights`.

For a selected reset word, all unselected atoms and the diagonal spectral
translation `-z` are frozen in `paperIndicatorFreshBase`.  The one selected
atom in each row is the corresponding variable of a genuine
`MultiAffine C (d + 1)`.  Evaluation recovers the full alternating exterior
trace, while the top coefficient is exactly the isolated weighted word
coefficient.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

namespace PaperIndicatorWeights

variable {d : ℕ} {c₀ C₀ : ℝ}

/-- The deterministic spectral translation in ordered reset/star labels.
Only the interior label representing offset zero receives `-z`. -/
def freshSpectralShift (center : Fin (d + 1)) (z : ℂ) :
    ResetLabel (d + 1) → ℂ
  | none => 0
  | some j => if j = center then -z else 0

/-- The full denominator-cleared exterior row after substituting the paper's
indicator amplitudes and atoms. -/
def freshExteriorRow
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1)) (t : Fin (d + 1)) :
    Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ :=
  (∑ ell : ResetLabel (d + 1),
      (profile.orderedResetWeight ell * atoms t ell) •
        orderedCoefficient d q ell) +
    ∑ ell : ResetLabel (d + 1),
      (freshSpectralShift center z ell) • orderedCoefficient d q ell

/-- Frozen part of a fresh row after reserving the atom selected by `word t`
as the `t`th multiaffine variable. -/
def paperIndicatorFreshBase
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (word : Fin (d + 1) → ResetLabel (d + 1))
    (q : ExteriorDegree (d + 1)) (t : Fin (d + 1)) :
    Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ :=
  (∑ ell ∈ (Finset.univ.erase (word t)),
      (profile.orderedResetWeight ell * atoms t ell) •
        orderedCoefficient d q ell) +
    ∑ ell : ResetLabel (d + 1),
      (freshSpectralShift center z ell) • orderedCoefficient d q ell

/-- Reinsert the selected atom into its frozen row. -/
theorem paperIndicatorFreshBase_add_selected
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (word : Fin (d + 1) → ResetLabel (d + 1))
    (q : ExteriorDegree (d + 1)) (t : Fin (d + 1)) :
    profile.paperIndicatorFreshBase center z atoms word q t +
        atoms t (word t) •
          (profile.orderedResetWeight (word t) •
            orderedCoefficient d q (word t)) =
      profile.freshExteriorRow center z atoms q t := by
  classical
  let f : ResetLabel (d + 1) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ :=
    fun ell => (profile.orderedResetWeight ell * atoms t ell) •
      orderedCoefficient d q ell
  have hselected :
      atoms t (word t) •
          (profile.orderedResetWeight (word t) •
            orderedCoefficient d q (word t)) = f (word t) := by
    simp only [f, smul_smul]
    rw [mul_comm]
  have hsum :
      (∑ ell ∈ (Finset.univ.erase (word t)), f ell) + f (word t) =
        ∑ ell, f ell := by
    exact Finset.sum_erase_add _ _ (Finset.mem_univ (word t))
  rw [paperIndicatorFreshBase, freshExteriorRow, hselected]
  change
    ((∑ ell ∈ (Finset.univ.erase (word t)), f ell) +
        ∑ ell, freshSpectralShift center z ell • orderedCoefficient d q ell) +
      f (word t) =
        (∑ ell, f ell) +
          ∑ ell, freshSpectralShift center z ell • orderedCoefficient d q ell
  rw [← hsum]
  abel

/-- The exact manuscript fresh polynomial associated with the singleton word
that isolates the entry `(J,I)` of exterior degree `r`. -/
def paperIndicatorFreshPolynomial
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (r : ExteriorDegree (d + 1))
    (I J : ExteriorIndex (d + 1) r) : MultiAffine ℂ (d + 1) :=
  let word := arbitrarySupportWord I J
  orderedFreshPolynomial profile.orderedResetWeight B
    (profile.paperIndicatorFreshBase center z atoms word) r I J

set_option maxHeartbeats 800000 in
/-- Evaluation of the manuscript polynomial is the actual alternating trace
of the full fresh exterior rows. -/
theorem eval_paperIndicatorFreshPolynomial
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (r : ExteriorDegree (d + 1))
    (I J : ExteriorIndex (d + 1) r) :
    MultiAffine.eval
        (profile.paperIndicatorFreshPolynomial center z atoms B r I J)
        (fun t => atoms t (arbitrarySupportWord I J t)) =
      ∑ q : ExteriorDegree (d + 1), (-1 : ℂ) ^ q.val *
        Matrix.trace (B q * chronologicalProduct
          (List.ofFn fun t => profile.freshExteriorRow center z atoms q t)) := by
  classical
  rw [paperIndicatorFreshPolynomial, orderedFreshPolynomial]
  rw [eval_weightedAlternatingFreshPolynomial]
  apply Finset.sum_congr rfl
  intro q _
  congr 2
  congr 1
  apply congrArg chronologicalProduct
  apply List.ofFn_inj.2
  funext t
  exact profile.paperIndicatorFreshBase_add_selected center z atoms
    (arbitrarySupportWord I J) q t

/-- Its top coefficient is exactly the genuine ordered reset-word
coefficient; all frozen atoms and the `-z` shift disappear. -/
@[simp] theorem topCoeff_paperIndicatorFreshPolynomial
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (r : ExteriorDegree (d + 1))
    (I J : ExteriorIndex (d + 1) r) :
    MultiAffine.topCoeff
        (profile.paperIndicatorFreshPolynomial center z atoms B r I J) =
      weightedFullMonomialCoefficient profile.orderedResetWeight B
        (orderedCoefficient d) (arbitrarySupportWord I J) := by
  simp [paperIndicatorFreshPolynomial]

/-- Paper-profile version of the isolated top-coefficient lower bound.  The
polynomial is now the actual fresh-row alternating trace rather than an
abstract coefficient model. -/
theorem exists_paperIndicatorFreshPolynomial_topCoeff_maxEntry_lower_bound
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        (Real.sqrt (c₀ / (d + 2 : ℝ))) ^ (d + 1) *
            exteriorFamilyMaxEntryNorm B ≤
          ‖MultiAffine.topCoeff
            (profile.paperIndicatorFreshPolynomial center z atoms B r I J)‖ := by
  obtain ⟨r, I, J, h⟩ :=
    profile.exists_indicator_isolated_orderedCoefficient_maxEntry_lower_bound B
  refine ⟨r, I, J, ?_⟩
  simpa using h

/-- Operator-norm form of the same paper-specific top-coefficient bound. -/
theorem exists_paperIndicatorFreshPolynomial_topCoeff_maxL2OpNorm_lower_bound
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        (Real.sqrt (c₀ / (d + 2 : ℝ))) ^ (d + 1) *
            (exteriorFamilyMaxL2OpNorm B /
              (Fintype.card (ExteriorFamilyEntry (d + 1)) : ℝ)) ≤
          ‖MultiAffine.topCoeff
            (profile.paperIndicatorFreshPolynomial center z atoms B r I J)‖ := by
  obtain ⟨r, I, J, h⟩ :=
    profile.exists_indicator_isolated_orderedCoefficient_maxL2OpNorm_lower_bound B
  refine ⟨r, I, J, ?_⟩
  simpa using h

end PaperIndicatorWeights

end CircularLawSection4
