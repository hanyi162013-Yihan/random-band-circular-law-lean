import CircularLawSection4.PaperCyclicBandReindex
import CircularLawSection4.CyclicPhysicalDeterminantBridge

/-!
# Final paper-specific periodic determinant bridge

This module closes the deterministic bookkeeping in the manuscript's periodic
state-copy argument.  It combines:

* the independent raw-row/raw-column relabeling of the cyclic band matrix;
* the independent equation/state relabeling of the cyclic companion system;
* the product of the anchor-row denominator-clearing factors.

The result compares the determinant of the raw cyclic band matrix directly
with that of the raw cyclic companion state matrix.  Both reindexing factors
are retained in one explicit deterministic sign.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix

/-- The total deterministic sign in the paper-specific periodic determinant
bridge: raw-band row/column reindexing followed by cyclic state reindexing. -/
def paperPeriodicDeterminantSign
    {R : Type*} [Field R] (N m : ℕ) [NeZero N]
    (offset : ZMod N) : R :=
  paperCyclicBandReindexSign (R := R) N m offset *
    cyclicStateReindexSign (R := R) N m offset

/-- The total paper-specific periodic determinant sign is `+1` or `-1`. -/
theorem paperPeriodicDeterminantSign_spec
    {R : Type*} [Field R] (N m : ℕ) [NeZero N]
    (offset : ZMod N) :
    paperPeriodicDeterminantSign (R := R) N m offset = 1 ∨
      paperPeriodicDeterminantSign (R := R) N m offset = -1 := by
  rcases paperCyclicBandReindexSign_spec (R := R) N m offset with hBand | hBand
  · rcases cyclicStateReindexSign_spec (R := R) N m offset with hState | hState
    · left
      simp [paperPeriodicDeterminantSign, hBand, hState]
    · right
      simp [paperPeriodicDeterminantSign, hBand, hState]
  · rcases cyclicStateReindexSign_spec (R := R) N m offset with hState | hState
    · right
      simp [paperPeriodicDeterminantSign, hBand, hState]
    · left
      simp [paperPeriodicDeterminantSign, hBand, hState]

/-- Final exact periodic determinant comparison in the manuscript's raw
cyclic coordinates.  The determinant of the raw closure-plus-band matrix is
the total deterministic reindexing sign, times every denominator-clearing
factor, times the determinant of the raw cyclic companion state system. -/
theorem paperCyclicRawBandMatrix_det
    {R : Type*} [Field R] (N m : ℕ) [NeZero N]
    (offset : ZMod N)
    (βraw : ZMod N → R) (hβ : ∀ i, βraw i ≠ 0)
    (a : ZMod N → Fin (m + 1) → R) :
    (paperCyclicRawBandMatrix N m offset βraw a).det =
      paperPeriodicDeterminantSign (R := R) N m offset *
        (∏ p, paperCyclicOrderedScaling N m offset βraw p) *
          (cyclicCompanionStateMatrix N m offset
            (paperSparseCyclicLastRow N m βraw a)).det := by
  have hPhysical :
      (paperCyclicPhysicalMatrix N m offset βraw a).det =
        cyclicStateReindexSign (R := R) N m offset *
          (∏ p, paperCyclicOrderedScaling N m offset βraw p) *
            (cyclicCompanionStateMatrix N m offset
              (paperSparseCyclicLastRow N m βraw a)).det := by
    rw [← scaledPaperCyclicCompanionPhysicalBlock_eq
      (R := R) N m offset βraw hβ a]
    exact scaledCyclicCompanionPhysicalBlock_det
      (R := R) N m offset
      (paperCyclicOrderedScaling N m offset βraw)
      (paperSparseCyclicLastRow N m βraw a)
  have hReindex :=
    paperCyclicPhysicalMatrix_det (R := R) N m offset βraw a
  have hCompare :
      paperCyclicBandReindexSign (R := R) N m offset *
          (paperCyclicRawBandMatrix N m offset βraw a).det =
        cyclicStateReindexSign (R := R) N m offset *
          (∏ p, paperCyclicOrderedScaling N m offset βraw p) *
            (cyclicCompanionStateMatrix N m offset
              (paperSparseCyclicLastRow N m βraw a)).det := by
    exact hReindex.symm.trans hPhysical
  have hBandSq :
      paperCyclicBandReindexSign (R := R) N m offset *
          paperCyclicBandReindexSign (R := R) N m offset = 1 := by
    rcases paperCyclicBandReindexSign_spec (R := R) N m offset with h | h
    · simp [h]
    · simp [h]
  calc
    (paperCyclicRawBandMatrix N m offset βraw a).det =
        1 * (paperCyclicRawBandMatrix N m offset βraw a).det := by simp
    _ =
        (paperCyclicBandReindexSign (R := R) N m offset *
            paperCyclicBandReindexSign (R := R) N m offset) *
          (paperCyclicRawBandMatrix N m offset βraw a).det := by rw [hBandSq]
    _ =
        paperCyclicBandReindexSign (R := R) N m offset *
          (paperCyclicBandReindexSign (R := R) N m offset *
            (paperCyclicRawBandMatrix N m offset βraw a).det) := by ring
    _ =
        paperCyclicBandReindexSign (R := R) N m offset *
          (cyclicStateReindexSign (R := R) N m offset *
            (∏ p, paperCyclicOrderedScaling N m offset βraw p) *
              (cyclicCompanionStateMatrix N m offset
                (paperSparseCyclicLastRow N m βraw a)).det) := by rw [hCompare]
    _ =
        paperPeriodicDeterminantSign (R := R) N m offset *
          (∏ p, paperCyclicOrderedScaling N m offset βraw p) *
            (cyclicCompanionStateMatrix N m offset
              (paperSparseCyclicLastRow N m βraw a)).det := by
      simp only [paperPeriodicDeterminantSign]
      ring

/-- Sign-only form of `paperCyclicRawBandMatrix_det`. -/
theorem exists_sign_paperCyclicRawBandMatrix_det
    {R : Type*} [Field R] (N m : ℕ) [NeZero N]
    (offset : ZMod N)
    (βraw : ZMod N → R) (hβ : ∀ i, βraw i ≠ 0)
    (a : ZMod N → Fin (m + 1) → R) :
    ∃ σ : R, (σ = 1 ∨ σ = -1) ∧
      (paperCyclicRawBandMatrix N m offset βraw a).det =
        σ * (∏ p, paperCyclicOrderedScaling N m offset βraw p) *
          (cyclicCompanionStateMatrix N m offset
            (paperSparseCyclicLastRow N m βraw a)).det := by
  refine ⟨paperPeriodicDeterminantSign (R := R) N m offset,
    paperPeriodicDeterminantSign_spec (R := R) N m offset, ?_⟩
  exact paperCyclicRawBandMatrix_det (R := R) N m offset βraw hβ a

end CircularLawSection4
