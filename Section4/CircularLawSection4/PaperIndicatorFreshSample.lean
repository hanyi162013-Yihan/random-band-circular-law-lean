import CircularLawSection4.PaperIndicatorFreshRows
import CircularLawSection4.PaperIndicatorRandomMatrix
import CircularLawSection4.OrderedRowLinearity

/-!
# Flat IID samples as actual fresh companion rows

This file connects the flat finite sample used by
`PaperIndicatorRandomMatrix` to the reset/star-labelled atoms used by
`PaperIndicatorFreshRows`.  Starting at a cyclic row `start`, the next
`m + 1` rows form one fresh block.  Label `none` reads the final (right-edge)
coefficient slot, while `some j` reads the interior slot `j.castSucc`.

The main row theorem identifies `freshExteriorRow` with the actual
denominator-cleared compound of the paper's companion transfer.  Consequently
the evaluation of `paperIndicatorFreshPolynomial` is the alternating trace of
the genuine random-matrix fresh block, not merely an abstract affine-row
model.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

/-- Cyclic site occupied by fresh-row number `t`, starting from `start`. -/
def paperIndicatorFreshRowSite (N m : ℕ) [NeZero N]
    (start : ZMod N) (t : Fin (m + 1)) : ZMod N :=
  start + (t.val : ZMod N)

/-- The profile-weighted scalar coefficient array of the flat sample. -/
def paperIndicatorWeightedCoefficients
    (N m : ℕ) [NeZero N] {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (ω : Fin (N * (m + 2)) → ℂ) : ZMod N → Fin (m + 2) → ℂ :=
  fun i k ↦ profile.b k * paperIndicatorXi N m ω i k

/-- Right-edge coefficients `beta_i` of the sampled companion rows. -/
def paperIndicatorBetaRaw
    (N m : ℕ) [NeZero N] {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (ω : Fin (N * (m + 2)) → ℂ) : ZMod N → ℂ :=
  paperRightEdgeCoefficient m
    (paperIndicatorWeightedCoefficients N m profile ω)

/-- Interior sampled row after inserting the diagonal spectral shift. -/
def paperIndicatorShiftedInterior
    (N m : ℕ) [NeZero N] {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (ω : Fin (N * (m + 2)) → ℂ) :
    ZMod N → Fin (m + 1) → ℂ :=
  paperShiftedInteriorCoefficient m center
    (paperIndicatorWeightedCoefficients N m profile ω) z

/-- Relabel a block of `m + 1` rows from the flat IID sample by the ordered
reset/star alphabet.  `none` is the final coefficient slot and `some j` is
the interior slot `j.castSucc`. -/
def paperIndicatorFreshAtoms
    (N m : ℕ) [NeZero N] (start : ZMod N)
    (ω : Fin (N * (m + 2)) → ℂ) :
    Fin (m + 1) → ResetLabel (m + 1) → ℂ :=
  fun t ell ↦
    match ell with
    | none =>
        paperIndicatorXi N m ω (paperIndicatorFreshRowSite N m start t)
          (Fin.last (m + 1))
    | some j =>
        paperIndicatorXi N m ω (paperIndicatorFreshRowSite N m start t)
          j.castSucc

@[simp] theorem paperIndicatorFreshAtoms_none
    (N m : ℕ) [NeZero N] (start : ZMod N)
    (ω : Fin (N * (m + 2)) → ℂ) (t : Fin (m + 1)) :
    paperIndicatorFreshAtoms N m start ω t none =
      paperIndicatorXi N m ω (paperIndicatorFreshRowSite N m start t)
        (Fin.last (m + 1)) := rfl

@[simp] theorem paperIndicatorFreshAtoms_some
    (N m : ℕ) [NeZero N] (start : ZMod N)
    (ω : Fin (N * (m + 2)) → ℂ) (t : Fin (m + 1))
    (j : Fin (m + 1)) :
    paperIndicatorFreshAtoms N m start ω t (some j) =
      paperIndicatorXi N m ω (paperIndicatorFreshRowSite N m start t)
        j.castSucc := rfl

@[simp] theorem paperIndicatorBetaRaw_apply
    (N m : ℕ) [NeZero N] {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (ω : Fin (N * (m + 2)) → ℂ) (i : ZMod N) :
    paperIndicatorBetaRaw N m profile ω i =
      profile.b (Fin.last (m + 1)) *
        paperIndicatorXi N m ω i (Fin.last (m + 1)) := rfl

@[simp] theorem paperIndicatorShiftedInterior_apply
    (N m : ℕ) [NeZero N] {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (ω : Fin (N * (m + 2)) → ℂ) (i : ZMod N) (j : Fin (m + 1)) :
    paperIndicatorShiftedInterior N m profile center z ω i j =
      profile.b j.castSucc * paperIndicatorXi N m ω i j.castSucc -
        if j = center then z else 0 := rfl

/-- The paper's explicit companion transfer is the generic one-row companion
used by the row-linearity theorem. -/
theorem paperCyclicTransferMatrix_eq_rowCompanion
    (N m : ℕ) [NeZero N]
    (βraw : ZMod N → ℂ) (a : ZMod N → Fin (m + 1) → ℂ)
    (i : ZMod N) :
    paperCyclicTransferMatrix N m βraw a i =
      rowCompanion (finLeftShift m) (Fin.last m) (βraw i) (a i) := by
  classical
  ext row col
  refine Fin.lastCases ?_ (fun k ↦ ?_) row
  · simp [paperCyclicTransferMatrix, rowCompanion, Matrix.updateRow_apply]
  · by_cases hcol : col = k.succ
    · simp [paperCyclicTransferMatrix, rowCompanion, Matrix.updateRow_apply,
        finLeftShift, Fin.castSucc_ne_last, hcol]
    · have hval : k.val + 1 ≠ col.val := by
        intro h
        apply hcol
        apply Fin.ext
        exact h.symm
      simp [paperCyclicTransferMatrix, rowCompanion, Matrix.updateRow_apply,
        finLeftShift, Fin.castSucc_ne_last, hcol, hval]

/-- One relabelled fresh exterior row is exactly the denominator-cleared
compound of the corresponding sampled companion row. -/
theorem paperIndicatorFreshExteriorRow_eq_clearedRowCompanionCompound
    (N m : ℕ) [NeZero N] {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (start : ZMod N) (ω : Fin (N * (m + 2)) → ℂ)
    (q : ExteriorDegree (m + 1)) (t : Fin (m + 1))
    (hβ : paperIndicatorBetaRaw N m profile ω
      (paperIndicatorFreshRowSite N m start t) ≠ 0) :
    profile.freshExteriorRow center z
        (paperIndicatorFreshAtoms N m start ω) q t =
      clearedRowCompanionCompound q.val (finLeftShift m) (Fin.last m)
        (paperIndicatorBetaRaw N m profile ω
          (paperIndicatorFreshRowSite N m start t))
        (paperIndicatorShiftedInterior N m profile center z ω
          (paperIndicatorFreshRowSite N m start t)) := by
  classical
  rw [clearedRowCompanionCompound_eq_orderedCoefficient m q _ _ hβ]
  rw [PaperIndicatorWeights.freshExteriorRow]
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [PaperIndicatorWeights.orderedResetWeight,
    paperIndicatorFreshAtoms_none, paperIndicatorFreshAtoms_some,
    PaperIndicatorWeights.freshSpectralShift, zero_smul, zero_add,
    paperIndicatorBetaRaw_apply]
  rw [add_assoc]
  rw [← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← add_smul]
  by_cases hj : j = center
  · subst j
    simp [paperIndicatorShiftedInterior_apply, sub_eq_add_neg]
  · simp [paperIndicatorShiftedInterior_apply, hj]

/-- Equivalent matrix-level form: the fresh row is the clearing scalar times
the exterior power of the paper's actual sampled transfer matrix. -/
theorem paperIndicatorFreshExteriorRow_eq_clearedCompound_transfer
    (N m : ℕ) [NeZero N] {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (start : ZMod N) (ω : Fin (N * (m + 2)) → ℂ)
    (q : ExteriorDegree (m + 1)) (t : Fin (m + 1))
    (hβ : paperIndicatorBetaRaw N m profile ω
      (paperIndicatorFreshRowSite N m start t) ≠ 0) :
    profile.freshExteriorRow center z
        (paperIndicatorFreshAtoms N m start ω) q t =
      paperIndicatorBetaRaw N m profile ω
          (paperIndicatorFreshRowSite N m start t) •
        compound q.val
          (paperCyclicTransferMatrix N m
            (paperIndicatorBetaRaw N m profile ω)
            (paperIndicatorShiftedInterior N m profile center z ω)
            (paperIndicatorFreshRowSite N m start t)) := by
  rw [paperIndicatorFreshExteriorRow_eq_clearedRowCompanionCompound
    N m profile center z start ω q t hβ]
  rw [clearedRowCompanionCompound,
    paperCyclicTransferMatrix_eq_rowCompanion]

/-- The actual list of denominator-cleared exterior rows in one sampled fresh
block. -/
def paperIndicatorFreshClearedExteriorRows
    (N m : ℕ) [NeZero N] {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (start : ZMod N) (ω : Fin (N * (m + 2)) → ℂ)
    (q : ExteriorDegree (m + 1)) :
    List (Matrix (ExteriorIndex (m + 1) q) (ExteriorIndex (m + 1) q) ℂ) :=
  List.ofFn fun t : Fin (m + 1) =>
    paperIndicatorBetaRaw N m profile ω
        (paperIndicatorFreshRowSite N m start t) •
      compound q.val
        (paperCyclicTransferMatrix N m
          (paperIndicatorBetaRaw N m profile ω)
          (paperIndicatorShiftedInterior N m profile center z ω)
          (paperIndicatorFreshRowSite N m start t))

/-- Alternating exterior trace of the genuine sampled fresh block, with the
outside/frozen product represented by `B`. -/
def paperIndicatorFreshBlockAlternatingTrace
    (N m : ℕ) [NeZero N] {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (start : ZMod N) (ω : Fin (N * (m + 2)) → ℂ)
    (B : (q : ExteriorDegree (m + 1)) →
      Matrix (ExteriorIndex (m + 1) q) (ExteriorIndex (m + 1) q) ℂ) : ℂ :=
  ∑ q : ExteriorDegree (m + 1), (-1 : ℂ) ^ q.val *
    Matrix.trace (B q * chronologicalProduct
      (paperIndicatorFreshClearedExteriorRows
        N m profile center z start ω q))

set_option maxHeartbeats 800000 in
/-- Evaluation of the concrete paper fresh polynomial is exactly the
alternating trace of the actual random-matrix fresh block. -/
theorem eval_paperIndicatorFreshPolynomial_flatSample
    (N m : ℕ) [NeZero N] {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (start : ZMod N) (ω : Fin (N * (m + 2)) → ℂ)
    (B : (q : ExteriorDegree (m + 1)) →
      Matrix (ExteriorIndex (m + 1) q) (ExteriorIndex (m + 1) q) ℂ)
    (r : ExteriorDegree (m + 1))
    (I J : ExteriorIndex (m + 1) r)
    (hβ : ∀ t : Fin (m + 1),
      paperIndicatorBetaRaw N m profile ω
        (paperIndicatorFreshRowSite N m start t) ≠ 0) :
    MultiAffine.eval
        (profile.paperIndicatorFreshPolynomial center z
          (paperIndicatorFreshAtoms N m start ω) B r I J)
        (fun t => paperIndicatorFreshAtoms N m start ω t
          (arbitrarySupportWord I J t)) =
      paperIndicatorFreshBlockAlternatingTrace
        N m profile center z start ω B := by
  rw [profile.eval_paperIndicatorFreshPolynomial]
  unfold paperIndicatorFreshBlockAlternatingTrace
  apply Finset.sum_congr rfl
  intro q _
  apply congrArg (fun X => (-1 : ℂ) ^ q.val * Matrix.trace (B q * X))
  apply congrArg chronologicalProduct
  apply List.ofFn_inj.2
  funext t
  exact paperIndicatorFreshExteriorRow_eq_clearedCompound_transfer
    N m profile center z start ω q t (hβ t)

end CircularLawSection4
