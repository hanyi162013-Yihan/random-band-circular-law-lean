import CircularLawSection4.PaperPressureRow
import CircularLawSection4.OrderedRowLinearity

/-!
# The paper's open exterior pressure on an IID row sample

The concentration argument treats an entire band row as one independent
coordinate.  This file therefore packages the scalar atom law into a row
law and then takes an IID product of rows.  On that literal probability
space it defines the denominator-cleared exterior rows, their chronological
open product, and the pressure observable

`Y_q(n) = log ||A_[1,n]^(q)||`.

The row formula below is not a surrogate model: whenever the right-edge
coefficient is nonzero it is exactly `beta_i * compound q T_i` for the
paper's companion transfer `T_i`.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

namespace PaperIndicatorWeights

variable {m n : ℕ} {c₀ C₀ : ℝ}

/-- One row of scalar atoms, with the paper's `m + 2` band slots. -/
abbrev PaperIndicatorAtomRow (m : ℕ) := Fin (m + 2) → ℂ

/-- IID law of all scalar atoms in one paper row. -/
def paperIndicatorRowMeasure (m : ℕ) (ν : Measure ℂ) [SFinite ν] :
    Measure (PaperIndicatorAtomRow m) :=
  iidMeasure ν (m + 2)

/-- IID law of `n` complete rows.  This is the product structure used when
Efron--Stein replaces one row rather than one scalar entry. -/
def paperIndicatorOpenRowSampleMeasure
    (n m : ℕ) (ν : Measure ℂ) [SFinite ν]
    [IsProbabilityMeasure ν] :
    Measure (Fin n → PaperIndicatorAtomRow m) :=
  let μ := paperIndicatorRowMeasure m ν
  letI : IsProbabilityMeasure μ := iidMeasure_isProbability ν (m + 2)
  iidMeasure μ n

/-- Relabel the scalar slots of one sampled row by the ordered reset/star
alphabet used in the exterior row-linearity identity. -/
def paperIndicatorOpenRowAtoms
    (row : PaperIndicatorAtomRow m) : ResetLabel (m + 1) → ℂ
  | none => row (Fin.last (m + 1))
  | some j => row j.castSucc

@[simp] theorem paperIndicatorOpenRowAtoms_none
    (row : PaperIndicatorAtomRow m) :
    paperIndicatorOpenRowAtoms row none = row (Fin.last (m + 1)) := rfl

@[simp] theorem paperIndicatorOpenRowAtoms_some
    (row : PaperIndicatorAtomRow m) (j : Fin (m + 1)) :
    paperIndicatorOpenRowAtoms row (some j) = row j.castSucc := rfl

/-- The right-edge coefficient `beta_i = b_W xi_{i,W}` of a sampled row. -/
def paperIndicatorOpenBeta
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (row : PaperIndicatorAtomRow m) : ℂ :=
  profile.b (Fin.last (m + 1)) * row (Fin.last (m + 1))

/-- The interior companion row, including the spectral translation in the
slot corresponding to offset zero. -/
def paperIndicatorOpenShiftedInterior
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (row : PaperIndicatorAtomRow m) : Fin (m + 1) → ℂ :=
  fun j => profile.b j.castSucc * row j.castSucc -
    if j = center then z else 0

/-- The paper's companion transfer built from one literal sampled row. -/
def paperIndicatorOpenTransfer
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (row : PaperIndicatorAtomRow m) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  rowCompanion (finLeftShift m) (Fin.last m)
    (profile.paperIndicatorOpenBeta row)
    (profile.paperIndicatorOpenShiftedInterior center z row)

/-- The row-linear exterior matrix, defined without division by `beta`.
This expression therefore exists on every sample, including the null set
where the companion transfer itself would have a zero denominator. -/
def paperIndicatorOpenExteriorRow
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (row : PaperIndicatorAtomRow m) :
    Matrix (ExteriorIndex (m + 1) q) (ExteriorIndex (m + 1) q) ℂ :=
  (∑ ell : ResetLabel (m + 1),
      (profile.orderedResetWeight ell *
        paperIndicatorOpenRowAtoms row ell) • orderedCoefficient m q ell) -
    z • orderedCoefficient m q (some center)

/-- The literal row-linear exterior matrix is the generic `freshExteriorRow`
used by the isolated-monomial and pressure interfaces. -/
theorem paperIndicatorOpenExteriorRow_eq_freshExteriorRow
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (row : PaperIndicatorAtomRow m) :
    profile.paperIndicatorOpenExteriorRow center z q row =
      profile.freshExteriorRow center z
        (fun _ => paperIndicatorOpenRowAtoms row) q (0 : Fin (m + 1)) := by
  classical
  rw [paperIndicatorOpenExteriorRow, freshExteriorRow]
  simp [freshSpectralShift, Fintype.sum_option, sub_eq_add_neg]

/-- On `beta != 0`, one row is exactly the denominator-cleared exterior
power `beta * wedge^q T` of the paper's sampled companion transfer. -/
theorem paperIndicatorOpenExteriorRow_eq_clearedCompound
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (row : PaperIndicatorAtomRow m)
    (hbeta : profile.paperIndicatorOpenBeta row ≠ 0) :
    profile.paperIndicatorOpenExteriorRow center z q row =
      profile.paperIndicatorOpenBeta row •
        compound q.val
          (profile.paperIndicatorOpenTransfer center z row) := by
  classical
  change
    (∑ ell : ResetLabel (m + 1),
        (profile.orderedResetWeight ell *
          paperIndicatorOpenRowAtoms row ell) • orderedCoefficient m q ell) -
        z • orderedCoefficient m q (some center) =
      clearedRowCompanionCompound q.val (finLeftShift m) (Fin.last m)
        (profile.b (Fin.last (m + 1)) * row (Fin.last (m + 1)))
        (fun j => profile.b j.castSucc * row j.castSucc -
          if j = center then z else 0)
  change profile.b (Fin.last (m + 1)) * row (Fin.last (m + 1)) ≠ 0 at hbeta
  rw [clearedRowCompanionCompound_eq_orderedCoefficient m q _ _ hbeta]
  rw [Fintype.sum_option]
  simp only [paperIndicatorOpenRowAtoms_none,
    paperIndicatorOpenRowAtoms_some, orderedResetWeight]
  simp_rw [sub_smul]
  rw [Finset.sum_sub_distrib]
  simp
  abel

/-- The open denominator-cleared exterior product of `n` sampled rows. -/
def paperIndicatorOpenExteriorProduct
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin n → PaperIndicatorAtomRow m) :
    Matrix (ExteriorIndex (m + 1) q) (ExteriorIndex (m + 1) q) ℂ :=
  chronologicalProduct
    (List.ofFn fun i =>
      profile.paperIndicatorOpenExteriorRow center z q (rows i))

/-- The manuscript's random open pressure observable
`Y_q(n) = log ||A_[1,n]^(q)||`. -/
def paperIndicatorOpenPressure
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin n → PaperIndicatorAtomRow m) : ℝ :=
  Real.log ‖profile.paperIndicatorOpenExteriorProduct center z q rows‖

/-- If every right-edge coefficient is nonzero, the open product is
literally the chronological product of the paper's cleared companion
exterior powers. -/
theorem paperIndicatorOpenExteriorProduct_eq_clearedCompounds
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin n → PaperIndicatorAtomRow m)
    (hbeta : ∀ i, profile.paperIndicatorOpenBeta (rows i) ≠ 0) :
    profile.paperIndicatorOpenExteriorProduct center z q rows =
      chronologicalProduct
        (List.ofFn fun i =>
          profile.paperIndicatorOpenBeta (rows i) •
            compound q.val
              (profile.paperIndicatorOpenTransfer center z (rows i))) := by
  unfold paperIndicatorOpenExteriorProduct
  congr 1
  apply List.ofFn_inj.2
  funext i
  exact profile.paperIndicatorOpenExteriorRow_eq_clearedCompound
    center z q (rows i) (hbeta i)

end PaperIndicatorWeights

end CircularLawSection4
