import CircularLawSections56.Section5.LiteralProjectiveCellInputAdapter
import CircularLawSection4.PaperCompanionInvertibility
import CircularLawSection4.PaperIndicatorFlatConcentration

/-!
# Almost-sure invertibility of the literal IID exterior cell

This file transports Section 4's simultaneous companion/compound
invertibility certificate through the exact flat-to-row and reset-labelled
IID equivalences.  The resulting theorem has the literal cell and literal
cell law used by the matrix-product telescope in its conclusion.
-/

open scoped ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
  Matrix Set Set.powersetCard

variable {d : Nat} {c0 C0 : Real}

private theorem chronologicalProduct_isUnit_literal
    {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n]
    (xs : List (Matrix n n R))
    (hxs : ∀ A ∈ xs, IsUnit A) :
    IsUnit (chronologicalProduct xs) := by
  induction xs with
  | nil => simp
  | cons A xs ih =>
      rw [chronologicalProduct_cons]
      exact (ih (fun B hB => hxs B (List.mem_cons_of_mem A hB))).mul
        (hxs A (List.mem_cons_self))

@[simp]
theorem paperIndicatorOpenBeta_flatRows
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (omega : Fin ((d + 1) * (d + 2)) -> Complex)
    (t : Fin (d + 1)) :
    profile.paperIndicatorOpenBeta
        (paperIndicatorFlatRowsEquiv (d + 1) d omega t) =
      profile.b (Fin.last (d + 1)) *
        paperIndicatorXi (d + 1) d omega
          (ZMod.finEquiv (d + 1) t) (Fin.last (d + 1)) := by
  simp [paperIndicatorOpenBeta]

@[simp]
theorem paperIndicatorOpenTransfer_flatRows
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (omega : Fin ((d + 1) * (d + 2)) -> Complex)
    (t : Fin (d + 1)) :
    profile.paperIndicatorOpenTransfer center z
        (paperIndicatorFlatRowsEquiv (d + 1) d omega t) =
      paperIndicatorTransferMatrix (d + 1) d center profile.b omega z
        (ZMod.finEquiv (d + 1) t) := by
  unfold paperIndicatorOpenTransfer paperIndicatorTransferMatrix
    paperShiftedScalarTransfer
  rw [paperCyclicTransferMatrix_eq_rowCompanion]
  congr 2

/-- On the canonical flat sample, Section 4's simultaneous cleared-compound
certificate makes the literal open exterior product invertible almost surely.
-/
theorem ae_paperIndicatorOpenExteriorProduct_flatRows_isUnit_complex_withDensity
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : Complex)
    (q : ExteriorDegree (d + 1))
    {f : Complex -> ENNReal} {L : ENNReal}
    [IsProbabilityMeasure ((volume : Measure Complex).withDensity f)]
    (hf : ∀ᵐ w : Complex ∂volume, f w ≤ L) :
    ∀ᵐ omega ∂paperIndicatorSampleMeasure (d + 1) d
          ((volume : Measure Complex).withDensity f),
      IsUnit (profile.paperIndicatorOpenExteriorProduct center z q
        (paperIndicatorFlatRowsEquiv (d + 1) d omega)) := by
  let _ : NeZero (d + 1) := ⟨Nat.succ_ne_zero d⟩
  filter_upwards [
    ae_paperIndicator_rightEdge_ne_zero_complex_withDensity
      (d + 1) d profile.b
        (profile.b_ne_zero hc0 (Fin.last (d + 1))) hf,
    ae_paperIndicatorTransferMatrix_all_isUnit_complex_withDensity
      (d + 1) d center hcenter profile.b
        (profile.b_ne_zero hc0 0)
        (profile.b_ne_zero hc0 (Fin.last (d + 1))) z hf] with omega hbeta hall
  rw [profile.paperIndicatorOpenExteriorProduct_eq_clearedCompounds]
  · apply chronologicalProduct_isUnit_literal
    intro A hA
    simp only [List.mem_ofFn] at hA
    obtain ⟨t, rfl⟩ := hA
    simpa using (hall (ZMod.finEquiv (d + 1) t)).2 q.val |>.2
  · intro t
    simpa using hbeta (ZMod.finEquiv (d + 1) t)

/-- The exact target needed by an AE matrix telescope: a literal IID exterior
cell is a unit almost surely under the literal reset-labelled cell law. -/
theorem ae_literalPaperExteriorCell_isUnit_complex_withDensity
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : Complex)
    (q : ExteriorDegree (d + 1))
    {f : Complex -> ENNReal} {L : ENNReal}
    [IsProbabilityMeasure ((volume : Measure Complex).withDensity f)]
    (hf : ∀ᵐ w : Complex ∂volume, f w ≤ L) :
    ∀ᵐ omega ∂literalPaperExteriorCellMeasure d
          ((volume : Measure Complex).withDensity f),
      IsUnit (literalPaperExteriorCell profile center z q omega) := by
  let nu : Measure Complex := (volume : Measure Complex).withDensity f
  let _ : SigmaFinite nu := inferInstance
  let _ : IsProbabilityMeasure nu := inferInstance
  let _ : NeZero (d + 1) := ⟨Nat.succ_ne_zero d⟩
  let P : (Fin (d + 1) -> PaperIndicatorAtomRow d) -> Prop :=
    fun rows => IsUnit (profile.paperIndicatorOpenExteriorProduct center z q rows)
  have hflat : ∀ᵐ omega ∂paperIndicatorSampleMeasure (d + 1) d nu,
      P (paperIndicatorFlatRowsEquiv (d + 1) d omega) := by
    simpa only [nu, P] using
      ae_paperIndicatorOpenExteriorProduct_flatRows_isUnit_complex_withDensity
        profile hc0 center hcenter z q hf
  have hrows : ∀ᵐ rows ∂paperIndicatorOpenRowSampleMeasure (d + 1) d nu,
      P rows := by
    have hback :=
      (paperIndicatorFlatRows_measurePreserving (d + 1) d nu).symm
    have hpull := hback.quasiMeasurePreserving.ae hflat
    simpa [P] using hpull
  have hliteral :=
    (literalPaperCellRows_measurePreserving d nu).quasiMeasurePreserving.ae hrows
  filter_upwards [hliteral] with omega homega
  have hrowsEq : literalPaperCellRowsMeasurableEquiv d omega =
      literalPaperCellRows omega := by
    funext t k
    rfl
  rw [hrowsEq] at homega
  simpa only [P, literalPaperExteriorCell] using homega

end CircularLawSections56.Section5
