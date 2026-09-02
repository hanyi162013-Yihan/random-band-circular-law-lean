import CircularLawSections56.Section5.LiteralProjectiveCellInputAdapter

/-!
# Global integrability of the literal IID cell product

This file reassociates `n` literal cells, each containing `d + 1` complete
rows, with one chronological open product of `n * (d + 1)` complete IID
rows.  It then transports Section 4's global `L²` open-pressure theorem
back to the genuine IID matrix-cell product.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

set_option maxHeartbeats 800000

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights Matrix

variable {d : Nat} {c0 C0 : Real}

local instance literalPaperExteriorCellMeasureProbability
    (d : Nat) (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (literalPaperExteriorCellMeasure d nu) := by
  unfold literalPaperExteriorCellMeasure
  infer_instance

local instance literalPaperExteriorCellMeasureSigmaFinite
    (d : Nat) (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    SigmaFinite (literalPaperExteriorCellMeasure d nu) := by
  infer_instance

local instance literalPaperExteriorCellIidProbability
    (N d : Nat) (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    IsProbabilityMeasure
      (iidMeasure (literalPaperExteriorCellMeasure d nu) N) :=
  iidMeasure_isProbability (literalPaperExteriorCellMeasure d nu) N

local instance literalPaperExteriorCellIidSigmaFinite
    (N d : Nat) (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    SigmaFinite (iidMeasure (literalPaperExteriorCellMeasure d nu) N) := by
  infer_instance

local instance paperIndicatorOpenRowSampleMeasureProbability
    (N d : Nat) (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (paperIndicatorOpenRowSampleMeasure N d nu) := by
  let muRow := paperIndicatorRowMeasure d nu
  let _ : IsProbabilityMeasure muRow := iidMeasure_isProbability nu (d + 2)
  simpa only [paperIndicatorOpenRowSampleMeasure, muRow] using
    iidMeasure_isProbability muRow N

local instance paperIndicatorOpenRowSampleMeasureSigmaFinite
    (N d : Nat) (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    SigmaFinite (paperIndicatorOpenRowSampleMeasure N d nu) := by
  infer_instance

/-- Apply a measurable equivalence independently in every coordinate of a
finite IID sample. -/
theorem measurePreserving_iid_piCongrRight
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (n : Nat) (mu : Measure X) (nu : Measure Y)
    [SFinite mu] [SFinite nu]
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (e : X ≃ᵐ Y) (he : MeasurePreserving e mu nu) :
    MeasurePreserving (MeasurableEquiv.piCongrRight (fun _ : Fin n => e))
      (iidMeasure mu n) (iidMeasure nu n) := by
  refine ⟨(MeasurableEquiv.piCongrRight (fun _ : Fin n => e)).measurable, ?_⟩
  rw [iidMeasure_eq_pi, iidMeasure_eq_pi]
  change Measure.map (fun x i => e (x i)) (Measure.pi fun _ : Fin n => mu) =
    Measure.pi fun _ : Fin n => nu
  rw [Measure.pi_map_pi (fun _ => e.measurable.aemeasurable)]
  simp_rw [he.map_eq]

/-- Reassociate `n` reset-labelled literal cells as one flat chronological
block of `n * (d + 1)` complete paper rows.  The row coordinate varies
fastest inside each cell. -/
def literalIidCellRowsMeasurableEquiv (n d : Nat) :
    (Fin n -> LiteralPaperCellAtoms d) ≃ᵐ
      (Fin (n * (d + 1)) -> PaperIndicatorAtomRow d) :=
  (MeasurableEquiv.piCongrRight
      (fun _ : Fin n => literalPaperCellRowsMeasurableEquiv d)).trans
    (flatIIDRowsMeasurableEquiv n (d + 1)).symm

@[simp]
theorem literalIidCellRowsMeasurableEquiv_apply
    (n d : Nat) (omega : Fin n -> LiteralPaperCellAtoms d)
    (r : Fin (n * (d + 1))) (k : Fin (d + 2)) :
    literalIidCellRowsMeasurableEquiv n d omega r k =
      literalPaperCellRows
        (omega (finProdFinEquiv.symm r).1)
        (finProdFinEquiv.symm r).2 k := by
  unfold literalIidCellRowsMeasurableEquiv
  change (flatIIDRowsMeasurableEquiv n (d + 1)).symm
      ((MeasurableEquiv.piCongrRight
        (fun _ : Fin n => literalPaperCellRowsMeasurableEquiv d)) omega) r k = _
  rw [flatIIDRowsMeasurableEquiv_symm_apply]
  change literalPaperCellRowsMeasurableEquiv d
      (omega (finProdFinEquiv.symm r).1)
      (finProdFinEquiv.symm r).2 k = _
  rw [literalPaperCellRowsMeasurableEquiv_apply]

/-- The reassociation from IID literal cells to one IID row block preserves
the laws exactly. -/
theorem literalIidCellRows_measurePreserving
    (n d : Nat) (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    MeasurePreserving (literalIidCellRowsMeasurableEquiv n d)
      (iidMeasure (literalPaperExteriorCellMeasure d nu) n)
      (paperIndicatorOpenRowSampleMeasure (n * (d + 1)) d nu) := by
  let muCell := literalPaperExteriorCellMeasure d nu
  let muRow := paperIndicatorRowMeasure d nu
  let _ : IsProbabilityMeasure muCell :=
    literalPaperExteriorCellMeasureProbability d nu
  let _ : IsProbabilityMeasure muRow := iidMeasure_isProbability nu (d + 2)
  have hCells := measurePreserving_iid_piCongrRight n muCell
    (paperIndicatorOpenRowSampleMeasure (d + 1) d nu)
    (literalPaperCellRowsMeasurableEquiv d)
    (literalPaperCellRows_measurePreserving d nu)
  have hFlatten := (flatIIDRows_measurePreserving n (d + 1) muRow).symm
  change MeasurePreserving (literalIidCellRowsMeasurableEquiv n d)
    (iidMeasure muCell n) (iidMeasure muRow (n * (d + 1)))
  simpa only [literalIidCellRowsMeasurableEquiv,
    paperIndicatorOpenRowSampleMeasure, muRow,
    MeasurableEquiv.coe_trans, Function.comp_def] using hFlatten.comp hCells

/-- Chronological multiplication commutes with flattening a list of row
blocks. -/
theorem chronologicalProduct_flatten
    {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (xss : List (List (Matrix ι ι R))) :
    chronologicalProduct xss.flatten =
      chronologicalProduct (xss.map chronologicalProduct) := by
  induction xss with
  | nil => simp
  | cons xs xss ih =>
      simp only [List.flatten_cons, List.map_cons, chronologicalProduct_append,
        chronologicalProduct_cons, ih]

/-- The genuine product of literal cells is pointwise the single open
exterior product on the flattened chronological row block. -/
theorem iidMatrixCellProduct_literalPaperExteriorCell_eq_openProduct
    (n : Nat)
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (omega : Fin n -> LiteralPaperCellAtoms d) :
    iidMatrixCellProduct (literalPaperExteriorCell profile center z q) omega =
      profile.paperIndicatorOpenExteriorProduct center z q
        (literalIidCellRowsMeasurableEquiv n d omega) := by
  classical
  unfold iidMatrixCellProduct literalPaperExteriorCell
    paperIndicatorOpenExteriorProduct
  rw [List.ofFn_comp']
  rw [← chronologicalProduct_flatten]
  congr 1
  rw [List.ofFn_mul]
  congr 1
  apply List.ofFn_inj.2
  funext i
  apply List.ofFn_inj.2
  funext j
  have hrBound : i * (d + 1) + j < n * (d + 1) := by
    calc
      i * (d + 1) + j < i * (d + 1) + (d + 1) :=
        Nat.add_lt_add_left j.isLt _
      _ = (i + 1) * (d + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      _ <= n * (d + 1) := Nat.mul_le_mul_right (d + 1) i.isLt
  let r0 : Fin (n * (d + 1)) := finProdFinEquiv (i, j)
  have hr : (⟨i * (d + 1) + j, hrBound⟩ : Fin (n * (d + 1))) = r0 := by
    apply Fin.ext
    change i * (d + 1) + j = j + (d + 1) * i
    rw [Nat.mul_comm (d + 1) i, Nat.add_comm]
  rw [hr]
  congr 1
  funext k
  rw [literalIidCellRowsMeasurableEquiv_apply]
  simp only [r0, Equiv.symm_apply_apply]

/-- Under the same bounded-density and second-moment hypotheses as Section
4, the logarithmic operator norm of every finite genuine IID cell product is
integrable. -/
theorem complex_literalPaperExteriorCell_iidMatrixCellLogPotential_integrable
    {L : Real}
    (nu : Measure Complex) [SigmaFinite nu] [IsProbabilityMeasure nu]
    (hnu : ComplexBallBound nu (ENNReal.ofReal L)) (hL : 0 <= L)
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (hnuInt : Integrable (fun u : Complex => ‖u‖ ^ 2) nu)
    (hnuSecond : ∫ u : Complex, ‖u‖ ^ 2 ∂nu <= 1) :
    ∀ n, Integrable
      (iidMatrixCellLogPotential
        (literalPaperExteriorCell profile center z q))
      (iidMeasure (literalPaperExteriorCellMeasure d nu) n) := by
  let _ : Nonempty (ExteriorIndex (d + 1) q) :=
    CircularLawSection4.exteriorIndex_nonempty (d + 1) q
  intro n
  by_cases hn : n = 0
  · subst n
    have hzero :
        iidMatrixCellLogPotential
          (literalPaperExteriorCell profile center z q) =
            (fun _ : Fin 0 -> LiteralPaperCellAtoms d => 0) := by
      funext omega
      exact iidMatrixCellLogPotential_zero _ omega
    rw [hzero]
    exact integrable_const 0
  · have hRowsPos : 0 < n * (d + 1) :=
      Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.succ_pos d)
    have hCount : (n * (d + 1) - 1) + 1 = n * (d + 1) :=
      Nat.sub_add_cancel hRowsPos
    have hmem := profile.complex_paperIndicatorOpenPressure_memLp_two
      (m := d) (n := n * (d + 1) - 1) nu hnu hL hc0 hsqrt
        center z q hnuInt hnuSecond
    have hrowInt : Integrable
        (profile.paperIndicatorOpenPressure center z q)
        (paperIndicatorOpenRowSampleMeasure (n * (d + 1)) d nu) := by
      rw [← hCount]
      exact hmem.integrable (by norm_num)
    have hmp := literalIidCellRows_measurePreserving n d nu
    have hcomp :=
      (hmp.integrable_comp_emb
        (literalIidCellRowsMeasurableEquiv n d).measurableEmbedding).2 hrowInt
    have hfun :
        (profile.paperIndicatorOpenPressure center z q) ∘
            (literalIidCellRowsMeasurableEquiv n d) =
          iidMatrixCellLogPotential
            (literalPaperExteriorCell profile center z q) := by
      funext omega
      unfold Function.comp paperIndicatorOpenPressure iidMatrixCellLogPotential
      rw [iidMatrixCellProduct_literalPaperExteriorCell_eq_openProduct]
    rw [← hfun]
    exact hcomp

end CircularLawSections56.Section5
