import CircularLawSections56.Section5.LiteralProjectiveCellInputAdapter
import CircularLawSections56.Section5.LiteralIidMatrixCellAEAdapter
import CircularLawSections56.Section5.LiteralGlobalIntegrabilityAdapter
import CircularLawSection4.PaperCompanionInvertibility
import CircularLawSection4.PaperIndicatorFlatConcentration

/-!
# Literal real-input exterior-cell package

Real scalar atoms are complexified coordinatewise, while all transfer and
exterior matrices remain complex.  This file transports Section 4's real
projective, open-pressure, and invertibility results to the exact literal
cell law and then instantiates the AE matrix-product telescope.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

set_option maxHeartbeats 1200000

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
  Matrix Set Set.powersetCard

variable {d : Nat} {c0 C0 : Real}

local instance realOpenRowSampleProbability
    (n d : Nat) (nu : Measure Real)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (paperIndicatorRealOpenRowSampleMeasure n d nu) := by
  let muRow := paperIndicatorRealRowMeasure d nu
  let _ : IsProbabilityMeasure muRow := iidMeasure_isProbability nu (d + 2)
  simpa only [paperIndicatorRealOpenRowSampleMeasure, muRow] using
    iidMeasure_isProbability muRow n

abbrev LiteralRealPaperCellAtoms (d : Nat) := FreshAtomIndex (d + 1) -> Real

def literalRealPaperCellRows (omega : LiteralRealPaperCellAtoms d) :
    Fin (d + 1) -> PaperIndicatorRealAtomRow d :=
  fun t k => omega (t, paperOperatorAffineLabelEquiv d k)

def literalRealPaperCellRowsMeasurableEquiv (d : Nat) :
    LiteralRealPaperCellAtoms d ≃ᵐ
      (Fin (d + 1) -> PaperIndicatorRealAtomRow d) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : FreshAtomIndex (d + 1) => Real)
      (Equiv.prodCongr (Equiv.refl (Fin (d + 1)))
        (paperOperatorAffineLabelEquiv d))).symm.trans
    (MeasurableEquiv.curry (Fin (d + 1)) (Fin (d + 2)) Real)

@[simp] theorem literalRealPaperCellRowsMeasurableEquiv_apply
    (omega : LiteralRealPaperCellAtoms d) (t : Fin (d + 1))
    (k : Fin (d + 2)) :
    literalRealPaperCellRowsMeasurableEquiv d omega t k =
      literalRealPaperCellRows omega t k := by
  rfl

def literalRealPaperExteriorCellMeasure (d : Nat) (nu : Measure Real) :
    Measure (LiteralRealPaperCellAtoms d) :=
  Measure.pi (fun _ : FreshAtomIndex (d + 1) => nu)

local instance literalRealPaperCellMeasureProbability
    (d : Nat) (nu : Measure Real)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (literalRealPaperExteriorCellMeasure d nu) := by
  unfold literalRealPaperExteriorCellMeasure
  infer_instance

local instance literalRealPaperCellMeasureSigmaFinite
    (d : Nat) (nu : Measure Real)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    SigmaFinite (literalRealPaperExteriorCellMeasure d nu) := by
  infer_instance

local instance literalRealPaperCellIidProbability
    (n d : Nat) (nu : Measure Real)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (iidMeasure (literalRealPaperExteriorCellMeasure d nu) n) :=
  iidMeasure_isProbability _ n

local instance literalRealPaperCellIidSigmaFinite
    (n d : Nat) (nu : Measure Real)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    SigmaFinite (iidMeasure (literalRealPaperExteriorCellMeasure d nu) n) := by
  infer_instance

theorem literalRealPaperCellRows_measurePreserving
    (d : Nat) (nu : Measure Real)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    MeasurePreserving (literalRealPaperCellRowsMeasurableEquiv d)
      (literalRealPaperExteriorCellMeasure d nu)
      (paperIndicatorRealOpenRowSampleMeasure (d + 1) d nu) := by
  let e := Equiv.prodCongr (Equiv.refl (Fin (d + 1)))
    (paperOperatorAffineLabelEquiv d)
  have hreindex : MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : FreshAtomIndex (d + 1) => Real) e).symm
      (Measure.pi (fun _ : FreshAtomIndex (d + 1) => nu))
      (Measure.pi (fun _ : Fin (d + 1) × Fin (d + 2) => nu)) := by
    exact (measurePreserving_piCongrLeft
      (fun _ : FreshAtomIndex (d + 1) => nu) e).symm
  let _ : IsProbabilityMeasure (iidMeasure nu (d + 2)) :=
    iidMeasure_isProbability nu (d + 2)
  have hcurry := measurePreserving_curry_fin_iid (d + 1) (d + 2) nu
  change MeasurePreserving (literalRealPaperCellRowsMeasurableEquiv d)
    (Measure.pi (fun _ : FreshAtomIndex (d + 1) => nu))
    (iidMeasure (iidMeasure nu (d + 2)) (d + 1))
  rw [iidMeasure_eq_pi]
  simp_rw [iidMeasure_eq_pi nu (d + 2)]
  simpa only [literalRealPaperExteriorCellMeasure,
    literalRealPaperCellRowsMeasurableEquiv, e,
    MeasurableEquiv.coe_trans, Function.comp_def] using hcurry.comp hreindex

def literalRealPaperExteriorCell
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (omega : LiteralRealPaperCellAtoms d) :
    Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex :=
  profile.paperIndicatorOpenExteriorProduct center z q
    (paperIndicatorComplexifyRealRows (literalRealPaperCellRows omega))

theorem measurable_literalRealPaperExteriorCell_vectorNorm
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (v : EuclideanSpace Complex (ExteriorIndex (d + 1) q)) :
    Measurable (fun omega : LiteralRealPaperCellAtoms d =>
      ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
        ((literalRealPaperExteriorCell profile center z q omega).mulVec
          (fun j => v j))‖) := by
  have hrows : Continuous (fun omega : LiteralRealPaperCellAtoms d =>
      paperIndicatorComplexifyRealRows (literalRealPaperCellRows omega)) := by
    apply continuous_pi
    intro t
    apply continuous_pi
    intro k
    exact Complex.continuous_ofReal.comp
      (continuous_apply (t, paperOperatorAffineLabelEquiv d k))
  have hcell : Continuous (fun omega : LiteralRealPaperCellAtoms d =>
      literalRealPaperExteriorCell profile center z q omega) :=
    (profile.continuous_paperIndicatorOpenExteriorProduct
      center z q (d + 1)).comp hrows
  have hmul : Measurable (fun omega : LiteralRealPaperCellAtoms d =>
      (literalRealPaperExteriorCell profile center z q omega).mulVec
        (fun j => v j)) := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec]
    exact Finset.measurable_sum Finset.univ fun j _ =>
      Measurable.mul
        (((continuous_apply j).comp ((continuous_apply i).comp hcell)).measurable)
        measurable_const
  exact (((EuclideanSpace.equiv
    (ExteriorIndex (d + 1) q) Complex).symm.continuous.measurable.comp hmul).norm)

theorem real_literalPaperExteriorCell_logOpNorm_integrable
    {L : Real}
    (nu : Measure Real) [SigmaFinite nu] [IsProbabilityMeasure nu]
    (hnu : RealIntervalBound nu (ENNReal.ofReal L)) (hL : 0 <= L)
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (hnuInt : Integrable (fun u : Real => u ^ 2) nu)
    (hnuSecond : ∫ u : Real, u ^ 2 ∂nu = 1)
    (theta : Real) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    Integrable (fun omega : LiteralRealPaperCellAtoms d =>
      Real.log ‖literalRealPaperExteriorCell profile center z q omega‖)
      (literalRealPaperExteriorCellMeasure d nu) := by
  have hmem := profile.real_paperIndicatorOpenPressure_memLp_two
    (m := d) (n := d) nu hnu hL hc0 hsqrt center z q
      hnuInt hnuSecond theta htheta0 htheta1
  have hrow : Integrable
      (profile.paperIndicatorOpenPressureOfReal center z q)
      (paperIndicatorRealOpenRowSampleMeasure (d + 1) d nu) :=
    hmem.integrable (by norm_num)
  have hmp := literalRealPaperCellRows_measurePreserving d nu
  have hcomp := (hmp.integrable_comp_emb
    (literalRealPaperCellRowsMeasurableEquiv d).measurableEmbedding).2 hrow
  have heq : (literalRealPaperCellRowsMeasurableEquiv d :
      LiteralRealPaperCellAtoms d -> Fin (d + 1) -> PaperIndicatorRealAtomRow d) =
      literalRealPaperCellRows := by
    funext omega t k
    rfl
  simpa only [Function.comp_def, paperIndicatorOpenPressureOfReal,
    paperIndicatorOpenPressure, literalRealPaperExteriorCell, heq] using hcomp

private theorem chronologicalProduct_isUnit_realCell
    {n : Type*} [Fintype n] [DecidableEq n]
    (xs : List (Matrix n n Complex)) (hxs : ∀ A ∈ xs, IsUnit A) :
    IsUnit (chronologicalProduct xs) := by
  induction xs with
  | nil => simp
  | cons A xs ih =>
      rw [chronologicalProduct_cons]
      exact (ih (fun B hB => hxs B (List.mem_cons_of_mem A hB))).mul
        (hxs A List.mem_cons_self)

@[simp] theorem paperIndicatorOpenTransfer_realFlatRows
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (omega : Fin ((d + 1) * (d + 2)) -> Real) (t : Fin (d + 1)) :
    profile.paperIndicatorOpenTransfer center z
        (paperIndicatorComplexifyRealRow
          (paperIndicatorRealFlatRowsEquiv (d + 1) d omega t)) =
      paperIndicatorTransferMatrixOfReal (d + 1) d center profile.b omega z
        (ZMod.finEquiv (d + 1) t) := by
  unfold paperIndicatorOpenTransfer paperIndicatorTransferMatrixOfReal
    paperShiftedScalarTransfer
  rw [paperCyclicTransferMatrix_eq_rowCompanion]
  congr 2

theorem ae_literalRealPaperExteriorCell_isUnit_withDensity
    (profile : PaperIndicatorWeights (d + 1) c0 C0) (hc0 : 0 < c0)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : Complex)
    (q : ExteriorDegree (d + 1))
    {f : Real -> ENNReal} {L : ENNReal}
    [IsProbabilityMeasure ((volume : Measure Real).withDensity f)]
    (hf : ∀ᵐ w : Real ∂volume, f w <= L) :
    ∀ᵐ omega ∂literalRealPaperExteriorCellMeasure d
        ((volume : Measure Real).withDensity f),
      IsUnit (literalRealPaperExteriorCell profile center z q omega) := by
  let nu : Measure Real := volume.withDensity f
  let _ : SigmaFinite nu := inferInstance
  let _ : IsProbabilityMeasure nu := inferInstance
  let _ : NeZero (d + 1) := ⟨Nat.succ_ne_zero d⟩
  let P : (Fin (d + 1) -> PaperIndicatorRealAtomRow d) -> Prop := fun rows =>
    IsUnit (profile.paperIndicatorOpenExteriorProduct center z q
      (paperIndicatorComplexifyRealRows rows))
  have hflat : ∀ᵐ omega ∂iidMeasure nu ((d + 1) * (d + 2)),
      P (paperIndicatorRealFlatRowsEquiv (d + 1) d omega) := by
    filter_upwards [
      ae_paperIndicator_rightEdge_ne_zero_real_withDensity
        (d + 1) d profile.b
          (profile.b_ne_zero hc0 (Fin.last (d + 1))) hf,
      ae_paperIndicatorTransferMatrix_all_isUnit_real_withDensity
        (d + 1) d center hcenter profile.b
          (profile.b_ne_zero hc0 0)
          (profile.b_ne_zero hc0 (Fin.last (d + 1))) z hf] with omega hbeta hall
    dsimp only [P]
    rw [profile.paperIndicatorOpenExteriorProduct_eq_clearedCompounds]
    · apply chronologicalProduct_isUnit_realCell
      intro A hA
      simp only [List.mem_ofFn] at hA
      obtain ⟨t, rfl⟩ := hA
      change IsUnit
        (profile.paperIndicatorOpenBeta
            (paperIndicatorComplexifyRealRow
              (paperIndicatorRealFlatRowsEquiv (d + 1) d omega t)) •
          compound q.val (profile.paperIndicatorOpenTransfer center z
            (paperIndicatorComplexifyRealRow
              (paperIndicatorRealFlatRowsEquiv (d + 1) d omega t))))
      rw [paperIndicatorOpenTransfer_realFlatRows]
      simpa [paperIndicatorOpenBeta, paperIndicatorComplexifyRealRows,
        paperIndicatorComplexifyRealRow] using
          (hall (ZMod.finEquiv (d + 1) t)).2 q.val |>.2
    · intro t
      simpa [paperIndicatorOpenBeta, paperIndicatorComplexifyRealRows,
        paperIndicatorComplexifyRealRow] using
          hbeta (ZMod.finEquiv (d + 1) t)
  have hrows : ∀ᵐ rows ∂paperIndicatorRealOpenRowSampleMeasure (d + 1) d nu,
      P rows := by
    have hback := (paperIndicatorRealFlatRows_measurePreserving
      (d + 1) d nu).symm
    have hpull := hback.quasiMeasurePreserving.ae hflat
    simpa [P] using hpull
  have hlit := (literalRealPaperCellRows_measurePreserving d nu)
    |>.quasiMeasurePreserving.ae hrows
  filter_upwards [hlit] with omega homega
  have heq : literalRealPaperCellRowsMeasurableEquiv d omega =
      literalRealPaperCellRows omega := by
    funext t k
    rfl
  rw [heq] at homega
  simpa only [P, literalRealPaperExteriorCell] using homega

/-! ## Real projective one-cell lower input -/

noncomputable def realLiteralProjectiveCellLoss
    (d : Nat) (c0 L : Real) (q : ExteriorDegree (d + 1)) : Real :=
  paperProjectiveCoefficientLogLoss d c0 q +
    (Real.log (max 1 (((d + 1 : Nat) : Real) * (4 * L))) + 1) /
      (((1 : Nat) : Real) / ((d + 1 : Nat) : Real))

theorem realLiteralProjectiveCellLoss_nonneg
    (d : Nat) (c0 L : Real) (q : ExteriorDegree (d + 1)) :
    0 <= realLiteralProjectiveCellLoss d c0 L q := by
  unfold realLiteralProjectiveCellLoss
  apply add_nonneg (paperProjectiveCoefficientLogLoss_nonneg d c0 q)
  apply div_nonneg
  · have hlog : 0 <= Real.log
        (max 1 (((d + 1 : Nat) : Real) * (4 * L))) :=
      Real.log_nonneg (le_max_left _ _)
    linarith
  · positivity

theorem paperProjectiveFreshVector_real_logDeficit_of_topCoeff
    (profile : PaperIndicatorWeights (d + 1) c0 C0) (hc0 : 0 < c0)
    (center : Fin (d + 1)) (z : Complex)
    (atoms : Fin (d + 1) -> ResetLabel (d + 1) -> Complex)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) Complex) (hB : 0 < ‖B‖)
    (v : EuclideanSpace Complex (ExteriorIndex (d + 1) q))
    (o I J : ExteriorIndex (d + 1) q)
    (hcoefficient :
      (Real.sqrt (c0 / (d + 2 : Real))) ^ (d + 1) *
          (‖B‖ / (Fintype.card (ExteriorIndex (d + 1) q) : Real) ^ 3) <=
        ‖MultiAffine.topCoeff
          (profile.paperProjectiveFreshPolynomial center z atoms q B v o I J)‖)
    (nu : Measure Real) [SFinite nu] [IsProbabilityMeasure nu]
    {L : Real} (hL : 0 <= L)
    (hnu : RealIntervalBound nu (ENNReal.ofReal L)) :
    let radius := fun x : Fin (d + 1) -> Real =>
      ‖profile.paperProjectiveFreshVectorOfReal center z atoms q B v I J x‖
    iidMeasure nu (d + 1) {x | radius x = 0} = 0 ∧
      Integrable (fun x => logDeficit ‖B‖ (radius x))
        (iidMeasure nu (d + 1)) ∧
      (∫ x, logDeficit ‖B‖ (radius x) ∂iidMeasure nu (d + 1)) <=
        realLiteralProjectiveCellLoss d c0 L q := by
  let _ := iidMeasure_isProbability nu (d + 1)
  let _ : Nonempty (ExteriorIndex (d + 1) q) :=
    exteriorIndex_nonempty (d + 1) q
  let p := profile.paperProjectiveFreshPolynomial center z atoms q B v o I J
  let radius := fun x : Fin (d + 1) -> Real =>
    ‖profile.paperProjectiveFreshVectorOfReal center z atoms q B v I J x‖
  have hbmin : 0 < Real.sqrt (c0 / (d + 2 : Real)) :=
    Real.sqrt_pos.2 (div_pos hc0 (by positivity))
  have hcard : 0 < (Fintype.card (ExteriorIndex (d + 1) q) : Real) := by
    exact_mod_cast Fintype.card_pos
  have htop : 0 < ‖p.topCoeff‖ := by
    apply (mul_pos (pow_pos hbmin _)
      (div_pos hB (pow_pos hcard _))).trans_le
    exact hcoefficient
  obtain ⟨hzero, _hae, hcoordinate, hcoordinateBound⟩ :=
    iid_realInput_complex_positiveLogLoss_of_intervalBound nu hL hnu p htop
  have hscale :=
    profile.log_norm_sub_log_topCoeff_le_paperProjectiveCoefficientLogLoss
      hc0 center z atoms q B hB v o I J hcoefficient
  have hlift := integrable_logDeficit_of_coordinate (iidMeasure nu (d + 1))
    p.continuous_realInputEval.norm.measurable
    (profile.continuous_paperProjectiveFreshVectorOfReal
      center z atoms q B v I J).norm.measurable
    (fun x => norm_nonneg _) (fun x => norm_nonneg _) hzero
    (fun x => profile.norm_realInputEval_paperProjectiveFreshPolynomial_le
      center z atoms q B v o I J x)
    (paperProjectiveCoefficientLogLoss_nonneg d c0 q) hscale
    (by simpa only [logDeficit_eq_positiveLogLoss] using hcoordinate)
  refine ⟨measure_zeroSet_of_coordinate (iidMeasure nu (d + 1))
      (fun x => norm_nonneg _) hzero
      (fun x => profile.norm_realInputEval_paperProjectiveFreshPolynomial_le
        center z atoms q B v o I J x), hlift.1, ?_⟩
  calc
    (∫ x, logDeficit ‖B‖ (radius x) ∂iidMeasure nu (d + 1)) <=
        paperProjectiveCoefficientLogLoss d c0 q +
          ∫ x, logDeficit ‖p.topCoeff‖ ‖realInputEval p x‖
            ∂iidMeasure nu (d + 1) := hlift.2
    _ <= realLiteralProjectiveCellLoss d c0 L q := by
      simpa only [logDeficit_eq_positiveLogLoss,
        realLiteralProjectiveCellLoss, add_comm] using
        add_le_add_right hcoordinateBound
          (paperProjectiveCoefficientLogLoss d c0 q)

theorem literalPaperExteriorCell_complexify_eq_real
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (omega : LiteralRealPaperCellAtoms d) :
    literalPaperExteriorCell profile center z q (fun u => (omega u : Complex)) =
      literalRealPaperExteriorCell profile center z q omega := by
  unfold literalPaperExteriorCell literalRealPaperExteriorCell
  congr 2

theorem real_literalPaperExteriorCell_vector_logDeficit
    (profile : PaperIndicatorWeights (d + 1) c0 C0) (hc0 : 0 < c0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (v : EuclideanSpace Complex (ExteriorIndex (d + 1) q)) (hv : ‖v‖ = 1)
    (nu : Measure Real) [SigmaFinite nu] [IsProbabilityMeasure nu]
    {L : Real} (hL : 0 <= L)
    (hnu : RealIntervalBound nu (ENNReal.ofReal L)) :
    let radius := fun omega : LiteralRealPaperCellAtoms d =>
      ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
        ((literalRealPaperExteriorCell profile center z q omega).mulVec
          (fun j => v j))‖
    let mu := literalRealPaperExteriorCellMeasure d nu
    mu {omega | radius omega = 0} = 0 ∧
      Integrable (fun omega => logDeficit 1 (radius omega)) mu ∧
      (∫ omega, logDeficit 1 (radius omega) ∂mu) <=
        realLiteralProjectiveCellLoss d c0 L q := by
  classical
  let _ : Nonempty (ExteriorIndex (d + 1) q) := exteriorIndex_nonempty _ q
  obtain ⟨o, I, J, hcoef⟩ :=
    exists_uniform_paperProjectiveFreshPolynomial_topCoeff_lower
      profile center z q (1 : Matrix _ _ Complex) v hv
  let word := arbitrarySupportWord I J
  let e := splitFreshAtomMeasurableEquiv (K := Real) word
  let mux := Measure.pi (fun _ : Fin (d + 1) => nu)
  let muy := Measure.pi (fun _ : UnselectedFreshIndex word => nu)
  let mu := literalRealPaperExteriorCellMeasure d nu
  let baseAtoms := fun y : UnselectedFreshIndex word -> Real =>
    fun t ell => ((e.symm ((fun _ => 0), y) (t, ell) : Real) : Complex)
  let radius := fun omega : LiteralRealPaperCellAtoms d =>
    ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
      ((literalRealPaperExteriorCell profile center z q omega).mulVec
        (fun j => v j))‖
  have heval (x : Fin (d + 1) -> Real)
      (y : UnselectedFreshIndex word -> Real) :
      ‖profile.paperProjectiveFreshVectorOfReal center z (baseAtoms y) q 1
          v I J x‖ = radius (e.symm (x, y)) := by
    rw [paperProjectiveFreshVectorOfReal]
    rw [paperProjectiveFreshVector_one_eq_literalPaperExteriorCell_action]
    have hatoms : Function.uncurry
        (replaceSelectedFreshAtoms (baseAtoms y) word
          (fun t => (x t : Complex))) =
        (fun u => ((e.symm (x, y) u : Real) : Complex)) := by
      funext u
      rcases u with ⟨t, ell⟩
      have hreconstruct :=
        splitFreshAtom_symm_realCast_eq_replacePaperFreshSelectedAtoms word x y
      have h := congrFun (congrFun hreconstruct t) ell
      simpa only [baseAtoms, e, Function.uncurry,
        replaceSelectedFreshAtoms, replacePaperFreshSelectedAtoms] using h.symm
    rw [hatoms, literalPaperExteriorCell_complexify_eq_real]
  let F := fun xy : (Fin (d + 1) -> Real) ×
      (UnselectedFreshIndex word -> Real) => logDeficit 1 (radius (e.symm xy))
  have hFmeas : Measurable F :=
    (measurable_logDeficit 1
      (measurable_literalRealPaperExteriorCell_vectorNorm
        profile center z q v)).comp e.symm.measurable
  have hfiber (y : UnselectedFreshIndex word -> Real) :=
    paperProjectiveFreshVector_real_logDeficit_of_topCoeff
      profile hc0 center z (baseAtoms y) q (1 : Matrix _ _ Complex)
        (by simp) v o I J (hcoef (baseAtoms y)) nu hL hnu
  have hsectionInt (y : UnselectedFreshIndex word -> Real) :
      Integrable (fun x => F (x, y)) mux := by
    simpa only [F, heval, mux, iidMeasure_eq_pi, norm_one] using (hfiber y).2.1
  have hsectionBound (y : UnselectedFreshIndex word -> Real) :
      (∫ x, F (x, y) ∂mux) <= realLiteralProjectiveCellLoss d c0 L q := by
    simpa only [F, heval, mux, iidMeasure_eq_pi, norm_one] using (hfiber y).2.2
  let _ : IsProbabilityMeasure mux := by dsimp only [mux]; infer_instance
  let _ : IsProbabilityMeasure muy := by dsimp only [muy]; infer_instance
  obtain ⟨hFint, hFbound⟩ :=
    integrable_prod_and_integral_le_of_forall_integrable_integral_le
      mux muy F hFmeas (fun xy => logDeficit_nonneg _ _)
      (realLiteralProjectiveCellLoss d c0 L q)
      (realLiteralProjectiveCellLoss_nonneg d c0 L q)
      hsectionInt hsectionBound
  have hmp : MeasurePreserving e mu (mux.prod muy) := by
    simpa only [e, mu, mux, muy, literalRealPaperExteriorCellMeasure] using
      splitFreshAtom_measurePreserving word nu
  have hGint : Integrable (fun omega => logDeficit 1 (radius omega)) mu := by
    have hcomp := (hmp.integrable_comp_emb e.measurableEmbedding).2 hFint
    simpa only [F, Function.comp_def, MeasurableEquiv.symm_apply_apply] using hcomp
  have hGbound : (∫ omega, logDeficit 1 (radius omega) ∂mu) <=
      realLiteralProjectiveCellLoss d c0 L q := by
    calc
      _ = ∫ xy, F xy ∂(mux.prod muy) := by
        rw [← hmp.integral_comp' F]
        apply integral_congr_ae
        filter_upwards with omega
        simp only [F, MeasurableEquiv.symm_apply_apply]
      _ <= _ := hFbound
  let ZF : Set ((Fin (d + 1) -> Real) ×
      (UnselectedFreshIndex word -> Real)) := {xy | radius (e.symm xy) = 0}
  have hZFmeas : MeasurableSet ZF := measurableSet_eq_fun
    ((measurable_literalRealPaperExteriorCell_vectorNorm
      profile center z q v).comp e.symm.measurable) measurable_const
  have hzeroSection (y : UnselectedFreshIndex word -> Real) :
      mux {x | radius (e.symm (x, y)) = 0} = 0 := by
    have hset : {x | radius (e.symm (x, y)) = 0} =
        {x | ‖profile.paperProjectiveFreshVectorOfReal center z (baseAtoms y)
          q 1 v I J x‖ = 0} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      rw [heval x y]
    rw [hset]
    simpa only [mux, iidMeasure_eq_pi] using (hfiber y).1
  have hzeroProd : (mux.prod muy) ZF = 0 := by
    rw [Measure.prod_apply_symm hZFmeas]
    have hs : (fun y => mux ((fun x => (x, y)) ⁻¹' ZF)) = fun _ => 0 := by
      funext y
      simpa only [ZF, Set.preimage_ofPred_eq] using hzeroSection y
    rw [hs]
    simp
  have hzero : mu {omega | radius omega = 0} = 0 := by
    have hp : {omega | radius omega = 0} = e ⁻¹' ZF := by
      ext omega
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, ZF,
        MeasurableEquiv.symm_apply_apply]
    rw [hp, ← Measure.map_apply e.measurable hZFmeas, hmp.map_eq]
    exact hzeroProd
  exact ⟨hzero, hGint, hGbound⟩

theorem real_literalPaperExteriorCell_hOneLower
    (profile : PaperIndicatorWeights (d + 1) c0 C0) (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (nu : Measure Real) [SigmaFinite nu] [IsProbabilityMeasure nu]
    {L : Real} (hL : 0 <= L)
    (hnu : RealIntervalBound nu (ENNReal.ofReal L))
    (hsecondInt : Integrable (fun u : Real => u ^ 2) nu)
    (hsecond : ∫ u : Real, u ^ 2 ∂nu = 1) :
    forall v : EuclideanSpace Complex (ExteriorIndex (d + 1) q), ‖v‖ = 1 ->
      Integrable (fun omega => matrixCellVectorLog
          (literalRealPaperExteriorCell profile center z q) omega v)
        (literalRealPaperExteriorCellMeasure d nu) ∧
      0 - realLiteralProjectiveCellLoss d c0 L q <=
        ∫ omega, matrixCellVectorLog
          (literalRealPaperExteriorCell profile center z q) omega v
          ∂literalRealPaperExteriorCellMeasure d nu := by
  intro v hv
  let mu := literalRealPaperExteriorCellMeasure d nu
  let radius := fun omega : LiteralRealPaperCellAtoms d =>
    ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
      ((literalRealPaperExteriorCell profile center z q omega).mulVec
        (fun j => v j))‖
  let T := fun omega : LiteralRealPaperCellAtoms d =>
    ‖literalRealPaperExteriorCell profile center z q omega‖
  have hdef := real_literalPaperExteriorCell_vector_logDeficit
    profile hc0 center z q v hv nu hL hnu
  have hlogT : Integrable (fun omega => Real.log (T omega)) mu := by
    simpa only [mu, T] using real_literalPaperExteriorCell_logOpNorm_integrable
      nu hnu hL profile hc0 hsqrt center z q hsecondInt hsecond
        (1 / 2) (by norm_num) (by norm_num)
  have hrpos : ∀ᵐ omega ∂mu, 0 < radius omega := by
    have hn := measure_eq_zero_iff_ae_notMem.mp
      (by simpa only [mu, radius] using hdef.1)
    filter_upwards [hn] with omega homega
    have hne : radius omega ≠ 0 := by
      simpa only [Set.mem_ofPred_eq] using homega
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  have hrle (omega : LiteralRealPaperCellAtoms d) : radius omega <= T omega := by
    have h :=
      (literalRealPaperExteriorCell profile center z q omega).l2_opNorm_mulVec v
    simpa only [radius, T, hv, mul_one] using h
  have hexcess : Integrable (fun omega => logExcess 1 (radius omega)) mu := by
    apply hlogT.abs.mono'
      (measurable_logExcess 1
        (measurable_literalRealPaperExteriorCell_vectorNorm
          profile center z q v)).aestronglyMeasurable
    filter_upwards [hrpos] with omega hr
    have hT : 0 < T omega := hr.trans_le (hrle omega)
    change |logExcess 1 (radius omega)| <= |Real.log (T omega)|
    rw [abs_of_nonneg (logExcess_nonneg _ _)]
    exact (logExcess_le_max_zero_log_of_le_scale_mul
      (by norm_num) hr hT (by simpa using hrle omega)).trans
        (max_le (abs_nonneg _) (le_abs_self _))
  let _ : IsProbabilityMeasure mu := inferInstance
  have hclosure := integrable_log_and_integral_log_ge_of_logDeficit
    mu 1 (realLiteralProjectiveCellLoss d c0 L q)
      (by simpa only [mu, radius] using hdef.2.1) hexcess
      (by simpa only [mu, radius] using hdef.2.2)
  simpa only [matrixCellVectorLog, radius, mu, Real.log_one, zero_sub]
    using hclosure

theorem real_literalPaperExteriorCell_oneCellInputs
    (profile : PaperIndicatorWeights (d + 1) c0 C0) (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (nu : Measure Real) [SigmaFinite nu] [IsProbabilityMeasure nu]
    {L : Real} (hL : 0 <= L)
    (hnu : RealIntervalBound nu (ENNReal.ofReal L))
    (hsecondInt : Integrable (fun u : Real => u ^ 2) nu)
    (hsecond : ∫ u : Real, u ^ 2 ∂nu = 1) :
    let C := literalRealPaperExteriorCell profile center z q
    let mu := literalRealPaperExteriorCellMeasure d nu
    let pressure := ∫ omega, Real.log ‖C omega‖ ∂mu
    let error := max (realLiteralProjectiveCellLoss d c0 L q) pressure
    (forall v : EuclideanSpace Complex (ExteriorIndex (d + 1) q),
        ‖v‖ = 1 -> Integrable (fun omega => matrixCellVectorLog C omega v) mu ∧
          0 - error <= ∫ omega, matrixCellVectorLog C omega v ∂mu) ∧
      (Integrable (fun omega => Real.log ‖C omega‖) mu ∧
        (∫ omega, Real.log ‖C omega‖ ∂mu) <= 0 + error) := by
  let C := literalRealPaperExteriorCell profile center z q
  let mu := literalRealPaperExteriorCellMeasure d nu
  let pressure := ∫ omega, Real.log ‖C omega‖ ∂mu
  let error := max (realLiteralProjectiveCellLoss d c0 L q) pressure
  have hlower := real_literalPaperExteriorCell_hOneLower
    profile hc0 hsqrt center z q nu hL hnu hsecondInt hsecond
  have hupper : Integrable (fun omega => Real.log ‖C omega‖) mu := by
    simpa only [C, mu] using real_literalPaperExteriorCell_logOpNorm_integrable
      nu hnu hL profile hc0 hsqrt center z q hsecondInt hsecond
        (1 / 2) (by norm_num) (by norm_num)
  constructor
  · intro v hv
    have h := hlower v hv
    refine ⟨by simpa only [C, mu] using h.1, ?_⟩
    exact (sub_le_sub_left (le_max_left _ _) 0).trans
      (by simpa only [C, mu] using h.2)
  · refine ⟨hupper, ?_⟩
    simpa only [pressure, zero_add] using (le_max_right
      (realLiteralProjectiveCellLoss d c0 L q) pressure)

/-! ## Global products and final telescope -/

def literalRealIidCellRowsMeasurableEquiv (n d : Nat) :
    (Fin n -> LiteralRealPaperCellAtoms d) ≃ᵐ
      (Fin (n * (d + 1)) -> PaperIndicatorRealAtomRow d) :=
  (MeasurableEquiv.piCongrRight
      (fun _ : Fin n => literalRealPaperCellRowsMeasurableEquiv d)).trans
    (flatIIDRowsMeasurableEquiv n (d + 1)).symm

@[simp] theorem literalRealIidCellRowsMeasurableEquiv_apply
    (n d : Nat) (omega : Fin n -> LiteralRealPaperCellAtoms d)
    (r : Fin (n * (d + 1))) (k : Fin (d + 2)) :
    literalRealIidCellRowsMeasurableEquiv n d omega r k =
      literalRealPaperCellRows (omega (finProdFinEquiv.symm r).1)
        (finProdFinEquiv.symm r).2 k := by
  unfold literalRealIidCellRowsMeasurableEquiv
  change (flatIIDRowsMeasurableEquiv n (d + 1)).symm
      ((MeasurableEquiv.piCongrRight
        (fun _ : Fin n => literalRealPaperCellRowsMeasurableEquiv d)) omega)
        r k = _
  rw [flatIIDRowsMeasurableEquiv_symm_apply]
  change literalRealPaperCellRowsMeasurableEquiv d
      (omega (finProdFinEquiv.symm r).1)
      (finProdFinEquiv.symm r).2 k = _
  rw [literalRealPaperCellRowsMeasurableEquiv_apply]

theorem literalRealIidCellRows_measurePreserving
    (n d : Nat) (nu : Measure Real)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    MeasurePreserving (literalRealIidCellRowsMeasurableEquiv n d)
      (iidMeasure (literalRealPaperExteriorCellMeasure d nu) n)
      (paperIndicatorRealOpenRowSampleMeasure (n * (d + 1)) d nu) := by
  let muCell := literalRealPaperExteriorCellMeasure d nu
  let muRow := paperIndicatorRealRowMeasure d nu
  let _ : IsProbabilityMeasure muCell := inferInstance
  let _ : IsProbabilityMeasure muRow := iidMeasure_isProbability nu (d + 2)
  have hCells := measurePreserving_iid_piCongrRight n muCell
    (paperIndicatorRealOpenRowSampleMeasure (d + 1) d nu)
    (literalRealPaperCellRowsMeasurableEquiv d)
    (literalRealPaperCellRows_measurePreserving d nu)
  have hFlatten := (flatIIDRows_measurePreserving n (d + 1) muRow).symm
  change MeasurePreserving (literalRealIidCellRowsMeasurableEquiv n d)
    (iidMeasure muCell n) (iidMeasure muRow (n * (d + 1)))
  simpa only [literalRealIidCellRowsMeasurableEquiv,
    paperIndicatorRealOpenRowSampleMeasure, muRow,
    MeasurableEquiv.coe_trans, Function.comp_def] using hFlatten.comp hCells

theorem iidMatrixCellProduct_literalRealCell_eq_openProduct
    (n : Nat) (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex) (q : ExteriorDegree (d + 1))
    (omega : Fin n -> LiteralRealPaperCellAtoms d) :
    iidMatrixCellProduct (literalRealPaperExteriorCell profile center z q) omega =
      profile.paperIndicatorOpenExteriorProduct center z q
        (paperIndicatorComplexifyRealRows
          (literalRealIidCellRowsMeasurableEquiv n d omega)) := by
  classical
  unfold iidMatrixCellProduct literalRealPaperExteriorCell
    paperIndicatorOpenExteriorProduct
  rw [List.ofFn_comp', ← chronologicalProduct_flatten]
  congr 1
  rw [List.ofFn_mul]
  congr 1
  apply List.ofFn_inj.2
  funext i
  apply List.ofFn_inj.2
  funext j
  have hrBound : i * (d + 1) + j < n * (d + 1) := by
    calc
      _ < i * (d + 1) + (d + 1) := Nat.add_lt_add_left j.isLt _
      _ = (i + 1) * (d + 1) := by rw [Nat.add_mul, Nat.one_mul]
      _ <= n * (d + 1) := Nat.mul_le_mul_right (d + 1) i.isLt
  let r0 : Fin (n * (d + 1)) := finProdFinEquiv (i, j)
  have hr : (⟨i * (d + 1) + j, hrBound⟩ : Fin (n * (d + 1))) = r0 := by
    apply Fin.ext
    change i * (d + 1) + j = j + (d + 1) * i
    rw [Nat.mul_comm (d + 1) i, Nat.add_comm]
  rw [hr]
  congr 1
  funext k
  simp only [paperIndicatorComplexifyRealRows,
    paperIndicatorComplexifyRealRow]
  rw [literalRealIidCellRowsMeasurableEquiv_apply]
  simp only [r0, Equiv.symm_apply_apply]

theorem real_literalPaperExteriorCell_global_integrable
    {L : Real} (nu : Measure Real) [SigmaFinite nu] [IsProbabilityMeasure nu]
    (hnu : RealIntervalBound nu (ENNReal.ofReal L)) (hL : 0 <= L)
    (profile : PaperIndicatorWeights (d + 1) c0 C0) (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex) (q : ExteriorDegree (d + 1))
    (hsecondInt : Integrable (fun u : Real => u ^ 2) nu)
    (hsecond : ∫ u : Real, u ^ 2 ∂nu = 1) :
    ∀ n, Integrable (iidMatrixCellLogPotential
      (literalRealPaperExteriorCell profile center z q))
      (iidMeasure (literalRealPaperExteriorCellMeasure d nu) n) := by
  let _ : Nonempty (ExteriorIndex (d + 1) q) := exteriorIndex_nonempty _ q
  intro n
  by_cases hn : n = 0
  · subst n
    have hzero : iidMatrixCellLogPotential
        (literalRealPaperExteriorCell profile center z q) =
        (fun _ : Fin 0 -> LiteralRealPaperCellAtoms d => 0) := by
      funext omega
      exact iidMatrixCellLogPotential_zero _ omega
    rw [hzero]
    exact integrable_const 0
  · have hpos : 0 < n * (d + 1) :=
      Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.succ_pos d)
    have hcount : (n * (d + 1) - 1) + 1 = n * (d + 1) :=
      Nat.sub_add_cancel hpos
    have hmem := profile.real_paperIndicatorOpenPressure_memLp_two
      (m := d) (n := n * (d + 1) - 1) nu hnu hL hc0 hsqrt center z q
        hsecondInt hsecond (1 / 2) (by norm_num) (by norm_num)
    have hrow : Integrable (profile.paperIndicatorOpenPressureOfReal center z q)
        (paperIndicatorRealOpenRowSampleMeasure (n * (d + 1)) d nu) := by
      rw [← hcount]
      exact hmem.integrable (by norm_num)
    have hmp := literalRealIidCellRows_measurePreserving n d nu
    have hcomp := (hmp.integrable_comp_emb
      (literalRealIidCellRowsMeasurableEquiv n d).measurableEmbedding).2 hrow
    have hfun : (profile.paperIndicatorOpenPressureOfReal center z q) ∘
        (literalRealIidCellRowsMeasurableEquiv n d) =
      iidMatrixCellLogPotential
        (literalRealPaperExteriorCell profile center z q) := by
      funext omega
      unfold Function.comp paperIndicatorOpenPressureOfReal
        paperIndicatorOpenPressure iidMatrixCellLogPotential
      rw [iidMatrixCellProduct_literalRealCell_eq_openProduct]
    rw [← hfun]
    exact hcomp

theorem real_literalPaperExteriorCell_expectedLog_telescope
    (profile : PaperIndicatorWeights (d + 1) c0 C0) (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (f : Real -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ w ∂(volume : Measure Real), f w <= ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Real => u ^ 2) (volume.withDensity f))
    (hsecond : ∫ u : Real, u ^ 2 ∂(volume.withDensity f) = 1)
    (cellCount : Nat) :
    let C := literalRealPaperExteriorCell profile center z q
    let mu := literalRealPaperExteriorCellMeasure d (volume.withDensity f)
    let pressure := ∫ omega, Real.log ‖C omega‖ ∂mu
    let error := max (realLiteralProjectiveCellLoss d c0 L q) pressure
    (cellCount : Real) * (0 - error) <=
        ∫ omega, iidMatrixCellLogPotential C omega ∂iidMeasure mu cellCount ∧
      (∫ omega, iidMatrixCellLogPotential C omega ∂iidMeasure mu cellCount) <=
        (cellCount : Real) * (0 + error) := by
  classical
  let nu : Measure Real := volume.withDensity f
  let C := literalRealPaperExteriorCell profile center z q
  let mu := literalRealPaperExteriorCellMeasure d nu
  let pressure := ∫ omega, Real.log ‖C omega‖ ∂mu
  let error := max (realLiteralProjectiveCellLoss d c0 L q) pressure
  let _ : SigmaFinite nu := inferInstance
  let _ : IsProbabilityMeasure nu := inferInstance
  let _ : SigmaFinite mu := inferInstance
  let _ : IsProbabilityMeasure mu := inferInstance
  let _ : Nonempty (ExteriorIndex (d + 1) q) := exteriorIndex_nonempty _ q
  have hOne := real_literalPaperExteriorCell_oneCellInputs
    profile hc0 hsqrt center z q nu hL (realIntervalBound_withDensity hf)
      hsecondInt hsecond
  have hUnit : ∀ᵐ omega ∂mu, IsUnit (C omega) := by
    simpa only [C, mu, nu] using ae_literalRealPaperExteriorCell_isUnit_withDensity
      (d := d) (c0 := c0) (C0 := C0) profile hc0 center hcenter z q
        (f := f) (L := ENNReal.ofReal L) hf
  have hGlobal := real_literalPaperExteriorCell_global_integrable
    nu (realIntervalBound_withDensity hf) hL profile hc0 hsqrt center z q
      hsecondInt hsecond
  have htel := iidMatrixCellProduct_expectedLog_telescope_autoDirection_ae
    mu C cellCount 0 error
      (by simpa only [C, mu, nu, pressure, error] using hOne.1)
      (by simpa only [C, mu, nu, pressure, error] using hOne.2)
      hUnit (fun n _ => hGlobal n)
  simpa only [C, mu, nu, pressure, error] using htel

end CircularLawSections56.Section5
