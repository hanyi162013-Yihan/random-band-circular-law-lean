import CircularLawSections56.Section5.LiteralIidMatrixCellProductAdapter
import CircularLawSections56.Section5.LiteralFreshCoordinateTransport
import CircularLawSection4.PaperConditionalCompletion
import CircularLawSection4.PaperPressureAssumptionFree

/-!
# Literal projective inputs for one IID exterior cell

This file puts the Section 4 projective lower estimate and the positive
open-pressure estimate on the exact matrix-cell type consumed by
`iidMatrixCellProduct_expectedLog_telescope`.

The cell is the literal `paperIndicatorOpenExteriorProduct` of `d + 1`
complete IID rows at one fixed exterior degree.  The selected-coordinate
projective theorem is first recorded with a fixed coefficient selector; this
is important because the same cell law must work for every deterministic unit
vector.  The finite product split then identifies that selected fiber with the
corresponding coordinates of the complete IID cell.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
  Matrix Set Set.powersetCard

variable {d : Nat} {c0 C0 : Real}

/-- A complete reset-labelled atom array, written as one flat finite product
index so that `splitFreshAtomMeasurableEquiv` applies literally. -/
abbrev LiteralPaperCellAtoms (d : Nat) := FreshAtomIndex (d + 1) -> Complex

/-- Convert reset-labelled atoms into the complete paper row format. -/
def literalPaperCellRows (omega : LiteralPaperCellAtoms d) :
    Fin (d + 1) -> PaperIndicatorAtomRow d :=
  fun t k => omega (t, paperOperatorAffineLabelEquiv d k)

/-- One mesoscopic matrix cell: the literal open exterior product of `d + 1`
complete rows at fixed exterior degree `q`. -/
def literalPaperExteriorCell
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (omega : LiteralPaperCellAtoms d) :
    Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex :=
  profile.paperIndicatorOpenExteriorProduct center z q
    (literalPaperCellRows omega)

/-- The literal cell law: all `(d + 1)(d + 2)` scalar atoms are IID. -/
def literalPaperExteriorCellMeasure (d : Nat) (nu : Measure Complex) :
    Measure (LiteralPaperCellAtoms d) :=
  Measure.pi (fun _ : FreshAtomIndex (d + 1) => nu)

/-- Relabel the reset/star atom product as `d + 1` complete paper rows. -/
def literalPaperCellRowsMeasurableEquiv (d : Nat) :
    LiteralPaperCellAtoms d ≃ᵐ
      (Fin (d + 1) -> PaperIndicatorAtomRow d) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : FreshAtomIndex (d + 1) => Complex)
      (Equiv.prodCongr (Equiv.refl (Fin (d + 1)))
        (paperOperatorAffineLabelEquiv d))).symm.trans
    (MeasurableEquiv.curry (Fin (d + 1)) (Fin (d + 2)) Complex)

@[simp]
theorem literalPaperCellRowsMeasurableEquiv_apply
    (omega : LiteralPaperCellAtoms d) (t : Fin (d + 1))
    (k : Fin (d + 2)) :
    literalPaperCellRowsMeasurableEquiv d omega t k =
      literalPaperCellRows omega t k := by
  rfl

/-- The relabeling from reset/star atoms to complete rows preserves the full
IID law exactly. -/
theorem literalPaperCellRows_measurePreserving
    (d : Nat) (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    MeasurePreserving (literalPaperCellRowsMeasurableEquiv d)
      (literalPaperExteriorCellMeasure d nu)
      (paperIndicatorOpenRowSampleMeasure (d + 1) d nu) := by
  let e := Equiv.prodCongr (Equiv.refl (Fin (d + 1)))
    (paperOperatorAffineLabelEquiv d)
  have hreindex : MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : FreshAtomIndex (d + 1) => Complex) e).symm
      (Measure.pi (fun _ : FreshAtomIndex (d + 1) => nu))
      (Measure.pi (fun _ : Fin (d + 1) × Fin (d + 2) => nu)) := by
    exact (measurePreserving_piCongrLeft
      (fun _ : FreshAtomIndex (d + 1) => nu) e).symm
  let _ : IsProbabilityMeasure (iidMeasure nu (d + 2)) :=
    iidMeasure_isProbability nu (d + 2)
  have hcurry := measurePreserving_curry_fin_iid (d + 1) (d + 2) nu
  change MeasurePreserving (literalPaperCellRowsMeasurableEquiv d)
    (Measure.pi (fun _ : FreshAtomIndex (d + 1) => nu))
    (iidMeasure (iidMeasure nu (d + 2)) (d + 1))
  rw [iidMeasure_eq_pi]
  simp_rw [iidMeasure_eq_pi nu (d + 2)]
  simpa only [literalPaperExteriorCellMeasure,
    literalPaperCellRowsMeasurableEquiv, e,
    MeasurableEquiv.coe_trans, Function.comp_def] using hcurry.comp hreindex

/-- Section 4's assumption-free open-pressure `L²` theorem, transported to
the reset-labelled atom coordinates used by the literal matrix cell. -/
theorem complex_literalPaperExteriorCell_logOpNorm_integrable
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
    Integrable (fun omega : LiteralPaperCellAtoms d =>
      Real.log ‖literalPaperExteriorCell profile center z q omega‖)
      (literalPaperExteriorCellMeasure d nu) := by
  let muRows := paperIndicatorOpenRowSampleMeasure (d + 1) d nu
  let _ : IsProbabilityMeasure (iidMeasure nu (d + 2)) :=
    iidMeasure_isProbability nu (d + 2)
  let _ : IsProbabilityMeasure muRows := by
    simpa only [muRows, paperIndicatorOpenRowSampleMeasure,
      paperIndicatorRowMeasure] using
        iidMeasure_isProbability (iidMeasure nu (d + 2)) (d + 1)
  have hmem := profile.complex_paperIndicatorOpenPressure_memLp_two
    (m := d) (n := d) nu hnu hL hc0 hsqrt center z q hnuInt hnuSecond
  have hrowInt : Integrable
      (profile.paperIndicatorOpenPressure center z q) muRows := by
    exact hmem.integrable (by norm_num)
  have hmp := literalPaperCellRows_measurePreserving d nu
  have hcomp :=
    (hmp.integrable_comp_emb
      (literalPaperCellRowsMeasurableEquiv d).measurableEmbedding).2 hrowInt
  have hrowsEq : (literalPaperCellRowsMeasurableEquiv d :
      LiteralPaperCellAtoms d -> Fin (d + 1) -> PaperIndicatorAtomRow d) =
      literalPaperCellRows := by
    funext omega t k
    rfl
  simpa only [muRows, Function.comp_def, paperIndicatorOpenPressure,
    literalPaperExteriorCell, hrowsEq] using hcomp

@[simp]
theorem paperIndicatorOpenRowAtoms_literalPaperCellRows
    (omega : LiteralPaperCellAtoms d) (t : Fin (d + 1)) :
    paperIndicatorOpenRowAtoms (literalPaperCellRows omega t) =
      fun ell => omega (t, ell) := by
  funext ell
  rw [paperIndicatorOpenRowAtoms_eq_paperOperatorAffineAtoms]
  simp [literalPaperCellRows, paperOperatorAffineAtoms]

/-- The open-product spelling of the cell is exactly the chronological
product of Section 4's fresh exterior rows. -/
theorem literalPaperExteriorCell_eq_freshProduct
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (omega : LiteralPaperCellAtoms d) :
    literalPaperExteriorCell profile center z q omega =
      chronologicalProduct (List.ofFn fun t : Fin (d + 1) =>
        profile.freshExteriorRow center z (Function.curry omega) q t) := by
  classical
  unfold literalPaperExteriorCell paperIndicatorOpenExteriorProduct
  congr 1
  apply List.ofFn_inj.2
  funext t
  rw [profile.paperIndicatorOpenExteriorRow_eq_freshExteriorRow]
  unfold freshExteriorRow
  rw [paperIndicatorOpenRowAtoms_literalPaperCellRows]
  rfl

/-- Acting with the literal open-product cell is exactly the projective
vector with identity frozen operator, after replacing the selected atoms. -/
theorem paperProjectiveFreshVector_one_eq_literalPaperExteriorCell_action
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (atoms : Fin (d + 1) -> ResetLabel (d + 1) -> Complex)
    (q : ExteriorDegree (d + 1))
    (v : EuclideanSpace Complex (ExteriorIndex (d + 1) q))
    (I J : ExteriorIndex (d + 1) q) (x : Fin (d + 1) -> Complex) :
    profile.paperProjectiveFreshVector center z atoms q 1 v I J x =
      (EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
        ((literalPaperExteriorCell profile center z q
          (Function.uncurry (replaceSelectedFreshAtoms atoms
            (arbitrarySupportWord I J) x))).mulVec (fun j => v j)) := by
  rw [paperProjectiveFreshVector, literalPaperExteriorCell_eq_freshProduct]
  simp

/-- The literal vector action is a measurable function of every atom in the
complete IID cell. -/
theorem measurable_literalPaperExteriorCell_vectorNorm
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (v : EuclideanSpace Complex (ExteriorIndex (d + 1) q)) :
    Measurable (fun omega : LiteralPaperCellAtoms d =>
      ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
        ((literalPaperExteriorCell profile center z q omega).mulVec
          (fun j => v j))‖) := by
  have hrows : Continuous (fun omega : LiteralPaperCellAtoms d =>
      literalPaperCellRows omega) := by
    apply continuous_pi
    intro t
    apply continuous_pi
    intro k
    exact continuous_apply (t, paperOperatorAffineLabelEquiv d k)
  have hcell : Continuous (fun omega : LiteralPaperCellAtoms d =>
      literalPaperExteriorCell profile center z q omega) :=
    (profile.continuous_paperIndicatorOpenExteriorProduct
      center z q (d + 1)).comp hrows
  have hmulVec : Measurable (fun omega : LiteralPaperCellAtoms d =>
      (literalPaperExteriorCell profile center z q omega).mulVec
        (fun j => v j)) := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec]
    exact Finset.measurable_sum Finset.univ fun j _ =>
      Measurable.mul
        (((continuous_apply j).comp ((continuous_apply i).comp hcell)).measurable)
        measurable_const
  exact (((EuclideanSpace.equiv
    (ExteriorIndex (d + 1) q) Complex).symm.continuous.measurable.comp
      hmulVec).norm)

/-! ## A selector independent of all frozen atoms -/

/-- The projective coefficient selector can be chosen before the unselected
atoms are revealed.  This is not visible in the existential Section 4 API,
but follows from its atom-independent exact top-coefficient formula. -/
theorem exists_uniform_paperProjectiveFreshPolynomial_topCoeff_lower
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) Complex)
    (v : EuclideanSpace Complex (ExteriorIndex (d + 1) q))
    (hv : ‖v‖ = 1) :
    exists o I J : ExteriorIndex (d + 1) q,
      forall atoms : Fin (d + 1) -> ResetLabel (d + 1) -> Complex,
        (Real.sqrt (c0 / (d + 2 : Real))) ^ (d + 1) *
            (‖B‖ / (Fintype.card (ExteriorIndex (d + 1) q) : Real) ^ 3) <=
          ‖MultiAffine.topCoeff
            (profile.paperProjectiveFreshPolynomial
              center z atoms q B v o I J)‖ := by
  let zeroAtoms : Fin (d + 1) -> ResetLabel (d + 1) -> Complex :=
    fun _ _ => 0
  obtain ⟨o, I, J, hzero⟩ :=
    profile.exists_paperProjectiveFreshPolynomial_topCoeff_lower
      center z zeroAtoms q B v hv
  refine ⟨o, I, J, fun atoms => ?_⟩
  rw [profile.norm_topCoeff_paperProjectiveFreshPolynomial]
  rw [profile.norm_topCoeff_paperProjectiveFreshPolynomial] at hzero
  exact hzero

/-- Fixed-selector form of Section 4's complex projective negative-half
closure.  Its hypotheses expose exactly the coefficient certificate which
the uniform selector above supplies. -/
theorem paperProjectiveFreshVector_complex_logDeficit_withDensity_of_topCoeff
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (center : Fin (d + 1)) (z : Complex)
    (atoms : Fin (d + 1) -> ResetLabel (d + 1) -> Complex)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) Complex)
    (hB : 0 < ‖B‖)
    (v : EuclideanSpace Complex (ExteriorIndex (d + 1) q))
    (o I J : ExteriorIndex (d + 1) q)
    (hcoefficient :
      (Real.sqrt (c0 / (d + 2 : Real))) ^ (d + 1) *
          (‖B‖ / (Fintype.card (ExteriorIndex (d + 1) q) : Real) ^ 3) <=
        ‖MultiAffine.topCoeff
          (profile.paperProjectiveFreshPolynomial
            center z atoms q B v o I J)‖)
    (f : Complex -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ w ∂(volume : Measure Complex),
      f w <= ENNReal.ofReal L) :
    let radius := fun x : Fin (d + 1) -> Complex =>
      ‖profile.paperProjectiveFreshVector center z atoms q B v I J x‖
    iidMeasure (volume.withDensity f) (d + 1) {x | radius x = 0} = 0 ∧
      Integrable (fun x => logDeficit ‖B‖ (radius x))
        (iidMeasure (volume.withDensity f) (d + 1)) ∧
      (∫ x, logDeficit ‖B‖ (radius x)
          ∂iidMeasure (volume.withDensity f) (d + 1)) <=
        paperProjectiveCoefficientLogLoss d c0 q +
          (Real.log
            (max 1 (((d + 1 : Nat) : Real) * (Real.pi * L))) + 1) /
            (((2 : Nat) : Real) / ((d + 1 : Nat) : Real)) := by
  let _ := iidMeasure_isProbability (volume.withDensity f) (d + 1)
  let _ : Nonempty (ExteriorIndex (d + 1) q) :=
    exteriorIndex_nonempty (d + 1) q
  let p := profile.paperProjectiveFreshPolynomial
    center z atoms q B v o I J
  let radius := fun x : Fin (d + 1) -> Complex =>
    ‖profile.paperProjectiveFreshVector center z atoms q B v I J x‖
  have hbmin : 0 < Real.sqrt (c0 / (d + 2 : Real)) :=
    Real.sqrt_pos.2 (div_pos hc0 (by positivity))
  have hcard : 0 < (Fintype.card (ExteriorIndex (d + 1) q) : Real) := by
    exact_mod_cast Fintype.card_pos
  have htop : 0 < ‖p.topCoeff‖ := by
    apply (mul_pos (pow_pos hbmin _)
      (div_pos hB (pow_pos hcard _))).trans_le
    exact hcoefficient
  obtain ⟨hzero, _hae, hcoordinate, hcoordinateBound⟩ :=
    iid_complex_positiveLogLoss_withDensity f hL hf p htop
  have hscale :=
    profile.log_norm_sub_log_topCoeff_le_paperProjectiveCoefficientLogLoss
      hc0 center z atoms q B hB v o I J hcoefficient
  have hlift := integrable_logDeficit_of_coordinate
    (iidMeasure (volume.withDensity f) (d + 1))
    p.continuous_eval_complex.norm.measurable
    (profile.continuous_paperProjectiveFreshVector
      center z atoms q B v I J).norm.measurable
    (fun x => norm_nonneg _) (fun x => norm_nonneg _) hzero
    (fun x => profile.norm_eval_paperProjectiveFreshPolynomial_replaced_le
      center z atoms q B v o I J x)
    (paperProjectiveCoefficientLogLoss_nonneg d c0 q) hscale
    (by simpa only [logDeficit_eq_positiveLogLoss] using hcoordinate)
  refine ⟨measure_zeroSet_of_coordinate
      (iidMeasure (volume.withDensity f) (d + 1))
      (fun x => norm_nonneg _) hzero
      (fun x => profile.norm_eval_paperProjectiveFreshPolynomial_replaced_le
        center z atoms q B v o I J x), hlift.1, ?_⟩
  calc
    (∫ x, logDeficit ‖B‖ (radius x)
        ∂iidMeasure (volume.withDensity f) (d + 1)) <=
      paperProjectiveCoefficientLogLoss d c0 q +
        ∫ x, logDeficit ‖p.topCoeff‖ ‖p.eval x‖
          ∂iidMeasure (volume.withDensity f) (d + 1) := hlift.2
    _ <= paperProjectiveCoefficientLogLoss d c0 q +
        (Real.log
          (max 1 (((d + 1 : Nat) : Real) * (Real.pi * L))) + 1) /
          (((2 : Nat) : Real) / ((d + 1 : Nat) : Real)) := by
      simpa only [logDeficit_eq_positiveLogLoss, add_comm] using
        add_le_add_right hcoordinateBound
          (paperProjectiveCoefficientLogLoss d c0 q)

/-! ## Transport from the selected fiber to the complete IID cell -/

/-- The explicit lower-tail loss for one complex literal projective cell. -/
noncomputable def complexLiteralProjectiveCellLoss
    (d : Nat) (c0 L : Real) (q : ExteriorDegree (d + 1)) : Real :=
  paperProjectiveCoefficientLogLoss d c0 q +
    (Real.log (max 1 (((d + 1 : Nat) : Real) * (Real.pi * L))) + 1) /
      (((2 : Nat) : Real) / ((d + 1 : Nat) : Real))

theorem complexLiteralProjectiveCellLoss_nonneg
    (d : Nat) (c0 L : Real) (q : ExteriorDegree (d + 1)) :
    0 <= complexLiteralProjectiveCellLoss d c0 L q := by
  unfold complexLiteralProjectiveCellLoss
  apply add_nonneg (paperProjectiveCoefficientLogLoss_nonneg d c0 q)
  apply div_nonneg
  · have hlog : 0 <= Real.log
        (max 1 (((d + 1 : Nat) : Real) * (Real.pi * L))) :=
      Real.log_nonneg (le_max_left _ _)
    linarith
  · positivity

/-- Full-product negative-half closure for the action of the literal
fixed-degree exterior cell on one deterministic unit vector.  The selector
is chosen once, then the selected/unselected product split is transported
back to the original complete IID atom law. -/
theorem complex_literalPaperExteriorCell_vector_logDeficit
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (v : EuclideanSpace Complex (ExteriorIndex (d + 1) q))
    (hv : ‖v‖ = 1)
    (f : Complex -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ w ∂(volume : Measure Complex),
      f w <= ENNReal.ofReal L) :
    let radius := fun omega : LiteralPaperCellAtoms d =>
      ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
        ((literalPaperExteriorCell profile center z q omega).mulVec
          (fun j => v j))‖
    let mu := literalPaperExteriorCellMeasure d (volume.withDensity f)
    mu {omega | radius omega = 0} = 0 ∧
      Integrable (fun omega => logDeficit 1 (radius omega)) mu ∧
      (∫ omega, logDeficit 1 (radius omega) ∂mu) <=
        complexLiteralProjectiveCellLoss d c0 L q := by
  classical
  let _ : Nonempty (ExteriorIndex (d + 1) q) :=
    exteriorIndex_nonempty (d + 1) q
  let nu : Measure Complex := volume.withDensity f
  let zeroAtoms : Fin (d + 1) -> ResetLabel (d + 1) -> Complex :=
    fun _ _ => 0
  obtain ⟨o, I, J, hcoefficient⟩ :=
    exists_uniform_paperProjectiveFreshPolynomial_topCoeff_lower
      profile center z q (1 : Matrix (ExteriorIndex (d + 1) q)
        (ExteriorIndex (d + 1) q) Complex) v hv
  let word : Fin (d + 1) -> ResetLabel (d + 1) :=
    arbitrarySupportWord I J
  let mu : Measure (LiteralPaperCellAtoms d) :=
    literalPaperExteriorCellMeasure d nu
  let mux := Measure.pi (fun _ : Fin (d + 1) => nu)
  let muy := Measure.pi (fun _ : UnselectedFreshIndex word => nu)
  let e := splitFreshAtomMeasurableEquiv (K := Complex) word
  let baseAtoms := fun y : UnselectedFreshIndex word -> Complex =>
    fun t ell => e.symm ((fun _ => 0), y) (t, ell)
  let radius := fun omega : LiteralPaperCellAtoms d =>
    ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
      ((literalPaperExteriorCell profile center z q omega).mulVec
        (fun j => v j))‖
  have heval (x : Fin (d + 1) -> Complex)
      (y : UnselectedFreshIndex word -> Complex) :
      ‖profile.paperProjectiveFreshVector center z (baseAtoms y) q 1
          v I J x‖ = radius (e.symm (x, y)) := by
    rw [paperProjectiveFreshVector_one_eq_literalPaperExteriorCell_action]
    apply congrArg fun omega : LiteralPaperCellAtoms d =>
      ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
        ((literalPaperExteriorCell profile center z q omega).mulVec
          (fun j => v j))‖
    have hreconstruct :=
      splitFreshAtom_symm_eq_replacePaperFreshSelectedAtoms word x y
    funext u
    rcases u with ⟨t, ell⟩
    have h := congrFun (congrFun hreconstruct t) ell
    simpa only [word, e, baseAtoms, Function.uncurry,
      replaceSelectedFreshAtoms, replacePaperFreshSelectedAtoms] using h.symm
  let F : (Fin (d + 1) -> Complex) ×
      (UnselectedFreshIndex word -> Complex) -> Real := fun xy =>
    logDeficit 1 (radius (e.symm xy))
  have hradiusMeas : Measurable radius :=
    measurable_literalPaperExteriorCell_vectorNorm profile center z q v
  have hFmeas : Measurable F :=
    (measurable_logDeficit 1 hradiusMeas).comp e.symm.measurable
  have hfiber (y : UnselectedFreshIndex word -> Complex) :=
    paperProjectiveFreshVector_complex_logDeficit_withDensity_of_topCoeff
      profile hc0 center z (baseAtoms y) q
      (1 : Matrix (ExteriorIndex (d + 1) q)
        (ExteriorIndex (d + 1) q) Complex)
      (by simp) v o I J (hcoefficient (baseAtoms y)) f hL hf
  have hsectionInt (y : UnselectedFreshIndex word -> Complex) :
      Integrable (fun x => F (x, y)) mux := by
    have h := (hfiber y).2.1
    simpa only [F, heval, mux, nu, iidMeasure_eq_pi, norm_one] using h
  have hsectionBound (y : UnselectedFreshIndex word -> Complex) :
      (∫ x, F (x, y) ∂mux) <=
        complexLiteralProjectiveCellLoss d c0 L q := by
    have h := (hfiber y).2.2
    simpa only [F, heval, mux, nu, iidMeasure_eq_pi, norm_one,
      complexLiteralProjectiveCellLoss] using h
  let _ : IsProbabilityMeasure mux := by
    dsimp only [mux]
    infer_instance
  let _ : IsProbabilityMeasure muy := by
    dsimp only [muy]
    infer_instance
  obtain ⟨hFint, hFbound⟩ :=
    integrable_prod_and_integral_le_of_forall_integrable_integral_le
      mux muy F hFmeas (fun xy => logDeficit_nonneg _ _)
      (complexLiteralProjectiveCellLoss d c0 L q)
      (complexLiteralProjectiveCellLoss_nonneg d c0 L q)
      hsectionInt hsectionBound
  have hmp : MeasurePreserving e mu (mux.prod muy) := by
    simpa only [e, mu, mux, muy, nu, literalPaperExteriorCellMeasure] using
      splitFreshAtom_measurePreserving word nu
  have hGint : Integrable (fun omega => logDeficit 1 (radius omega)) mu := by
    have hcomp := (hmp.integrable_comp_emb e.measurableEmbedding).2 hFint
    simpa only [F, Function.comp_def, MeasurableEquiv.symm_apply_apply] using hcomp
  have hGbound : (∫ omega, logDeficit 1 (radius omega) ∂mu) <=
      complexLiteralProjectiveCellLoss d c0 L q := by
    calc
      (∫ omega, logDeficit 1 (radius omega) ∂mu) =
          ∫ omega, F (e omega) ∂mu := by
        apply integral_congr_ae
        filter_upwards with omega
        simp only [F, MeasurableEquiv.symm_apply_apply]
      _ = ∫ xy, F xy ∂(mux.prod muy) := hmp.integral_comp' F
      _ <= complexLiteralProjectiveCellLoss d c0 L q := hFbound
  let ZF : Set ((Fin (d + 1) -> Complex) ×
      (UnselectedFreshIndex word -> Complex)) :=
    {xy | radius (e.symm xy) = 0}
  have hZFmeas : MeasurableSet ZF :=
    measurableSet_eq_fun (hradiusMeas.comp e.symm.measurable) measurable_const
  have hzeroSection (y : UnselectedFreshIndex word -> Complex) :
      mux {x | radius (e.symm (x, y)) = 0} = 0 := by
    have hset : {x | radius (e.symm (x, y)) = 0} =
        {x | ‖profile.paperProjectiveFreshVector center z (baseAtoms y) q 1
          v I J x‖ = 0} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      rw [heval x y]
    rw [hset]
    simpa only [mux, nu, iidMeasure_eq_pi] using (hfiber y).1
  have hzeroProd : (mux.prod muy) ZF = 0 := by
    rw [Measure.prod_apply_symm hZFmeas]
    have hsections : (fun y => mux ((fun x => (x, y)) ⁻¹' ZF)) =
        (fun _ => 0) := by
      funext y
      simpa only [ZF, Set.preimage_ofPred_eq] using hzeroSection y
    rw [hsections]
    simp
  have hzero : mu {omega | radius omega = 0} = 0 := by
    have hpreimage : {omega | radius omega = 0} = e ⁻¹' ZF := by
      ext omega
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, ZF,
        MeasurableEquiv.symm_apply_apply]
    calc
      mu {omega | radius omega = 0} = mu (e ⁻¹' ZF) := congrArg mu hpreimage
      _ = Measure.map e mu ZF :=
        (Measure.map_apply e.measurable hZFmeas).symm
      _ = (mux.prod muy) ZF :=
        congrArg (fun m : Measure _ => m ZF) hmp.map_eq
      _ = 0 := hzeroProd
  exact ⟨hzero, hGint, hGbound⟩

/-- Adding the positive logarithmic half turns the full-product deficit
bound into the exact one-vector input expected by the IID matrix-cell
telescope. -/
theorem complex_literalPaperExteriorCell_vector_hOneLower_of_logExcess
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (v : EuclideanSpace Complex (ExteriorIndex (d + 1) q))
    (hv : ‖v‖ = 1)
    (f : Complex -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ w ∂(volume : Measure Complex),
      f w <= ENNReal.ofReal L)
    (hexcess :
      let radius := fun omega : LiteralPaperCellAtoms d =>
        ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
          ((literalPaperExteriorCell profile center z q omega).mulVec
            (fun j => v j))‖
      Integrable (fun omega => logExcess 1 (radius omega))
        (literalPaperExteriorCellMeasure d (volume.withDensity f))) :
    let C := literalPaperExteriorCell profile center z q
    let mu := literalPaperExteriorCellMeasure d (volume.withDensity f)
    Integrable (fun omega => matrixCellVectorLog C omega v) mu ∧
      0 - complexLiteralProjectiveCellLoss d c0 L q <=
        ∫ omega, matrixCellVectorLog C omega v ∂mu := by
  let radius := fun omega : LiteralPaperCellAtoms d =>
    ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
      ((literalPaperExteriorCell profile center z q omega).mulVec
        (fun j => v j))‖
  let mu := literalPaperExteriorCellMeasure d (volume.withDensity f)
  let _ : IsProbabilityMeasure mu := by
    dsimp only [mu, literalPaperExteriorCellMeasure]
    infer_instance
  have hdeficit := complex_literalPaperExteriorCell_vector_logDeficit
    profile hc0 center z q v hv f hL hf
  have hclosure := integrable_log_and_integral_log_ge_of_logDeficit
    mu 1 (complexLiteralProjectiveCellLoss d c0 L q)
    (by simpa only [mu, radius] using hdeficit.2.1)
    (by simpa only [mu, radius] using hexcess)
    (by simpa only [mu, radius] using hdeficit.2.2)
  simpa only [matrixCellVectorLog, radius, mu, Real.log_one, zero_sub]
    using hclosure

/-- Uniform deterministic-unit-vector receiver, exactly matching
`iidMatrixCellProduct_expectedLog_telescope`'s `hOneLower` argument with
base `0` and the explicit projective loss as error. -/
theorem complex_literalPaperExteriorCell_hOneLower_of_logExcess
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (f : Complex -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ w ∂(volume : Measure Complex),
      f w <= ENNReal.ofReal L)
    (hExcess : forall
      v : EuclideanSpace Complex (ExteriorIndex (d + 1) q), ‖v‖ = 1 ->
      let radius := fun omega : LiteralPaperCellAtoms d =>
        ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
          ((literalPaperExteriorCell profile center z q omega).mulVec
            (fun j => v j))‖
      Integrable (fun omega => logExcess 1 (radius omega))
        (literalPaperExteriorCellMeasure d (volume.withDensity f))) :
    forall v : EuclideanSpace Complex (ExteriorIndex (d + 1) q), ‖v‖ = 1 ->
      Integrable (fun omega => matrixCellVectorLog
          (literalPaperExteriorCell profile center z q) omega v)
        (literalPaperExteriorCellMeasure d (volume.withDensity f)) ∧
      0 - complexLiteralProjectiveCellLoss d c0 L q <=
        ∫ omega, matrixCellVectorLog
          (literalPaperExteriorCell profile center z q) omega v
          ∂literalPaperExteriorCellMeasure d (volume.withDensity f) := by
  intro v hv
  exact complex_literalPaperExteriorCell_vector_hOneLower_of_logExcess
    profile hc0 center z q v hv f hL hf (hExcess v hv)

/-! ## Automatic positive half and literal `hOneLower` -/

/-- The positive logarithmic half of a literal cell action is automatic.
The operator pressure is globally integrable by Section 4, and
`‖C omega v‖ <= ‖C omega‖` for a unit vector. -/
theorem complex_literalPaperExteriorCell_vector_logExcess_integrable
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (v : EuclideanSpace Complex (ExteriorIndex (d + 1) q))
    (hv : ‖v‖ = 1)
    (f : Complex -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ w ∂(volume : Measure Complex),
      f w <= ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Complex => ‖u‖ ^ 2)
      (volume.withDensity f))
    (hsecond : ∫ u : Complex, ‖u‖ ^ 2 ∂(volume.withDensity f) <= 1) :
    let radius := fun omega : LiteralPaperCellAtoms d =>
      ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
        ((literalPaperExteriorCell profile center z q omega).mulVec
          (fun j => v j))‖
    Integrable (fun omega => logExcess 1 (radius omega))
      (literalPaperExteriorCellMeasure d (volume.withDensity f)) := by
  let mu := literalPaperExteriorCellMeasure d (volume.withDensity f)
  let radius := fun omega : LiteralPaperCellAtoms d =>
    ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
      ((literalPaperExteriorCell profile center z q omega).mulVec
        (fun j => v j))‖
  let T := fun omega : LiteralPaperCellAtoms d =>
    ‖literalPaperExteriorCell profile center z q omega‖
  have hlogT : Integrable (fun omega => Real.log (T omega)) mu := by
    simpa only [mu, T] using
      complex_literalPaperExteriorCell_logOpNorm_integrable
        (d := d) (c0 := c0) (C0 := C0) (L := L)
        (volume.withDensity f) (complexBallBound_withDensity hf) hL
        profile hc0 hsqrt center z q hsecondInt hsecond
  have hmajor : Integrable (fun omega => |Real.log (T omega)|) mu :=
    hlogT.abs
  have hdeficit := complex_literalPaperExteriorCell_vector_logDeficit
    profile hc0 center z q v hv f hL hf
  have hradiusPos : ∀ᵐ omega ∂mu, 0 < radius omega := by
    have hnotMem := measure_eq_zero_iff_ae_notMem.mp
      (by simpa only [mu, radius] using hdeficit.1)
    filter_upwards [hnotMem] with omega homega
    have hne : radius omega ≠ 0 := by
      simpa only [Set.mem_ofPred_eq] using homega
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  have hradiusLe (omega : LiteralPaperCellAtoms d) :
      radius omega <= T omega := by
    have h :=
      (literalPaperExteriorCell profile center z q omega).l2_opNorm_mulVec v
    simpa only [radius, T, hv, mul_one] using h
  have hdom : (fun omega => logExcess 1 (radius omega)) ≤ᵐ[mu]
      (fun omega => |Real.log (T omega)|) := by
    filter_upwards [hradiusPos] with omega hradius
    have hT : 0 < T omega := hradius.trans_le (hradiusLe omega)
    calc
      logExcess 1 (radius omega) <= max 0 (Real.log (T omega)) :=
        logExcess_le_max_zero_log_of_le_scale_mul
          (by norm_num) hradius hT (by simpa using hradiusLe omega)
      _ <= |Real.log (T omega)| :=
        max_le (abs_nonneg _) (le_abs_self _)
  apply hmajor.mono'
    (measurable_logExcess 1
      (measurable_literalPaperExteriorCell_vectorNorm
        profile center z q v)).aestronglyMeasurable
  filter_upwards [hdom] with omega homega
  simpa only [radius, Real.norm_eq_abs,
    abs_of_nonneg (logExcess_nonneg _ _)] using homega

/-- Assumption-free literal projective lower input for every deterministic
unit vector.  This is the `hOneLower` field of the IID matrix-cell telescope,
with base `0` and the explicit projective error. -/
theorem complex_literalPaperExteriorCell_hOneLower
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (f : Complex -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ w ∂(volume : Measure Complex),
      f w <= ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Complex => ‖u‖ ^ 2)
      (volume.withDensity f))
    (hsecond : ∫ u : Complex, ‖u‖ ^ 2 ∂(volume.withDensity f) <= 1) :
    forall v : EuclideanSpace Complex (ExteriorIndex (d + 1) q), ‖v‖ = 1 ->
      Integrable (fun omega => matrixCellVectorLog
          (literalPaperExteriorCell profile center z q) omega v)
        (literalPaperExteriorCellMeasure d (volume.withDensity f)) ∧
      0 - complexLiteralProjectiveCellLoss d c0 L q <=
        ∫ omega, matrixCellVectorLog
          (literalPaperExteriorCell profile center z q) omega v
          ∂literalPaperExteriorCellMeasure d (volume.withDensity f) := by
  apply complex_literalPaperExteriorCell_hOneLower_of_logExcess
    profile hc0 center z q f hL hf
  intro v hv
  exact complex_literalPaperExteriorCell_vector_logExcess_integrable
    profile hc0 hsqrt center z q v hv f hL hf hsecondInt hsecond

/-! ## Aligned one-cell lower and upper inputs -/

/-- Both one-cell inputs of `iidMatrixCellProduct_expectedLog_telescope`,
on one common base/error pair.  The common base is `0`; the error is the
maximum of the explicit projective loss and the literal expected open
pressure.  This closes the receiver interface without pretending that
Section 4 already supplies a sharper deterministic upper-pressure center. -/
theorem complex_literalPaperExteriorCell_oneCellInputs
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (f : Complex -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ w ∂(volume : Measure Complex),
      f w <= ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Complex => ‖u‖ ^ 2)
      (volume.withDensity f))
    (hsecond : ∫ u : Complex, ‖u‖ ^ 2 ∂(volume.withDensity f) <= 1) :
    let C := literalPaperExteriorCell profile center z q
    let mu := literalPaperExteriorCellMeasure d (volume.withDensity f)
    let pressure := ∫ omega, Real.log ‖C omega‖ ∂mu
    let error := max (complexLiteralProjectiveCellLoss d c0 L q) pressure
    (forall v : EuclideanSpace Complex (ExteriorIndex (d + 1) q),
        ‖v‖ = 1 ->
        Integrable (fun omega => matrixCellVectorLog C omega v) mu ∧
          0 - error <= ∫ omega, matrixCellVectorLog C omega v ∂mu) ∧
      (Integrable (fun omega => Real.log ‖C omega‖) mu ∧
        (∫ omega, Real.log ‖C omega‖ ∂mu) <= 0 + error) := by
  let C := literalPaperExteriorCell profile center z q
  let mu := literalPaperExteriorCellMeasure d (volume.withDensity f)
  let pressure := ∫ omega, Real.log ‖C omega‖ ∂mu
  let error := max (complexLiteralProjectiveCellLoss d c0 L q) pressure
  have hlower := complex_literalPaperExteriorCell_hOneLower
    profile hc0 hsqrt center z q f hL hf hsecondInt hsecond
  have hupper : Integrable (fun omega => Real.log ‖C omega‖) mu := by
    simpa only [C, mu] using
      complex_literalPaperExteriorCell_logOpNorm_integrable
        (d := d) (c0 := c0) (C0 := C0) (L := L)
        (volume.withDensity f) (complexBallBound_withDensity hf) hL
        profile hc0 hsqrt center z q hsecondInt hsecond
  constructor
  · intro v hv
    have h := hlower v hv
    refine ⟨by simpa only [C, mu] using h.1, ?_⟩
    have hloss : complexLiteralProjectiveCellLoss d c0 L q <= error :=
      le_max_left _ _
    have hweaken : 0 - error <=
        0 - complexLiteralProjectiveCellLoss d c0 L q := by
      linarith
    exact hweaken.trans (by simpa only [C, mu] using h.2)
  · refine ⟨hupper, ?_⟩
    have hp : pressure <= error := le_max_right _ _
    simpa only [pressure, zero_add] using hp

end CircularLawSections56.Section5
