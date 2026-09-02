import CircularLawSections56.Section5.LiteralProjectiveCellInputAdapter
import CircularLawSections56.Section5.LiteralIidMatrixCellAEAdapter

/-!
# Centered literal matrix cells

The paper's mesoscopic cell is `B * Q`: `B` is the outside product and `Q`
is the reserved fresh product.  Keeping `B` in the definition is essential.
The one-cell comparison is centered at `log ‖B‖`; only the projective/fresh
loss belongs to the error term.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
  Matrix Set Set.powersetCard

variable {d : Nat} {c0 C0 : Real}

/-- One fixed-degree paper cell with its frozen outside product retained. -/
def literalPaperExteriorCellWithLeft
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) Complex)
    (omega : LiteralPaperCellAtoms d) :
    Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) Complex :=
  B * literalPaperExteriorCell profile center z q omega

/-- The projective vector with frozen operator `B` is exactly the action of
the literal centered cell `B * Q`. -/
theorem paperProjectiveFreshVector_eq_literalPaperExteriorCellWithLeft_action
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (atoms : Fin (d + 1) -> ResetLabel (d + 1) -> Complex)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) Complex)
    (v : EuclideanSpace Complex (ExteriorIndex (d + 1) q))
    (I J : ExteriorIndex (d + 1) q) (x : Fin (d + 1) -> Complex) :
    profile.paperProjectiveFreshVector center z atoms q B v I J x =
      (EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
        ((literalPaperExteriorCellWithLeft profile center z q B
          (Function.uncurry (replaceSelectedFreshAtoms atoms
            (arbitrarySupportWord I J) x))).mulVec (fun j => v j)) := by
  rw [paperProjectiveFreshVector, literalPaperExteriorCellWithLeft,
    literalPaperExteriorCell_eq_freshProduct]
  simp

/-- The centered cell action is measurable for every fixed outside matrix. -/
theorem measurable_literalPaperExteriorCellWithLeft_vectorNorm
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) Complex)
    (v : EuclideanSpace Complex (ExteriorIndex (d + 1) q)) :
    Measurable (fun omega : LiteralPaperCellAtoms d =>
      ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
        ((literalPaperExteriorCellWithLeft profile center z q B omega).mulVec
          (fun j => v j))‖) := by
  have hrows : Continuous (fun omega : LiteralPaperCellAtoms d =>
      literalPaperCellRows omega) := by
    apply continuous_pi
    intro t
    apply continuous_pi
    intro ell
    exact continuous_apply (t, paperOperatorAffineLabelEquiv d ell)
  have hQ : Continuous (fun omega : LiteralPaperCellAtoms d =>
      literalPaperExteriorCell profile center z q omega) :=
    (profile.continuous_paperIndicatorOpenExteriorProduct
      center z q (d + 1)).comp hrows
  have hcell : Continuous (fun omega : LiteralPaperCellAtoms d =>
      literalPaperExteriorCellWithLeft profile center z q B omega) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [literalPaperExteriorCellWithLeft, Matrix.mul_apply]
    exact continuous_finsetSum Finset.univ fun k _ =>
      continuous_const.mul (((continuous_apply j).comp
        ((continuous_apply k).comp hQ)))
  have hmul : Measurable (fun omega : LiteralPaperCellAtoms d =>
      (literalPaperExteriorCellWithLeft profile center z q B omega).mulVec
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

/-- Full fresh-product deficit estimate at the genuine outside scale `‖B‖`.
Unlike the earlier identity-outside adapter, this is centered at the matrix
that will become the random outside product of the mesoscopic cell. -/
theorem complex_literalPaperExteriorCellWithLeft_vector_logDeficit
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) Complex)
    (hB : 0 < ‖B‖)
    (v : EuclideanSpace Complex (ExteriorIndex (d + 1) q))
    (hv : ‖v‖ = 1)
    (f : Complex -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ w ∂(volume : Measure Complex),
      f w <= ENNReal.ofReal L) :
    let radius := fun omega : LiteralPaperCellAtoms d =>
      ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
        ((literalPaperExteriorCellWithLeft profile center z q B omega).mulVec
          (fun j => v j))‖
    let mu := literalPaperExteriorCellMeasure d (volume.withDensity f)
    mu {omega | radius omega = 0} = 0 ∧
      Integrable (fun omega => logDeficit ‖B‖ (radius omega)) mu ∧
      (∫ omega, logDeficit ‖B‖ (radius omega) ∂mu) <=
        complexLiteralProjectiveCellLoss d c0 L q := by
  classical
  let _ : Nonempty (ExteriorIndex (d + 1) q) :=
    exteriorIndex_nonempty (d + 1) q
  let nu : Measure Complex := volume.withDensity f
  obtain ⟨o, I, J, hcoefficient⟩ :=
    exists_uniform_paperProjectiveFreshPolynomial_topCoeff_lower
      profile center z q B v hv
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
      ((literalPaperExteriorCellWithLeft profile center z q B omega).mulVec
        (fun j => v j))‖
  have heval (x : Fin (d + 1) -> Complex)
      (y : UnselectedFreshIndex word -> Complex) :
      ‖profile.paperProjectiveFreshVector center z (baseAtoms y) q B
          v I J x‖ = radius (e.symm (x, y)) := by
    rw [paperProjectiveFreshVector_eq_literalPaperExteriorCellWithLeft_action]
    apply congrArg fun omega : LiteralPaperCellAtoms d =>
      ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
        ((literalPaperExteriorCellWithLeft profile center z q B omega).mulVec
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
    logDeficit ‖B‖ (radius (e.symm xy))
  have hradiusMeas : Measurable radius :=
    measurable_literalPaperExteriorCellWithLeft_vectorNorm
      profile center z q B v
  have hFmeas : Measurable F :=
    (measurable_logDeficit ‖B‖ hradiusMeas).comp e.symm.measurable
  have hfiber (y : UnselectedFreshIndex word -> Complex) :=
    paperProjectiveFreshVector_complex_logDeficit_withDensity_of_topCoeff
      profile hc0 center z (baseAtoms y) q B hB v o I J
        (hcoefficient (baseAtoms y)) f hL hf
  have hsectionInt (y : UnselectedFreshIndex word -> Complex) :
      Integrable (fun x => F (x, y)) mux := by
    have h := (hfiber y).2.1
    simpa only [F, heval, mux, nu, iidMeasure_eq_pi] using h
  have hsectionBound (y : UnselectedFreshIndex word -> Complex) :
      (∫ x, F (x, y) ∂mux) <=
        complexLiteralProjectiveCellLoss d c0 L q := by
    have h := (hfiber y).2.2
    simpa only [F, heval, mux, nu, iidMeasure_eq_pi,
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
  have hGint : Integrable
      (fun omega => logDeficit ‖B‖ (radius omega)) mu := by
    have hcomp := (hmp.integrable_comp_emb e.measurableEmbedding).2 hFint
    simpa only [F, Function.comp_def, MeasurableEquiv.symm_apply_apply] using hcomp
  have hGbound :
      (∫ omega, logDeficit ‖B‖ (radius omega) ∂mu) <=
        complexLiteralProjectiveCellLoss d c0 L q := by
    calc
      (∫ omega, logDeficit ‖B‖ (radius omega) ∂mu) =
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
        {x | ‖profile.paperProjectiveFreshVector center z (baseAtoms y) q B
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

/-- The positive logarithmic half of `B * Q` relative to the outside scale
`‖B‖` is integrable.  It is dominated by the logarithmic operator pressure
of the fresh product `Q`. -/
theorem complex_literalPaperExteriorCellWithLeft_vector_logExcess_integrable
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) Complex)
    (hB : 0 < ‖B‖)
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
        ((literalPaperExteriorCellWithLeft profile center z q B omega).mulVec
          (fun j => v j))‖
    Integrable (fun omega => logExcess ‖B‖ (radius omega))
      (literalPaperExteriorCellMeasure d (volume.withDensity f)) := by
  let mu := literalPaperExteriorCellMeasure d (volume.withDensity f)
  let radius := fun omega : LiteralPaperCellAtoms d =>
    ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
      ((literalPaperExteriorCellWithLeft profile center z q B omega).mulVec
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
  have hdeficit := complex_literalPaperExteriorCellWithLeft_vector_logDeficit
    profile hc0 center z q B hB v hv f hL hf
  have hradiusPos : ∀ᵐ omega ∂mu, 0 < radius omega := by
    have hnotMem := measure_eq_zero_iff_ae_notMem.mp
      (by simpa only [mu, radius] using hdeficit.1)
    filter_upwards [hnotMem] with omega homega
    have hne : radius omega ≠ 0 := by
      simpa only [Set.mem_ofPred_eq] using homega
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  have hradiusLe (omega : LiteralPaperCellAtoms d) :
      radius omega <= ‖B‖ * T omega := by
    have haction :=
      (literalPaperExteriorCellWithLeft profile center z q B omega).l2_opNorm_mulVec v
    have hmul := Matrix.l2_opNorm_mul B
      (literalPaperExteriorCell profile center z q omega)
    calc
      radius omega <=
          ‖literalPaperExteriorCellWithLeft profile center z q B omega‖ * ‖v‖ :=
        haction
      _ = ‖literalPaperExteriorCellWithLeft profile center z q B omega‖ := by
        rw [hv, mul_one]
      _ <= ‖B‖ * T omega := by
        simpa only [literalPaperExteriorCellWithLeft, T] using hmul
  have hdom : (fun omega => logExcess ‖B‖ (radius omega)) ≤ᵐ[mu]
      (fun omega => |Real.log (T omega)|) := by
    filter_upwards [hradiusPos] with omega hradius
    have hT : 0 < T omega := by
      by_contra hnot
      have hTzero : T omega = 0 := le_antisymm (le_of_not_gt hnot) (norm_nonneg _)
      have := hradiusLe omega
      rw [hTzero, mul_zero] at this
      exact (not_lt_of_ge this) hradius
    calc
      logExcess ‖B‖ (radius omega) <= max 0 (Real.log (T omega)) :=
        logExcess_le_max_zero_log_of_le_scale_mul
          hB hradius hT (hradiusLe omega)
      _ <= |Real.log (T omega)| :=
        max_le (abs_nonneg _) (le_abs_self _)
  apply hmajor.mono'
    (measurable_logExcess ‖B‖
      (measurable_literalPaperExteriorCellWithLeft_vectorNorm
        profile center z q B v)).aestronglyMeasurable
  filter_upwards [hdom] with omega homega
  simpa only [radius, Real.norm_eq_abs,
    abs_of_nonneg (logExcess_nonneg _ _)] using homega

/-- Fixed-outside one-cell lower input.  Its base is the genuine outside
pressure `log ‖B‖`; the error is only the explicit projective loss. -/
theorem complex_literalPaperExteriorCellWithLeft_vector_hOneLower
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) Complex)
    (hB : 0 < ‖B‖)
    (v : EuclideanSpace Complex (ExteriorIndex (d + 1) q))
    (hv : ‖v‖ = 1)
    (f : Complex -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ w ∂(volume : Measure Complex),
      f w <= ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Complex => ‖u‖ ^ 2)
      (volume.withDensity f))
    (hsecond : ∫ u : Complex, ‖u‖ ^ 2 ∂(volume.withDensity f) <= 1) :
    let C := literalPaperExteriorCellWithLeft profile center z q B
    let mu := literalPaperExteriorCellMeasure d (volume.withDensity f)
    Integrable (fun omega => matrixCellVectorLog C omega v) mu ∧
      Real.log ‖B‖ - complexLiteralProjectiveCellLoss d c0 L q <=
        ∫ omega, matrixCellVectorLog C omega v ∂mu := by
  let radius := fun omega : LiteralPaperCellAtoms d =>
    ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
      ((literalPaperExteriorCellWithLeft profile center z q B omega).mulVec
        (fun j => v j))‖
  let mu := literalPaperExteriorCellMeasure d (volume.withDensity f)
  let _ : IsProbabilityMeasure mu := by
    dsimp only [mu, literalPaperExteriorCellMeasure]
    infer_instance
  have hdeficit := complex_literalPaperExteriorCellWithLeft_vector_logDeficit
    profile hc0 center z q B hB v hv f hL hf
  have hexcess :=
    complex_literalPaperExteriorCellWithLeft_vector_logExcess_integrable
      profile hc0 hsqrt center z q B hB v hv f hL hf hsecondInt hsecond
  have hclosure := integrable_log_and_integral_log_ge_of_logDeficit
    mu ‖B‖ (complexLiteralProjectiveCellLoss d c0 L q)
    (by simpa only [mu, radius] using hdeficit.2.1)
    (by simpa only [mu, radius] using hexcess)
    (by simpa only [mu, radius] using hdeficit.2.2)
  simpa only [matrixCellVectorLog, radius, mu] using hclosure

end CircularLawSections56.Section5
