import CircularLawSections56.Section5.LiteralCenteredMesoscopicTelescope

/-!
# Physical open-row realization of centered mesoscopic cells

This module realizes the random outside matrix in the centered `B * Q`
telescope as an actual IID open-row product.  A physical cell contains the
`d + 1` fresh rows first and then `ell` outside rows; chronological
multiplication therefore gives `B * Q`.  The cell law is transported exactly
to `d + 1 + ell` IID paper rows, and IID cells are then flattened to one IID
chronological row block.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

set_option maxHeartbeats 1800000

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights Matrix Set

variable {d ell : Nat} {c0 C0 : Real}

/-- The physical outside block consists of `ell` complete IID paper rows. -/
abbrev LiteralPhysicalOutsideRows (ell d : Nat) :=
  Fin ell -> PaperIndicatorAtomRow d

/-- The exterior product of the physical outside rows. -/
def literalPhysicalOutsideExteriorProduct
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (degree : ExteriorDegree (d + 1))
    (outside : LiteralPhysicalOutsideRows ell d) :
    Matrix (ExteriorIndex (d + 1) degree)
      (ExteriorIndex (d + 1) degree) Complex :=
  profile.paperIndicatorOpenExteriorProduct center z degree outside

/-- The literal physical cell `B * Q`, with a random outside open-row block
and the reset-labelled fresh block used by the projective estimate. -/
def literalPhysicalMesoscopicCell
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (degree : ExteriorDegree (d + 1)) :
    (LiteralPhysicalOutsideRows ell d × LiteralPaperCellAtoms d) ->
      Matrix (ExteriorIndex (d + 1) degree)
        (ExteriorIndex (d + 1) degree) Complex :=
  literalRandomOutsideExteriorCell profile center z degree
    (literalPhysicalOutsideExteriorProduct profile center z degree)

/-- Reassemble one physical cell as `d + 1 + ell` chronological open rows.
The fresh block comes first, so the open product is literally `B * Q`. -/
def literalPhysicalCellRowsMeasurableEquiv (ell d : Nat) :
    (LiteralPhysicalOutsideRows ell d × LiteralPaperCellAtoms d) ≃ᵐ
      (Fin ((d + 1) + ell) -> PaperIndicatorAtomRow d) :=
  MeasurableEquiv.prodComm.trans
    ((MeasurableEquiv.prodCongr (literalPaperCellRowsMeasurableEquiv d)
      (MeasurableEquiv.refl _)).trans
      ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin (d + 1) ⊕ Fin ell => PaperIndicatorAtomRow d)).symm.trans
        (MeasurableEquiv.piCongrLeft
          (fun _ : Fin ((d + 1) + ell) => PaperIndicatorAtomRow d)
          finSumFinEquiv)))

@[simp]
theorem literalPhysicalCellRowsMeasurableEquiv_castAdd
    (sample : LiteralPhysicalOutsideRows ell d × LiteralPaperCellAtoms d)
    (t : Fin (d + 1)) :
    literalPhysicalCellRowsMeasurableEquiv ell d sample (Fin.castAdd ell t) =
      literalPaperCellRows sample.2 t := by
  change (MeasurableEquiv.piCongrLeft
    (fun _ : Fin ((d + 1) + ell) => PaperIndicatorAtomRow d)
    finSumFinEquiv) _ (finSumFinEquiv (Sum.inl t)) = _
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

@[simp]
theorem literalPhysicalCellRowsMeasurableEquiv_natAdd
    (sample : LiteralPhysicalOutsideRows ell d × LiteralPaperCellAtoms d)
    (i : Fin ell) :
    literalPhysicalCellRowsMeasurableEquiv ell d sample (Fin.natAdd (d + 1) i) =
      sample.1 i := by
  change (MeasurableEquiv.piCongrLeft
    (fun _ : Fin ((d + 1) + ell) => PaperIndicatorAtomRow d)
    finSumFinEquiv) _ (finSumFinEquiv (Sum.inr i)) = _
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

/-- Product law of the independent physical outside and fresh row blocks. -/
def literalPhysicalMesoscopicCellMeasure (ell d : Nat) (nu : Measure Complex)
    [SFinite nu] [IsProbabilityMeasure nu] :
    Measure (LiteralPhysicalOutsideRows ell d × LiteralPaperCellAtoms d) :=
  (paperIndicatorOpenRowSampleMeasure ell d nu).prod
    (literalPaperExteriorCellMeasure d nu)

local instance physicalRowMeasureProbability
    (d : Nat) (nu : Measure Complex) [SigmaFinite nu] [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (paperIndicatorRowMeasure d nu) :=
  iidMeasure_isProbability nu (d + 2)

local instance physicalOpenRowsProbability
    (n d : Nat) (nu : Measure Complex) [SigmaFinite nu] [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (paperIndicatorOpenRowSampleMeasure n d nu) :=
  iidMeasure_isProbability (paperIndicatorRowMeasure d nu) n

local instance physicalOpenRowsSigmaFinite
    (n d : Nat) (nu : Measure Complex) [SigmaFinite nu] [IsProbabilityMeasure nu] :
    SigmaFinite (paperIndicatorOpenRowSampleMeasure n d nu) := by infer_instance

local instance physicalFreshProbability
    (d : Nat) (nu : Measure Complex) [SigmaFinite nu] [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (literalPaperExteriorCellMeasure d nu) := by
  unfold literalPaperExteriorCellMeasure
  infer_instance

local instance physicalFreshSigmaFinite
    (d : Nat) (nu : Measure Complex) [SigmaFinite nu] [IsProbabilityMeasure nu] :
    SigmaFinite (literalPaperExteriorCellMeasure d nu) := by infer_instance

instance literalPhysicalMesoscopicCellMeasure_isProbability
    (ell d : Nat) (nu : Measure Complex) [SigmaFinite nu] [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (literalPhysicalMesoscopicCellMeasure ell d nu) := by
  unfold literalPhysicalMesoscopicCellMeasure
  infer_instance

instance literalPhysicalMesoscopicCellMeasure_sigmaFinite
    (ell d : Nat) (nu : Measure Complex) [SigmaFinite nu] [IsProbabilityMeasure nu] :
    SigmaFinite (literalPhysicalMesoscopicCellMeasure ell d nu) := by infer_instance

/-- The one-cell concatenation preserves the full IID row law exactly. -/
theorem literalPhysicalCellRows_measurePreserving
    (ell d : Nat) (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    MeasurePreserving (literalPhysicalCellRowsMeasurableEquiv ell d)
      (literalPhysicalMesoscopicCellMeasure ell d nu)
      (paperIndicatorOpenRowSampleMeasure ((d + 1) + ell) d nu) := by
  let muRow := paperIndicatorRowMeasure d nu
  have hSwap := (Measure.measurePreserving_swap : MeasurePreserving
    (MeasurableEquiv.prodComm :
      (LiteralPhysicalOutsideRows ell d × LiteralPaperCellAtoms d) ≃ᵐ
        (LiteralPaperCellAtoms d × LiteralPhysicalOutsideRows ell d))
    ((paperIndicatorOpenRowSampleMeasure ell d nu).prod
      (literalPaperExteriorCellMeasure d nu))
    ((literalPaperExteriorCellMeasure d nu).prod
      (paperIndicatorOpenRowSampleMeasure ell d nu)))
  have hProd := (literalPaperCellRows_measurePreserving d nu).prod
    (MeasurePreserving.id (paperIndicatorOpenRowSampleMeasure ell d nu))
  have hSum := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin (d + 1) ⊕ Fin ell => muRow)
  have hFin := measurePreserving_piCongrLeft
    (fun _ : Fin ((d + 1) + ell) => muRow) finSumFinEquiv
  have hSum' : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin (d + 1) ⊕ Fin ell => PaperIndicatorAtomRow d)).symm
      ((paperIndicatorOpenRowSampleMeasure (d + 1) d nu).prod
        (paperIndicatorOpenRowSampleMeasure ell d nu))
      (Measure.pi fun _ : Fin (d + 1) ⊕ Fin ell => muRow) := by
    simpa only [paperIndicatorOpenRowSampleMeasure, iidMeasure_eq_pi, muRow] using hSum
  have hFin' : MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin ((d + 1) + ell) => PaperIndicatorAtomRow d) finSumFinEquiv)
      (Measure.pi fun _ : Fin (d + 1) ⊕ Fin ell => muRow)
      (paperIndicatorOpenRowSampleMeasure ((d + 1) + ell) d nu) := by
    simpa only [paperIndicatorOpenRowSampleMeasure, iidMeasure_eq_pi, muRow] using hFin
  have hProdFun (x : LiteralPaperCellAtoms d × LiteralPhysicalOutsideRows ell d) :
      (MeasurableEquiv.prodCongr (literalPaperCellRowsMeasurableEquiv d)
        (MeasurableEquiv.refl _)) x =
        Prod.map (literalPaperCellRowsMeasurableEquiv d) id x := by rfl
  have hSwapFun (x : LiteralPhysicalOutsideRows ell d × LiteralPaperCellAtoms d) :
      (MeasurableEquiv.prodComm :
        (LiteralPhysicalOutsideRows ell d × LiteralPaperCellAtoms d) ≃ᵐ
          (LiteralPaperCellAtoms d × LiteralPhysicalOutsideRows ell d)) x = x.swap := by rfl
  simpa only [literalPhysicalCellRowsMeasurableEquiv,
    literalPhysicalMesoscopicCellMeasure, MeasurableEquiv.coe_trans,
    Function.comp_def, hProdFun, hSwapFun] using hFin'.comp (hSum'.comp (hProd.comp hSwap))

/-- One physical matrix cell is exactly the open exterior product of its
chronologically reassembled complete rows. -/
theorem literalPhysicalMesoscopicCell_eq_openProduct
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (degree : ExteriorDegree (d + 1))
    (sample : LiteralPhysicalOutsideRows ell d × LiteralPaperCellAtoms d) :
    literalPhysicalMesoscopicCell profile center z degree sample =
      profile.paperIndicatorOpenExteriorProduct center z degree
        (literalPhysicalCellRowsMeasurableEquiv ell d sample) := by
  unfold literalPhysicalMesoscopicCell literalRandomOutsideExteriorCell
    literalPaperExteriorCellWithLeft literalPhysicalOutsideExteriorProduct
    literalPaperExteriorCell paperIndicatorOpenExteriorProduct
  conv_rhs => rw [List.ofFn_add, chronologicalProduct_append]
  simp only [literalPhysicalCellRowsMeasurableEquiv_natAdd]
  congr 1
  congr 1
  apply List.ofFn_inj.2
  funext t
  congr 1
  exact (literalPhysicalCellRowsMeasurableEquiv_castAdd sample t).symm

/-- Flatten `n` physical cells to `n * (d + 1 + ell)` chronological rows. -/
def literalPhysicalIidCellRowsMeasurableEquiv (n ell d : Nat) :
    (Fin n -> LiteralPhysicalOutsideRows ell d × LiteralPaperCellAtoms d) ≃ᵐ
      (Fin (n * ((d + 1) + ell)) -> PaperIndicatorAtomRow d) :=
  (MeasurableEquiv.piCongrRight
    (fun _ : Fin n => literalPhysicalCellRowsMeasurableEquiv ell d)).trans
      (flatIIDRowsMeasurableEquiv n ((d + 1) + ell)).symm

@[simp]
theorem literalPhysicalIidCellRowsMeasurableEquiv_apply
    (n ell d : Nat)
    (sample : Fin n -> LiteralPhysicalOutsideRows ell d × LiteralPaperCellAtoms d)
    (r : Fin (n * ((d + 1) + ell))) :
    literalPhysicalIidCellRowsMeasurableEquiv n ell d sample r =
      literalPhysicalCellRowsMeasurableEquiv ell d
        (sample (finProdFinEquiv.symm r).1) (finProdFinEquiv.symm r).2 := by
  unfold literalPhysicalIidCellRowsMeasurableEquiv
  rw [MeasurableEquiv.trans_apply, flatIIDRowsMeasurableEquiv_symm_apply]
  rfl

/-- IID physical cells have exactly the law of one long IID open-row block. -/
theorem literalPhysicalIidCellRows_measurePreserving
    (n ell d : Nat) (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    MeasurePreserving (literalPhysicalIidCellRowsMeasurableEquiv n ell d)
      (iidMeasure (literalPhysicalMesoscopicCellMeasure ell d nu) n)
      (paperIndicatorOpenRowSampleMeasure (n * ((d + 1) + ell)) d nu) := by
  have hCells := measurePreserving_iid_piCongrRight n
    (literalPhysicalMesoscopicCellMeasure ell d nu)
    (paperIndicatorOpenRowSampleMeasure ((d + 1) + ell) d nu)
    (literalPhysicalCellRowsMeasurableEquiv ell d)
    (literalPhysicalCellRows_measurePreserving ell d nu)
  have hFlatten := (flatIIDRows_measurePreserving n ((d + 1) + ell)
    (paperIndicatorRowMeasure d nu)).symm
  simpa only [literalPhysicalIidCellRowsMeasurableEquiv,
    paperIndicatorOpenRowSampleMeasure, MeasurableEquiv.coe_trans,
    Function.comp_def] using hFlatten.comp hCells

/-- Exact chronological product identification for any finite number of
physical `B * Q` cells.  No independence or nonvanishing is needed here. -/
theorem iidMatrixCellProduct_literalPhysicalMesoscopicCell_eq_openProduct
    (n : Nat)
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (degree : ExteriorDegree (d + 1))
    (sample : Fin n -> LiteralPhysicalOutsideRows ell d × LiteralPaperCellAtoms d) :
    iidMatrixCellProduct (literalPhysicalMesoscopicCell profile center z degree) sample =
      profile.paperIndicatorOpenExteriorProduct center z degree
        (literalPhysicalIidCellRowsMeasurableEquiv n ell d sample) := by
  classical
  unfold iidMatrixCellProduct
  simp_rw [literalPhysicalMesoscopicCell_eq_openProduct]
  unfold paperIndicatorOpenExteriorProduct
  rw [List.ofFn_comp']
  rw [← chronologicalProduct_flatten]
  congr 1
  rw [List.ofFn_mul]
  congr 1
  apply List.ofFn_inj.2
  funext i
  apply List.ofFn_inj.2
  funext j
  have hrBound : i * ((d + 1) + ell) + j < n * ((d + 1) + ell) := by
    calc
      i * ((d + 1) + ell) + j < i * ((d + 1) + ell) + ((d + 1) + ell) :=
        Nat.add_lt_add_left j.isLt _
      _ = (i + 1) * ((d + 1) + ell) := by rw [Nat.add_mul, Nat.one_mul]
      _ <= n * ((d + 1) + ell) := Nat.mul_le_mul_right _ i.isLt
  let r0 : Fin (n * ((d + 1) + ell)) := finProdFinEquiv (i, j)
  have hr : (⟨i * ((d + 1) + ell) + j, hrBound⟩ :
      Fin (n * ((d + 1) + ell))) = r0 := by
    apply Fin.ext
    change i * ((d + 1) + ell) + j = j + ((d + 1) + ell) * i
    rw [Nat.mul_comm ((d + 1) + ell) i, Nat.add_comm]
  rw [hr]
  congr 1
  rw [literalPhysicalIidCellRowsMeasurableEquiv_apply]
  simp only [r0, Equiv.symm_apply_apply]

/-- Section 4 gives integrability of the actual pressure at every finite
open-row length, including the empty block. -/
theorem complex_literalPhysicalOpenPressure_integrable
    (n : Nat) {L : Real}
    (nu : Measure Complex) [SigmaFinite nu] [IsProbabilityMeasure nu]
    (hnu : ComplexBallBound nu (ENNReal.ofReal L)) (hL : 0 <= L)
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex)
    (degree : ExteriorDegree (d + 1))
    (hsecondInt : Integrable (fun u : Complex => ‖u‖ ^ 2) nu)
    (hsecond : ∫ u : Complex, ‖u‖ ^ 2 ∂nu <= 1) :
    Integrable (profile.paperIndicatorOpenPressure center z degree)
      (paperIndicatorOpenRowSampleMeasure n d nu) := by
  cases n with
  | zero =>
      change Integrable (fun _ : Fin 0 -> PaperIndicatorAtomRow d =>
        Real.log ‖(1 : Matrix (ExteriorIndex (d + 1) degree)
          (ExteriorIndex (d + 1) degree) Complex)‖) _
      exact integrable_const _
  | succ n =>
      exact (profile.complex_paperIndicatorOpenPressure_memLp_two
        (m := d) (n := n) nu hnu hL hc0 hsqrt center z degree
        hsecondInt hsecond).integrable (by norm_num)

/-- The one-cell log-integrability premise of the centered telescope is
automatic for a physical outside block. -/
theorem complex_literalPhysicalMesoscopicCell_logOpNorm_integrable
    {L : Real}
    (nu : Measure Complex) [SigmaFinite nu] [IsProbabilityMeasure nu]
    (hnu : ComplexBallBound nu (ENNReal.ofReal L)) (hL : 0 <= L)
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex)
    (degree : ExteriorDegree (d + 1))
    (hsecondInt : Integrable (fun u : Complex => ‖u‖ ^ 2) nu)
    (hsecond : ∫ u : Complex, ‖u‖ ^ 2 ∂nu <= 1) :
    Integrable
      (fun sample : LiteralPhysicalOutsideRows ell d × LiteralPaperCellAtoms d =>
        Real.log ‖literalPhysicalMesoscopicCell profile center z degree sample‖)
      (literalPhysicalMesoscopicCellMeasure ell d nu) := by
  have hrows := complex_literalPhysicalOpenPressure_integrable ((d + 1) + ell)
    nu hnu hL profile hc0 hsqrt center z degree hsecondInt hsecond
  have hpull := (literalPhysicalCellRows_measurePreserving ell d nu).integrable_comp_of_integrable hrows
  have hfun : (profile.paperIndicatorOpenPressure center z degree) ∘
      (literalPhysicalCellRowsMeasurableEquiv ell d) =
      (fun sample => Real.log ‖literalPhysicalMesoscopicCell profile center z degree sample‖) := by
    funext sample
    simp only [Function.comp_def, paperIndicatorOpenPressure,
      literalPhysicalMesoscopicCell_eq_openProduct]
  rwa [hfun] at hpull

/-- The global log-integrability premise of the centered telescope is
automatic simultaneously for every number of physical cells. -/
theorem complex_literalPhysicalMesoscopicCell_global_integrable
    {L : Real}
    (nu : Measure Complex) [SigmaFinite nu] [IsProbabilityMeasure nu]
    (hnu : ComplexBallBound nu (ENNReal.ofReal L)) (hL : 0 <= L)
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex)
    (degree : ExteriorDegree (d + 1))
    (hsecondInt : Integrable (fun u : Complex => ‖u‖ ^ 2) nu)
    (hsecond : ∫ u : Complex, ‖u‖ ^ 2 ∂nu <= 1) :
    ∀ n, Integrable
      (iidMatrixCellLogPotential (literalPhysicalMesoscopicCell profile center z degree))
      (iidMeasure (literalPhysicalMesoscopicCellMeasure ell d nu) n) := by
  intro n
  have hrows := complex_literalPhysicalOpenPressure_integrable (n * ((d + 1) + ell))
    nu hnu hL profile hc0 hsqrt center z degree hsecondInt hsecond
  have hpull := (literalPhysicalIidCellRows_measurePreserving n ell d nu).integrable_comp_of_integrable hrows
  have hfun : (profile.paperIndicatorOpenPressure center z degree) ∘
      (literalPhysicalIidCellRowsMeasurableEquiv n ell d) =
      iidMatrixCellLogPotential (literalPhysicalMesoscopicCell profile center z degree) := by
    funext sample
    simp only [Function.comp_def, paperIndicatorOpenPressure,
      iidMatrixCellLogPotential,
      iidMatrixCellProduct_literalPhysicalMesoscopicCell_eq_openProduct]
  rwa [hfun] at hpull

@[simp]
theorem paperIndicatorOpenBeta_flatRows_any
    (n : Nat) [NeZero n]
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (omega : Fin (n * (d + 2)) -> Complex) (t : Fin n) :
    profile.paperIndicatorOpenBeta (paperIndicatorFlatRowsEquiv n d omega t) =
      profile.b (Fin.last (d + 1)) *
        paperIndicatorXi n d omega (ZMod.finEquiv n t) (Fin.last (d + 1)) := by
  simp [paperIndicatorOpenBeta]

@[simp]
theorem paperIndicatorOpenTransfer_flatRows_any
    (n : Nat) [NeZero n]
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (omega : Fin (n * (d + 2)) -> Complex) (t : Fin n) :
    profile.paperIndicatorOpenTransfer center z (paperIndicatorFlatRowsEquiv n d omega t) =
      paperIndicatorTransferMatrix n d center profile.b omega z (ZMod.finEquiv n t) := by
  unfold paperIndicatorOpenTransfer paperIndicatorTransferMatrix paperShiftedScalarTransfer
  rw [paperCyclicTransferMatrix_eq_rowCompanion]
  congr 2
  all_goals
    funext k
    exact paperIndicatorFlatRowsEquiv_apply_eq_Xi n d omega t k

/-- Every finite physical outside open product is a unit almost surely.
This is Section 4's companion certificate transported to arbitrary row
length, with the empty block handled by the identity matrix. -/
theorem ae_literalPhysicalOutsideExteriorProduct_isUnit_complex_withDensity
    (ell : Nat)
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : Complex)
    (degree : ExteriorDegree (d + 1))
    {f : Complex -> ENNReal} {L : ENNReal}
    [IsProbabilityMeasure ((volume : Measure Complex).withDensity f)]
    (hf : ∀ᵐ w : Complex ∂volume, f w ≤ L) :
    ∀ᵐ outside ∂paperIndicatorOpenRowSampleMeasure ell d (volume.withDensity f),
      IsUnit (literalPhysicalOutsideExteriorProduct profile center z degree outside) := by
  by_cases hell : ell = 0
  · subst ell
    exact ae_of_all _ fun outside => by
      simp [literalPhysicalOutsideExteriorProduct, paperIndicatorOpenExteriorProduct]
  · let _ : NeZero ell := ⟨hell⟩
    let nu : Measure Complex := volume.withDensity f
    have hflat : ∀ᵐ omega ∂paperIndicatorSampleMeasure ell d nu,
        IsUnit (profile.paperIndicatorOpenExteriorProduct center z degree
          (paperIndicatorFlatRowsEquiv ell d omega)) := by
      filter_upwards [
        ae_paperIndicator_rightEdge_ne_zero_complex_withDensity ell d profile.b
          (profile.b_ne_zero hc0 (Fin.last (d + 1))) hf,
        ae_paperIndicatorTransferMatrix_all_isUnit_complex_withDensity ell d
          center hcenter profile.b (profile.b_ne_zero hc0 0)
          (profile.b_ne_zero hc0 (Fin.last (d + 1))) z hf] with omega hbeta hall
      rw [profile.paperIndicatorOpenExteriorProduct_eq_clearedCompounds]
      · apply chronologicalProduct_isUnit_of_forall_mem_matrixCell
        intro A hA
        simp only [List.mem_ofFn] at hA
        obtain ⟨t, rfl⟩ := hA
        simpa only [paperIndicatorOpenBeta_flatRows_any,
          paperIndicatorOpenTransfer_flatRows_any] using
          (hall (ZMod.finEquiv ell t)).2 degree.val |>.2
      · intro t
        simpa only [paperIndicatorOpenBeta_flatRows_any] using hbeta (ZMod.finEquiv ell t)
    have hpull := (paperIndicatorFlatRows_measurePreserving ell d nu).symm.quasiMeasurePreserving.ae hflat
    simpa only [literalPhysicalOutsideExteriorProduct,
      MeasurableEquiv.apply_symm_apply, nu] using hpull

/-- Exact expectation transport from the matrix-cell probability space to
the physical IID open-row probability space. -/
theorem literalPhysicalMesoscopicCell_expectedLog_eq_openPressure
    (n ell : Nat) (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu]
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (degree : ExteriorDegree (d + 1)) :
    (∫ sample, iidMatrixCellLogPotential
      (literalPhysicalMesoscopicCell profile center z degree) sample
      ∂iidMeasure (literalPhysicalMesoscopicCellMeasure ell d nu) n) =
    ∫ rows, profile.paperIndicatorOpenPressure center z degree rows
      ∂paperIndicatorOpenRowSampleMeasure (n * ((d + 1) + ell)) d nu := by
  have h := (literalPhysicalIidCellRows_measurePreserving n ell d nu).integral_comp'
    (profile.paperIndicatorOpenPressure center z degree)
  simpa only [paperIndicatorOpenPressure, iidMatrixCellLogPotential,
    iidMatrixCellProduct_literalPhysicalMesoscopicCell_eq_openProduct] using h

/-- Concrete physical version of the centered matrix telescope.  All
measurability, factor-unit, one-cell integrability and global integrability
premises have been discharged.  The conclusion is stated directly for the
paper's `cellCount * (d + 1 + ell)` IID open-row pressure, centered at the
actual `ell`-row outside pressure. -/
theorem complex_literalPhysicalMesoscopicCell_expectedLog_telescope
    (ell cellCount : Nat)
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : Complex)
    (degree : ExteriorDegree (d + 1))
    (f : Complex -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ w ∂(volume : Measure Complex), f w ≤ ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Complex => ‖u‖ ^ 2) (volume.withDensity f))
    (hsecond : ∫ u : Complex, ‖u‖ ^ 2 ∂(volume.withDensity f) <= 1) :
    let nu : Measure Complex := volume.withDensity f
    let base := ∫ outside : LiteralPhysicalOutsideRows ell d,
      profile.paperIndicatorOpenPressure center z degree outside
      ∂paperIndicatorOpenRowSampleMeasure ell d nu
    let freshPressure := ∫ omega,
      Real.log ‖literalPaperExteriorCell profile center z degree omega‖
      ∂literalPaperExteriorCellMeasure d nu
    let error := max (complexLiteralProjectiveCellLoss d c0 L degree) freshPressure
    (cellCount : Real) * (base - error) ≤
      (∫ rows, profile.paperIndicatorOpenPressure center z degree rows
        ∂paperIndicatorOpenRowSampleMeasure (cellCount * ((d + 1) + ell)) d nu) ∧
    (∫ rows, profile.paperIndicatorOpenPressure center z degree rows
      ∂paperIndicatorOpenRowSampleMeasure (cellCount * ((d + 1) + ell)) d nu) ≤
      (cellCount : Real) * (base + error) := by
  let nu : Measure Complex := volume.withDensity f
  let B := literalPhysicalOutsideExteriorProduct (ell := ell) profile center z degree
  have hBcont : Continuous B :=
    profile.continuous_paperIndicatorOpenExteriorProduct center z degree ell
  have hBmeas : ∀ i j, Measurable (fun outside => B outside i j) :=
    fun i j => ((continuous_apply j).comp ((continuous_apply i).comp hBcont)).measurable
  have hBnorm : Measurable (fun outside => ‖B outside‖) := hBcont.norm.measurable
  have hBunit : ∀ᵐ outside ∂paperIndicatorOpenRowSampleMeasure ell d nu,
      IsUnit (B outside) := by
    exact ae_literalPhysicalOutsideExteriorProduct_isUnit_complex_withDensity
      ell profile hc0 center hcenter z degree hf
  have hbaseInt : Integrable (fun outside => Real.log ‖B outside‖)
      (paperIndicatorOpenRowSampleMeasure ell d nu) :=
    complex_literalPhysicalOpenPressure_integrable ell nu (complexBallBound_withDensity hf)
      hL profile hc0 hsqrt center z degree hsecondInt hsecond
  have hCellInt := complex_literalPhysicalMesoscopicCell_logOpNorm_integrable
    (ell := ell) nu (complexBallBound_withDensity hf) hL profile hc0 hsqrt
    center z degree hsecondInt hsecond
  have hGlobalInt := complex_literalPhysicalMesoscopicCell_global_integrable
    (ell := ell) nu (complexBallBound_withDensity hf) hL profile hc0 hsqrt
    center z degree hsecondInt hsecond
  have hTel := complex_literalRandomOutsideExteriorCell_expectedLog_telescope_autoUnits
    (paperIndicatorOpenRowSampleMeasure ell d nu) profile hc0 hsqrt
    center hcenter z degree B hBmeas hBnorm hBunit hbaseInt
    f hL hf hsecondInt hsecond
    (by simpa only [literalPhysicalMesoscopicCell,
      literalPhysicalMesoscopicCellMeasure, B, nu] using hCellInt)
    cellCount (fun n _ => by
      simpa only [literalPhysicalMesoscopicCell,
        literalPhysicalMesoscopicCellMeasure, B, nu] using hGlobalInt n)
  have hPressure := literalPhysicalMesoscopicCell_expectedLog_eq_openPressure
    cellCount ell nu profile center z degree
  change (∫ sample, iidMatrixCellLogPotential
    (literalRandomOutsideExteriorCell profile center z degree B) sample
    ∂iidMeasure ((paperIndicatorOpenRowSampleMeasure ell d nu).prod
      (literalPaperExteriorCellMeasure d nu)) cellCount) = _ at hPressure
  simpa only [nu, B, literalPhysicalOutsideExteriorProduct,
    paperIndicatorOpenPressure, hPressure] using hTel

end CircularLawSections56.Section5
