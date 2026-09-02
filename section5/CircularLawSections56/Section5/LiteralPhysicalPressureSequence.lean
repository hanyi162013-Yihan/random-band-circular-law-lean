import CircularLawSections56.Section5.LiteralPhysicalMesoscopicCellAdapter
import CircularLawSections56.Section5.LiteralNearEndToEndAssembly

/-!
# Physical pressure sequences for the literal assembly

This module supplies the cumulative `cell_bounds` field of the literal near-end
assembly from the actual physical open-row telescope.  The bandwidth dimension,
outside length, cell count, and exterior-degree type may all vary with the triangular
index.  The calibration pressure is transported from the common sample space by a
measure-preserving restriction to the outside rows; equality of coordinate means is
proved from that transport, not assumed.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

universe u

variable {Omega : Nat -> Type u} [forall n, MeasurableSpace (Omega n)]
variable {c0 C0 : Nat -> Real}

private theorem physicalPressure_integral_comp_of_measurePreserving
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    {mu : Measure Alpha} {nu : Measure Beta} {e : Alpha -> Beta}
    (he : MeasurePreserving e mu nu) (g : Beta -> Real) (hg : Integrable g nu) :
    (∫ x, g (e x) ∂mu) = ∫ y, g y ∂nu := by
  have hgMap : AEStronglyMeasurable g (Measure.map e mu) := by
    rw [he.map_eq]
    exact hg.aestronglyMeasurable
  calc
    (∫ x, g (e x) ∂mu) = ∫ y, g y ∂Measure.map e mu :=
      (integral_map he.measurable.aemeasurable hgMap).symm
    _ = ∫ y, g y ∂nu := by rw [he.map_eq]

/-- The actual number of rows in one physical fresh/outside cell. -/
def literalPhysicalCellLengthSequence (d ell : Nat -> Nat) (n : Nat) : Nat :=
  (d n + 1) + ell n

/-- Expected pressure of the actual `ell(n)`-row outside product. -/
def literalPhysicalOutsideMeanSequence
    (d ell : Nat -> Nat) (nu : Nat -> Measure Complex)
    [forall n, SigmaFinite (nu n)] [forall n, IsProbabilityMeasure (nu n)]
    (profile : forall n, PaperIndicatorWeights (d n + 1) (c0 n) (C0 n))
    (center : forall n, Fin (d n + 1)) (z : Nat -> Complex) :
    forall n, ExteriorDegree (d n + 1) -> Real :=
  fun n r => ∫ rows, (profile n).paperIndicatorOpenPressure
    (center n) (z n) r rows ∂paperIndicatorOpenRowSampleMeasure (ell n) (d n) (nu n)

/-- Expected pressure of the actual `q(n)`-cell chronological open-row product. -/
def literalPhysicalLiftedMeanSequence
    (d ell q : Nat -> Nat) (nu : Nat -> Measure Complex)
    [forall n, SigmaFinite (nu n)] [forall n, IsProbabilityMeasure (nu n)]
    (profile : forall n, PaperIndicatorWeights (d n + 1) (c0 n) (C0 n))
    (center : forall n, Fin (d n + 1)) (z : Nat -> Complex) :
    forall n, ExteriorDegree (d n + 1) -> Real :=
  fun n r => ∫ rows, (profile n).paperIndicatorOpenPressure
    (center n) (z n) r rows
    ∂paperIndicatorOpenRowSampleMeasure
      (q n * literalPhysicalCellLengthSequence d ell n) (d n) (nu n)

/-- The normalization length may be the full cell length `m`, while the calibration
base remains the `ell`-row outside pressure.  An exact fresh/outside decomposition
identifies the actual lifted row count with `q * m`; it does not identify `ell` with `m`.
-/
theorem literalPhysicalLiftedMeanSequence_eq_fullLength
    (active : Nat -> Bool) (d ell q m : Nat -> Nat) (nu : Nat -> Measure Complex)
    [forall n, SigmaFinite (nu n)] [forall n, IsProbabilityMeasure (nu n)]
    (profile : forall n, PaperIndicatorWeights (d n + 1) (c0 n) (C0 n))
    (center : forall n, Fin (d n + 1)) (z : Nat -> Complex)
    (hCellLength : forall n, active n = true -> (d n + 1) + ell n = m n) :
    forall n, active n = true -> forall r,
      literalPhysicalLiftedMeanSequence d ell q nu profile center z n r =
        ∫ rows, (profile n).paperIndicatorOpenPressure (center n) (z n) r rows
          ∂paperIndicatorOpenRowSampleMeasure (q n * m n) (d n) (nu n) := by
  intro n hn r
  exact congrArg
    (fun k : Nat =>
      ∫ rows : Fin (q n * k) -> PaperIndicatorAtomRow (d n),
        (profile n).paperIndicatorOpenPressure (center n) (z n) r rows
          ∂paperIndicatorOpenRowSampleMeasure (q n * k) (d n) (nu n))
    (hCellLength n hn)

/-- Expected pressure of the reserved literal fresh product alone. -/
def literalPhysicalFreshMeanSequence
    (d : Nat -> Nat) (nu : Nat -> Measure Complex)
    (profile : forall n, PaperIndicatorWeights (d n + 1) (c0 n) (C0 n))
    (center : forall n, Fin (d n + 1)) (z : Nat -> Complex) :
    forall n, ExteriorDegree (d n + 1) -> Real :=
  fun n r => ∫ omega,
    Real.log ‖literalPaperExteriorCell (profile n) (center n) (z n) r omega‖
    ∂literalPaperExteriorCellMeasure (d n) (nu n)

/-- The exact degreewise error in the physical centered telescope.  The outside
pressure is the base and does not occur inside this maximum. -/
def literalPhysicalCellErrorSequence
    (d : Nat -> Nat) (nu : Nat -> Measure Complex)
    (profile : forall n, PaperIndicatorWeights (d n + 1) (c0 n) (C0 n))
    (center : forall n, Fin (d n + 1)) (z : Nat -> Complex) (L : Nat -> Real) :
    forall n, ExteriorDegree (d n + 1) -> Real :=
  fun n r => max (complexLiteralProjectiveCellLoss (d n) (c0 n) (L n) r)
    (literalPhysicalFreshMeanSequence d nu profile center z n r)

/-- The exact physical error is nonnegative at every exterior degree. -/
theorem literalPhysicalCellErrorSequence_nonneg
    (d : Nat -> Nat) (nu : Nat -> Measure Complex)
    (profile : forall n, PaperIndicatorWeights (d n + 1) (c0 n) (C0 n))
    (center : forall n, Fin (d n + 1)) (z : Nat -> Complex) (L : Nat -> Real)
    (n : Nat) (r : ExteriorDegree (d n + 1)) :
    0 <= literalPhysicalCellErrorSequence d nu profile center z L n r :=
  (complexLiteralProjectiveCellLoss_nonneg (d n) (c0 n) (L n) r).trans
    (le_max_left _ _)

/-- Any degree-uniform upper bound for the physical cell error is automatically
nonnegative on the active branch, as required by the assembly's scale interface. -/
theorem literalPhysicalUniformCellError_nonneg
    (active : Nat -> Bool) (d : Nat -> Nat) (nu : Nat -> Measure Complex)
    (profile : forall n, PaperIndicatorWeights (d n + 1) (c0 n) (C0 n))
    (center : forall n, Fin (d n + 1)) (z : Nat -> Complex) (L error : Nat -> Real)
    (hError : forall n, active n = true -> forall r,
      literalPhysicalCellErrorSequence d nu profile center z L n r <= error n) :
    forall n, active n = true -> 0 <= error n := by
  intro n hn
  exact (literalPhysicalCellErrorSequence_nonneg d nu profile center z L n 0).trans
    (hError n hn 0)

/-- The literal outside pressure pulled back to the common triangular sample space.
The restriction map may forget coordinates; it need not be an embedding. -/
def literalPhysicalCalibrationPressureSequence
    (d ell : Nat -> Nat)
    (profile : forall n, PaperIndicatorWeights (d n + 1) (c0 n) (C0 n))
    (center : forall n, Fin (d n + 1)) (z : Nat -> Complex)
    (restriction : forall n, Omega n -> LiteralPhysicalOutsideRows (ell n) (d n)) :
    forall n, ExteriorDegree (d n + 1) -> Omega n -> Real :=
  fun n r omega => (profile n).paperIndicatorOpenPressure
    (center n) (z n) r (restriction n omega)

/-- Measure-preserving restriction proves the coordinate-mean identification with the
physical outside pressure.  The displayed density/second-moment inputs derive the
integrability needed to transport the integral along a possibly noninjective map. -/
theorem literalCoordinateMeanPressure_eq_physicalOutsideMean_of_ae
    (mu : forall n, Measure (Omega n))
    (active : Nat -> Bool)
    (d ell : Nat -> Nat) (nu : Nat -> Measure Complex)
    [forall n, SigmaFinite (nu n)] [forall n, IsProbabilityMeasure (nu n)]
    (profile : forall n, PaperIndicatorWeights (d n + 1) (c0 n) (C0 n))
    (center : forall n, Fin (d n + 1)) (z : Nat -> Complex) (L : Nat -> Real)
    (restriction : forall n, Omega n -> LiteralPhysicalOutsideRows (ell n) (d n))
    (calibrationY : forall n, ExteriorDegree (d n + 1) -> Omega n -> Real)
    (hRestriction : forall n, active n = true ->
      MeasurePreserving (restriction n) (mu n)
        (paperIndicatorOpenRowSampleMeasure (ell n) (d n) (nu n)))
    (hCalibration : forall n, active n = true -> forall r,
      calibrationY n r =ᵐ[mu n]
        literalPhysicalCalibrationPressureSequence d ell profile center z restriction n r)
    (hc0 : forall n, active n = true -> 0 < c0 n)
    (hsqrt : forall n, active n = true ->
      Real.sqrt (c0 n / (d n + 2 : Real)) <= 1)
    (hL : forall n, active n = true -> 0 <= L n)
    (hnu : forall n, active n = true ->
      ComplexBallBound (nu n) (ENNReal.ofReal (L n)))
    (hsecondInt : forall n, active n = true ->
      Integrable (fun u : Complex => ‖u‖ ^ 2) (nu n))
    (hsecond : forall n, active n = true ->
      (∫ u : Complex, ‖u‖ ^ 2 ∂nu n) <= 1) :
    forall n, active n = true -> forall r,
      literalCoordinateMeanPressure mu calibrationY n r =
        literalPhysicalOutsideMeanSequence d ell nu profile center z n r := by
  intro n hn r
  have hIntegrable := complex_literalPhysicalOpenPressure_integrable
    (ell n) (nu n) (hnu n hn) (hL n hn) (profile n) (hc0 n hn)
    (hsqrt n hn) (center n) (z n) r (hsecondInt n hn) (hsecond n hn)
  calc
    literalCoordinateMeanPressure mu calibrationY n r =
        ∫ omega, (profile n).paperIndicatorOpenPressure (center n) (z n) r
          (restriction n omega) ∂mu n := by
      exact integral_congr_ae (hCalibration n hn r)
    _ = literalPhysicalOutsideMeanSequence d ell nu profile center z n r := by
      exact physicalPressure_integral_comp_of_measurePreserving (hRestriction n hn)
        ((profile n).paperIndicatorOpenPressure (center n) (z n) r) hIntegrable

/-- Pointwise identification is a convenient special case of the AE transport theorem;
no equality of expected pressures is supplied by the caller. -/
theorem literalCoordinateMeanPressure_eq_physicalOutsideMean_of_pointwise
    (mu : forall n, Measure (Omega n))
    (active : Nat -> Bool)
    (d ell : Nat -> Nat) (nu : Nat -> Measure Complex)
    [forall n, SigmaFinite (nu n)] [forall n, IsProbabilityMeasure (nu n)]
    (profile : forall n, PaperIndicatorWeights (d n + 1) (c0 n) (C0 n))
    (center : forall n, Fin (d n + 1)) (z : Nat -> Complex) (L : Nat -> Real)
    (restriction : forall n, Omega n -> LiteralPhysicalOutsideRows (ell n) (d n))
    (calibrationY : forall n, ExteriorDegree (d n + 1) -> Omega n -> Real)
    (hRestriction : forall n, active n = true ->
      MeasurePreserving (restriction n) (mu n)
        (paperIndicatorOpenRowSampleMeasure (ell n) (d n) (nu n)))
    (hCalibration : forall n, active n = true -> forall r omega,
      calibrationY n r omega =
        literalPhysicalCalibrationPressureSequence d ell profile center z restriction n r omega)
    (hc0 : forall n, active n = true -> 0 < c0 n)
    (hsqrt : forall n, active n = true ->
      Real.sqrt (c0 n / (d n + 2 : Real)) <= 1)
    (hL : forall n, active n = true -> 0 <= L n)
    (hnu : forall n, active n = true ->
      ComplexBallBound (nu n) (ENNReal.ofReal (L n)))
    (hsecondInt : forall n, active n = true ->
      Integrable (fun u : Complex => ‖u‖ ^ 2) (nu n))
    (hsecond : forall n, active n = true ->
      (∫ u : Complex, ‖u‖ ^ 2 ∂nu n) <= 1) :
    forall n, active n = true -> forall r,
      literalCoordinateMeanPressure mu calibrationY n r =
        literalPhysicalOutsideMeanSequence d ell nu profile center z n r := by
  apply literalCoordinateMeanPressure_eq_physicalOutsideMean_of_ae
    mu active d ell nu profile center z L restriction calibrationY hRestriction
    _ hc0 hsqrt hL hnu hsecondInt hsecond
  intro n hn r
  exact ae_of_all _ (hCalibration n hn r)

/-- The actual varying-dimensional physical sequences satisfy the centered cumulative
cell bounds with their exact degreewise error. -/
theorem complex_literalPhysicalPressureSequence_bounds
    (active : Nat -> Bool) (d ell q : Nat -> Nat)
    (profile : forall n, PaperIndicatorWeights (d n + 1) (c0 n) (C0 n))
    (center : forall n, Fin (d n + 1)) (z : Nat -> Complex)
    (f : Nat -> Complex -> ENNReal)
    [forall n, IsProbabilityMeasure ((volume : Measure Complex).withDensity (f n))]
    (L : Nat -> Real)
    (hc0 : forall n, active n = true -> 0 < c0 n)
    (hsqrt : forall n, active n = true ->
      Real.sqrt (c0 n / (d n + 2 : Real)) <= 1)
    (hcenter : forall n, active n = true -> center n ≠ 0)
    (hL : forall n, active n = true -> 0 <= L n)
    (hf : forall n, active n = true ->
      ∀ᵐ w ∂(volume : Measure Complex), f n w <= ENNReal.ofReal (L n))
    (hsecondInt : forall n, active n = true ->
      Integrable (fun u : Complex => ‖u‖ ^ 2) (volume.withDensity (f n)))
    (hsecond : forall n, active n = true ->
      (∫ u : Complex, ‖u‖ ^ 2 ∂volume.withDensity (f n)) <= 1) :
    let nu := fun n => (volume : Measure Complex).withDensity (f n)
    forall n, active n = true -> forall r,
      (q n : Real) *
          (literalPhysicalOutsideMeanSequence d ell nu profile center z n r -
            literalPhysicalCellErrorSequence d nu profile center z L n r) <=
        literalPhysicalLiftedMeanSequence d ell q nu profile center z n r ∧
      literalPhysicalLiftedMeanSequence d ell q nu profile center z n r <=
        (q n : Real) *
          (literalPhysicalOutsideMeanSequence d ell nu profile center z n r +
            literalPhysicalCellErrorSequence d nu profile center z L n r) := by
  dsimp only
  intro n hn r
  have h := complex_literalPhysicalMesoscopicCell_expectedLog_telescope
    (ell n) (q n) (profile n) (hc0 n hn) (hsqrt n hn)
    (center n) (hcenter n hn) (z n) r (f n) (hL n hn) (hf n hn)
    (hsecondInt n hn) (hsecond n hn)
  dsimp only [literalPhysicalOutsideMeanSequence, literalPhysicalLiftedMeanSequence,
    literalPhysicalCellErrorSequence, literalPhysicalFreshMeanSequence,
    literalPhysicalCellLengthSequence]
  convert h using 3 <;> rfl

/-- The exact `cell_bounds` shape of `PhysicalLiteralLongBranchInputTri`, now supplied
by actual physical pressures.  A uniform error may dominate the concrete degreewise
maximum; physical-product integrability, almost-everywhere units, and chronological
row reassembly are derived from the displayed natural assumptions.

The calibration observable is identified only almost everywhere after restriction to
the physical outside rows.  Its expected-pressure identity is proved internally. -/
theorem complex_literalPhysicalPressureSequence_cell_bounds
    (mu : forall n, Measure (Omega n))
    (active : Nat -> Bool) (d ell q : Nat -> Nat)
    (profile : forall n, PaperIndicatorWeights (d n + 1) (c0 n) (C0 n))
    (center : forall n, Fin (d n + 1)) (z : Nat -> Complex)
    (f : Nat -> Complex -> ENNReal)
    [forall n, IsProbabilityMeasure ((volume : Measure Complex).withDensity (f n))]
    (L error : Nat -> Real)
    (restriction : forall n, Omega n -> LiteralPhysicalOutsideRows (ell n) (d n))
    (calibrationY : forall n, ExteriorDegree (d n + 1) -> Omega n -> Real)
    (hRestriction : forall n, active n = true ->
      MeasurePreserving (restriction n) (mu n)
        (paperIndicatorOpenRowSampleMeasure (ell n) (d n) (volume.withDensity (f n))))
    (hCalibration : forall n, active n = true -> forall r,
      calibrationY n r =ᵐ[mu n]
        literalPhysicalCalibrationPressureSequence d ell profile center z restriction n r)
    (hc0 : forall n, active n = true -> 0 < c0 n)
    (hsqrt : forall n, active n = true ->
      Real.sqrt (c0 n / (d n + 2 : Real)) <= 1)
    (hcenter : forall n, active n = true -> center n ≠ 0)
    (hL : forall n, active n = true -> 0 <= L n)
    (hf : forall n, active n = true ->
      ∀ᵐ w ∂(volume : Measure Complex), f n w <= ENNReal.ofReal (L n))
    (hsecondInt : forall n, active n = true ->
      Integrable (fun u : Complex => ‖u‖ ^ 2) (volume.withDensity (f n)))
    (hsecond : forall n, active n = true ->
      (∫ u : Complex, ‖u‖ ^ 2 ∂volume.withDensity (f n)) <= 1)
    (hError : forall n, active n = true -> forall r,
      literalPhysicalCellErrorSequence d
        (fun n => (volume : Measure Complex).withDensity (f n))
        profile center z L n r <= error n) :
    let nu := fun n => (volume : Measure Complex).withDensity (f n)
    forall n, active n = true -> forall r,
      (q n : Real) * (literalCoordinateMeanPressure mu calibrationY n r - error n) <=
        literalPhysicalLiftedMeanSequence d ell q nu profile center z n r ∧
      literalPhysicalLiftedMeanSequence d ell q nu profile center z n r <=
        (q n : Real) * (literalCoordinateMeanPressure mu calibrationY n r + error n) := by
  dsimp only
  have hMean := literalCoordinateMeanPressure_eq_physicalOutsideMean_of_ae
    mu active d ell (fun n => (volume : Measure Complex).withDensity (f n))
    profile center z L restriction calibrationY hRestriction hCalibration hc0 hsqrt
    hL (fun n hn => complexBallBound_withDensity (hf n hn)) hsecondInt hsecond
  have hBounds := complex_literalPhysicalPressureSequence_bounds
    active d ell q profile center z f L hc0 hsqrt hcenter hL hf hsecondInt hsecond
  intro n hn r
  rw [hMean n hn r]
  have hq : 0 <= (q n : Real) := Nat.cast_nonneg _
  have hError' := hError n hn r
  constructor
  · exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hError' _) hq).trans
      (hBounds n hn r).1
  · exact (hBounds n hn r).2.trans
      (mul_le_mul_of_nonneg_left (add_le_add_right hError' _) hq)

end CircularLawSections56.Section5
