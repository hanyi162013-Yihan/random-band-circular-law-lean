import CircularLawSections56.Section5.LiteralProjectiveCellInputAdapter
import CircularLawSections56.Section5.LiteralIidMatrixCellAEAdapter
import CircularLawSections56.Section5.LiteralIidCellInvertibilityAdapter
import CircularLawSections56.Section5.LiteralGlobalIntegrabilityAdapter

/-!
# End-to-end literal complex IID cell telescope

This file closes the finite-cell interface for the genuine chronological
product of literal Section 4 exterior cells.  The projective one-cell lower
bound, the one-cell open-pressure upper bound, almost-sure invertibility, and
global product-potential integrability are all instantiated from the common
bounded-density and second-moment hypotheses.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights Matrix

variable {d : Nat} {c0 C0 : Real}

local instance literalPaperExteriorCellMeasureSigmaFiniteTelescope
    (d : Nat) (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    SigmaFinite (literalPaperExteriorCellMeasure d nu) := by
  unfold literalPaperExteriorCellMeasure
  infer_instance

local instance literalPaperExteriorCellMeasureProbabilityTelescope
    (d : Nat) (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (literalPaperExteriorCellMeasure d nu) := by
  unfold literalPaperExteriorCellMeasure
  infer_instance

/-- The genuine literal-cell expected-log telescope.  Its terminal observable
is the logarithmic operator norm of the actual chronological product of
`cellCount` independent literal exterior cells.  No additional analytic
premise remains beyond the common Section 4 density and second-moment inputs.
-/
theorem complex_literalPaperExteriorCell_expectedLog_telescope
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (f : Complex -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ w ∂(volume : Measure Complex),
      f w <= ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Complex => ‖u‖ ^ 2)
      (volume.withDensity f))
    (hsecond : ∫ u : Complex, ‖u‖ ^ 2 ∂(volume.withDensity f) <= 1)
    (cellCount : Nat) :
    let C := literalPaperExteriorCell profile center z q
    let mu := literalPaperExteriorCellMeasure d (volume.withDensity f)
    let pressure := ∫ omega, Real.log ‖C omega‖ ∂mu
    let error := max (complexLiteralProjectiveCellLoss d c0 L q) pressure
    (cellCount : Real) * (0 - error) <=
        ∫ omega, iidMatrixCellLogPotential C omega ∂iidMeasure mu cellCount /\
      (∫ omega, iidMatrixCellLogPotential C omega ∂iidMeasure mu cellCount) <=
        (cellCount : Real) * (0 + error) := by
  classical
  let nu : Measure Complex := volume.withDensity f
  let C := literalPaperExteriorCell profile center z q
  let mu := literalPaperExteriorCellMeasure d nu
  let pressure := ∫ omega, Real.log ‖C omega‖ ∂mu
  let error := max (complexLiteralProjectiveCellLoss d c0 L q) pressure
  let _ : SigmaFinite nu := inferInstance
  let _ : IsProbabilityMeasure nu := inferInstance
  let _ : SigmaFinite mu := inferInstance
  let _ : IsProbabilityMeasure mu := by
    unfold mu literalPaperExteriorCellMeasure
    infer_instance
  let _ : Nonempty (ExteriorIndex (d + 1) q) :=
    exteriorIndex_nonempty (d + 1) q

  have hOne :
      (forall v : EuclideanSpace Complex (ExteriorIndex (d + 1) q),
          ‖v‖ = 1 ->
          Integrable (fun omega => matrixCellVectorLog C omega v) mu /\
            0 - error <= ∫ omega, matrixCellVectorLog C omega v ∂mu) /\
        (Integrable (fun omega => Real.log ‖C omega‖) mu /\
          (∫ omega, Real.log ‖C omega‖ ∂mu) <= 0 + error) := by
    simpa only [C, mu, nu, pressure, error] using
      (complex_literalPaperExteriorCell_oneCellInputs
        (d := d) (c0 := c0) (C0 := C0)
        profile hc0 hsqrt center z q f hL hf hsecondInt hsecond)
  have hCellUnit : ∀ᵐ omega ∂mu, IsUnit (C omega) := by
    simpa only [C, mu, nu] using
      (ae_literalPaperExteriorCell_isUnit_complex_withDensity
        (d := d) (c0 := c0) (C0 := C0)
        profile hc0 center hcenter z q
        (f := f) (L := ENNReal.ofReal L) hf)
  have hGlobal : forall n, Integrable
      (iidMatrixCellLogPotential C) (iidMeasure mu n) := by
    simpa only [C, mu, nu] using
      (complex_literalPaperExteriorCell_iidMatrixCellLogPotential_integrable
        (d := d) (c0 := c0) (C0 := C0) (L := L)
        nu (complexBallBound_withDensity hf) hL profile hc0 hsqrt
        center z q hsecondInt hsecond)
  have htelescope :=
    iidMatrixCellProduct_expectedLog_telescope_autoDirection_ae
      mu C cellCount 0 error hOne.1 hOne.2 hCellUnit
        (fun n _hn => hGlobal n)
  simpa only [C, mu, nu, pressure, error] using htelescope

end CircularLawSections56.Section5
