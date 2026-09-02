import CircularLawSection4.PaperFreshClosureFull
import CircularLawSections56.Section5.PressureLifting

/-!
# Literal IID fresh-cell pressure adapter

This file turns the end-to-end one-fresh-block estimates of Section 4 into the
two-sided expected-log increment bounds consumed by the Section 5 telescope.

There is no abstract probabilistic estimate among the hypotheses below.  For a
fixed frozen exterior family, the complex and real cell bounds are direct
consequences of Section 4's literal flat-IID `FreshZ` theorems.  The last two
results telescope a finite list of such already-identified cell increments.
The separate identification of those increments with successive log norms of
an adapted product is intentionally not asserted here.
-/

open scoped ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator BigOperators
open MeasureTheory

noncomputable section

namespace CircularLawSections56.Section5

open CircularLawSection4
open CircularLawSection4.PaperIndicatorWeights

/-- An integrable absolute deviation from a constant bounds the expectation
on both sides.  This is the analytic conversion used after the literal
Section 4 one-cell `L¹` theorem. -/
theorem integral_between_of_integrable_abs_sub_const
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu] (X : Omega -> Real) (center error : Real)
    (hX : AEStronglyMeasurable X mu)
    (hAbs : Integrable (fun omega => |X omega - center|) mu)
    (hBound : (∫ omega, |X omega - center| ∂mu) <= error) :
    center - error <= ∫ omega, X omega ∂mu /\
      (∫ omega, X omega ∂mu) <= center + error := by
  have hDiffMeas : AEStronglyMeasurable (fun omega => X omega - center) mu :=
    hX.sub aestronglyMeasurable_const
  have hDiff : Integrable (fun omega => X omega - center) mu := by
    apply (integrable_norm_iff hDiffMeas).mp
    simpa only [Real.norm_eq_abs] using hAbs
  have hXInt : Integrable X mu := by
    have h := hDiff.add (integrable_const center)
    apply h.congr
    filter_upwards with omega
    exact sub_add_cancel (X omega) center
  have hMean : |(∫ omega, X omega ∂mu) - center| <=
      ∫ omega, |X omega - center| ∂mu := by
    have hNorm := abs_integral_le_integral_abs
      (μ := mu) (f := fun omega => X omega - center)
    simpa [integral_sub hXInt (integrable_const center), Real.norm_eq_abs] using hNorm
  have hFinal : |(∫ omega, X omega ∂mu) - center| <= error := hMean.trans hBound
  have h := abs_le.mp hFinal
  constructor <;> linarith

/-- The literal expected logarithmic pressure of one complex flat-IID fresh
cell with a deterministic frozen exterior family. -/
noncomputable def complexIidFreshCellPressure
    (N d : Nat) [NeZero N] {c0 C0 : Real}
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex) (start : ZMod N)
    (B : (q : ExteriorDegree (d + 1)) ->
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex)
    (f : Complex -> ENNReal) : Real :=
  ∫ omega, Real.log
      ‖profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtoms N d start omega) B‖
    ∂paperIndicatorSampleMeasure N d (volume.withDensity f)

/-- The explicit complex one-cell error furnished by Section 4. -/
noncomputable def complexIidFreshCellError
    (d : Nat) (c0 L : Real) (z : Complex) : Real :=
  paperIsolatedCoefficientLoss d c0 +
    complexFreshNegativeBound d L + paperFreshPositiveBound d z

/-- Literal complex flat-IID cell upper and lower bounds.  In particular,
the right conjunct is the missing one-cell upper estimate; it is not assumed.
-/
theorem complex_iidFreshCellPressure_bounds
    (N d : Nat) [NeZero N] (hsize : d + 1 <= N)
    {c0 C0 : Real} (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0) (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex) (start : ZMod N)
    (B : (q : ExteriorDegree (d + 1)) ->
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex)
    (hB : 0 < exteriorFamilyMaxL2OpNorm B)
    (f : Complex -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ w : Complex ∂(volume : Measure Complex),
      f w <= ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Complex => ‖u‖ ^ 2)
      (volume.withDensity f))
    (hsecond : (∫ u : Complex, ‖u‖ ^ 2 ∂(volume.withDensity f)) <= 1) :
    Real.log (exteriorFamilyMaxL2OpNorm B) -
        complexIidFreshCellError d c0 L z <=
      complexIidFreshCellPressure N d profile center z start B f /\
    complexIidFreshCellPressure N d profile center z start B f <=
      Real.log (exteriorFamilyMaxL2OpNorm B) +
        complexIidFreshCellError d c0 L z := by
  let mu := paperIndicatorSampleMeasure N d (volume.withDensity f)
  let X := fun omega : Fin (N * (d + 2)) -> Complex => Real.log
    ‖profile.paperIndicatorFreshZ center z
      (paperIndicatorFreshAtoms N d start omega) B‖
  let scale := exteriorFamilyMaxL2OpNorm B
  let error := complexIidFreshCellError d c0 L z
  let _ : IsProbabilityMeasure mu := by
    simpa only [mu, paperIndicatorSampleMeasure] using
      iidMeasure_isProbability (volume.withDensity f) (N * (d + 2))
  have hClosure := profile.complex_paperIndicatorFlatFreshZ_absLog_L1_withDensity
    N d hsize hc0 hsqrt center z start B hB f hL hf hsecondInt hsecond
  have hXMeas : Measurable X := by
    dsimp only [X]
    exact Real.measurable_log.comp
      (measurable_norm_paperIndicatorFreshZ
        (d := d) (c₀ := c0) (C₀ := C0) profile center z
        (fun omega => paperIndicatorFreshAtoms N d start omega)
        (fun t ell => measurable_paperIndicatorFreshAtoms N d start t ell) B)
  have hBounds := integral_between_of_integrable_abs_sub_const
    mu X (Real.log scale) error hXMeas.aestronglyMeasurable
    (by simpa only [mu, X, scale] using hClosure.2.1)
    (by simpa only [mu, X, scale, error, complexIidFreshCellError] using hClosure.2.2)
  simpa only [mu, X, scale, error, complexIidFreshCellPressure] using hBounds

/-- The literal expected logarithmic pressure of one real flat-IID fresh
cell, after the canonical embedding into `Complex`. -/
noncomputable def realIidFreshCellPressure
    (N d : Nat) [NeZero N] {c0 C0 : Real}
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex) (start : ZMod N)
    (B : (q : ExteriorDegree (d + 1)) ->
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex)
    (f : Real -> ENNReal) : Real :=
  ∫ omega, Real.log
      ‖profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtomsOfReal N d start omega) B‖
    ∂paperIndicatorRealSampleMeasure N d (volume.withDensity f)

/-- The explicit real one-cell error furnished by Section 4. -/
noncomputable def realIidFreshCellError
    (d : Nat) (c0 L : Real) (z : Complex) : Real :=
  paperIsolatedCoefficientLoss d c0 +
    realFreshNegativeBound d L + paperFreshPositiveBound d z

/-- Literal real flat-IID cell upper and lower bounds. -/
theorem real_iidFreshCellPressure_bounds
    (N d : Nat) [NeZero N] (hsize : d + 1 <= N)
    {c0 C0 : Real} (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0) (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex) (start : ZMod N)
    (B : (q : ExteriorDegree (d + 1)) ->
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex)
    (hB : 0 < exteriorFamilyMaxL2OpNorm B)
    (f : Real -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ x : Real ∂(volume : Measure Real),
      f x <= ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Real => u ^ 2) (volume.withDensity f))
    (hsecond : (∫ u : Real, u ^ 2 ∂(volume.withDensity f)) <= 1) :
    Real.log (exteriorFamilyMaxL2OpNorm B) -
        realIidFreshCellError d c0 L z <=
      realIidFreshCellPressure N d profile center z start B f /\
    realIidFreshCellPressure N d profile center z start B f <=
      Real.log (exteriorFamilyMaxL2OpNorm B) +
        realIidFreshCellError d c0 L z := by
  let mu := paperIndicatorRealSampleMeasure N d (volume.withDensity f)
  let X := fun omega : Fin (N * (d + 2)) -> Real => Real.log
    ‖profile.paperIndicatorFreshZ center z
      (paperIndicatorFreshAtomsOfReal N d start omega) B‖
  let scale := exteriorFamilyMaxL2OpNorm B
  let error := realIidFreshCellError d c0 L z
  let _ : IsProbabilityMeasure mu := by
    simpa only [mu, paperIndicatorRealSampleMeasure] using
      iidMeasure_isProbability (volume.withDensity f) (N * (d + 2))
  have hClosure := profile.real_paperIndicatorFlatFreshZ_absLog_L1_withDensity
    N d hsize hc0 hsqrt center z start B hB f hL hf hsecondInt hsecond
  have hXMeas : Measurable X := by
    dsimp only [X]
    exact Real.measurable_log.comp
      (measurable_norm_paperIndicatorFreshZ
        (d := d) (c₀ := c0) (C₀ := C0) profile center z
        (fun omega => paperIndicatorFreshAtomsOfReal N d start omega)
        (fun t ell => measurable_paperIndicatorFreshAtomsOfReal N d start t ell) B)
  have hBounds := integral_between_of_integrable_abs_sub_const
    mu X (Real.log scale) error hXMeas.aestronglyMeasurable
    (by simpa only [mu, X, scale] using hClosure.2.1)
    (by simpa only [mu, X, scale, error, realIidFreshCellError] using hClosure.2.2)
  simpa only [mu, X, scale, error, realIidFreshCellPressure] using hBounds

/-- Cell-dependent literal bounds telescope with the exact sum of the
Section 4 errors.  This is the form used when the frozen exterior family
changes from cell to cell. -/
theorem iidFreshCell_telescope_sum_bounds
    (potential base error : Nat -> Real) (q : Nat)
    (hzero : potential 0 = 0)
    (hcell : ∀ j < q,
      base j - error j <= potential (j + 1) - potential j /\
        potential (j + 1) - potential j <= base j + error j) :
    (∑ j ∈ Finset.range q, base j) - (∑ j ∈ Finset.range q, error j) <=
        potential q /\
      potential q <=
        (∑ j ∈ Finset.range q, base j) + (∑ j ∈ Finset.range q, error j) := by
  have h := cell_telescope_sum_bounds potential
    (fun j => base j - error j) (fun j => base j + error j) q hcell
  simpa only [hzero, sub_zero, Finset.sum_sub_distrib, Finset.sum_add_distrib] using h

/-- Constant one-cell errors give the exact Section 5 pressure-lifting
telescope once the literal iid-cell bound has identified each increment. -/
theorem iidFreshCell_pressure_lift
    (potential : Nat -> Real) (base error : Real) (q : Nat)
    (hzero : potential 0 = 0)
    (hcell : ∀ j < q,
      base - error <= potential (j + 1) - potential j /\
        potential (j + 1) - potential j <= base + error) :
    (q : Real) * (base - error) <= potential q /\
      potential q <= (q : Real) * (base + error) :=
  pressure_lift_degree potential base error q hzero hcell

/-- Cumulative pressure formed from a sequence of already-identified iid
fresh-cell expected log increments. -/
noncomputable def cumulativeIidFreshCellPressure (increment : Nat -> Real) :
    Nat -> Real
  | 0 => 0
  | j + 1 => cumulativeIidFreshCellPressure increment j + increment j

@[simp] theorem cumulativeIidFreshCellPressure_zero (increment : Nat -> Real) :
    cumulativeIidFreshCellPressure increment 0 = 0 := rfl

@[simp] theorem cumulativeIidFreshCellPressure_succ
    (increment : Nat -> Real) (j : Nat) :
    cumulativeIidFreshCellPressure increment (j + 1) =
      cumulativeIidFreshCellPressure increment j + increment j := rfl

/-- A finite sequence of literal complex iid fresh cells telescopes with
exactly the sum of the explicit Section 4 one-cell errors.  No cell upper or
lower estimate is an input: each is obtained by invoking
`complex_paperIndicatorFlatFreshZ_absLog_L1_withDensity` at that cell. -/
theorem complex_iidFreshCell_cumulative_telescope
    (N d : Nat) [NeZero N] (hsize : d + 1 <= N)
    {c0 C0 : Real} (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0) (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex) (start : ZMod N)
    (B : Nat -> (q : ExteriorDegree (d + 1)) ->
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex)
    (hB : ∀ j, 0 < exteriorFamilyMaxL2OpNorm (B j))
    (f : Complex -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ w : Complex ∂(volume : Measure Complex),
      f w <= ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Complex => ‖u‖ ^ 2)
      (volume.withDensity f))
    (hsecond : (∫ u : Complex, ‖u‖ ^ 2 ∂(volume.withDensity f)) <= 1)
    (cellCount : Nat) :
    (∑ j ∈ Finset.range cellCount,
        Real.log (exteriorFamilyMaxL2OpNorm (B j))) -
          (cellCount : Real) * complexIidFreshCellError d c0 L z <=
      cumulativeIidFreshCellPressure
        (fun j => complexIidFreshCellPressure N d profile center z start (B j) f)
        cellCount /\
    cumulativeIidFreshCellPressure
        (fun j => complexIidFreshCellPressure N d profile center z start (B j) f)
        cellCount <=
      (∑ j ∈ Finset.range cellCount,
        Real.log (exteriorFamilyMaxL2OpNorm (B j))) +
          (cellCount : Real) * complexIidFreshCellError d c0 L z := by
  have hTel := iidFreshCell_telescope_sum_bounds
    (cumulativeIidFreshCellPressure
      (fun j => complexIidFreshCellPressure N d profile center z start (B j) f))
    (fun j => Real.log (exteriorFamilyMaxL2OpNorm (B j)))
    (fun _ => complexIidFreshCellError d c0 L z) cellCount rfl
    (fun j _ => by
      simpa only [cumulativeIidFreshCellPressure_succ, add_sub_cancel_left] using
        (complex_iidFreshCellPressure_bounds N d hsize profile hc0 hsqrt
          center z start (B j) (hB j) f hL hf hsecondInt hsecond))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_ofNat] using hTel

end CircularLawSections56.Section5
