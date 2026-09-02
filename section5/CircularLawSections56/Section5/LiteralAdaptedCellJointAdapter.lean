import CircularLawSections56.Section5.LiteralDeterminantFreshAdapter
import CircularLawSections56.Section5.LiteralFreshCoordinateTransport
import CircularLawSections56.Section5.LiteralIidCellAdapter

/-!
# Literal adapted-cell joint pressure adapter

This file upgrades Section 4's past-dependent joint `FreshZ` closure to the
two-sided expected-log estimates needed by a finite Section 5 telescope.  The frozen
exterior family may depend measurably on an arbitrary past probability space.

No one-cell upper or lower bound is assumed: both follow from the literal complex or
real flat-IID closure theorem.  Integrability of the new cell pressure is obtained at
the same time.  The only integrability input is the logically necessary one for the
random baseline `log (exteriorFamilyMaxL2OpNorm B)`; the joint closure controls the
absolute difference from that baseline, but cannot make an arbitrary past-dependent
baseline integrable.

The cumulative theorems telescope a finite sequence of these genuine adapted-cell
expectations with exactly the sum of the Section 4 errors.  Identifying that scalar
cumulative pressure with the log norm of a successive adapted product is a separate
deterministic product/reassembly identity and is not asserted here.
-/

open scoped ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator BigOperators
open MeasureTheory

noncomputable section

namespace CircularLawSections56.Section5

open CircularLawSection4
open CircularLawSection4.PaperIndicatorWeights

universe u

/-! ## Analytic conversion -/

/-- An integrable absolute difference from an integrable random baseline makes the
observable integrable and bounds the difference of their expectations. -/
theorem integrable_and_integral_between_of_integrable_abs_sub
    {Omega : Type u} [MeasurableSpace Omega] (mu : Measure Omega)
    (X Y : Omega -> Real) (error : Real)
    (hX : AEStronglyMeasurable X mu) (hY : Integrable Y mu)
    (hAbs : Integrable (fun omega => |X omega - Y omega|) mu)
    (hBound : (∫ omega, |X omega - Y omega| ∂mu) <= error) :
    Integrable X mu /\
      (∫ omega, Y omega ∂mu) - error <= ∫ omega, X omega ∂mu /\
      (∫ omega, X omega ∂mu) <= (∫ omega, Y omega ∂mu) + error := by
  have hDiffMeas : AEStronglyMeasurable (fun omega => X omega - Y omega) mu :=
    hX.sub hY.aestronglyMeasurable
  have hDiff : Integrable (fun omega => X omega - Y omega) mu := by
    apply (integrable_norm_iff hDiffMeas).mp
    simpa only [Real.norm_eq_abs] using hAbs
  have hXInt : Integrable X mu := by
    apply (hDiff.add hY).congr
    filter_upwards with omega
    exact sub_add_cancel (X omega) (Y omega)
  have hMean : |(∫ omega, X omega ∂mu) - (∫ omega, Y omega ∂mu)| <=
      ∫ omega, |X omega - Y omega| ∂mu := by
    have hNorm := abs_integral_le_integral_abs
      (μ := mu) (f := fun omega => X omega - Y omega)
    simpa only [integral_sub hXInt hY, Real.norm_eq_abs] using hNorm
  have hFinal : |(∫ omega, X omega ∂mu) - (∫ omega, Y omega ∂mu)| <= error :=
    hMean.trans hBound
  have hSides := abs_le.mp hFinal
  exact ⟨hXInt, by linarith, by linarith⟩

/-! ## Complex adapted cell -/

/-- The joint logarithmic observable for a complex fresh cell whose frozen exterior
family is a measurable function of the past. -/
noncomputable def complexAdaptedFreshCellLog
    {Past : Type u} [MeasurableSpace Past]
    (N d : Nat) [NeZero N] {c0 C0 : Real}
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex) (start : ZMod N)
    (B : Past -> (q : ExteriorDegree (d + 1)) ->
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex) :
    Past × (Fin (N * (d + 2)) -> Complex) -> Real :=
  fun w => Real.log
    ‖profile.paperIndicatorFreshZ center z
      (paperIndicatorFreshAtoms N d start w.2) (B w.1)‖

/-- Expected joint logarithmic pressure of one complex adapted cell. -/
noncomputable def complexAdaptedFreshCellPressure
    {Past : Type u} [MeasurableSpace Past]
    (muPast : Measure Past) (N d : Nat) [NeZero N] {c0 C0 : Real}
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex) (start : ZMod N)
    (B : Past -> (q : ExteriorDegree (d + 1)) ->
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex)
    (f : Complex -> ENNReal) : Real :=
  ∫ w, complexAdaptedFreshCellLog N d profile center z start B w
    ∂(muPast.prod (paperIndicatorSampleMeasure N d (volume.withDensity f)))

/-- Expected logarithmic exterior-family scale of a random frozen family. -/
noncomputable def adaptedExteriorFamilyBasePressure
    {Past : Type u} [MeasurableSpace Past] (muPast : Measure Past)
    (d : Nat)
    (B : Past -> (q : ExteriorDegree (d + 1)) ->
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex) : Real :=
  ∫ a, Real.log (exteriorFamilyMaxL2OpNorm (B a)) ∂muPast

/-- Section 4's literal complex joint closure gives the complete expected-log
one-cell estimate for a random frozen exterior family.  In particular the fresh-cell
logarithm is automatically integrable once the random baseline logarithm is. -/
theorem complex_adaptedFreshCell_integrable_and_pressure_bounds
    {Past : Type u} [MeasurableSpace Past]
    (muPast : Measure Past) [IsProbabilityMeasure muPast]
    (N d : Nat) [NeZero N] (hsize : d + 1 <= N)
    {c0 C0 : Real} (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0) (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex) (start : ZMod N)
    (B : Past -> (q : ExteriorDegree (d + 1)) ->
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex)
    (hBpos : forall a, 0 < exteriorFamilyMaxL2OpNorm (B a))
    (hBmeas : forall q i j, Measurable (fun a => B a q i j))
    (hBnorm : forall q, Measurable (fun a => ‖B a q‖))
    (hbaseInt : Integrable
      (fun a => Real.log (exteriorFamilyMaxL2OpNorm (B a))) muPast)
    (f : Complex -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ w : Complex ∂(volume : Measure Complex), f w <= ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Complex => ‖u‖ ^ 2)
      (volume.withDensity f))
    (hsecond : (∫ u : Complex, ‖u‖ ^ 2 ∂(volume.withDensity f)) <= 1) :
    Integrable (complexAdaptedFreshCellLog N d profile center z start B)
      (muPast.prod (paperIndicatorSampleMeasure N d (volume.withDensity f))) /\
    adaptedExteriorFamilyBasePressure muPast d B -
        complexIidFreshCellError d c0 L z <=
      complexAdaptedFreshCellPressure muPast N d profile center z start B f /\
    complexAdaptedFreshCellPressure muPast N d profile center z start B f <=
      adaptedExteriorFamilyBasePressure muPast d B +
        complexIidFreshCellError d c0 L z := by
  let muFresh := paperIndicatorSampleMeasure N d (volume.withDensity f)
  let X := complexAdaptedFreshCellLog N d profile center z start B
  let Y := fun w : Past × (Fin (N * (d + 2)) -> Complex) =>
    Real.log (exteriorFamilyMaxL2OpNorm (B w.1))
  let C := complexIidFreshCellError d c0 L z
  let _ : IsProbabilityMeasure muFresh := by
    simpa only [muFresh, paperIndicatorSampleMeasure] using
      iidMeasure_isProbability (volume.withDensity f) (N * (d + 2))
  have hClosure := profile.complex_paperIndicatorFlatFreshZ_rawJointClosure_withDensity
    muPast N d hsize hc0 hsqrt center z start B hBpos hBmeas hBnorm
      f hL hf hsecondInt hsecond
  have hXMeas : Measurable X := by
    dsimp only [X, complexAdaptedFreshCellLog]
    exact Real.measurable_log.comp <| by
      apply profile.measurable_norm_paperIndicatorFreshZ_of_measurable_family
      · intro t ell
        exact (measurable_paperIndicatorFreshAtoms N d start t ell).comp measurable_snd
      · intro q i j
        exact (hBmeas q i j).comp measurable_fst
  have hYInt : Integrable Y (muPast.prod muFresh) := by
    exact measurePreserving_fst.integrable_comp_of_integrable hbaseInt
  have hAbs : Integrable (fun w => |X w - Y w|) (muPast.prod muFresh) := by
    simpa only [X, Y, complexAdaptedFreshCellLog, muFresh] using hClosure.1
  have hAbsBound : (∫ w, |X w - Y w| ∂(muPast.prod muFresh)) <= C := by
    simpa only [X, Y, C, complexAdaptedFreshCellLog, muFresh,
      complexIidFreshCellError] using hClosure.2.1
  have hBounds := integrable_and_integral_between_of_integrable_abs_sub
    (muPast.prod muFresh) X Y C hXMeas.aestronglyMeasurable hYInt hAbs hAbsBound
  have hYIntegral : (∫ w, Y w ∂(muPast.prod muFresh)) =
      adaptedExteriorFamilyBasePressure muPast d B := by
    simpa only [Y, adaptedExteriorFamilyBasePressure] using
      integral_comp_of_measurePreserving measurePreserving_fst
        (fun a => Real.log (exteriorFamilyMaxL2OpNorm (B a))) hbaseInt
  simpa only [X, C, muFresh, complexAdaptedFreshCellPressure, hYIntegral] using hBounds

/-! ## Pullback to one literal full flat sample -/

/-- The adapted complex cell as an observable on one literal full flat sample.  Its
frozen family reads only the genuine complement of the selected fresh block. -/
noncomputable def complexFullFlatAdaptedFreshCellLog
    (N d : Nat) [NeZero N] (start : ZMod N) (hsize : d + 1 <= N)
    {c0 C0 : Real} (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (B : (PaperIndicatorNonfreshCoordinateIndex N d start -> Complex) ->
      (q : ExteriorDegree (d + 1)) ->
        Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex) :
    (Fin (N * (d + 2)) -> Complex) -> Real :=
  fun omega => Real.log
    ‖profile.paperIndicatorFreshZ center z
      (paperIndicatorFreshAtoms N d start omega)
      (B (paperIndicatorNonfreshFreshSplitMeasurableEquiv
        N d start hsize omega).1)‖

/-- Expected pressure of the preceding observable under the single full flat IID law. -/
noncomputable def complexFullFlatAdaptedFreshCellPressure
    (N d : Nat) [NeZero N] (start : ZMod N) (hsize : d + 1 <= N)
    {c0 C0 : Real} (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (B : (PaperIndicatorNonfreshCoordinateIndex N d start -> Complex) ->
      (q : ExteriorDegree (d + 1)) ->
        Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex)
    (f : Complex -> ENNReal) : Real :=
  ∫ omega, complexFullFlatAdaptedFreshCellLog
      N d start hsize profile center z B omega
    ∂paperIndicatorSampleMeasure N d (volume.withDensity f)

/-- Exact full-flat-law wrapper for the complex adapted-cell estimate.  The
outside/fresh product used by Section 4 is reassembled measure-preservingly into one
flat IID sample, and both the fresh atoms and the nonfresh coordinates reduce
pointwise to the corresponding factors. -/
theorem complex_fullFlatAdaptedFreshCell_integrable_and_pressure_bounds
    (N d : Nat) [NeZero N] (hsize : d + 1 <= N)
    {c0 C0 : Real} (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0) (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex) (start : ZMod N)
    (B : (PaperIndicatorNonfreshCoordinateIndex N d start -> Complex) ->
      (q : ExteriorDegree (d + 1)) ->
        Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex)
    (hBpos : forall a, 0 < exteriorFamilyMaxL2OpNorm (B a))
    (hBmeas : forall q i j, Measurable (fun a => B a q i j))
    (hBnorm : forall q, Measurable (fun a => ‖B a q‖))
    (f : Complex -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    (hbaseInt : Integrable
      (fun a => Real.log (exteriorFamilyMaxL2OpNorm (B a)))
      (Measure.pi (fun _ : PaperIndicatorNonfreshCoordinateIndex N d start =>
        volume.withDensity f)))
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ w : Complex ∂(volume : Measure Complex), f w <= ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Complex => ‖u‖ ^ 2)
      (volume.withDensity f))
    (hsecond : (∫ u : Complex, ‖u‖ ^ 2 ∂(volume.withDensity f)) <= 1) :
    Integrable (complexFullFlatAdaptedFreshCellLog
        N d start hsize profile center z B)
      (paperIndicatorSampleMeasure N d (volume.withDensity f)) /\
    adaptedExteriorFamilyBasePressure
        (Measure.pi (fun _ : PaperIndicatorNonfreshCoordinateIndex N d start =>
          volume.withDensity f)) d B -
        complexIidFreshCellError d c0 L z <=
      complexFullFlatAdaptedFreshCellPressure
        N d start hsize profile center z B f /\
    complexFullFlatAdaptedFreshCellPressure
        N d start hsize profile center z B f <=
      adaptedExteriorFamilyBasePressure
        (Measure.pi (fun _ : PaperIndicatorNonfreshCoordinateIndex N d start =>
          volume.withDensity f)) d B +
        complexIidFreshCellError d c0 L z := by
  let nu := volume.withDensity f
  let muOutside := Measure.pi
    (fun _ : PaperIndicatorNonfreshCoordinateIndex N d start => nu)
  let muFull := paperIndicatorSampleMeasure N d nu
  let assemble :
      (PaperIndicatorNonfreshCoordinateIndex N d start -> Complex) ×
          (Fin (N * (d + 2)) -> Complex) ->
        (Fin (N * (d + 2)) -> Complex) :=
    assembleNonfreshWithFreshFull N d start hsize
  let fullLog := complexFullFlatAdaptedFreshCellLog
    N d start hsize profile center z B
  have hJoint := complex_adaptedFreshCell_integrable_and_pressure_bounds
    muOutside N d hsize profile hc0 hsqrt center z start B
      hBpos hBmeas hBnorm (by simpa only [muOutside, nu] using hbaseInt)
      f hL hf hsecondInt hsecond
  have he : MeasurePreserving assemble (muOutside.prod muFull) muFull := by
    simpa only [assemble, muOutside, muFull, nu, paperIndicatorSampleMeasure] using
      assembleNonfreshWithFreshFull_measurePreserving
        N d start hsize (volume.withDensity f)
  have hFullMeas : Measurable fullLog := by
    dsimp only [fullLog, complexFullFlatAdaptedFreshCellLog]
    apply Real.measurable_log.comp
    apply profile.measurable_norm_paperIndicatorFreshZ_of_measurable_family
    · intro t ell
      exact measurable_paperIndicatorFreshAtoms N d start t ell
    · intro q i j
      exact (hBmeas q i j).comp <|
        measurable_fst.comp
          (paperIndicatorNonfreshFreshSplitMeasurableEquiv
            N d start hsize).measurable
  have hComp : fullLog ∘ assemble =
      complexAdaptedFreshCellLog N d profile center z start B := by
    funext sample
    dsimp only [fullLog, assemble, complexFullFlatAdaptedFreshCellLog,
      complexAdaptedFreshCellLog, Function.comp_apply]
    rw [paperIndicatorNonfreshFreshSplit_assemble_nonfresh]
    rw [profile.paperIndicatorFreshZ_assembleNonfreshWithFreshFull]
  have hPull : Integrable (fullLog ∘ assemble) (muOutside.prod muFull) := by
    rw [hComp]
    simpa only [muOutside, muFull, nu] using hJoint.1
  have hFullInt : Integrable fullLog muFull :=
    (he.integrable_comp hFullMeas.aestronglyMeasurable).mp hPull
  have hPressureEq :
      complexAdaptedFreshCellPressure
          muOutside N d profile center z start B f =
        complexFullFlatAdaptedFreshCellPressure
          N d start hsize profile center z B f := by
    have hIntegral := integral_comp_of_measurePreserving he fullLog hFullInt
    have hJointIntegral :
        (∫ sample, complexAdaptedFreshCellLog
            N d profile center z start B sample ∂(muOutside.prod muFull)) =
          ∫ omega, fullLog omega ∂muFull := by
      calc
        (∫ sample, complexAdaptedFreshCellLog
            N d profile center z start B sample ∂(muOutside.prod muFull)) =
            ∫ sample, fullLog (assemble sample) ∂(muOutside.prod muFull) := by
              apply integral_congr_ae
              filter_upwards with sample
              exact (congrFun hComp sample).symm
        _ = ∫ omega, fullLog omega ∂muFull := hIntegral
    simpa only [complexAdaptedFreshCellPressure,
      complexFullFlatAdaptedFreshCellPressure, fullLog, muOutside, muFull, nu] using
        hJointIntegral
  refine ⟨by simpa only [fullLog, muFull, nu] using hFullInt, ?_⟩
  simpa only [muOutside, nu, hPressureEq] using hJoint.2

/-! ## Real adapted cell -/

/-- Real-law version of `complexAdaptedFreshCellLog`, using the canonical embedding of
the fresh real sample into `Complex`. -/
noncomputable def realAdaptedFreshCellLog
    {Past : Type u} [MeasurableSpace Past]
    (N d : Nat) [NeZero N] {c0 C0 : Real}
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex) (start : ZMod N)
    (B : Past -> (q : ExteriorDegree (d + 1)) ->
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex) :
    Past × (Fin (N * (d + 2)) -> Real) -> Real :=
  fun w => Real.log
    ‖profile.paperIndicatorFreshZ center z
      (paperIndicatorFreshAtomsOfReal N d start w.2) (B w.1)‖

/-- Expected joint logarithmic pressure of one real adapted cell. -/
noncomputable def realAdaptedFreshCellPressure
    {Past : Type u} [MeasurableSpace Past]
    (muPast : Measure Past) (N d : Nat) [NeZero N] {c0 C0 : Real}
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex) (start : ZMod N)
    (B : Past -> (q : ExteriorDegree (d + 1)) ->
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex)
    (f : Real -> ENNReal) : Real :=
  ∫ w, realAdaptedFreshCellLog N d profile center z start B w
    ∂(muPast.prod (paperIndicatorRealSampleMeasure N d (volume.withDensity f)))

/-- Real-law past-dependent cell integrability and its literal two-sided expected-log
bound.  Neither side of the cell estimate is a premise. -/
theorem real_adaptedFreshCell_integrable_and_pressure_bounds
    {Past : Type u} [MeasurableSpace Past]
    (muPast : Measure Past) [IsProbabilityMeasure muPast]
    (N d : Nat) [NeZero N] (hsize : d + 1 <= N)
    {c0 C0 : Real} (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0) (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex) (start : ZMod N)
    (B : Past -> (q : ExteriorDegree (d + 1)) ->
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex)
    (hBpos : forall a, 0 < exteriorFamilyMaxL2OpNorm (B a))
    (hBmeas : forall q i j, Measurable (fun a => B a q i j))
    (hBnorm : forall q, Measurable (fun a => ‖B a q‖))
    (hbaseInt : Integrable
      (fun a => Real.log (exteriorFamilyMaxL2OpNorm (B a))) muPast)
    (f : Real -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ x : Real ∂(volume : Measure Real), f x <= ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Real => u ^ 2) (volume.withDensity f))
    (hsecond : (∫ u : Real, u ^ 2 ∂(volume.withDensity f)) <= 1) :
    Integrable (realAdaptedFreshCellLog N d profile center z start B)
      (muPast.prod (paperIndicatorRealSampleMeasure N d (volume.withDensity f))) /\
    adaptedExteriorFamilyBasePressure muPast d B -
        realIidFreshCellError d c0 L z <=
      realAdaptedFreshCellPressure muPast N d profile center z start B f /\
    realAdaptedFreshCellPressure muPast N d profile center z start B f <=
      adaptedExteriorFamilyBasePressure muPast d B +
        realIidFreshCellError d c0 L z := by
  let muFresh := paperIndicatorRealSampleMeasure N d (volume.withDensity f)
  let X := realAdaptedFreshCellLog N d profile center z start B
  let Y := fun w : Past × (Fin (N * (d + 2)) -> Real) =>
    Real.log (exteriorFamilyMaxL2OpNorm (B w.1))
  let C := realIidFreshCellError d c0 L z
  let _ : IsProbabilityMeasure muFresh := by
    simpa only [muFresh, paperIndicatorRealSampleMeasure] using
      iidMeasure_isProbability (volume.withDensity f) (N * (d + 2))
  have hClosure := profile.real_paperIndicatorFlatFreshZ_rawJointClosure_withDensity
    muPast N d hsize hc0 hsqrt center z start B hBpos hBmeas hBnorm
      f hL hf hsecondInt hsecond
  have hXMeas : Measurable X := by
    dsimp only [X, realAdaptedFreshCellLog]
    exact Real.measurable_log.comp <| by
      apply profile.measurable_norm_paperIndicatorFreshZ_of_measurable_family
      · intro t ell
        exact (measurable_paperIndicatorFreshAtomsOfReal N d start t ell).comp measurable_snd
      · intro q i j
        exact (hBmeas q i j).comp measurable_fst
  have hYInt : Integrable Y (muPast.prod muFresh) := by
    exact measurePreserving_fst.integrable_comp_of_integrable hbaseInt
  have hAbs : Integrable (fun w => |X w - Y w|) (muPast.prod muFresh) := by
    simpa only [X, Y, realAdaptedFreshCellLog, muFresh] using hClosure.1
  have hAbsBound : (∫ w, |X w - Y w| ∂(muPast.prod muFresh)) <= C := by
    simpa only [X, Y, C, realAdaptedFreshCellLog, muFresh,
      realIidFreshCellError] using hClosure.2.1
  have hBounds := integrable_and_integral_between_of_integrable_abs_sub
    (muPast.prod muFresh) X Y C hXMeas.aestronglyMeasurable hYInt hAbs hAbsBound
  have hYIntegral : (∫ w, Y w ∂(muPast.prod muFresh)) =
      adaptedExteriorFamilyBasePressure muPast d B := by
    simpa only [Y, adaptedExteriorFamilyBasePressure] using
      integral_comp_of_measurePreserving measurePreserving_fst
        (fun a => Real.log (exteriorFamilyMaxL2OpNorm (B a))) hbaseInt
  simpa only [X, C, muFresh, realAdaptedFreshCellPressure, hYIntegral] using hBounds

/-- The canonically complexified fresh atoms of an assembled real sample are exactly
those read from the supplied full fresh sample. -/
theorem paperIndicatorFreshAtomsOfReal_assembleNonfreshWithFreshFull_adapter
    (N d : Nat) [NeZero N] (start : ZMod N) (hsize : d + 1 <= N)
    (sample :
      (PaperIndicatorNonfreshCoordinateIndex N d start -> Real) ×
        (Fin (N * (d + 2)) -> Real)) :
    paperIndicatorFreshAtomsOfReal N d start
        (assembleNonfreshWithFreshFull N d start hsize sample) =
      paperIndicatorFreshAtomsOfReal N d start sample.2 := by
  rw [paperIndicatorFreshAtomsOfReal_eq_coordinateRestriction,
    paperIndicatorFreshAtomsOfReal_eq_coordinateRestriction]
  funext t ell
  apply congrArg Complex.ofReal
  calc
    assembleNonfreshWithFreshFull N d start hsize sample
        (paperIndicatorFreshCoordinateIndex N d start (t, ell)) =
      (paperIndicatorNonfreshFreshSplitMeasurableEquiv N d start hsize
        (assembleNonfreshWithFreshFull N d start hsize sample)).2 (t, ell) :=
          (paperIndicatorNonfreshFreshSplitMeasurableEquiv_fresh
            N d start hsize
              (assembleNonfreshWithFreshFull N d start hsize sample)
              (t, ell)).symm
    _ = sample.2 (paperIndicatorFreshCoordinateIndex N d start (t, ell)) := by
      rw [paperIndicatorNonfreshFreshSplit_assembleNonfreshWithFreshFull]
      rfl

/-- The real adapted cell as an observable on one literal full flat sample. -/
noncomputable def realFullFlatAdaptedFreshCellLog
    (N d : Nat) [NeZero N] (start : ZMod N) (hsize : d + 1 <= N)
    {c0 C0 : Real} (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (B : (PaperIndicatorNonfreshCoordinateIndex N d start -> Real) ->
      (q : ExteriorDegree (d + 1)) ->
        Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex) :
    (Fin (N * (d + 2)) -> Real) -> Real :=
  fun omega => Real.log
    ‖profile.paperIndicatorFreshZ center z
      (paperIndicatorFreshAtomsOfReal N d start omega)
      (B (paperIndicatorNonfreshFreshSplitMeasurableEquiv
        N d start hsize omega).1)‖

/-- Expected pressure of the real full-flat adapted-cell observable. -/
noncomputable def realFullFlatAdaptedFreshCellPressure
    (N d : Nat) [NeZero N] (start : ZMod N) (hsize : d + 1 <= N)
    {c0 C0 : Real} (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (B : (PaperIndicatorNonfreshCoordinateIndex N d start -> Real) ->
      (q : ExteriorDegree (d + 1)) ->
        Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex)
    (f : Real -> ENNReal) : Real :=
  ∫ omega, realFullFlatAdaptedFreshCellLog
      N d start hsize profile center z B omega
    ∂paperIndicatorRealSampleMeasure N d (volume.withDensity f)

/-- Exact real full-flat-law wrapper.  It transports the real joint closure through
the same literal reassembly and derives integrability and both expected-log bounds on
one real flat IID sample. -/
theorem real_fullFlatAdaptedFreshCell_integrable_and_pressure_bounds
    (N d : Nat) [NeZero N] (hsize : d + 1 <= N)
    {c0 C0 : Real} (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0) (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex) (start : ZMod N)
    (B : (PaperIndicatorNonfreshCoordinateIndex N d start -> Real) ->
      (q : ExteriorDegree (d + 1)) ->
        Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex)
    (hBpos : forall a, 0 < exteriorFamilyMaxL2OpNorm (B a))
    (hBmeas : forall q i j, Measurable (fun a => B a q i j))
    (hBnorm : forall q, Measurable (fun a => ‖B a q‖))
    (f : Real -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    (hbaseInt : Integrable
      (fun a => Real.log (exteriorFamilyMaxL2OpNorm (B a)))
      (Measure.pi (fun _ : PaperIndicatorNonfreshCoordinateIndex N d start =>
        volume.withDensity f)))
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ x : Real ∂(volume : Measure Real), f x <= ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Real => u ^ 2) (volume.withDensity f))
    (hsecond : (∫ u : Real, u ^ 2 ∂(volume.withDensity f)) <= 1) :
    Integrable (realFullFlatAdaptedFreshCellLog
        N d start hsize profile center z B)
      (paperIndicatorRealSampleMeasure N d (volume.withDensity f)) /\
    adaptedExteriorFamilyBasePressure
        (Measure.pi (fun _ : PaperIndicatorNonfreshCoordinateIndex N d start =>
          volume.withDensity f)) d B -
        realIidFreshCellError d c0 L z <=
      realFullFlatAdaptedFreshCellPressure
        N d start hsize profile center z B f /\
    realFullFlatAdaptedFreshCellPressure
        N d start hsize profile center z B f <=
      adaptedExteriorFamilyBasePressure
        (Measure.pi (fun _ : PaperIndicatorNonfreshCoordinateIndex N d start =>
          volume.withDensity f)) d B +
        realIidFreshCellError d c0 L z := by
  let nu := volume.withDensity f
  let muOutside := Measure.pi
    (fun _ : PaperIndicatorNonfreshCoordinateIndex N d start => nu)
  let muFull := paperIndicatorRealSampleMeasure N d nu
  let assemble :
      (PaperIndicatorNonfreshCoordinateIndex N d start -> Real) ×
          (Fin (N * (d + 2)) -> Real) ->
        (Fin (N * (d + 2)) -> Real) :=
    assembleNonfreshWithFreshFull N d start hsize
  let fullLog := realFullFlatAdaptedFreshCellLog
    N d start hsize profile center z B
  have hJoint := real_adaptedFreshCell_integrable_and_pressure_bounds
    muOutside N d hsize profile hc0 hsqrt center z start B
      hBpos hBmeas hBnorm (by simpa only [muOutside, nu] using hbaseInt)
      f hL hf hsecondInt hsecond
  have he : MeasurePreserving assemble (muOutside.prod muFull) muFull := by
    simpa only [assemble, muOutside, muFull, nu,
      paperIndicatorRealSampleMeasure] using
        assembleNonfreshWithFreshFull_measurePreserving
          N d start hsize (volume.withDensity f)
  have hFullMeas : Measurable fullLog := by
    dsimp only [fullLog, realFullFlatAdaptedFreshCellLog]
    apply Real.measurable_log.comp
    apply profile.measurable_norm_paperIndicatorFreshZ_of_measurable_family
    · intro t ell
      exact measurable_paperIndicatorFreshAtomsOfReal N d start t ell
    · intro q i j
      exact (hBmeas q i j).comp <|
        measurable_fst.comp
          (paperIndicatorNonfreshFreshSplitMeasurableEquiv
            N d start hsize).measurable
  have hComp : fullLog ∘ assemble =
      realAdaptedFreshCellLog N d profile center z start B := by
    funext sample
    dsimp only [fullLog, assemble, realFullFlatAdaptedFreshCellLog,
      realAdaptedFreshCellLog, Function.comp_apply]
    rw [paperIndicatorNonfreshFreshSplit_assemble_nonfresh]
    rw [paperIndicatorFreshAtomsOfReal_assembleNonfreshWithFreshFull_adapter]
  have hPull : Integrable (fullLog ∘ assemble) (muOutside.prod muFull) := by
    rw [hComp]
    simpa only [muOutside, muFull, nu] using hJoint.1
  have hFullInt : Integrable fullLog muFull :=
    (he.integrable_comp hFullMeas.aestronglyMeasurable).mp hPull
  have hPressureEq :
      realAdaptedFreshCellPressure
          muOutside N d profile center z start B f =
        realFullFlatAdaptedFreshCellPressure
          N d start hsize profile center z B f := by
    have hIntegral := integral_comp_of_measurePreserving he fullLog hFullInt
    have hJointIntegral :
        (∫ sample, realAdaptedFreshCellLog
            N d profile center z start B sample ∂(muOutside.prod muFull)) =
          ∫ omega, fullLog omega ∂muFull := by
      calc
        (∫ sample, realAdaptedFreshCellLog
            N d profile center z start B sample ∂(muOutside.prod muFull)) =
            ∫ sample, fullLog (assemble sample) ∂(muOutside.prod muFull) := by
              apply integral_congr_ae
              filter_upwards with sample
              exact (congrFun hComp sample).symm
        _ = ∫ omega, fullLog omega ∂muFull := hIntegral
    simpa only [realAdaptedFreshCellPressure,
      realFullFlatAdaptedFreshCellPressure, fullLog, muOutside, muFull, nu] using
        hJointIntegral
  refine ⟨by simpa only [fullLog, muFull, nu] using hFullInt, ?_⟩
  simpa only [muOutside, nu, hPressureEq] using hJoint.2

/-! ## Finite adapted-cell telescopes -/

/-- A finite sequence of complex cells with past-dependent frozen families telescopes
with the exact sum of the literal Section 4 cell errors.  The first conjunct records
the automatically derived integrability of every used cell observable. -/
theorem complex_adaptedFreshCell_cumulative_telescope
    {Past : Type u} [MeasurableSpace Past]
    (muPast : Measure Past) [IsProbabilityMeasure muPast]
    (N d : Nat) [NeZero N] (hsize : d + 1 <= N)
    {c0 C0 : Real} (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0) (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex) (start : ZMod N)
    (B : Nat -> Past -> (q : ExteriorDegree (d + 1)) ->
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex)
    (hBpos : forall j a, 0 < exteriorFamilyMaxL2OpNorm (B j a))
    (hBmeas : forall j q i k, Measurable (fun a => B j a q i k))
    (hBnorm : forall j q, Measurable (fun a => ‖B j a q‖))
    (hbaseInt : forall j, Integrable
      (fun a => Real.log (exteriorFamilyMaxL2OpNorm (B j a))) muPast)
    (f : Complex -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ w : Complex ∂(volume : Measure Complex), f w <= ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Complex => ‖u‖ ^ 2)
      (volume.withDensity f))
    (hsecond : (∫ u : Complex, ‖u‖ ^ 2 ∂(volume.withDensity f)) <= 1)
    (cellCount : Nat) :
    (∀ j, j < cellCount →
      Integrable (complexAdaptedFreshCellLog N d profile center z start (B j))
        (muPast.prod (paperIndicatorSampleMeasure N d (volume.withDensity f)))) /\
    (∑ j ∈ Finset.range cellCount,
        adaptedExteriorFamilyBasePressure muPast d (B j)) -
          (cellCount : Real) * complexIidFreshCellError d c0 L z <=
      cumulativeIidFreshCellPressure
        (fun j => complexAdaptedFreshCellPressure
          muPast N d profile center z start (B j) f) cellCount /\
    cumulativeIidFreshCellPressure
        (fun j => complexAdaptedFreshCellPressure
          muPast N d profile center z start (B j) f) cellCount <=
      (∑ j ∈ Finset.range cellCount,
        adaptedExteriorFamilyBasePressure muPast d (B j)) +
          (cellCount : Real) * complexIidFreshCellError d c0 L z := by
  have hCell (j : Nat) :=
    complex_adaptedFreshCell_integrable_and_pressure_bounds
      muPast N d hsize profile hc0 hsqrt center z start (B j)
        (hBpos j) (hBmeas j) (hBnorm j) (hbaseInt j)
        f hL hf hsecondInt hsecond
  refine ⟨fun j _ => (hCell j).1, ?_⟩
  have hTel := iidFreshCell_telescope_sum_bounds
    (cumulativeIidFreshCellPressure
      (fun j => complexAdaptedFreshCellPressure
        muPast N d profile center z start (B j) f))
    (fun j => adaptedExteriorFamilyBasePressure muPast d (B j))
    (fun _ => complexIidFreshCellError d c0 L z) cellCount rfl
    (fun j _ => by
      simpa only [cumulativeIidFreshCellPressure_succ, add_sub_cancel_left] using
        (hCell j).2)
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_ofNat] using hTel

/-- Real-law finite adapted-cell telescope, again with no cell bound among its
hypotheses. -/
theorem real_adaptedFreshCell_cumulative_telescope
    {Past : Type u} [MeasurableSpace Past]
    (muPast : Measure Past) [IsProbabilityMeasure muPast]
    (N d : Nat) [NeZero N] (hsize : d + 1 <= N)
    {c0 C0 : Real} (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0) (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex) (start : ZMod N)
    (B : Nat -> Past -> (q : ExteriorDegree (d + 1)) ->
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex)
    (hBpos : forall j a, 0 < exteriorFamilyMaxL2OpNorm (B j a))
    (hBmeas : forall j q i k, Measurable (fun a => B j a q i k))
    (hBnorm : forall j q, Measurable (fun a => ‖B j a q‖))
    (hbaseInt : forall j, Integrable
      (fun a => Real.log (exteriorFamilyMaxL2OpNorm (B j a))) muPast)
    (f : Real -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ x : Real ∂(volume : Measure Real), f x <= ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Real => u ^ 2) (volume.withDensity f))
    (hsecond : (∫ u : Real, u ^ 2 ∂(volume.withDensity f)) <= 1)
    (cellCount : Nat) :
    (∀ j, j < cellCount →
      Integrable (realAdaptedFreshCellLog N d profile center z start (B j))
        (muPast.prod (paperIndicatorRealSampleMeasure N d (volume.withDensity f)))) /\
    (∑ j ∈ Finset.range cellCount,
        adaptedExteriorFamilyBasePressure muPast d (B j)) -
          (cellCount : Real) * realIidFreshCellError d c0 L z <=
      cumulativeIidFreshCellPressure
        (fun j => realAdaptedFreshCellPressure
          muPast N d profile center z start (B j) f) cellCount /\
    cumulativeIidFreshCellPressure
        (fun j => realAdaptedFreshCellPressure
          muPast N d profile center z start (B j) f) cellCount <=
      (∑ j ∈ Finset.range cellCount,
        adaptedExteriorFamilyBasePressure muPast d (B j)) +
          (cellCount : Real) * realIidFreshCellError d c0 L z := by
  have hCell (j : Nat) :=
    real_adaptedFreshCell_integrable_and_pressure_bounds
      muPast N d hsize profile hc0 hsqrt center z start (B j)
        (hBpos j) (hBmeas j) (hBnorm j) (hbaseInt j)
        f hL hf hsecondInt hsecond
  refine ⟨fun j _ => (hCell j).1, ?_⟩
  have hTel := iidFreshCell_telescope_sum_bounds
    (cumulativeIidFreshCellPressure
      (fun j => realAdaptedFreshCellPressure
        muPast N d profile center z start (B j) f))
    (fun j => adaptedExteriorFamilyBasePressure muPast d (B j))
    (fun _ => realIidFreshCellError d c0 L z) cellCount rfl
    (fun j _ => by
      simpa only [cumulativeIidFreshCellPressure_succ, add_sub_cancel_left] using
        (hCell j).2)
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_ofNat] using hTel

end CircularLawSections56.Section5
