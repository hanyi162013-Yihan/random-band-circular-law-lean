import CircularLawSections56.Section5.LiteralCenteredMatrixCellAdapter
import CircularLawSections56.Section5.LiteralIidCellInvertibilityAdapter
import CircularLawSections56.Section5.LiteralGlobalIntegrabilityAdapter

/-!
# Centered mesoscopic matrix-cell telescope

This file averages the genuine fixed-outside `B * Q` cell over a random outside
matrix, then feeds the resulting centered one-cell bounds to the AE chronological
matrix-product telescope.  The center is the actual outside pressure
`∫ log ‖B‖`; the fresh/projective losses are the only error terms.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

set_option maxHeartbeats 1600000

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights Matrix Set

variable {d : Nat} {c0 C0 : Real}

local instance literalCenteredFreshMeasureSigmaFinite
    (d : Nat) (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    SigmaFinite (literalPaperExteriorCellMeasure d nu) := by
  unfold literalPaperExteriorCellMeasure
  infer_instance

local instance literalCenteredFreshMeasureProbability
    (d : Nat) (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (literalPaperExteriorCellMeasure d nu) := by
  unfold literalPaperExteriorCellMeasure
  infer_instance

/-- Product-Fubini helper with hypotheses only almost everywhere in the outer
variable.  This is the form needed when the random outside product is invertible
almost surely rather than pointwise. -/
theorem integrable_prod_and_integral_le_of_ae_integrable_integral_le
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    (mu : Measure Alpha) (nu : Measure Beta)
    [SFinite mu] [SFinite nu]
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (F : Alpha × Beta → ℝ) (hF : Measurable F)
    (hF0 : ∀ z, 0 ≤ F z) (bound : ℝ)
    (hsectionInt : ∀ᵐ x ∂mu, Integrable (fun y => F (x, y)) nu)
    (hsectionBound : ∀ᵐ x ∂mu, ∫ y, F (x, y) ∂nu ≤ bound) :
    Integrable F (mu.prod nu) ∧ ∫ z, F z ∂(mu.prod nu) ≤ bound := by
  let G : Alpha → ℝ := fun x => ∫ y, ‖F (x, y)‖ ∂nu
  have hGstrong : StronglyMeasurable G :=
    hF.norm.stronglyMeasurable.integral_prod_right'
  have hGle : ∀ᵐ x ∂mu, G x ≤ bound := by
    filter_upwards [hsectionBound] with x hx
    have hnorm : (fun y => ‖F (x, y)‖) = fun y => F (x, y) := by
      funext y
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 (x, y))]
    simpa only [G, hnorm] using hx
  have hGnonneg : ∀ x, 0 ≤ G x := fun x => integral_nonneg fun y => norm_nonneg _
  have hGint : Integrable G mu := by
    apply (integrable_const bound).mono' hGstrong.aestronglyMeasurable
    filter_upwards [hGle] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hGnonneg x)]
    exact hx
  have hFint : Integrable F (mu.prod nu) :=
    (integrable_prod_iff hF.aestronglyMeasurable).2 ⟨hsectionInt, hGint⟩
  refine ⟨hFint, ?_⟩
  rw [integral_prod F hFint]
  calc
    (∫ x, ∫ y, F (x, y) ∂nu ∂mu) ≤ ∫ _x : Alpha, bound ∂mu :=
      integral_mono_ae hFint.integral_prod_left (integrable_const bound)
        hsectionBound
    _ = bound := by simp

/-- A random outside matrix followed by the literal fresh exterior product. -/
def literalRandomOutsideExteriorCell
    {Outside : Type*}
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (B : Outside → Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) Complex) :
    Outside × LiteralPaperCellAtoms d →
      Matrix (ExteriorIndex (d + 1) q)
        (ExteriorIndex (d + 1) q) Complex :=
  fun sample => literalPaperExteriorCellWithLeft
    profile center z q (B sample.1) sample.2

/-- Coordinate measurability of the genuine random `B * Q` cell. -/
theorem measurable_literalRandomOutsideExteriorCell_apply
    {Outside : Type*} [MeasurableSpace Outside]
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (B : Outside → Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) Complex)
    (hBmeas : ∀ i j, Measurable (fun b => B b i j))
    (i j : ExteriorIndex (d + 1) q) :
    Measurable (fun sample : Outside × LiteralPaperCellAtoms d =>
      literalRandomOutsideExteriorCell profile center z q B sample i j) := by
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
  simp only [literalRandomOutsideExteriorCell,
    literalPaperExteriorCellWithLeft, Matrix.mul_apply]
  exact Finset.measurable_sum Finset.univ fun k _ =>
    ((hBmeas i k).comp measurable_fst).mul
      (((continuous_apply j).comp ((continuous_apply k).comp hQ)).measurable.comp
        measurable_snd)

/-- Measurability of the random centered action radius. -/
theorem measurable_literalRandomOutsideExteriorCell_vectorNorm
    {Outside : Type*} [MeasurableSpace Outside]
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (B : Outside → Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) Complex)
    (hBmeas : ∀ i j, Measurable (fun b => B b i j))
    (v : EuclideanSpace Complex (ExteriorIndex (d + 1) q)) :
    Measurable (fun sample : Outside × LiteralPaperCellAtoms d =>
      ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
        ((literalRandomOutsideExteriorCell profile center z q B sample).mulVec
          (fun j => v j))‖) := by
  apply Measurable.norm
  apply (EuclideanSpace.equiv
    (ExteriorIndex (d + 1) q) Complex).symm.continuous.measurable.comp
  apply measurable_pi_lambda
  intro i
  simp only [Matrix.mulVec]
  exact Finset.measurable_sum Finset.univ fun j _ =>
    (measurable_literalRandomOutsideExteriorCell_apply
      profile center z q B hBmeas i j).mul measurable_const

/-- The outside and fresh factors are jointly units almost surely.  Projection of AE
events is performed through the two measure-preserving coordinate maps, avoiding any
pointwise invertibility strengthening. -/
theorem ae_literalRandomOutsideExteriorCell_factorUnits
    {Outside : Type*} [MeasurableSpace Outside]
    (muOutside : Measure Outside) [SigmaFinite muOutside]
    [IsProbabilityMeasure muOutside]
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (B : Outside → Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) Complex)
    (hBunit : ∀ᵐ b ∂muOutside, IsUnit (B b))
    (f : Complex → ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real}
    (hf : ∀ᵐ w ∂(volume : Measure Complex), f w ≤ ENNReal.ofReal L) :
    ∀ᵐ sample ∂muOutside.prod
      (literalPaperExteriorCellMeasure d (volume.withDensity f)),
      IsUnit (B sample.1) ∧
        IsUnit (literalPaperExteriorCell profile center z q sample.2) := by
  let muFresh := literalPaperExteriorCellMeasure d (volume.withDensity f)
  have hQ : ∀ᵐ omega ∂muFresh,
      IsUnit (literalPaperExteriorCell profile center z q omega) := by
    simpa only [muFresh] using
      (ae_literalPaperExteriorCell_isUnit_complex_withDensity
        (d := d) (c0 := c0) (C0 := C0)
        profile hc0 center hcenter z q
        (f := f) (L := ENNReal.ofReal L) hf)
  have hb : ∀ᵐ sample : Outside × LiteralPaperCellAtoms d
      ∂muOutside.prod muFresh, IsUnit (B sample.1) :=
    measurePreserving_fst.quasiMeasurePreserving.ae hBunit
  have hq : ∀ᵐ sample : Outside × LiteralPaperCellAtoms d
      ∂muOutside.prod muFresh,
      IsUnit (literalPaperExteriorCell profile center z q sample.2) :=
    measurePreserving_snd.quasiMeasurePreserving.ae hQ
  filter_upwards [hb, hq] with sample hb hq
  exact ⟨hb, hq⟩

/-- Random-outside one-cell inputs centered at the genuine outside pressure.

For an actual mesoscopic open-row cell, the global log-norm integrability premise can
be supplied by exact row reassembly and Section 4's open-pressure `L²` theorem; it
remains an explicit premise of the generic theorem here.
Everything specific to the directional lower bound is derived here from the fixed-`B`
theorem and Fubini. -/
theorem complex_literalRandomOutsideExteriorCell_oneCellInputs
    {Outside : Type*} [MeasurableSpace Outside]
    (muOutside : Measure Outside) [SigmaFinite muOutside]
    [IsProbabilityMeasure muOutside]
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (B : Outside → Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) Complex)
    (hBmeas : ∀ i j, Measurable (fun b => B b i j))
    (hBnorm : Measurable (fun b => ‖B b‖))
    (hBunit : ∀ᵐ b ∂muOutside, IsUnit (B b))
    (hbaseInt : Integrable (fun b => Real.log ‖B b‖) muOutside)
    (f : Complex → ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 ≤ L)
    (hf : ∀ᵐ w ∂(volume : Measure Complex), f w ≤ ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Complex => ‖u‖ ^ 2)
      (volume.withDensity f))
    (hsecond : ∫ u : Complex, ‖u‖ ^ 2 ∂(volume.withDensity f) ≤ 1)
    (hFactorUnits : ∀ᵐ sample ∂muOutside.prod
      (literalPaperExteriorCellMeasure d (volume.withDensity f)),
      IsUnit (B sample.1) ∧
        IsUnit (literalPaperExteriorCell profile center z q sample.2))
    (hCellLogInt : Integrable
      (fun sample : Outside × LiteralPaperCellAtoms d =>
        Real.log ‖literalRandomOutsideExteriorCell profile center z q B sample‖)
      (muOutside.prod
        (literalPaperExteriorCellMeasure d (volume.withDensity f)))) :
    let muFresh := literalPaperExteriorCellMeasure d (volume.withDensity f)
    let muCell := muOutside.prod muFresh
    let C := literalRandomOutsideExteriorCell profile center z q B
    let base := ∫ b, Real.log ‖B b‖ ∂muOutside
    let freshPressure := ∫ omega,
      Real.log ‖literalPaperExteriorCell profile center z q omega‖ ∂muFresh
    let error := max (complexLiteralProjectiveCellLoss d c0 L q) freshPressure
    (∀ v : EuclideanSpace Complex (ExteriorIndex (d + 1) q), ‖v‖ = 1 →
      Integrable (fun sample => matrixCellVectorLog C sample v) muCell ∧
        base - error ≤ ∫ sample, matrixCellVectorLog C sample v ∂muCell) ∧
    (Integrable (fun sample => Real.log ‖C sample‖) muCell ∧
      (∫ sample, Real.log ‖C sample‖ ∂muCell) ≤ base + error) ∧
    (∀ᵐ sample ∂muCell, IsUnit (C sample)) := by
  classical
  let nu : Measure Complex := volume.withDensity f
  let muFresh := literalPaperExteriorCellMeasure d nu
  let muCell := muOutside.prod muFresh
  let Q := literalPaperExteriorCell profile center z q
  let C := literalRandomOutsideExteriorCell profile center z q B
  let base := ∫ b, Real.log ‖B b‖ ∂muOutside
  let freshPressure := ∫ omega, Real.log ‖Q omega‖ ∂muFresh
  let loss := complexLiteralProjectiveCellLoss d c0 L q
  let error := max loss freshPressure
  let _ : SigmaFinite nu := inferInstance
  let _ : SigmaFinite muFresh := by
    dsimp only [muFresh, literalPaperExteriorCellMeasure]
    infer_instance
  let _ : IsProbabilityMeasure muFresh := by
    dsimp only [muFresh, literalPaperExteriorCellMeasure]
    infer_instance
  let _ : IsProbabilityMeasure muCell := by
    dsimp only [muCell]
    infer_instance
  let _ : Nonempty (ExteriorIndex (d + 1) q) :=
    exteriorIndex_nonempty (d + 1) q
  have hQlog : Integrable (fun omega => Real.log ‖Q omega‖) muFresh := by
    simpa only [Q, muFresh, nu] using
      (complex_literalPaperExteriorCell_logOpNorm_integrable
        (d := d) (c0 := c0) (C0 := C0) (L := L)
        nu (complexBallBound_withDensity hf) hL profile hc0 hsqrt
        center z q hsecondInt hsecond)
  have hFactorUnits' : ∀ᵐ sample ∂muCell,
      IsUnit (B sample.1) ∧ IsUnit (Q sample.2) := by
    simpa only [muCell, muFresh, nu, Q] using hFactorUnits
  have hCellUnit : ∀ᵐ sample ∂muCell, IsUnit (C sample) := by
    filter_upwards [hFactorUnits'] with sample hs
    exact hs.1.mul hs.2
  have hbaseLift : Integrable
      (fun sample : Outside × LiteralPaperCellAtoms d =>
        Real.log ‖B sample.1‖) muCell := by
    exact measurePreserving_fst.integrable_comp_of_integrable hbaseInt
  have hQlogLift : Integrable
      (fun sample : Outside × LiteralPaperCellAtoms d =>
        Real.log ‖Q sample.2‖) muCell := by
    exact measurePreserving_snd.integrable_comp_of_integrable hQlog
  have hbaseIntegral :
      (∫ sample : Outside × LiteralPaperCellAtoms d,
        Real.log ‖B sample.1‖ ∂muCell) = base := by
    rw [integral_prod _ hbaseLift]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, base]
  have hQIntegral :
      (∫ sample : Outside × LiteralPaperCellAtoms d,
        Real.log ‖Q sample.2‖ ∂muCell) = freshPressure := by
    rw [integral_prod _ hQlogLift]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
      freshPressure]
  have hOneLower : ∀ v : EuclideanSpace Complex (ExteriorIndex (d + 1) q),
      ‖v‖ = 1 →
      Integrable (fun sample => matrixCellVectorLog C sample v) muCell ∧
        base - error ≤ ∫ sample, matrixCellVectorLog C sample v ∂muCell := by
    intro v hv
    let radius := fun sample : Outside × LiteralPaperCellAtoms d =>
      ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
        ((C sample).mulVec fun j => v j)‖
    let D := fun sample : Outside × LiteralPaperCellAtoms d =>
      logDeficit ‖B sample.1‖ (radius sample)
    let E := fun sample : Outside × LiteralPaperCellAtoms d =>
      logExcess ‖B sample.1‖ (radius sample)
    let T := fun omega : LiteralPaperCellAtoms d => ‖Q omega‖
    have hradius : Measurable radius := by
      simpa only [radius, C] using
        measurable_literalRandomOutsideExteriorCell_vectorNorm
          profile center z q B hBmeas v
    have hDmeas : Measurable D := by
      unfold D logDeficit
      exact measurable_const.max
        ((Real.measurable_log.comp (hBnorm.comp measurable_fst)).sub
          (Real.measurable_log.comp hradius))
    have hEmeas : Measurable E := by
      unfold E logExcess
      exact measurable_const.max
        ((Real.measurable_log.comp hradius).sub
          (Real.measurable_log.comp (hBnorm.comp measurable_fst)))
    have hDsections : ∀ᵐ b ∂muOutside,
        Integrable (fun omega => D (b, omega)) muFresh ∧
          (∫ omega, D (b, omega) ∂muFresh) ≤ loss := by
      filter_upwards [hBunit] with b hb
      have hfixed :=
        complex_literalPaperExteriorCellWithLeft_vector_logDeficit
          profile hc0 center z q (B b) (norm_pos_iff.mpr hb.ne_zero)
          v hv f hL hf
      simpa only [D, radius, C, literalRandomOutsideExteriorCell,
        muFresh, nu, loss] using hfixed.2
    have hD := integrable_prod_and_integral_le_of_ae_integrable_integral_le
      muOutside muFresh D hDmeas (fun sample => logDeficit_nonneg _ _)
      loss (hDsections.mono fun _ h => h.1) (hDsections.mono fun _ h => h.2)
    have hEdom : ∀ᵐ sample ∂muCell, E sample ≤ |Real.log (T sample.2)| := by
      filter_upwards [hCellUnit, hFactorUnits'] with sample hcell hfactors
      have hB : 0 < ‖B sample.1‖ :=
        norm_pos_iff.mpr hfactors.1.ne_zero
      have hr : 0 < radius sample :=
        norm_euclidean_mulVec_pos_of_isUnit (C sample) v hv hcell
      have hT : 0 < T sample.2 := norm_pos_iff.mpr hfactors.2.ne_zero
      have hrle : radius sample ≤ ‖B sample.1‖ * T sample.2 := by
        have ha := (C sample).l2_opNorm_mulVec v
        have hm := Matrix.l2_opNorm_mul (B sample.1) (Q sample.2)
        calc
          radius sample ≤ ‖C sample‖ * ‖v‖ := ha
          _ = ‖C sample‖ := by rw [hv, mul_one]
          _ ≤ ‖B sample.1‖ * T sample.2 := by
            simpa only [C, literalRandomOutsideExteriorCell,
              literalPaperExteriorCellWithLeft, Q, T] using hm
      calc
        E sample ≤ max 0 (Real.log (T sample.2)) :=
          logExcess_le_max_zero_log_of_le_scale_mul hB hr hT hrle
        _ ≤ |Real.log (T sample.2)| :=
          max_le (abs_nonneg _) (le_abs_self _)
    have hEmajor : Integrable
        (fun sample : Outside × LiteralPaperCellAtoms d =>
          |Real.log (T sample.2)|) muCell := by
      simpa only [T, Q, Real.norm_eq_abs] using hQlogLift.abs
    have hEint : Integrable E muCell := by
      apply hEmajor.mono' hEmeas.aestronglyMeasurable
      filter_upwards [hEdom] with sample hs
      rw [Real.norm_eq_abs, abs_of_nonneg (logExcess_nonneg _ _)]
      exact hs
    have hidentity : (fun sample => matrixCellVectorLog C sample v) =
        (fun sample => Real.log ‖B sample.1‖ + E sample - D sample) := by
      funext sample
      change Real.log (radius sample) =
        Real.log ‖B sample.1‖ + E sample - D sample
      by_cases h : Real.log ‖B sample.1‖ ≤ Real.log (radius sample)
      · simp only [D, E, logDeficit, logExcess,
          max_eq_left (sub_nonpos.mpr h), max_eq_right (sub_nonneg.mpr h)]
        ring
      · have h' := le_of_not_ge h
        simp only [D, E, logDeficit, logExcess,
          max_eq_right (sub_nonneg.mpr h'), max_eq_left (sub_nonpos.mpr h')]
        ring
    have hXint : Integrable (fun sample => matrixCellVectorLog C sample v) muCell := by
      rw [hidentity]
      exact (hbaseLift.add hEint).sub hD.1
    refine ⟨hXint, ?_⟩
    have hE0 : 0 ≤ ∫ sample, E sample ∂muCell :=
      integral_nonneg fun sample => logExcess_nonneg _ _
    have hformula :
        (∫ sample, matrixCellVectorLog C sample v ∂muCell) =
          base + (∫ sample, E sample ∂muCell) -
            ∫ sample, D sample ∂muCell := by
      rw [hidentity]
      calc
        (∫ sample, Real.log ‖B sample.1‖ + E sample - D sample ∂muCell) =
            (∫ sample, Real.log ‖B sample.1‖ + E sample ∂muCell) -
              ∫ sample, D sample ∂muCell := by
          simpa only [Pi.add_apply, Pi.sub_apply] using
            integral_sub (hbaseLift.add hEint) hD.1
        _ = base + (∫ sample, E sample ∂muCell) -
              ∫ sample, D sample ∂muCell := by
          rw [show (∫ sample, Real.log ‖B sample.1‖ + E sample ∂muCell) =
              (∫ sample, Real.log ‖B sample.1‖ ∂muCell) +
                ∫ sample, E sample ∂muCell by
            simpa only [Pi.add_apply] using integral_add hbaseLift hEint]
          rw [hbaseIntegral]
    have hloss : loss ≤ error := le_max_left _ _
    rw [hformula]
    linarith [hD.2]
  have hUpperAE : ∀ᵐ sample ∂muCell,
      Real.log ‖C sample‖ ≤
        Real.log ‖B sample.1‖ + Real.log ‖Q sample.2‖ := by
    filter_upwards [hCellUnit, hFactorUnits'] with sample hcell hfactors
    have hbq : C sample = B sample.1 * Q sample.2 := rfl
    have hb : 0 < ‖B sample.1‖ := norm_pos_iff.mpr hfactors.1.ne_zero
    have hq : 0 < ‖Q sample.2‖ := norm_pos_iff.mpr hfactors.2.ne_zero
    have hc : 0 < ‖C sample‖ := norm_pos_iff.mpr hcell.ne_zero
    rw [← Real.log_mul hb.ne' hq.ne']
    exact (Real.log_le_log_iff hc (mul_pos hb hq)).2
      (by simpa only [hbq] using Matrix.l2_opNorm_mul (B sample.1) (Q sample.2))
  have hUpperInt := hbaseLift.add hQlogLift
  have hUpperBound : (∫ sample, Real.log ‖C sample‖ ∂muCell) ≤ base + error := by
    have hmono := integral_mono_ae hCellLogInt hUpperInt hUpperAE
    change (∫ sample, Real.log ‖C sample‖ ∂muCell) ≤
      ∫ sample, ((fun sample : Outside × LiteralPaperCellAtoms d =>
        Real.log ‖B sample.1‖) +
          fun sample : Outside × LiteralPaperCellAtoms d =>
            Real.log ‖Q sample.2‖)
          sample ∂muCell at hmono
    have hsum :
        (∫ sample, ((fun sample : Outside × LiteralPaperCellAtoms d =>
          Real.log ‖B sample.1‖) +
          fun sample : Outside × LiteralPaperCellAtoms d =>
            Real.log ‖Q sample.2‖) sample ∂muCell) =
        (∫ sample, Real.log ‖B sample.1‖ ∂muCell) +
          ∫ sample, Real.log ‖Q sample.2‖ ∂muCell := by
      exact integral_add hbaseLift hQlogLift
    rw [hsum, hbaseIntegral, hQIntegral] at hmono
    linarith [le_max_right loss freshPressure]
  exact ⟨hOneLower, ⟨hCellLogInt, hUpperBound⟩, hCellUnit⟩

/-- Genuine chronological `q`-cell telescope for random-outside `B * Q` cells.

The only global premise is integrability of the actual matrix-product potential;
for concrete open-row outside blocks this is supplied by row flattening and Section 4's
global open-pressure theorem. -/
theorem complex_literalRandomOutsideExteriorCell_expectedLog_telescope
    {Outside : Type*} [MeasurableSpace Outside]
    (muOutside : Measure Outside) [SigmaFinite muOutside]
    [IsProbabilityMeasure muOutside]
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (z : Complex)
    (degree : ExteriorDegree (d + 1))
    (B : Outside → Matrix (ExteriorIndex (d + 1) degree)
      (ExteriorIndex (d + 1) degree) Complex)
    (hBmeas : ∀ i j, Measurable (fun b => B b i j))
    (hBnorm : Measurable (fun b => ‖B b‖))
    (hBunit : ∀ᵐ b ∂muOutside, IsUnit (B b))
    (hbaseInt : Integrable (fun b => Real.log ‖B b‖) muOutside)
    (f : Complex → ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 ≤ L)
    (hf : ∀ᵐ w ∂(volume : Measure Complex), f w ≤ ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Complex => ‖u‖ ^ 2)
      (volume.withDensity f))
    (hsecond : ∫ u : Complex, ‖u‖ ^ 2 ∂(volume.withDensity f) ≤ 1)
    (hFactorUnits : ∀ᵐ sample ∂muOutside.prod
      (literalPaperExteriorCellMeasure d (volume.withDensity f)),
      IsUnit (B sample.1) ∧
        IsUnit (literalPaperExteriorCell profile center z degree sample.2))
    (hCellLogInt : Integrable
      (fun sample : Outside × LiteralPaperCellAtoms d =>
        Real.log ‖literalRandomOutsideExteriorCell
          profile center z degree B sample‖)
      (muOutside.prod
        (literalPaperExteriorCellMeasure d (volume.withDensity f))))
    (cellCount : Nat)
    (hGlobalInt : ∀ n, n ≤ cellCount → Integrable
      (iidMatrixCellLogPotential
        (literalRandomOutsideExteriorCell profile center z degree B))
      (iidMeasure
        (muOutside.prod
          (literalPaperExteriorCellMeasure d (volume.withDensity f))) n)) :
    let muFresh := literalPaperExteriorCellMeasure d (volume.withDensity f)
    let muCell := muOutside.prod muFresh
    let C := literalRandomOutsideExteriorCell profile center z degree B
    let base := ∫ b, Real.log ‖B b‖ ∂muOutside
    let freshPressure := ∫ omega,
      Real.log ‖literalPaperExteriorCell profile center z degree omega‖ ∂muFresh
    let error := max
      (complexLiteralProjectiveCellLoss d c0 L degree) freshPressure
    (cellCount : Real) * (base - error) ≤
        ∫ sample, iidMatrixCellLogPotential C sample ∂iidMeasure muCell cellCount ∧
      (∫ sample, iidMatrixCellLogPotential C sample ∂iidMeasure muCell cellCount) ≤
        (cellCount : Real) * (base + error) := by
  classical
  let muFresh := literalPaperExteriorCellMeasure d (volume.withDensity f)
  let muCell := muOutside.prod muFresh
  let C := literalRandomOutsideExteriorCell profile center z degree B
  let base := ∫ b, Real.log ‖B b‖ ∂muOutside
  let freshPressure := ∫ omega,
    Real.log ‖literalPaperExteriorCell profile center z degree omega‖ ∂muFresh
  let error := max
    (complexLiteralProjectiveCellLoss d c0 L degree) freshPressure
  let _ : SigmaFinite muFresh := by
    dsimp only [muFresh, literalPaperExteriorCellMeasure]
    infer_instance
  let _ : SigmaFinite muCell := by
    dsimp only [muCell]
    infer_instance
  let _ : IsProbabilityMeasure muCell := by
    dsimp only [muCell]
    infer_instance
  let _ : Nonempty (ExteriorIndex (d + 1) degree) :=
    exteriorIndex_nonempty (d + 1) degree
  have hOne := complex_literalRandomOutsideExteriorCell_oneCellInputs
    muOutside profile hc0 hsqrt center z degree B hBmeas hBnorm hBunit
      hbaseInt f hL hf hsecondInt hsecond hFactorUnits hCellLogInt
  have hTel := iidMatrixCellProduct_expectedLog_telescope_autoDirection_ae
    muCell C cellCount base error hOne.1 hOne.2.1 hOne.2.2
      (fun n hn => by simpa only [muCell, C] using hGlobalInt n hn)
  simpa only [muFresh, muCell, C, base, freshPressure, error] using hTel

/-- Public random-outside `B * Q` telescope with both factor-unit events generated
automatically from the outside AE hypothesis and the literal fresh invertibility
theorem. -/
theorem complex_literalRandomOutsideExteriorCell_expectedLog_telescope_autoUnits
    {Outside : Type*} [MeasurableSpace Outside]
    (muOutside : Measure Outside) [SigmaFinite muOutside]
    [IsProbabilityMeasure muOutside]
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : Complex)
    (degree : ExteriorDegree (d + 1))
    (B : Outside → Matrix (ExteriorIndex (d + 1) degree)
      (ExteriorIndex (d + 1) degree) Complex)
    (hBmeas : ∀ i j, Measurable (fun b => B b i j))
    (hBnorm : Measurable (fun b => ‖B b‖))
    (hBunit : ∀ᵐ b ∂muOutside, IsUnit (B b))
    (hbaseInt : Integrable (fun b => Real.log ‖B b‖) muOutside)
    (f : Complex → ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 ≤ L)
    (hf : ∀ᵐ w ∂(volume : Measure Complex), f w ≤ ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Complex => ‖u‖ ^ 2)
      (volume.withDensity f))
    (hsecond : ∫ u : Complex, ‖u‖ ^ 2 ∂(volume.withDensity f) ≤ 1)
    (hCellLogInt : Integrable
      (fun sample : Outside × LiteralPaperCellAtoms d =>
        Real.log ‖literalRandomOutsideExteriorCell
          profile center z degree B sample‖)
      (muOutside.prod
        (literalPaperExteriorCellMeasure d (volume.withDensity f))))
    (cellCount : Nat)
    (hGlobalInt : ∀ n, n ≤ cellCount → Integrable
      (iidMatrixCellLogPotential
        (literalRandomOutsideExteriorCell profile center z degree B))
      (iidMeasure
        (muOutside.prod
          (literalPaperExteriorCellMeasure d (volume.withDensity f))) n)) :
    let muFresh := literalPaperExteriorCellMeasure d (volume.withDensity f)
    let muCell := muOutside.prod muFresh
    let C := literalRandomOutsideExteriorCell profile center z degree B
    let base := ∫ b, Real.log ‖B b‖ ∂muOutside
    let freshPressure := ∫ omega,
      Real.log ‖literalPaperExteriorCell profile center z degree omega‖ ∂muFresh
    let error := max
      (complexLiteralProjectiveCellLoss d c0 L degree) freshPressure
    (cellCount : Real) * (base - error) ≤
        ∫ sample, iidMatrixCellLogPotential C sample ∂iidMeasure muCell cellCount ∧
      (∫ sample, iidMatrixCellLogPotential C sample ∂iidMeasure muCell cellCount) ≤
        (cellCount : Real) * (base + error) := by
  have hFactors := ae_literalRandomOutsideExteriorCell_factorUnits
    muOutside profile hc0 center hcenter z degree B hBunit f hf
  exact complex_literalRandomOutsideExteriorCell_expectedLog_telescope
    muOutside profile hc0 hsqrt center z degree B hBmeas hBnorm hBunit
      hbaseInt f hL hf hsecondInt hsecond hFactors hCellLogInt cellCount hGlobalInt

end CircularLawSections56.Section5
