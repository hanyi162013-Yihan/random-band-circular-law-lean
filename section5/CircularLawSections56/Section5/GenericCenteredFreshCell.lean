import CircularLawSections56.Section5.LiteralCenteredMesoscopicTelescope

/-! # Distribution-independent centered fresh-cell receiver

The projective deficit and fresh log integrability are finite analytic inputs.
All Fubini, vector-log reconstruction, and random-outside centering steps are
proved here.  Real and tapered callers instantiate the inputs, rather than
assuming any asymptotic pressure or spectral conclusion.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1200000

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights Matrix

variable {d : Nat} {c0 C0 : Real}

theorem literalRandomOutsideExteriorCell_oneCellInputs_of_projective
    {Outside : Type*} [MeasurableSpace Outside]
    (muOutside : Measure Outside) [SigmaFinite muOutside]
    [IsProbabilityMeasure muOutside]
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex)
    (q : ExteriorDegree (d + 1))
    (B : Outside → Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) Complex)
    (hBmeas : ∀ i j, Measurable (fun b => B b i j))
    (hBnorm : Measurable (fun b => ‖B b‖))
    (hBunit : ∀ᵐ b ∂muOutside, IsUnit (B b))
    (hbaseInt : Integrable (fun b => Real.log ‖B b‖) muOutside)
    (nu : Measure Complex) [IsProbabilityMeasure nu] (loss : Real)
    (hFreshLogInt : Integrable
      (fun omega => Real.log ‖literalPaperExteriorCell profile center z q omega‖)
      (literalPaperExteriorCellMeasure d nu))
    (hProjective : ∀ B : Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) Complex,
      0 < ‖B‖ → ∀ v : EuclideanSpace Complex (ExteriorIndex (d + 1) q), ‖v‖ = 1 →
      Integrable (fun omega => logDeficit ‖B‖
        ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
          ((literalPaperExteriorCellWithLeft profile center z q B omega).mulVec (fun j => v j))‖)
        (literalPaperExteriorCellMeasure d nu) ∧
      (∫ omega, logDeficit ‖B‖
        ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) Complex).symm
          ((literalPaperExteriorCellWithLeft profile center z q B omega).mulVec (fun j => v j))‖
        ∂literalPaperExteriorCellMeasure d nu) ≤ loss)
    (hFactorUnits : ∀ᵐ sample ∂muOutside.prod
      (literalPaperExteriorCellMeasure d nu),
      IsUnit (B sample.1) ∧
        IsUnit (literalPaperExteriorCell profile center z q sample.2))
    (hCellLogInt : Integrable
      (fun sample : Outside × LiteralPaperCellAtoms d =>
        Real.log ‖literalRandomOutsideExteriorCell profile center z q B sample‖)
      (muOutside.prod
        (literalPaperExteriorCellMeasure d nu))) :
    let muFresh := literalPaperExteriorCellMeasure d nu
    let muCell := muOutside.prod muFresh
    let C := literalRandomOutsideExteriorCell profile center z q B
    let base := ∫ b, Real.log ‖B b‖ ∂muOutside
    let freshPressure := ∫ omega,
      Real.log ‖literalPaperExteriorCell profile center z q omega‖ ∂muFresh
    let error := max loss freshPressure
    (∀ v : EuclideanSpace Complex (ExteriorIndex (d + 1) q), ‖v‖ = 1 →
      Integrable (fun sample => matrixCellVectorLog C sample v) muCell ∧
        base - error ≤ ∫ sample, matrixCellVectorLog C sample v ∂muCell) ∧
    (Integrable (fun sample => Real.log ‖C sample‖) muCell ∧
      (∫ sample, Real.log ‖C sample‖ ∂muCell) ≤ base + error) ∧
    (∀ᵐ sample ∂muCell, IsUnit (C sample)) := by
  classical
  let muFresh := literalPaperExteriorCellMeasure d nu
  let muCell := muOutside.prod muFresh
  let Q := literalPaperExteriorCell profile center z q
  let C := literalRandomOutsideExteriorCell profile center z q B
  let base := ∫ b, Real.log ‖B b‖ ∂muOutside
  let freshPressure := ∫ omega, Real.log ‖Q omega‖ ∂muFresh
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
  have hQlog : Integrable (fun omega => Real.log ‖Q omega‖) muFresh := hFreshLogInt
  have hFactorUnits' : ∀ᵐ sample ∂muCell,
      IsUnit (B sample.1) ∧ IsUnit (Q sample.2) := by
    simpa only [muCell, muFresh, Q] using hFactorUnits
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
      have hfixed := hProjective (B b) (norm_pos_iff.mpr hb.ne_zero) v hv
      simpa only [D, radius, C, literalRandomOutsideExteriorCell, muFresh] using hfixed
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

end CircularLawSections56.Section5
