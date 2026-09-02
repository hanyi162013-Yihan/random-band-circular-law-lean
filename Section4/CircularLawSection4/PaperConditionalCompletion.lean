import CircularLawSection4.PaperFreshClosureFull
import CircularLawSection4.PaperProjectiveConditional
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Completion of the conditional fresh-block and projective interfaces

This module closes two bookkeeping gaps left after the fiberwise Section 4
estimates.  First, the full one-fresh-block `L¹` estimate is transported to a
joint past/fresh product law and identified with the canonical conditional
expectation.  Second, finite second moments are used to prove the positive
logarithmic integrability of the actual projective vector, so the final
complex and real expectation lower bounds no longer require an external
`hexcess` hypothesis.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory Set

noncomputable section

namespace CircularLawSection4

open Matrix Set.powersetCard ProbabilityTheory

namespace PaperIndicatorWeights

variable {d : ℕ} {c₀ C₀ : ℝ}

/-- The actual projective vector is bounded by the operator norm, the input
vector norm, and the product of the genuine fresh-row majorants. -/
theorem norm_paperProjectiveFreshVector_le
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (I J : ExteriorIndex (d + 1) q) (x : Fin (d + 1) → ℂ) :
    ‖profile.paperProjectiveFreshVector center z atoms q B v I J x‖ ≤
      ‖B‖ * ‖v‖ *
        ∏ t : Fin (d + 1), profile.freshRowNormMajorant z
          (replaceSelectedFreshAtoms atoms (arbitrarySupportWord I J) x t) := by
  classical
  let replaced := replaceSelectedFreshAtoms atoms (arbitrarySupportWord I J) x
  let Q := chronologicalProduct
    (List.ofFn fun t : Fin (d + 1) =>
      profile.freshExteriorRow center z replaced q t)
  have hQ : ‖Q‖ ≤
      ∏ t : Fin (d + 1), profile.freshRowNormMajorant z (replaced t) := by
    letI : Nonempty (ExteriorIndex (d + 1) q) :=
      exteriorIndex_nonempty (d + 1) q
    calc
      ‖Q‖ ≤ (List.ofFn fun t : Fin (d + 1) =>
          ‖profile.freshExteriorRow center z replaced q t‖).prod := by
        simpa only [Q, List.map_ofFn, Function.comp_def] using
          norm_chronologicalProduct_le_prod
            (List.ofFn fun t : Fin (d + 1) =>
              profile.freshExteriorRow center z replaced q t)
      _ ≤ (List.ofFn fun t : Fin (d + 1) =>
          profile.freshRowNormMajorant z (replaced t)).prod := by
        simp only [List.prod_ofFn]
        exact Finset.prod_le_prod
          (fun t _ => norm_nonneg
            (profile.freshExteriorRow center z replaced q t))
          (fun t _ => profile.norm_freshExteriorRow_le_freshRowNormMajorant
            center z replaced q t)
      _ = ∏ t : Fin (d + 1),
          profile.freshRowNormMajorant z (replaced t) := by
        rw [List.prod_ofFn]
  rw [paperProjectiveFreshVector]
  change ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) ℂ).symm
      ((B * Q).mulVec (fun j => v j))‖ ≤ _
  calc
    ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) ℂ).symm
        ((B * Q).mulVec (fun j => v j))‖
        ≤ ‖B * Q‖ * ‖v‖ := (B * Q).l2_opNorm_mulVec v
    _ ≤ (‖B‖ * ‖Q‖) * ‖v‖ := by
      gcongr
      exact Matrix.l2_opNorm_mul B Q
    _ ≤ (‖B‖ * (∏ t : Fin (d + 1),
          profile.freshRowNormMajorant z (replaced t))) * ‖v‖ := by
      gcongr
    _ = ‖B‖ * ‖v‖ *
        ∏ t : Fin (d + 1), profile.freshRowNormMajorant z
          (replaceSelectedFreshAtoms atoms (arbitrarySupportWord I J) x t) := by
      simp only [replaced]
      ring

/-- Positive-log closure for the actual projective vector.  This is the
projective analogue of
`integrable_and_integral_paperIndicatorFreshZ_logExcess_le`; its input is
exactly a scaled second-moment bound for the selected-coordinate row sums. -/
theorem integrable_and_integral_paperProjectiveFreshVector_logExcess_le
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < ‖B‖)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q)) (hv : ‖v‖ = 1)
    (I J : ExteriorIndex (d + 1) q)
    (selected : Omega → Fin (d + 1) → ℂ)
    (hselected : Measurable selected)
    (hRpos : ∀ᵐ omega ∂mu,
      0 < ‖profile.paperProjectiveFreshVector center z atoms q B v I J
        (selected omega)‖)
    (rowScale V : ℝ) (hrowScale : 1 ≤ rowScale) (hV : 0 ≤ V)
    (hscaledInt : ∀ t : Fin (d + 1), Integrable (fun omega =>
      (profile.freshRowAtomSum
        (replaceSelectedFreshAtoms atoms (arbitrarySupportWord I J)
          (selected omega) t) / rowScale) ^ 2) mu)
    (hscaled : ∀ t : Fin (d + 1),
      ∫ omega, (profile.freshRowAtomSum
        (replaceSelectedFreshAtoms atoms (arbitrarySupportWord I J)
          (selected omega) t) / rowScale) ^ 2 ∂mu ≤ V) :
    Integrable (fun omega => logExcess ‖B‖
        ‖profile.paperProjectiveFreshVector center z atoms q B v I J
          (selected omega)‖) mu ∧
      ∫ omega, logExcess ‖B‖
          ‖profile.paperProjectiveFreshVector center z atoms q B v I J
            (selected omega)‖ ∂mu ≤
        (d + 1 : ℝ) * Real.sqrt
          (3 * (Real.log rowScale) ^ 2 + 3 * V + 3 * ‖z‖ ^ 2) := by
  classical
  let rowAtoms := fun omega t =>
    replaceSelectedFreshAtoms atoms (arbitrarySupportWord I J)
      (selected omega) t
  let C : ℝ := 3 * (Real.log rowScale) ^ 2 + 3 * V + 3 * ‖z‖ ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hSmeas : ∀ t : Fin (d + 1), Measurable (fun omega =>
      profile.freshRowAtomSum (rowAtoms omega t)) := by
    intro t
    unfold freshRowAtomSum rowAtoms replaceSelectedFreshAtoms
    apply Finset.measurable_sum
    intro ell _
    apply measurable_const.mul
    apply Measurable.norm
    split_ifs
    · exact (measurable_pi_apply t).comp hselected
    · exact measurable_const
  have hrowSq : ∀ t : Fin (d + 1),
      Integrable (fun omega =>
          (Real.posLog (profile.freshRowNormMajorant z
            (rowAtoms omega t))) ^ 2) mu ∧
        ∫ omega, (Real.posLog (profile.freshRowNormMajorant z
            (rowAtoms omega t))) ^ 2 ∂mu ≤ C := by
    intro t
    simpa only [Real.posLog_apply, freshRowNormMajorant_eq, C, rowAtoms] using
      integrable_and_integral_positiveLogSquare_le_of_scaledSecondMoment
        mu (fun omega => profile.freshRowAtomSum (rowAtoms omega t))
        (hSmeas t)
        (fun omega => Finset.sum_nonneg fun _ _ =>
          mul_nonneg (norm_nonneg _) (norm_nonneg _))
        ‖z‖ rowScale V (norm_nonneg _) hrowScale
        (hscaledInt t) (hscaled t)
  have hrow : ∀ t : Fin (d + 1),
      Integrable (fun omega => Real.posLog
          (profile.freshRowNormMajorant z (rowAtoms omega t))) mu := by
    intro t
    let G := fun omega => Real.posLog
      (profile.freshRowNormMajorant z (rowAtoms omega t))
    have hGmeas : Measurable G := by
      dsimp [G]
      exact Real.continuous_posLog.measurable.comp
        ((hSmeas t).add measurable_const)
    exact (integrable_and_integral_le_sqrt_integral_sq_of_nonneg
      mu G hGmeas (fun _ => Real.posLog_nonneg) (hrowSq t).1).1
  let E := fun omega => logExcess ‖B‖
    ‖profile.paperProjectiveFreshVector center z atoms q B v I J
      (selected omega)‖
  let D := fun omega => ∑ t : Fin (d + 1),
    Real.posLog (profile.freshRowNormMajorant z (rowAtoms omega t))
  have hRmeas : Measurable (fun omega =>
      ‖profile.paperProjectiveFreshVector center z atoms q B v I J
        (selected omega)‖) :=
    (profile.continuous_paperProjectiveFreshVector
      center z atoms q B v I J).norm.measurable.comp hselected
  have hEmeas : Measurable E := measurable_logExcess _ hRmeas
  have hDint : Integrable D mu :=
    integrable_finsetSum Finset.univ fun t _ => hrow t
  have hpoint : E ≤ᵐ[mu] D := by
    filter_upwards [hRpos] with omega hpos
    let R := ‖profile.paperProjectiveFreshVector center z atoms q B v I J
      (selected omega)‖
    let T := ∏ t : Fin (d + 1),
      max 1 (profile.freshRowNormMajorant z (rowAtoms omega t))
    have hT : 0 < T := Finset.prod_pos fun _ _ =>
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hR : R ≤ ‖B‖ * T := by
      calc
        R ≤ ‖B‖ * ‖v‖ * ∏ t : Fin (d + 1),
            profile.freshRowNormMajorant z (rowAtoms omega t) := by
          simpa only [R, rowAtoms] using
            profile.norm_paperProjectiveFreshVector_le
              center z atoms q B v I J (selected omega)
        _ = ‖B‖ * ∏ t : Fin (d + 1),
            profile.freshRowNormMajorant z (rowAtoms omega t) := by rw [hv, mul_one]
        _ ≤ ‖B‖ * ∏ t : Fin (d + 1),
            max 1 (profile.freshRowNormMajorant z (rowAtoms omega t)) := by
          apply mul_le_mul_of_nonneg_left
          · exact Finset.prod_le_prod
              (fun t _ => profile.freshRowNormMajorant_nonneg z
                (rowAtoms omega t))
              (fun t _ => le_max_right _ _)
          · exact hB.le
        _ = ‖B‖ * T := rfl
    calc
      E omega ≤ Real.posLog T := by
        simpa only [E, R, Real.posLog_apply] using
          logExcess_le_max_zero_log_of_le_scale_mul hB hpos hT hR
      _ ≤ ∑ t : Fin (d + 1), Real.posLog
          (max 1 (profile.freshRowNormMajorant z (rowAtoms omega t))) := by
        simpa only [T] using Real.posLog_prod Finset.univ
          (fun t : Fin (d + 1) =>
            max 1 (profile.freshRowNormMajorant z (rowAtoms omega t)))
      _ = D omega := by
        dsimp [D]
        apply Finset.sum_congr rfl
        intro t _
        rw [Real.posLog_eq_log_max_one
          (profile.freshRowNormMajorant_nonneg z (rowAtoms omega t))]
        rw [Real.posLog_eq_log]
        rw [abs_of_nonneg (zero_le_one.trans (le_max_left _ _))]
        exact le_max_left _ _
  have hEint : Integrable E mu := by
    apply hDint.mono' hEmeas.aestronglyMeasurable
    filter_upwards [hpoint] with omega homega
    rw [Real.norm_eq_abs, abs_of_nonneg (logExcess_nonneg _ _)]
    exact homega
  refine ⟨hEint, ?_⟩
  calc
    ∫ omega, E omega ∂mu ≤ ∫ omega, D omega ∂mu :=
      integral_mono_ae hEint hDint hpoint
    _ = ∑ t : Fin (d + 1), ∫ omega, Real.posLog
          (profile.freshRowNormMajorant z (rowAtoms omega t)) ∂mu := by
      rw [integral_finsetSum Finset.univ fun t _ => hrow t]
    _ ≤ ∑ _t : Fin (d + 1), Real.sqrt C := by
      gcongr with t
      exact (integrable_and_integral_le_sqrt_integral_sq_of_nonneg mu
        (fun omega => Real.posLog
          (profile.freshRowNormMajorant z (rowAtoms omega t)))
        (Real.continuous_posLog.measurable.comp
          ((hSmeas t).add measurable_const))
        (fun _ => Real.posLog_nonneg) (hrowSq t).1).2.trans
          (Real.sqrt_le_sqrt (hrowSq t).2)
    _ = (d + 1 : ℝ) * Real.sqrt C := by simp
    _ = (d + 1 : ℝ) * Real.sqrt
        (3 * (Real.log rowScale) ^ 2 + 3 * V + 3 * ‖z‖ ^ 2) := rfl

/-- A deterministic scale dominating every frozen atom.  The extra `1`
also makes division by this scale harmless. -/
noncomputable def paperProjectiveFrozenAtomScale
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ) : ℝ :=
  1 + ∑ t : Fin (d + 1), ∑ ell : ResetLabel (d + 1), ‖atoms t ell‖

theorem one_le_paperProjectiveFrozenAtomScale
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ) :
    1 ≤ paperProjectiveFrozenAtomScale atoms := by
  unfold paperProjectiveFrozenAtomScale
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem norm_atom_le_paperProjectiveFrozenAtomScale
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (t : Fin (d + 1)) (ell : ResetLabel (d + 1)) :
    ‖atoms t ell‖ ≤ paperProjectiveFrozenAtomScale atoms := by
  unfold paperProjectiveFrozenAtomScale
  have hrow : ‖atoms t ell‖ ≤
      ∑ j : ResetLabel (d + 1), ‖atoms t j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg (atoms t j))
      (Finset.mem_univ ell)
  have hall : (∑ j : ResetLabel (d + 1), ‖atoms t j‖) ≤
      ∑ s : Fin (d + 1), ∑ j : ResetLabel (d + 1), ‖atoms s j‖ :=
    Finset.single_le_sum
      (fun s _ => Finset.sum_nonneg fun j _ => norm_nonneg (atoms s j))
      (Finset.mem_univ t)
  linarith

/-- After division by the deterministic frozen-atom scale, every replaced
row has the same normalized second-moment estimate as a fully random row. -/
theorem replacedFreshRowAtomSum_scaledSecondMoment
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (word : Fin (d + 1) → ResetLabel (d + 1))
    (selected : Omega → Fin (d + 1) → ℂ)
    (hselected : Measurable selected)
    (hcoord : ∀ t : Fin (d + 1),
      Integrable (fun omega => ‖selected omega t‖ ^ 2) mu ∧
        ∫ omega, ‖selected omega t‖ ^ 2 ∂mu ≤ 1) :
    ∀ t : Fin (d + 1),
      Integrable (fun omega =>
        (profile.freshRowAtomSum
          (replaceSelectedFreshAtoms atoms word (selected omega) t) /
            ((d + 2 : ℝ) * paperProjectiveFrozenAtomScale atoms)) ^ 2) mu ∧
      ∫ omega, (profile.freshRowAtomSum
          (replaceSelectedFreshAtoms atoms word (selected omega) t) /
            ((d + 2 : ℝ) * paperProjectiveFrozenAtomScale atoms)) ^ 2
        ∂mu ≤ 1 := by
  classical
  intro t
  let K := paperProjectiveFrozenAtomScale atoms
  have hK : 1 ≤ K := one_le_paperProjectiveFrozenAtomScale atoms
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  let scaledAtoms := fun omega (ell : ResetLabel (d + 1)) =>
    replaceSelectedFreshAtoms atoms word (selected omega) t ell / (K : ℂ)
  have hscaledMeas : ∀ ell, Measurable (fun omega => scaledAtoms omega ell) := by
    intro ell
    dsimp [scaledAtoms, replaceSelectedFreshAtoms]
    split_ifs
    · exact ((measurable_pi_apply t).comp hselected).div_const (K : ℂ)
    · exact measurable_const
  have hscaledCoord : ∀ ell,
      Integrable (fun omega => ‖scaledAtoms omega ell‖ ^ 2) mu ∧
        ∫ omega, ‖scaledAtoms omega ell‖ ^ 2 ∂mu ≤ 1 := by
    intro ell
    by_cases hell : ell = word t
    · subst ell
      have hpoint : ∀ omega, ‖scaledAtoms omega (word t)‖ ^ 2 ≤
          ‖selected omega t‖ ^ 2 := by
        intro omega
        dsimp [scaledAtoms]
        rw [replaceSelectedFreshAtoms_selected, norm_div]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK0]
        have ha0 : 0 ≤ ‖selected omega t‖ := norm_nonneg _
        have hdiv0 : 0 ≤ ‖selected omega t‖ / K := div_nonneg ha0 hK0.le
        have hdivle : ‖selected omega t‖ / K ≤ ‖selected omega t‖ := by
          apply (div_le_iff₀ hK0).2
          nlinarith
        nlinarith [sq_nonneg (‖selected omega t‖ - ‖selected omega t‖ / K)]
      have hint : Integrable
          (fun omega => ‖scaledAtoms omega (word t)‖ ^ 2) mu := by
        have hm : Measurable
            (fun omega => ‖scaledAtoms omega (word t)‖ ^ 2) := by
          fun_prop
        refine (hcoord t).1.mono' hm.aestronglyMeasurable ?_
        filter_upwards with omega
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hpoint omega
      refine ⟨hint, (integral_mono hint (hcoord t).1 hpoint).trans (hcoord t).2⟩
    · have hconst : ∀ omega, scaledAtoms omega ell = atoms t ell / (K : ℂ) := by
        intro omega
        dsimp [scaledAtoms, replaceSelectedFreshAtoms]
        simp [hell]
      have hvalue : ‖atoms t ell / (K : ℂ)‖ ^ 2 ≤ 1 := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK0]
        have hatom := norm_atom_le_paperProjectiveFrozenAtomScale atoms t ell
        have hratio0 : 0 ≤ ‖atoms t ell‖ / K :=
          div_nonneg (norm_nonneg _) hK0.le
        have hratio1 : ‖atoms t ell‖ / K ≤ 1 :=
          (div_le_one hK0).2 hatom
        nlinarith [sq_nonneg (1 - ‖atoms t ell‖ / K)]
      have hfun : (fun omega => ‖scaledAtoms omega ell‖ ^ 2) =
          (fun _ => ‖atoms t ell / (K : ℂ)‖ ^ 2) := by
        funext omega
        rw [hconst]
      rw [hfun]
      refine ⟨integrable_const _, ?_⟩
      simpa using hvalue
  obtain ⟨hint, hbound⟩ :=
    profile.integrable_freshRowAtomSum_div_sq_and_integral_le_one
      mu hc₀ scaledAtoms hscaledMeas hscaledCoord
  have heq : (fun omega =>
      (profile.freshRowAtomSum
        (replaceSelectedFreshAtoms atoms word (selected omega) t) /
          ((d + 2 : ℝ) * K)) ^ 2) =
      (fun omega =>
        (profile.freshRowAtomSum (scaledAtoms omega) / (d + 2 : ℝ)) ^ 2) := by
    funext omega
    unfold freshRowAtomSum scaledAtoms
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hK0, Finset.sum_div]
    field_simp [hK0.ne']
  rw [heq]
  exact ⟨hint, hbound⟩

/-! ## Projective expectation closure under the manuscript moment input -/

/-- Complex planar-density projective observability with the positive half
proved internally from the manuscript's normalized second moment. -/
theorem exists_paperProjectiveFreshVector_complex_integral_log_ge_withDensity_andSecondMoment
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < ‖B‖)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (hv : ‖v‖ = 1)
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2)
      (volume.withDensity f))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(volume.withDensity f) ≤ 1) :
    ∃ o I J : ExteriorIndex (d + 1) q,
      let radius := fun x : Fin (d + 1) → ℂ =>
        ‖profile.paperProjectiveFreshVector center z atoms q B v I J x‖
      iidMeasure (volume.withDensity f) (d + 1) {x | radius x = 0} = 0 ∧
        Integrable (fun x => Real.log (radius x))
          (iidMeasure (volume.withDensity f) (d + 1)) ∧
        Real.log ‖B‖ -
            (paperProjectiveCoefficientLogLoss d c₀ q +
              (Real.log
                  (max 1 (((d + 1 : ℕ) : ℝ) * (Real.pi * L))) + 1) /
                (((2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ))) ≤
          ∫ x, Real.log (radius x)
            ∂iidMeasure (volume.withDensity f) (d + 1) := by
  classical
  let mu := iidMeasure (volume.withDensity f) (d + 1)
  letI : IsProbabilityMeasure mu :=
    iidMeasure_isProbability (volume.withDensity f) (d + 1)
  obtain ⟨o, I, J, hzero, hdeficit, hbound⟩ :=
    profile.exists_paperProjectiveFreshVector_complex_logDeficit_withDensity
      hc₀ center z atoms q B hB v hv f hL hf
  let radius := fun x : Fin (d + 1) → ℂ =>
    ‖profile.paperProjectiveFreshVector center z atoms q B v I J x‖
  have hRpos : ∀ᵐ x ∂mu, 0 < radius x := by
    have hnotMem := measure_eq_zero_iff_ae_notMem.mp
      (by simpa only [mu, radius] using hzero)
    filter_upwards [hnotMem] with x hx
    have hne : radius x ≠ 0 := by
      simpa only [Set.mem_setOf_eq] using hx
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  have hcoord : ∀ t : Fin (d + 1),
      Integrable (fun x : Fin (d + 1) → ℂ => ‖x t‖ ^ 2) mu ∧
        ∫ x, ‖x t‖ ^ 2 ∂mu ≤ 1 := by
    intro t
    simpa only [mu] using
      iidMeasure_coordinate_norm_sq_integrable_and_integral_le_one
        t hsecondInt hsecond
  let rowScale := (d + 2 : ℝ) * paperProjectiveFrozenAtomScale atoms
  have hrowScale : 1 ≤ rowScale := by
    have hD : 1 ≤ (d + 2 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (d + 1))
    have hK := one_le_paperProjectiveFrozenAtomScale atoms
    dsimp only [rowScale]
    nlinarith [mul_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr hK)]
  have hscaled := profile.replacedFreshRowAtomSum_scaledSecondMoment
    mu hc₀ atoms (arbitrarySupportWord I J) (fun x => x) measurable_id hcoord
  obtain ⟨hexcess, _hexcessBound⟩ :=
    profile.integrable_and_integral_paperProjectiveFreshVector_logExcess_le
      mu center z atoms q B hB v hv I J (fun x => x) measurable_id
      (by simpa only [radius] using hRpos) rowScale 1 hrowScale zero_le_one
      (fun t => by simpa only [rowScale] using (hscaled t).1)
      (fun t => by simpa only [rowScale] using (hscaled t).2)
  refine ⟨o, I, J, hzero, ?_⟩
  exact integrable_log_and_integral_log_ge_of_logDeficit
    mu ‖B‖
    (paperProjectiveCoefficientLogLoss d c₀ q +
      (Real.log (max 1 (((d + 1 : ℕ) : ℝ) * (Real.pi * L))) + 1) /
        (((2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)))
    (by simpa only [mu, radius] using hdeficit)
    (by simpa only [mu, radius] using hexcess)
    (by simpa only [mu, radius] using hbound)

/-- Real interval-density projective observability with the positive half
proved internally from the normalized real second moment. -/
theorem exists_paperProjectiveFreshVector_real_integral_log_ge_of_intervalBound_andSecondMoment
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < ‖B‖)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (hv : ‖v‖ = 1)
    (nu : Measure ℝ) [SFinite nu] [IsProbabilityMeasure nu]
    {L : ℝ} (hL : 0 ≤ L)
    (hnu : RealIntervalBound nu (ENNReal.ofReal L))
    (hsecondInt : Integrable (fun u : ℝ => u ^ 2) nu)
    (hsecond : ∫ u : ℝ, u ^ 2 ∂nu ≤ 1) :
    ∃ o I J : ExteriorIndex (d + 1) q,
      let radius := fun x : Fin (d + 1) → ℝ =>
        ‖profile.paperProjectiveFreshVectorOfReal center z atoms q B v I J x‖
      iidMeasure nu (d + 1) {x | radius x = 0} = 0 ∧
        Integrable (fun x => Real.log (radius x)) (iidMeasure nu (d + 1)) ∧
        Real.log ‖B‖ -
            (paperProjectiveCoefficientLogLoss d c₀ q +
              (Real.log (max 1 (((d + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
                (((1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ))) ≤
          ∫ x, Real.log (radius x) ∂iidMeasure nu (d + 1) := by
  classical
  let mu := iidMeasure nu (d + 1)
  let selected := fun x : Fin (d + 1) → ℝ => fun t => (x t : ℂ)
  letI : IsProbabilityMeasure mu := iidMeasure_isProbability nu (d + 1)
  obtain ⟨o, I, J, hzero, hdeficit, hbound⟩ :=
    profile.exists_paperProjectiveFreshVector_real_logDeficit_of_intervalBound
      hc₀ center z atoms q B hB v hv nu hL hnu
  let radius := fun x : Fin (d + 1) → ℝ =>
    ‖profile.paperProjectiveFreshVectorOfReal center z atoms q B v I J x‖
  have hselected : Measurable selected := by
    apply measurable_pi_lambda
    intro t
    exact Complex.continuous_ofReal.measurable.comp (measurable_pi_apply t)
  have hRpos : ∀ᵐ x ∂mu, 0 < radius x := by
    have hnotMem := measure_eq_zero_iff_ae_notMem.mp
      (by simpa only [mu, radius] using hzero)
    filter_upwards [hnotMem] with x hx
    have hne : radius x ≠ 0 := by
      simpa only [Set.mem_setOf_eq] using hx
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  have hcoord : ∀ t : Fin (d + 1),
      Integrable (fun x : Fin (d + 1) → ℝ => ‖(selected x) t‖ ^ 2) mu ∧
        ∫ x, ‖(selected x) t‖ ^ 2 ∂mu ≤ 1 := by
    intro t
    simpa only [mu, selected] using
      iidMeasure_coordinate_complexifiedReal_norm_sq_integrable_and_integral_le_one
        t hsecondInt hsecond
  let rowScale := (d + 2 : ℝ) * paperProjectiveFrozenAtomScale atoms
  have hrowScale : 1 ≤ rowScale := by
    have hD : 1 ≤ (d + 2 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (d + 1))
    have hK := one_le_paperProjectiveFrozenAtomScale atoms
    dsimp only [rowScale]
    nlinarith [mul_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr hK)]
  have hscaled := profile.replacedFreshRowAtomSum_scaledSecondMoment
    mu hc₀ atoms (arbitrarySupportWord I J) selected hselected hcoord
  obtain ⟨hexcess, _hexcessBound⟩ :=
    profile.integrable_and_integral_paperProjectiveFreshVector_logExcess_le
      mu center z atoms q B hB v hv I J selected hselected
      (by simpa only [radius, paperProjectiveFreshVectorOfReal, selected] using hRpos)
      rowScale 1 hrowScale zero_le_one
      (fun t => by simpa only [rowScale] using (hscaled t).1)
      (fun t => by simpa only [rowScale] using (hscaled t).2)
  refine ⟨o, I, J, hzero, ?_⟩
  exact integrable_log_and_integral_log_ge_of_logDeficit
    mu ‖B‖
    (paperProjectiveCoefficientLogLoss d c₀ q +
      (Real.log (max 1 (((d + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
        (((1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)))
    (by simpa only [mu, radius] using hdeficit)
    (by simpa only [mu, radius, paperProjectiveFreshVectorOfReal, selected] using hexcess)
    (by simpa only [mu, radius] using hbound)

/-! ## Measurability with a past-dependent frozen operator -/

/-- Joint measurability of the actual alternating fresh trace when both the
fresh atoms and every entry of the frozen exterior family are measurable. -/
theorem measurable_norm_paperIndicatorFreshZ_of_measurable_family
    {Omega : Type*} [MeasurableSpace Omega]
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Omega → Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (hatoms : ∀ t ell, Measurable (fun omega => atoms omega t ell))
    (B : Omega → (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : ∀ q i j, Measurable (fun omega => B omega q i j)) :
    Measurable (fun omega =>
      ‖profile.paperIndicatorFreshZ center z (atoms omega) (B omega)‖) := by
  apply Measurable.norm
  unfold paperIndicatorFreshZ
  apply Finset.measurable_sum
  intro q _
  apply measurable_const.mul
  apply measurable_matrix_trace
  apply measurable_matrix_mul
  · exact hB q
  · have hp := measurable_chronologicalProduct
        (List.ofFn fun t : Fin (d + 1) => fun omega =>
          profile.freshExteriorRow center z (atoms omega) q t)
        (by
          intro A hA i j
          simp only [List.mem_ofFn] at hA
          obtain ⟨t, rfl⟩ := hA
          exact profile.measurable_freshExteriorRow_entry
            center z atoms hatoms q t i j)
    simpa only [List.map_ofFn, Function.comp_def] using hp

/-- Measurability of the natural exterior-family scale from measurability
of each degreewise operator norm.  The latter is the right interface for
the custom `L²` operator norm used here: entrywise measurability alone does
not provide an `OpensMeasurableSpace` instance for that matrix norm. -/
theorem measurable_exteriorFamilyMaxL2OpNorm
    {Omega : Type*} [MeasurableSpace Omega]
    (B : Omega → (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hBnorm : ∀ q, Measurable (fun omega => ‖B omega q‖)) :
    Measurable (fun omega => exteriorFamilyMaxL2OpNorm (B omega)) := by
  unfold exteriorFamilyMaxL2OpNorm
  have hfun := Finset.measurable_sup' Finset.univ_nonempty
    (fun q (_hq : q ∈ Finset.univ) => hBnorm q)
  have heq :
      (fun omega => Finset.univ.sup' Finset.univ_nonempty
        (fun q => ‖B omega q‖)) =
      Finset.univ.sup' Finset.univ_nonempty
        (fun q omega => ‖B omega q‖) := by
    funext omega
    exact (Finset.sup'_apply Finset.univ_nonempty
      (fun q omega => ‖B omega q‖) omega).symm
  rw [heq]
  exact hfun

end PaperIndicatorWeights

/-! ## Product-law conditional expectation bridge -/

/-- Under a genuine product law, the canonical conditional distribution of
the second coordinate given the first is the constant fresh law. -/
theorem condDistrib_snd_fst_prod_ae_eq_const
    {Past Fresh : Type*} [MeasurableSpace Past] [MeasurableSpace Fresh]
    [StandardBorelSpace Fresh] [Nonempty Fresh]
    (muPast : Measure Past) (muFresh : Measure Fresh)
    [IsProbabilityMeasure muPast] [IsProbabilityMeasure muFresh] :
    condDistrib Prod.snd Prod.fst (muPast.prod muFresh) =ᵐ[muPast]
      Kernel.const Past muFresh := by
  let kappa : Kernel Past Fresh := Kernel.const Past muFresh
  let _ : IsMarkovKernel kappa := by
    dsimp only [kappa]
    infer_instance
  have hfst : (muPast.prod muFresh).map Prod.fst = muPast := by simp
  have hjoint :
      (muPast.prod muFresh).map (fun z => (z.1, z.2)) =
        (muPast.prod muFresh).map Prod.fst ⊗ₘ kappa := by
    calc
      (muPast.prod muFresh).map (fun z => (z.1, z.2)) =
          muPast.prod muFresh := by
        simpa only [Prod.eta, Measure.map_id']
      _ = muPast ⊗ₘ kappa := by
        simpa only [kappa] using
          (Measure.compProd_const (μ := muPast) (ν := muFresh)).symm
      _ = (muPast.prod muFresh).map Prod.fst ⊗ₘ kappa := by rw [hfst]
  have hcond := condDistrib_ae_eq_of_measure_eq_compProd
    (μ := muPast.prod muFresh) Prod.fst measurable_snd.aemeasurable hjoint
  rw [hfst] at hcond
  exact hcond

/-- Uniform nonnegative fiberwise `L¹` control gives joint integrability,
the same joint bound, the canonical conditional-expectation formula, and
an almost-everywhere conditional `L¹` bound. -/
theorem product_condExp_ae_eq_fiberIntegral_of_uniform_L1
    {Past Fresh : Type*} [MeasurableSpace Past] [MeasurableSpace Fresh]
    [StandardBorelSpace Fresh] [Nonempty Fresh]
    (muPast : Measure Past) (muFresh : Measure Fresh)
    [IsProbabilityMeasure muPast] [IsProbabilityMeasure muFresh]
    (g : Past × Fresh → ℝ) (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (C : ℝ) (hC : 0 ≤ C)
    (hfiberInt : ∀ a, Integrable (fun x => g (a, x)) muFresh)
    (hfiberBound : ∀ a, ∫ x, g (a, x) ∂muFresh ≤ C) :
    Integrable g (muPast.prod muFresh) ∧
      ∫ z, g z ∂(muPast.prod muFresh) ≤ C ∧
      (muPast.prod muFresh)[g |
          (inferInstance : MeasurableSpace Past).comap Prod.fst] =ᵐ[
            muPast.prod muFresh]
        (fun z => ∫ x, g (z.1, x) ∂muFresh) ∧
      (muPast.prod muFresh)[g |
          (inferInstance : MeasurableSpace Past).comap Prod.fst] ≤ᵐ[
            muPast.prod muFresh] (fun _ => C) := by
  let G := fun a => ∫ x, ‖g (a, x)‖ ∂muFresh
  have hGstrong : StronglyMeasurable G :=
    hg.norm.stronglyMeasurable.integral_prod_right'
  have hG0 : ∀ a, 0 ≤ G a := fun a => integral_nonneg fun x => norm_nonneg _
  have hGle : ∀ a, G a ≤ C := by
    intro a
    have heq : (fun x => ‖g (a, x)‖) = fun x => g (a, x) := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 (a, x))]
    simpa only [G, heq] using hfiberBound a
  have hGint : Integrable G muPast := by
    apply (integrable_const C).mono' hGstrong.aestronglyMeasurable
    filter_upwards with a
    rw [Real.norm_eq_abs, abs_of_nonneg (hG0 a)]
    exact hGle a
  have hgInt : Integrable g (muPast.prod muFresh) :=
    (integrable_prod_iff hg.aestronglyMeasurable).2
      ⟨ae_of_all muPast hfiberInt, hGint⟩
  have hJointBound : ∫ z, g z ∂(muPast.prod muFresh) ≤ C := by
    calc
      ∫ z, g z ∂(muPast.prod muFresh) =
          ∫ a, ∫ x, g (a, x) ∂muFresh ∂muPast := integral_prod g hgInt
      _ ≤ ∫ _a : Past, C ∂muPast :=
        integral_mono hgInt.integral_prod_left (integrable_const C) hfiberBound
      _ = C := by simp
  have heqCond := condExp_past_ae_eq_freshIntegral
    (muPast.prod muFresh) g hg.stronglyMeasurable hgInt
  have hk := condDistrib_snd_fst_prod_ae_eq_const muPast muFresh
  have hkMap : condDistrib Prod.snd Prod.fst (muPast.prod muFresh) =ᵐ[
      (muPast.prod muFresh).map Prod.fst] Kernel.const Past muFresh := by
    simpa only [Measure.map_fst_prod, measure_univ, one_smul] using hk
  have hkProd := ae_eq_comp measurable_fst.aemeasurable hkMap
  have heqFiber :
      (muPast.prod muFresh)[g |
          (inferInstance : MeasurableSpace Past).comap Prod.fst] =ᵐ[
            muPast.prod muFresh]
        (fun z => ∫ x, g (z.1, x) ∂muFresh) := by
    filter_upwards [heqCond, hkProd] with z hz hkz
    rw [hz]
    change (∫ x, g (z.1, x) ∂condDistrib Prod.snd Prod.fst
      (muPast.prod muFresh) z.1) = _
    have hkz' : condDistrib Prod.snd Prod.fst
        (muPast.prod muFresh) z.1 = muFresh := by
      simpa only [Function.comp_apply, Kernel.const_apply] using hkz
    rw [hkz']
  refine ⟨hgInt, hJointBound, heqFiber, ?_⟩
  filter_upwards [heqFiber] with z hz
  rw [hz]
  exact hfiberBound z.1

namespace PaperIndicatorWeights

theorem paperFreshPositiveBound_nonneg (d : ℕ) (z : ℂ) :
    0 ≤ paperFreshPositiveBound d z := by
  unfold paperFreshPositiveBound
  exact add_nonneg Real.posLog_nonneg
    (mul_nonneg (by positivity) (Real.sqrt_nonneg _))

/-- Global complex one-fresh-block closure for a past-measurable frozen
family.  The conclusion is about the literal paper `Z_B`, not an abstract
fiber function: it gives joint `L¹`, the uniform joint bound, the canonical
conditional expectation, and its almost-everywhere conditional bound. -/
theorem complex_paperIndicatorFlatFreshZ_joint_absLog_condExp_withDensity
    {Past : Type*} [MeasurableSpace Past]
    (muPast : Measure Past) [IsProbabilityMeasure muPast]
    (N d : ℕ) [NeZero N] (hsize : d + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1)) (z : ℂ) (start : ZMod N)
    (B : Past → (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hBpos : ∀ a, 0 < exteriorFamilyMaxL2OpNorm (B a))
    (hBmeas : ∀ q i j, Measurable (fun a => B a q i j))
    (hBnorm : ∀ q, Measurable (fun a => ‖B a q‖))
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2)
      (volume.withDensity f))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(volume.withDensity f) ≤ 1) :
    let muFresh := paperIndicatorSampleMeasure N d (volume.withDensity f)
    let radius := fun w : Past × (Fin (N * (d + 2)) → ℂ) =>
      ‖profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtoms N d start w.2) (B w.1)‖
    let scale := fun a : Past => exteriorFamilyMaxL2OpNorm (B a)
    let g := fun w => |Real.log (radius w) - Real.log (scale w.1)|
    let C := paperIsolatedCoefficientLoss d c₀ +
      complexFreshNegativeBound d L + paperFreshPositiveBound d z
    Integrable g (muPast.prod muFresh) ∧
      ∫ w, g w ∂(muPast.prod muFresh) ≤ C ∧
      (muPast.prod muFresh)[g |
          (inferInstance : MeasurableSpace Past).comap Prod.fst] =ᵐ[
            muPast.prod muFresh]
        (fun w => ∫ x, g (w.1, x) ∂muFresh) ∧
      (muPast.prod muFresh)[g |
          (inferInstance : MeasurableSpace Past).comap Prod.fst] ≤ᵐ[
            muPast.prod muFresh] (fun _ => C) := by
  classical
  let muFresh := paperIndicatorSampleMeasure N d (volume.withDensity f)
  let radius := fun w : Past × (Fin (N * (d + 2)) → ℂ) =>
    ‖profile.paperIndicatorFreshZ center z
      (paperIndicatorFreshAtoms N d start w.2) (B w.1)‖
  let scale := fun a : Past => exteriorFamilyMaxL2OpNorm (B a)
  let g := fun w => |Real.log (radius w) - Real.log (scale w.1)|
  let C := paperIsolatedCoefficientLoss d c₀ +
    complexFreshNegativeBound d L + paperFreshPositiveBound d z
  letI : IsProbabilityMeasure muFresh := by
    simpa only [muFresh, paperIndicatorSampleMeasure] using
      iidMeasure_isProbability (volume.withDensity f) (N * (d + 2))
  have hradius : Measurable radius := by
    dsimp only [radius]
    apply profile.measurable_norm_paperIndicatorFreshZ_of_measurable_family
    · intro t ell
      exact (measurable_paperIndicatorFreshAtoms N d start t ell).comp measurable_snd
    · intro q i j
      exact (hBmeas q i j).comp measurable_fst
  have hscale : Measurable scale :=
    measurable_exteriorFamilyMaxL2OpNorm B hBnorm
  have hg : Measurable g := by
    change Measurable (fun w =>
      ‖Real.log (radius w) - Real.log (scale w.1)‖)
    exact ((Real.measurable_log.comp hradius).sub
      (Real.measurable_log.comp (hscale.comp measurable_fst))).norm
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg
      (add_nonneg (paperIsolatedCoefficientLoss_nonneg hc₀ hsqrt)
        (complexFreshNegativeBound_nonneg d L))
      (paperFreshPositiveBound_nonneg d z)
  have hfiber (a : Past) :=
    profile.complex_paperIndicatorFlatFreshZ_absLog_L1_withDensity
      N d hsize hc₀ hsqrt center z start (B a) (hBpos a)
      f hL hf hsecondInt hsecond
  exact product_condExp_ae_eq_fiberIntegral_of_uniform_L1
    muPast muFresh g hg (fun w => abs_nonneg _) C hC
    (fun a => by
      simpa only [g, radius, scale, muFresh] using (hfiber a).2.1)
    (fun a => by
      simpa only [g, radius, scale, muFresh, C] using (hfiber a).2.2)

/-- Real analogue of
`complex_paperIndicatorFlatFreshZ_joint_absLog_condExp_withDensity`. -/
theorem real_paperIndicatorFlatFreshZ_joint_absLog_condExp_withDensity
    {Past : Type*} [MeasurableSpace Past]
    (muPast : Measure Past) [IsProbabilityMeasure muPast]
    (N d : ℕ) [NeZero N] (hsize : d + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1)) (z : ℂ) (start : ZMod N)
    (B : Past → (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hBpos : ∀ a, 0 < exteriorFamilyMaxL2OpNorm (B a))
    (hBmeas : ∀ q i j, Measurable (fun a => B a q i j))
    (hBnorm : ∀ q, Measurable (fun a => ‖B a q‖))
    (f : ℝ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ x ∂(volume : Measure ℝ), f x ≤ ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : ℝ => u ^ 2) (volume.withDensity f))
    (hsecond : ∫ u : ℝ, u ^ 2 ∂(volume.withDensity f) ≤ 1) :
    let muFresh := paperIndicatorRealSampleMeasure N d (volume.withDensity f)
    let radius := fun w : Past × (Fin (N * (d + 2)) → ℝ) =>
      ‖profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtomsOfReal N d start w.2) (B w.1)‖
    let scale := fun a : Past => exteriorFamilyMaxL2OpNorm (B a)
    let g := fun w => |Real.log (radius w) - Real.log (scale w.1)|
    let C := paperIsolatedCoefficientLoss d c₀ +
      realFreshNegativeBound d L + paperFreshPositiveBound d z
    Integrable g (muPast.prod muFresh) ∧
      ∫ w, g w ∂(muPast.prod muFresh) ≤ C ∧
      (muPast.prod muFresh)[g |
          (inferInstance : MeasurableSpace Past).comap Prod.fst] =ᵐ[
            muPast.prod muFresh]
        (fun w => ∫ x, g (w.1, x) ∂muFresh) ∧
      (muPast.prod muFresh)[g |
          (inferInstance : MeasurableSpace Past).comap Prod.fst] ≤ᵐ[
            muPast.prod muFresh] (fun _ => C) := by
  classical
  let muFresh := paperIndicatorRealSampleMeasure N d (volume.withDensity f)
  let radius := fun w : Past × (Fin (N * (d + 2)) → ℝ) =>
    ‖profile.paperIndicatorFreshZ center z
      (paperIndicatorFreshAtomsOfReal N d start w.2) (B w.1)‖
  let scale := fun a : Past => exteriorFamilyMaxL2OpNorm (B a)
  let g := fun w => |Real.log (radius w) - Real.log (scale w.1)|
  let C := paperIsolatedCoefficientLoss d c₀ +
    realFreshNegativeBound d L + paperFreshPositiveBound d z
  letI : IsProbabilityMeasure muFresh := by
    simpa only [muFresh, paperIndicatorRealSampleMeasure] using
      iidMeasure_isProbability (volume.withDensity f) (N * (d + 2))
  have hradius : Measurable radius := by
    dsimp only [radius]
    apply profile.measurable_norm_paperIndicatorFreshZ_of_measurable_family
    · intro t ell
      exact (measurable_paperIndicatorFreshAtomsOfReal N d start t ell).comp measurable_snd
    · intro q i j
      exact (hBmeas q i j).comp measurable_fst
  have hscale : Measurable scale :=
    measurable_exteriorFamilyMaxL2OpNorm B hBnorm
  have hg : Measurable g := by
    change Measurable (fun w =>
      ‖Real.log (radius w) - Real.log (scale w.1)‖)
    exact ((Real.measurable_log.comp hradius).sub
      (Real.measurable_log.comp (hscale.comp measurable_fst))).norm
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg
      (add_nonneg (paperIsolatedCoefficientLoss_nonneg hc₀ hsqrt)
        (realFreshNegativeBound_nonneg d L))
      (paperFreshPositiveBound_nonneg d z)
  have hfiber (a : Past) :=
    profile.real_paperIndicatorFlatFreshZ_absLog_L1_withDensity
      N d hsize hc₀ hsqrt center z start (B a) (hBpos a)
      f hL hf hsecondInt hsecond
  exact product_condExp_ae_eq_fiberIntegral_of_uniform_L1
    muPast muFresh g hg (fun w => abs_nonneg _) C hC
    (fun a => by
      simpa only [g, radius, scale, muFresh] using (hfiber a).2.1)
    (fun a => by
      simpa only [g, radius, scale, muFresh, C] using (hfiber a).2.2)

end PaperIndicatorWeights

end CircularLawSection4
