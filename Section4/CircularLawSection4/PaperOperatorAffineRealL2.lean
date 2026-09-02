import CircularLawSection4.PaperOperatorAffineL2
import CircularLawSection4.RealInputComplexOperatorAffine

/-!
# The paper operator-affine `L²` lemma for real atoms

This module closes the real-atom branch of the paper's operator-affine
logarithm estimate.  The deterministic weights and operators remain complex,
as does the spectral parameter, while a finite IID real vector is embedded
coordinatewise into `ℂ`.

The proof selects a large scalarized slope from the square-root profile
lower bound, applies the real-input/complex-operator small-ball theorem to
the logarithmic deficit, controls the excess from the unit second moment,
and combines the two `L²` halves.
-/

open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory Set

noncomputable section

namespace CircularLawSection4

universe w x

/-- The norm of the paper's labelled complex operator-affine expression
when its atom vector is real. -/
def paperRealOperatorAffineRadius
    {d : ℕ} {c₀ C₀ : ℝ} {E : Type w} {F : Type x}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1))
    (M : ResetLabel (d + 1) → E →L[ℂ] F) (z : ℂ)
    (η : Fin (d + 2) → ℝ) : ℝ :=
  ‖operatorAffine profile.orderedResetWeight
      (paperOperatorAffineAtoms d (fun i => (η i : ℂ))) M z
      (M (some center))‖

/-- The labelled paper radius is exactly the finite real-input expression
used by `RealInputComplexOperatorAffine`. -/
theorem realInputComplexOperatorAffine_norm_eq_paperRealOperatorAffineRadius
    {d : ℕ} {c₀ C₀ : ℝ} {E : Type w} {F : Type x}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1))
    (M : ResetLabel (d + 1) → E →L[ℂ] F) (z : ℂ)
    (η : Fin (d + 2) → ℝ) :
    ‖realInputComplexOperatorAffine
        (paperOperatorAffineWeightFin profile) η
        (paperOperatorAffineFamilyFin M) z
        (paperOperatorAffineFamilyFin M
          (paperOperatorAffineCenterFin center))‖ =
      paperRealOperatorAffineRadius profile center M z η := by
  have h := operatorAffine_paperOperatorAffineAtoms profile
    (fun i : Fin (d + 2) => (η i : ℂ)) M z (M (some center))
  unfold realInputComplexOperatorAffine paperRealOperatorAffineRadius
  simpa using congrArg norm h

/-- A real one-coordinate second moment transfers to every coordinate of
the recursive IID vector, in the complexified norm used by the operator
estimate. -/
theorem iidMeasure_coordinate_complexifiedReal_norm_sq_integrable_and_integral_le_one
    {ν : Measure ℝ} [SFinite ν] [IsProbabilityMeasure ν]
    {n : ℕ} (i : Fin n)
    (hνInt : Integrable (fun u : ℝ => u ^ 2) ν)
    (hνSecond : ∫ u : ℝ, u ^ 2 ∂ν ≤ 1) :
    Integrable (fun η : Fin n → ℝ => ‖(η i : ℂ)‖ ^ 2)
        (iidMeasure ν n) ∧
      ∫ η : Fin n → ℝ, ‖(η i : ℂ)‖ ^ 2 ∂iidMeasure ν n ≤ 1 := by
  have hνNormInt : Integrable (fun u : ℝ => ‖(u : ℂ)‖ ^ 2) ν := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hνInt
  have hνNormSecond : ∫ u : ℝ, ‖(u : ℂ)‖ ^ 2 ∂ν ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hνSecond
  have hmap := iidMeasure_map_coordinate ν i
  have hIntMap : Integrable (fun u : ℝ => ‖(u : ℂ)‖ ^ 2)
      (Measure.map (fun η : Fin n → ℝ => η i) (iidMeasure ν n)) := by
    rw [hmap]
    exact hνNormInt
  have hInt : Integrable (fun η : Fin n → ℝ => ‖(η i : ℂ)‖ ^ 2)
      (iidMeasure ν n) := by
    simpa only [Function.comp_def] using
      hIntMap.comp_measurable (measurable_pi_apply i)
  refine ⟨hInt, ?_⟩
  calc
    (∫ η : Fin n → ℝ, ‖(η i : ℂ)‖ ^ 2 ∂iidMeasure ν n) =
        ∫ u : ℝ, ‖(u : ℂ)‖ ^ 2
          ∂Measure.map (fun η : Fin n → ℝ => η i) (iidMeasure ν n) := by
      exact (integral_map_of_stronglyMeasurable
        (μ := iidMeasure ν n)
        (φ := fun η : Fin n → ℝ => η i)
        (f := fun u : ℝ => ‖(u : ℂ)‖ ^ 2)
        (measurable_pi_apply i)
        (Complex.continuous_ofReal.norm.pow 2).stronglyMeasurable).symm
    _ = ∫ u : ℝ, ‖(u : ℂ)‖ ^ 2 ∂ν := by rw [hmap]
    _ ≤ 1 := hνNormSecond

/-- Full two-sided operator-affine logarithmic `L²` estimate for the
paper's real atom and complex spectral-parameter branch.

`theta` is the loss in approximate norming, while
`sqrt (c₀ / (d + 2))` is the deterministic profile loss.  The hypothesis
that the latter is at most one is the natural normalization required by the
maximum-coefficient selector. -/
theorem paper_real_iid_operatorAffine_absLog_L2
    {d : ℕ} {c₀ C₀ : ℝ} {E : Type w} {F : Type x}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hbmin_le_one : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1))
    (M : ResetLabel (d + 1) → E →L[ℂ] F) (z : ℂ)
    (hscale : 0 < operatorAffineScale (some center)
      profile.orderedResetWeight M)
    (ν : Measure ℝ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ} (hL : 0 ≤ L)
    (hν : RealIntervalBound ν (ENNReal.ofReal L))
    (hνInt : Integrable (fun u : ℝ => u ^ 2) ν)
    (hνSecond : ∫ u : ℝ, u ^ 2 ∂ν = 1)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    iidMeasure ν (d + 2)
        {η | paperRealOperatorAffineRadius profile center M z η = 0} = 0 ∧
      MemLp (fun η =>
        |Real.log (paperRealOperatorAffineRadius profile center M z η) -
          Real.log (operatorAffineScale (some center)
            profile.orderedResetWeight M)|) 2 (iidMeasure ν (d + 2)) ∧
      ∫ η,
          |Real.log (paperRealOperatorAffineRadius profile center M z η) -
            Real.log (operatorAffineScale (some center)
              profile.orderedResetWeight M)| ^ 2
          ∂iidMeasure ν (d + 2) ≤
        2 * oneSidedLogSecondMomentBound
              ((4 * L) /
                (theta * Real.sqrt (c₀ / (d + 2 : ℝ)))) 1 +
          2 * (3 * (Real.log (d + 2 : ℝ)) ^ 2 + 3 + 3 * ‖z‖ ^ 2) := by
  let i₀ : Fin (d + 2) := paperOperatorAffineCenterFin center
  let bFin : Fin (d + 2) → ℂ := paperOperatorAffineWeightFin profile
  let MFin : Fin (d + 2) → E →L[ℂ] F := paperOperatorAffineFamilyFin M
  let scaleFin : ℝ := operatorAffineScale i₀ bFin MFin
  let radiusFin : (Fin (d + 2) → ℝ) → ℝ := fun η =>
    ‖realInputComplexOperatorAffine bFin η MFin z (MFin i₀)‖
  let bmin : ℝ := Real.sqrt (c₀ / (d + 2 : ℝ))
  have hbmin0 : 0 < bmin := by
    dsimp only [bmin]
    exact Real.sqrt_pos.2 (div_pos hc₀ (by positivity))
  have hbminCenter : bmin ≤ ‖bFin i₀‖ := by
    dsimp only [bmin, bFin, i₀]
    simpa using
      profile.sqrt_lower_le_norm_orderedResetWeight (some center)
  have hscaleEq : scaleFin =
      operatorAffineScale (some center) profile.orderedResetWeight M := by
    exact paperOperatorAffineScaleFin_eq profile center M
  have hscaleFin : 0 < scaleFin := hscaleEq.symm ▸ hscale
  obtain ⟨s, x, ell, hx, hell, hslope⟩ :=
    exists_large_scalarized_slope i₀ bFin MFin
      hbmin0 hbmin_le_one hbminCenter htheta0 htheta1 hscaleFin
  have hthreshold : 0 < theta * bmin := mul_pos htheta0 hbmin0
  let _ := iidMeasure_isProbability ν (d + 2)
  obtain ⟨hzero, hdeficitL2, hdeficitSq⟩ :=
    real_iid_complexOperatorAffine_logDeficit_L2_of_slope
      hL hν s bFin MFin z (MFin i₀) x ell hx.le hell
      scaleFin (theta * bmin) hscaleFin hthreshold hslope.le
  have hradiusMeas : Measurable radiusFin := by
    exact (continuous_realInputComplexOperatorAffine_fin bFin MFin z (MFin i₀)).norm.measurable
  have hsumMeas : Measurable (fun η : Fin (d + 2) → ℝ =>
      ∑ i, ‖(η i : ℂ)‖) := by
    fun_prop
  have hcoordinate (i : Fin (d + 2)) :
      Integrable (fun η : Fin (d + 2) → ℝ => ‖(η i : ℂ)‖ ^ 2)
          (iidMeasure ν (d + 2)) ∧
        ∫ η : Fin (d + 2) → ℝ, ‖(η i : ℂ)‖ ^ 2
            ∂iidMeasure ν (d + 2) ≤ 1 :=
    iidMeasure_coordinate_complexifiedReal_norm_sq_integrable_and_integral_le_one
      i hνInt hνSecond.le
  obtain ⟨hsumInt, hsumSq⟩ :=
    integrable_normalized_sum_sq_and_integral_le_one
      (iidMeasure ν (d + 2))
      (fun i η => ‖(η i : ℂ)‖)
      (fun _i => by fun_prop)
      (fun i => (hcoordinate i).1)
      (fun i => (hcoordinate i).2)
  have hradiusPos : ∀ᵐ η ∂iidMeasure ν (d + 2), 0 < radiusFin η := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with η hη
    have hne : radiusFin η ≠ 0 := by
      simpa only [Set.mem_ofPred_eq] using hη
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  obtain ⟨hexcessL2, hexcessSq⟩ :=
    operatorAffine_memLp_two_and_integral_sq_logExcess_of_scaledSecondMoment
      (iidMeasure ν (d + 2)) i₀ bFin MFin z
      (fun η i => (η i : ℂ)) hscaleFin
      (by simpa only [radiusFin, realInputComplexOperatorAffine] using hradiusMeas)
      hsumMeas
      (by simpa only [radiusFin, realInputComplexOperatorAffine] using hradiusPos)
      1 hsumInt hsumSq
  obtain ⟨hfullL2, hfullSq⟩ :=
    memLp_two_and_integral_sq_abs_log_sub_log_of_parts
      scaleFin hdeficitL2 hexcessL2 hdeficitSq hexcessSq
  have hnormEq : ∀ η : Fin (d + 2) → ℝ,
      ‖realInputComplexOperatorAffine bFin η MFin z (MFin i₀)‖ =
      paperRealOperatorAffineRadius profile center M z η := by
    intro η
    dsimp only [bFin, MFin, i₀]
    exact realInputComplexOperatorAffine_norm_eq_paperRealOperatorAffineRadius
      profile center M z η
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc, hnormEq] using hzero
  · simpa only [Nat.add_assoc, hnormEq, hscaleEq] using hfullL2
  · simpa only [Nat.add_assoc, hnormEq, hscaleEq, bmin,
      Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat, mul_one, one_mul]
      using hfullSq

end CircularLawSection4
