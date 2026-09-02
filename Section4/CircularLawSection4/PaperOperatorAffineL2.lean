import CircularLawSection4.PaperIndicatorWeights
import CircularLawSection4.IIDCoordinateFacts
import CircularLawSection4.IIDOperatorAffineSmallBall
import CircularLawSection4.OperatorAffinePositiveL2
import CircularLawSection4.OperatorAffineNegativeL2
import CircularLawSection4.RealInputComplexOperatorAffine

/-!
# The operator-affine logarithm lemma for the paper's indicator profile

This module inserts the square-root indicator weights and a finite IID row
directly into the abstract operator-affine logarithmic estimates.  The
complex result combines the planar bounded-density small-ball estimate with
the normalized second moment of the row and gives an explicit two-sided
`L²` bound for the logarithm at the natural operator-affine scale.
-/

open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory Set

noncomputable section

namespace CircularLawSection4

universe u v

/-- The canonical enumeration of the reset/star labels in one paper row. -/
def paperOperatorAffineLabelEquiv (d : ℕ) :
    Fin (d + 2) ≃ ResetLabel (d + 1) :=
  finSuccEquivLast

/-- A flat IID row, re-labelled by the reset/star coordinates used by the
paper transfer matrices. -/
def paperOperatorAffineAtoms (d : ℕ) (η : Fin (d + 2) → ℂ) :
    ResetLabel (d + 1) → ℂ :=
  fun ell ↦ η ((paperOperatorAffineLabelEquiv d).symm ell)

/-- A flat real IID row embedded into the complex reset/star coordinates. -/
def paperOperatorAffineAtomsOfReal (d : ℕ) (η : Fin (d + 2) → ℝ) :
    ResetLabel (d + 1) → ℂ :=
  fun ell ↦ (η ((paperOperatorAffineLabelEquiv d).symm ell) : ℂ)

/-- The paper weights enumerated by a standard finite IID coordinate type. -/
def paperOperatorAffineWeightFin {d : ℕ} {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀) : Fin (d + 2) → ℂ :=
  fun i ↦ profile.orderedResetWeight (paperOperatorAffineLabelEquiv d i)

/-- A reset-label operator family enumerated by a standard finite type. -/
def paperOperatorAffineFamilyFin {d : ℕ} {E F : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (M : ResetLabel (d + 1) → E →L[ℂ] F) : Fin (d + 2) → E →L[ℂ] F :=
  fun i ↦ M (paperOperatorAffineLabelEquiv d i)

/-- The distinguished finite index corresponding to an interior center
label. -/
def paperOperatorAffineCenterFin {d : ℕ} (center : Fin (d + 1)) :
    Fin (d + 2) :=
  (paperOperatorAffineLabelEquiv d).symm (some center)

@[simp] theorem paperOperatorAffineWeightFin_center {d : ℕ} {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) :
    paperOperatorAffineWeightFin profile (paperOperatorAffineCenterFin center) =
      profile.orderedResetWeight (some center) := by
  simp [paperOperatorAffineWeightFin, paperOperatorAffineCenterFin]

@[simp] theorem paperOperatorAffineFamilyFin_center
    {d : ℕ} {E F : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (M : ResetLabel (d + 1) → E →L[ℂ] F)
    (center : Fin (d + 1)) :
    paperOperatorAffineFamilyFin M (paperOperatorAffineCenterFin center) =
      M (some center) := by
  simp [paperOperatorAffineFamilyFin, paperOperatorAffineCenterFin]

/-- Re-indexing is definitionally compatible with the labelled IID row. -/
theorem operatorAffine_paperOperatorAffineAtoms
    {d : ℕ} {c₀ C₀ : ℝ} {E F : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (η : Fin (d + 2) → ℂ)
    (M : ResetLabel (d + 1) → E →L[ℂ] F)
    (z : ℂ) (M₀ : E →L[ℂ] F) :
    operatorAffine (paperOperatorAffineWeightFin profile) η
        (paperOperatorAffineFamilyFin M) z M₀ =
      operatorAffine profile.orderedResetWeight
        (paperOperatorAffineAtoms d η) M z M₀ := by
  classical
  unfold operatorAffine
  apply congrArg (fun T : E →L[ℂ] F => T - z • M₀)
  rw [← (paperOperatorAffineLabelEquiv d).sum_comp]
  apply Finset.sum_congr rfl
  intro i _hi
  simp [paperOperatorAffineWeightFin, paperOperatorAffineAtoms,
    paperOperatorAffineFamilyFin]

/-- Real flat inputs, embedded in `ℂ`, obey the same exact reset-label
re-indexing identity. -/
theorem realInputComplexOperatorAffine_paperOperatorAffineAtomsOfReal
    {d : ℕ} {c₀ C₀ : ℝ} {E F : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (η : Fin (d + 2) → ℝ)
    (M : ResetLabel (d + 1) → E →L[ℂ] F)
    (z : ℂ) (M₀ : E →L[ℂ] F) :
    realInputComplexOperatorAffine (paperOperatorAffineWeightFin profile) η
        (paperOperatorAffineFamilyFin M) z M₀ =
      operatorAffine profile.orderedResetWeight
        (paperOperatorAffineAtomsOfReal d η) M z M₀ := by
  change operatorAffine (paperOperatorAffineWeightFin profile)
      (fun i => (η i : ℂ)) (paperOperatorAffineFamilyFin M) z M₀ = _
  rw [operatorAffine_paperOperatorAffineAtoms]
  rfl

/-- The natural operator-affine scale is unchanged by the canonical finite
enumeration of reset labels. -/
theorem paperOperatorAffineScaleFin_eq
    {d : ℕ} {c₀ C₀ : ℝ} {E F : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1))
    (M : ResetLabel (d + 1) → E →L[ℂ] F) :
    operatorAffineScale (paperOperatorAffineCenterFin center)
        (paperOperatorAffineWeightFin profile)
        (paperOperatorAffineFamilyFin M) =
      operatorAffineScale (some center) profile.orderedResetWeight M := by
  classical
  unfold operatorAffineScale
  apply congrArg₂ max
  · simp
  · unfold operatorCoefficientMax
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _hi
      exact Finset.le_sup'
        (fun ell : ResetLabel (d + 1) =>
          ‖profile.orderedResetWeight ell‖ * ‖M ell‖)
        (Finset.mem_univ (paperOperatorAffineLabelEquiv d i))
    · apply Finset.sup'_le
      intro ell _hell
      obtain ⟨i, rfl⟩ := (paperOperatorAffineLabelEquiv d).surjective ell
      exact Finset.le_sup'
        (fun j : Fin (d + 2) =>
          ‖paperOperatorAffineWeightFin profile j‖ *
            ‖paperOperatorAffineFamilyFin M j‖)
        (Finset.mem_univ i)

/-- A quadratic small-ball estimate under a probability measure can be
weakened to a linear one by using the quadratic estimate below radius one
and the trivial probability bound above radius one. -/
theorem probability_quadratic_smallBall_to_linear
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Set Ω) (A ρ : ℝ)
    (hA : 0 ≤ A) (hρ : 0 < ρ)
    (hquad : μ S ≤ ENNReal.ofReal A * ENNReal.ofReal ρ ^ 2) :
    μ S ≤ ENNReal.ofReal (max 1 A * ρ) := by
  by_cases hρ1 : ρ ≤ 1
  · calc
      μ S ≤ ENNReal.ofReal A * ENNReal.ofReal ρ ^ 2 := hquad
      _ = ENNReal.ofReal (A * ρ ^ 2) := by
        rw [← ENNReal.ofReal_pow hρ.le,
          ← ENNReal.ofReal_mul hA]
      _ ≤ ENNReal.ofReal (max 1 A * ρ) := by
        apply ENNReal.ofReal_le_ofReal
        have hAmax : A ≤ max 1 A := le_max_right _ _
        have hρsq : ρ ^ 2 ≤ ρ := by nlinarith
        nlinarith [mul_nonneg hA hρ.le,
          mul_nonneg (le_trans hA hAmax) hρ.le]
  · calc
      μ S ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal (max 1 A * ρ) := by
        rw [ENNReal.one_le_ofReal]
        have hmax : 1 ≤ max 1 A := le_max_left _ _
        have hρ1' : 1 < ρ := lt_of_not_ge hρ1
        nlinarith

/-- Each coordinate of the recursive finite IID law inherits the
one-coordinate squared-norm integrability and bound. -/
theorem iidMeasure_coordinate_norm_sq_integrable_and_integral_le_one
    {ν : Measure ℂ} [SFinite ν] [IsProbabilityMeasure ν]
    {n : ℕ} (i : Fin n)
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    Integrable (fun η : Fin n → ℂ => ‖η i‖ ^ 2) (iidMeasure ν n) ∧
      ∫ η : Fin n → ℂ, ‖η i‖ ^ 2 ∂iidMeasure ν n ≤ 1 := by
  have hmap := iidMeasure_map_coordinate ν i
  have hIntMap : Integrable (fun u : ℂ => ‖u‖ ^ 2)
      (Measure.map (fun η : Fin n → ℂ => η i) (iidMeasure ν n)) := by
    rw [hmap]
    exact hνInt
  have hInt : Integrable (fun η : Fin n → ℂ => ‖η i‖ ^ 2)
      (iidMeasure ν n) := by
    simpa only [Function.comp_def] using
      hIntMap.comp_measurable (measurable_pi_apply i)
  refine ⟨hInt, ?_⟩
  calc
    (∫ η : Fin n → ℂ, ‖η i‖ ^ 2 ∂iidMeasure ν n) =
        ∫ u : ℂ, ‖u‖ ^ 2
          ∂Measure.map (fun η : Fin n → ℂ => η i) (iidMeasure ν n) := by
      exact (integral_map_of_stronglyMeasurable
        (μ := iidMeasure ν n) (φ := fun η : Fin n → ℂ => η i)
        (f := fun u : ℂ => ‖u‖ ^ 2) (measurable_pi_apply i)
        ((continuous_norm : Continuous (fun u : ℂ => ‖u‖)).pow 2).stronglyMeasurable).symm
    _ = ∫ u : ℂ, ‖u‖ ^ 2 ∂ν := by rw [hmap]
    _ ≤ 1 := hνSecond

/-- Real-coordinate analogue of
`iidMeasure_coordinate_norm_sq_integrable_and_integral_le_one`. -/
theorem iidMeasure_coordinate_abs_sq_integrable_and_integral_le_one
    {ν : Measure ℝ} [SFinite ν] [IsProbabilityMeasure ν]
    {n : ℕ} (i : Fin n)
    (hνInt : Integrable (fun u : ℝ => |u| ^ 2) ν)
    (hνSecond : ∫ u : ℝ, |u| ^ 2 ∂ν ≤ 1) :
    Integrable (fun η : Fin n → ℝ => |η i| ^ 2) (iidMeasure ν n) ∧
      ∫ η : Fin n → ℝ, |η i| ^ 2 ∂iidMeasure ν n ≤ 1 := by
  have hmap := iidMeasure_map_coordinate ν i
  have hIntMap : Integrable (fun u : ℝ => |u| ^ 2)
      (Measure.map (fun η : Fin n → ℝ => η i) (iidMeasure ν n)) := by
    rw [hmap]
    exact hνInt
  have hInt : Integrable (fun η : Fin n → ℝ => |η i| ^ 2)
      (iidMeasure ν n) := by
    simpa only [Function.comp_def] using
      hIntMap.comp_measurable (measurable_pi_apply i)
  refine ⟨hInt, ?_⟩
  calc
    (∫ η : Fin n → ℝ, |η i| ^ 2 ∂iidMeasure ν n) =
        ∫ u : ℝ, |u| ^ 2
          ∂Measure.map (fun η : Fin n → ℝ => η i) (iidMeasure ν n) := by
      exact (integral_map_of_stronglyMeasurable
        (μ := iidMeasure ν n) (φ := fun η : Fin n → ℝ => η i)
        (f := fun u : ℝ => |u| ^ 2) (measurable_pi_apply i)
        ((continuous_abs.pow 2).stronglyMeasurable)).symm
    _ = ∫ u : ℝ, |u| ^ 2 ∂ν := by rw [hmap]
    _ ≤ 1 := hνSecond

section ComplexIndicator

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [NormedSpace ℂ E] [NormedSpace ℂ F]

/-- Complex bounded-density operator-affine logarithm estimate with the
paper indicator weights inserted.  The IID sample is kept in its flat
`Fin (d + 2)` representation; the following theorem rewrites it into the
reset-label representation used by the paper transfer matrices. -/
theorem complex_paperIndicator_operatorAffineFin_memLp_two_and_integral_sq
    {d : ℕ} {c₀ C₀ L : ℝ}
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1))
    (M : ResetLabel (d + 1) → E →L[ℂ] F) (z : ℂ)
    (hscale : 0 < operatorAffineScale (some center)
      profile.orderedResetWeight M)
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    let b := paperOperatorAffineWeightFin profile
    let MF := paperOperatorAffineFamilyFin M
    let i₀ := paperOperatorAffineCenterFin center
    let scale := operatorAffineScale i₀ b MF
    MemLp (fun η : Fin (d + 2) → ℂ =>
        |Real.log ‖operatorAffine b η MF z (MF i₀)‖ - Real.log scale|)
        2 (iidMeasure ν (d + 2)) ∧
      ∫ η : Fin (d + 2) → ℂ,
          |Real.log ‖operatorAffine b η MF z (MF i₀)‖ -
            Real.log scale| ^ 2 ∂iidMeasure ν (d + 2) ≤
        2 * oneSidedLogSecondMomentBound
            ((max 1 (Real.pi * L)) /
              ((1 / 2 : ℝ) * Real.sqrt (c₀ / (d + 2 : ℝ)))) 1 +
          2 * (3 * (Real.log (d + 2 : ℝ)) ^ 2 + 3 * 1 +
            3 * ‖z‖ ^ 2) := by
  let b := paperOperatorAffineWeightFin profile
  let MF := paperOperatorAffineFamilyFin M
  let i₀ := paperOperatorAffineCenterFin center
  let scale := operatorAffineScale i₀ b MF
  let q := Real.sqrt (c₀ / (d + 2 : ℝ))
  let theta := (1 / 2 : ℝ) * q
  let C := max 1 (Real.pi * L)
  let μ := iidMeasure ν (d + 2)
  let radius : (Fin (d + 2) → ℂ) → ℝ := fun η =>
    ‖operatorAffine b η MF z (MF i₀)‖
  letI : IsProbabilityMeasure μ := iidMeasure_isProbability ν (d + 2)
  have hq : 0 < q := by
    dsimp [q]
    apply Real.sqrt_pos.2
    positivity
  have htheta : 0 < theta := by
    dsimp [theta]
    positivity
  have hscaleFin : 0 < scale := by
    dsimp [scale, i₀, b, MF]
    rw [paperOperatorAffineScaleFin_eq]
    exact hscale
  have hbcenter : q ≤ ‖b i₀‖ := by
    dsimp [q, b, i₀]
    simpa using
      profile.sqrt_lower_le_norm_orderedResetWeight (some center)
  obtain ⟨s, x, ell, hx, hell, hslope⟩ :=
    exists_large_scalarized_slope i₀ b MF hq hsqrt hbcenter
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      hscaleFin
  have hradiusMeas : Measurable radius := by
    dsimp [radius]
    exact (continuous_operatorAffine_fin b MF z (MF i₀)).norm.measurable
  have hradius0 : ∀ η, 0 ≤ radius η := fun η => by
    dsimp [radius]
    exact norm_nonneg _
  have hC : 0 ≤ C := by
    dsimp [C]
    exact (zero_le_one.trans (le_max_left 1 (Real.pi * L)))
  have hsmall : ∀ ρ : ℝ, 0 < ρ →
      μ {η | radius η ≤ theta * scale * ρ} ≤
        ENNReal.ofReal (C * ρ) := by
    intro ρ hρ
    have hquad :=
      complex_iid_operatorAffine_arbitraryCoordinate_smallBall
        hν s b MF z (MF i₀) x ell (le_of_lt hx) hell hρ.le
        (mul_pos htheta hscaleFin) (le_of_lt hslope)
    have hquad' :
        μ {η | radius η ≤ theta * scale * ρ} ≤
          ENNReal.ofReal (Real.pi * L) * ENNReal.ofReal ρ ^ 2 := by
      simpa only [μ, radius, theta, scale,
        ENNReal.ofReal_mul Real.pi_pos.le] using hquad
    simpa only [C] using
      probability_quadratic_smallBall_to_linear μ
        {η | radius η ≤ theta * scale * ρ} (Real.pi * L) ρ
        (mul_nonneg Real.pi_pos.le hL) hρ hquad'
  obtain ⟨hzero, hnegativeLp, hnegative⟩ :=
    zeroSet_memLp_two_and_integral_sq_logDeficit_of_threshold_linearSmallBall
      μ radius hradiusMeas hradius0 scale theta C hscaleFin htheta hC hsmall
  have hradiusPos : ∀ᵐ η ∂μ, 0 < radius η := by
    rw [ae_iff]
    have hset : {η | ¬ 0 < radius η} = {η | radius η = 0} := by
      ext η
      simp only [Set.mem_setOf_eq, not_lt]
      constructor
      · intro h
        exact le_antisymm h (hradius0 η)
      · intro h
        exact h.le
    rw [hset, hzero]
  have hcoord : ∀ i : Fin (d + 2),
      Integrable (fun η : Fin (d + 2) → ℂ => ‖η i‖ ^ 2) μ ∧
        ∫ η : Fin (d + 2) → ℂ, ‖η i‖ ^ 2 ∂μ ≤ 1 := by
    intro i
    simpa only [μ] using
      iidMeasure_coordinate_norm_sq_integrable_and_integral_le_one
        i hνInt hνSecond
  obtain ⟨hscaledInt, hscaled⟩ :=
    integrable_normalized_sum_sq_and_integral_le_one μ
      (fun (i : Fin (d + 2)) (η : Fin (d + 2) → ℂ) => ‖η i‖)
      (fun i => (measurable_pi_apply i).norm)
      (fun i => (hcoord i).1) (fun i => (hcoord i).2)
  have hSmeas : Measurable
      (fun η : Fin (d + 2) → ℂ => ∑ i, ‖η i‖) := by
    fun_prop
  obtain ⟨hpositiveLp, hpositive⟩ :=
    operatorAffine_memLp_two_and_integral_sq_logExcess_of_scaledSecondMoment
      μ i₀ b MF z (fun η => η) hscaleFin hradiusMeas hSmeas
      hradiusPos 1 hscaledInt hscaled
  have hcombined :=
    memLp_two_and_integral_sq_abs_log_sub_log_of_parts
      scale hnegativeLp hpositiveLp hnegative hpositive
  simpa only [b, MF, i₀, scale, q, theta, C, μ, radius,
    Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] using hcombined

/-- Paper-coordinate form of the complex operator-affine logarithm lemma.
The random argument is now literally the reset-labelled IID row used by the
indicator transfer matrices, and the reference scale is literally
`operatorAffineScale (some center) profile.orderedResetWeight M`. -/
theorem complex_paperIndicator_operatorAffine_memLp_two_and_integral_sq
    {d : ℕ} {c₀ C₀ L : ℝ}
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1))
    (M : ResetLabel (d + 1) → E →L[ℂ] F) (z : ℂ)
    (hscale : 0 < operatorAffineScale (some center)
      profile.orderedResetWeight M)
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    MemLp (fun η : Fin (d + 2) → ℂ =>
        |Real.log ‖operatorAffine profile.orderedResetWeight
            (paperOperatorAffineAtoms d η) M z (M (some center))‖ -
          Real.log (operatorAffineScale (some center)
            profile.orderedResetWeight M)|)
        2 (iidMeasure ν (d + 2)) ∧
      ∫ η : Fin (d + 2) → ℂ,
          |Real.log ‖operatorAffine profile.orderedResetWeight
              (paperOperatorAffineAtoms d η) M z (M (some center))‖ -
            Real.log (operatorAffineScale (some center)
              profile.orderedResetWeight M)| ^ 2
          ∂iidMeasure ν (d + 2) ≤
        2 * oneSidedLogSecondMomentBound
            ((max 1 (Real.pi * L)) /
              ((1 / 2 : ℝ) * Real.sqrt (c₀ / (d + 2 : ℝ)))) 1 +
          2 * (3 * (Real.log (d + 2 : ℝ)) ^ 2 + 3 * 1 +
            3 * ‖z‖ ^ 2) := by
  have h :=
    complex_paperIndicator_operatorAffineFin_memLp_two_and_integral_sq
      ν hν hL profile hc₀ hsqrt center M z hscale hνInt hνSecond
  simpa only [operatorAffine_paperOperatorAffineAtoms,
    paperOperatorAffineFamilyFin_center,
    paperOperatorAffineScaleFin_eq] using h

end ComplexIndicator

end CircularLawSection4
