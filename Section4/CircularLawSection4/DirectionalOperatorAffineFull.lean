import CircularLawSection4.DirectionalFreshClosure
import CircularLawSection4.PaperOperatorAffineL2

/-!
# Full directional operator-affine logarithmic estimate

The conditional directional density supplies the negative logarithmic half.
The positive half is proved only after transport to the actual IID complex
atom law and therefore uses the manuscript's unconditional second moment.
-/

open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory
open MeasureTheory Set ProbabilityTheory

noncomputable section

namespace CircularLawSection4

set_option maxHeartbeats 4000000

/-- Reconstructing every coordinate of a directionally split vector gives
the original complex operator-affine expression. -/
theorem reconstructedDirectionalOperatorAffine_split_eq
    {n : ℕ} (phase : ℝ) (b : Fin n → ℂ) (x : Fin n → ℂ)
    {E F : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (M : Fin n → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F) :
    reconstructedDirectionalOperatorAffine phase b
        ((directionalSplitVector n phase x).1)
        ((directionalSplitVector n phase x).2) M z M₀ =
      operatorAffine b x M z M₀ := by
  unfold reconstructedDirectionalOperatorAffine
  apply congrArg (fun ξ => operatorAffine b ξ M z M₀)
  funext i
  exact reconstructedDirectionalAtom_parts phase (x i)

/-- Multiplying a deterministic coefficient by the rotation phase does not
change the norm of its scalarized slope. -/
theorem norm_reconstructedDirectionalWeight_mul
    {n : ℕ} (phase : ℝ) (b : Fin n → ℂ) (s : Fin n) (w : ℂ) :
    ‖reconstructedDirectionalWeight phase b s * w‖ = ‖b s * w‖ := by
  have ha : ‖Complex.exp ((phase : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  unfold reconstructedDirectionalWeight
  rw [mul_assoc, norm_mul, norm_mul, ha]
  simp only [one_mul]
  exact (norm_mul (b s) w).symm

/-- Joint small-ball bound for the reconstructed operator under the
heterogeneous conditional directional product. -/
theorem directionalProduct_joint_reconstructedOperatorAffine_smallBall
    {n : ℕ} (D : DirectionalProductModel (n + 1))
    {L : ℝ≥0∞}
    (hinterval : ∀ v i,
      RealIntervalBound (D.coordinateLaw v i : Measure ℝ) L)
    (phase : ℝ)
    {E F : Type*}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (s : Fin (n + 1)) (b : Fin (n + 1) → ℂ)
    (M : Fin (n + 1) → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F)
    (x₀ : E) (ell : StrongDual ℂ F) (hx₀ : ‖x₀‖ ≤ 1)
    (hell : ‖ell‖ ≤ 1) {ε ρ : ℝ} (hρ : 0 ≤ ρ) (hε : 0 < ε)
    (hslope : ε ≤ ‖b s * ell (M s x₀)‖) :
    D.jointMeasure
        {vu | ‖reconstructedDirectionalOperatorAffine phase b
          vu.1 vu.2 M z M₀‖ ≤ ε * ρ} ≤
      (4 : ℝ≥0∞) * L * ENNReal.ofReal ρ := by
  let good : Set ((Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :=
    {vu | ‖reconstructedDirectionalOperatorAffine phase b
      vu.1 vu.2 M z M₀‖ ≤ ε * ρ}
  have hreconstruct : Continuous (fun vu :
      (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        fun i => reconstructedDirectionalAtom phase (vu.1 i) (vu.2 i)) := by
    apply continuous_pi
    intro i
    unfold reconstructedDirectionalAtom
    fun_prop
  have hgood : MeasurableSet good := by
    change MeasurableSet
      ((fun vu : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        ‖operatorAffine b
          (fun i => reconstructedDirectionalAtom phase (vu.1 i) (vu.2 i))
          M z M₀‖) ⁻¹' Iic (ε * ρ))
    exact ((continuous_operatorAffine_fin b M z M₀).comp hreconstruct).norm
      |>.measurable measurableSet_Iic
  let _ := D.conditionalULaw_isMarkov
  rw [DirectionalProductModel.jointMeasure, Measure.compProd_apply hgood]
  calc
    (∫⁻ v, D.conditionalULaw v (Prod.mk v ⁻¹' good)
        ∂(D.vLaw : Measure (Fin (n + 1) → ℝ))) ≤
      ∫⁻ _v, (4 : ℝ≥0∞) * L * ENNReal.ofReal ρ
        ∂(D.vLaw : Measure (Fin (n + 1) → ℝ)) := by
      apply lintegral_mono
      intro v
      change D.conditionalULaw v
          {u | ‖reconstructedDirectionalOperatorAffine phase b
            v u M z M₀‖ ≤ ε * ρ} ≤ _
      have hslope' : ε ≤
          ‖reconstructedDirectionalWeight phase b s * ell (M s x₀)‖ := by
        rw [norm_reconstructedDirectionalWeight_mul]
        exact hslope
      simpa only [reconstructedDirectionalOperatorAffine_eq_realInput] using
        directionalProduct_fiber_operatorAffine_smallBall D hinterval v s
          (reconstructedDirectionalWeight phase b) M 1
          (-(reconstructedDirectionalCenter phase b v M z M₀))
          x₀ ell hx₀ hell hρ hε hslope'
    _ = (4 : ℝ≥0∞) * L * ENNReal.ofReal ρ := by simp

/-- Actual-IID small-ball theorem under the raw directional-density
hypothesis. -/
theorem iid_complex_operatorAffine_smallBall_of_directionalDensity
    {n : ℕ} (atom : ProbabilityMeasure ℂ) (phase L : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L)
    {E F : Type*}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (s : Fin (n + 1)) (b : Fin (n + 1) → ℂ)
    (M : Fin (n + 1) → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F)
    (x₀ : E) (ell : StrongDual ℂ F) (hx₀ : ‖x₀‖ ≤ 1)
    (hell : ‖ell‖ ≤ 1) {ε ρ : ℝ} (hρ : 0 ≤ ρ) (hε : 0 < ε)
    (hslope : ε ≤ ‖b s * ell (M s x₀)‖) :
    iidMeasure (atom : Measure ℂ) (n + 1)
        {x | ‖operatorAffine b x M z M₀‖ ≤ ε * ρ} ≤
      (4 : ℝ≥0∞) * ENNReal.ofReal L * ENNReal.ofReal ρ := by
  let D := paperDirectionalProductModel (n + 1) atom phase L hdir
  let T := directionalSplitVector (n + 1) phase
  let good : Set ((Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :=
    {vu | ‖reconstructedDirectionalOperatorAffine phase b
      vu.1 vu.2 M z M₀‖ ≤ ε * ρ}
  have hreconstruct : Continuous (fun vu :
      (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        fun i => reconstructedDirectionalAtom phase (vu.1 i) (vu.2 i)) := by
    apply continuous_pi
    intro i
    unfold reconstructedDirectionalAtom
    fun_prop
  have hgood : MeasurableSet good := by
    change MeasurableSet
      ((fun vu : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        ‖operatorAffine b
          (fun i => reconstructedDirectionalAtom phase (vu.1 i) (vu.2 i))
          M z M₀‖) ⁻¹' Iic (ε * ρ))
    exact ((continuous_operatorAffine_fin b M z M₀).comp hreconstruct).norm
      |>.measurable measurableSet_Iic
  have hpreimage :
      {x | ‖operatorAffine b x M z M₀‖ ≤ ε * ρ} = T ⁻¹' good := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, good, T]
    rw [reconstructedDirectionalOperatorAffine_split_eq]
  have hT := iidAtom_directionalSplit_measurePreserving
    (n + 1) atom phase L hdir
  calc
    iidMeasure (atom : Measure ℂ) (n + 1)
        {x | ‖operatorAffine b x M z M₀‖ ≤ ε * ρ} =
      D.jointMeasure good := by
        rw [hpreimage, ← Measure.map_apply hT.measurable hgood, hT.map_eq]
    _ ≤ (4 : ℝ≥0∞) * ENNReal.ofReal L * ENNReal.ofReal ρ :=
      directionalProduct_joint_reconstructedOperatorAffine_smallBall D
        (paperDirectionalProductModel_intervalBound (n + 1)
          atom phase L hdir) phase s b M z M₀ x₀ ell hx₀ hell
          hρ hε hslope

/-- Negative `L²` logarithmic half for an actual complex IID
operator-affine expression under directional conditional density. -/
theorem iid_complex_operatorAffine_logDeficit_L2_of_directionalDensity
    {n : ℕ} (atom : ProbabilityMeasure ℂ) (phase L : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) (hL : 0 ≤ L)
    {E F : Type*}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (s : Fin (n + 1)) (b : Fin (n + 1) → ℂ)
    (M : Fin (n + 1) → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F)
    (x₀ : E) (ell : StrongDual ℂ F) (hx₀ : ‖x₀‖ ≤ 1)
    (hell : ‖ell‖ ≤ 1) (scale theta : ℝ)
    (hscale : 0 < scale) (htheta : 0 < theta)
    (hslope : theta * scale ≤ ‖b s * ell (M s x₀)‖) :
    let radius : (Fin (n + 1) → ℂ) → ℝ := fun x =>
      ‖operatorAffine b x M z M₀‖
    iidMeasure (atom : Measure ℂ) (n + 1) {x | radius x = 0} = 0 ∧
      MemLp (fun x => logDeficit scale (radius x)) 2
        (iidMeasure (atom : Measure ℂ) (n + 1)) ∧
      ∫ x, logDeficit scale (radius x) ^ 2
          ∂iidMeasure (atom : Measure ℂ) (n + 1) ≤
        oneSidedLogSecondMomentBound ((4 * L) / theta) 1 := by
  let radius : (Fin (n + 1) → ℂ) → ℝ := fun x =>
    ‖operatorAffine b x M z M₀‖
  have hradius : Measurable radius :=
    (continuous_operatorAffine_fin b M z M₀).norm.measurable
  have hradius0 : ∀ x, 0 ≤ radius x := fun x => norm_nonneg _
  let _ := iidMeasure_isProbability (atom : Measure ℂ) (n + 1)
  apply zeroSet_memLp_two_and_integral_sq_logDeficit_of_threshold_linearSmallBall
    (iidMeasure (atom : Measure ℂ) (n + 1)) radius hradius hradius0
      scale theta (4 * L) hscale htheta (mul_nonneg (by norm_num) hL)
  intro ρ hρ
  calc
    iidMeasure (atom : Measure ℂ) (n + 1)
        {x | radius x ≤ theta * scale * ρ} ≤
      (4 : ℝ≥0∞) * ENNReal.ofReal L * ENNReal.ofReal ρ := by
        exact iid_complex_operatorAffine_smallBall_of_directionalDensity
          atom phase L hdir s b M z M₀ x₀ ell hx₀ hell hρ.le
            (mul_pos htheta hscale) hslope
    _ = ENNReal.ofReal ((4 * L) * ρ) := by
      rw [← ENNReal.ofReal_ofNat 4,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
        ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hL)]

/-! ### Paper-weight specialization and the full two-sided estimate -/

/-- Full two-sided operator-affine logarithmic `L²` estimate on the actual
flat complex IID vector under the raw directional-density hypothesis. -/
theorem complex_paperIndicator_operatorAffineFin_absLog_L2_directional
    {d : ℕ} {c₀ C₀ : ℝ} {E F : Type*}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (atom : ProbabilityMeasure ℂ) (phase L : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1))
    (M : ResetLabel (d + 1) → E →L[ℂ] F) (z : ℂ)
    (hscale : 0 < operatorAffineScale (some center)
      profile.orderedResetWeight M)
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (atom : Measure ℂ))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(atom : Measure ℂ) ≤ 1) :
    let b := paperOperatorAffineWeightFin profile
    let MF := paperOperatorAffineFamilyFin M
    let i₀ := paperOperatorAffineCenterFin center
    let scale := operatorAffineScale i₀ b MF
    iidMeasure (atom : Measure ℂ) (d + 2)
        {η | ‖operatorAffine b η MF z (MF i₀)‖ = 0} = 0 ∧
      MemLp (fun η : Fin (d + 2) → ℂ =>
        |Real.log ‖operatorAffine b η MF z (MF i₀)‖ - Real.log scale|)
        2 (iidMeasure (atom : Measure ℂ) (d + 2)) ∧
      ∫ η : Fin (d + 2) → ℂ,
          |Real.log ‖operatorAffine b η MF z (MF i₀)‖ -
            Real.log scale| ^ 2 ∂iidMeasure (atom : Measure ℂ) (d + 2) ≤
        2 * oneSidedLogSecondMomentBound
            ((4 * L) /
              ((1 / 2 : ℝ) * Real.sqrt (c₀ / (d + 2 : ℝ)))) 1 +
          2 * (3 * (Real.log (d + 2 : ℝ)) ^ 2 + 3 + 3 * ‖z‖ ^ 2) := by
  let b := paperOperatorAffineWeightFin profile
  let MF := paperOperatorAffineFamilyFin M
  let i₀ := paperOperatorAffineCenterFin center
  let scale := operatorAffineScale i₀ b MF
  let q := Real.sqrt (c₀ / (d + 2 : ℝ))
  let theta := (1 / 2 : ℝ) * q
  let μ := iidMeasure (atom : Measure ℂ) (d + 2)
  let radius : (Fin (d + 2) → ℂ) → ℝ := fun η =>
    ‖operatorAffine b η MF z (MF i₀)‖
  letI : IsProbabilityMeasure μ :=
    iidMeasure_isProbability (atom : Measure ℂ) (d + 2)
  have hq : 0 < q := by
    dsimp only [q]
    exact Real.sqrt_pos.2 (div_pos hc₀ (by positivity))
  have htheta : 0 < theta := by
    dsimp only [theta]
    positivity
  have hscaleFin : 0 < scale := by
    dsimp only [scale, i₀, b, MF]
    rw [paperOperatorAffineScaleFin_eq]
    exact hscale
  have hbcenter : q ≤ ‖b i₀‖ := by
    dsimp only [q, b, i₀]
    simpa using
      profile.sqrt_lower_le_norm_orderedResetWeight (some center)
  obtain ⟨s, x, ell, hx, hell, hslope⟩ :=
    exists_large_scalarized_slope i₀ b MF hq hsqrt hbcenter
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      hscaleFin
  obtain ⟨hzero, hnegativeLp, hnegative⟩ :=
    iid_complex_operatorAffine_logDeficit_L2_of_directionalDensity
      atom phase L hdir hL s b MF z (MF i₀) x ell hx.le hell
        scale theta hscaleFin htheta hslope.le
  have hradiusMeas : Measurable radius := by
    dsimp only [radius]
    exact (continuous_operatorAffine_fin b MF z (MF i₀)).norm.measurable
  have hradiusPos : ∀ᵐ η ∂μ, 0 < radius η := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp
      (by simpa only [μ, radius] using hzero)] with η hη
    have hne : radius η ≠ 0 := by
      simpa only [Set.mem_ofPred_eq] using hη
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  have hcoord : ∀ i : Fin (d + 2),
      Integrable (fun η : Fin (d + 2) → ℂ => ‖η i‖ ^ 2) μ ∧
        ∫ η : Fin (d + 2) → ℂ, ‖η i‖ ^ 2 ∂μ ≤ 1 := by
    intro i
    simpa only [μ] using
      iidMeasure_coordinate_norm_sq_integrable_and_integral_le_one
        i hsecondInt hsecond
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
      (by simpa only [radius] using hradiusPos) 1 hscaledInt hscaled
  obtain ⟨hfullLp, hfull⟩ :=
    memLp_two_and_integral_sq_abs_log_sub_log_of_parts
      scale hnegativeLp hpositiveLp hnegative hpositive
  refine ⟨?_, hfullLp, ?_⟩
  · simpa only [μ, radius] using hzero
  · simpa only [b, MF, i₀, scale, q, theta, μ, radius,
      Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat, mul_one, one_mul]
      using hfull

/-- Reset-labelled paper-coordinate form of the full directional
operator-affine `L²` theorem. -/
theorem complex_paperIndicator_operatorAffine_absLog_L2_directional
    {d : ℕ} {c₀ C₀ : ℝ} {E F : Type*}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (atom : ProbabilityMeasure ℂ) (phase L : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1))
    (M : ResetLabel (d + 1) → E →L[ℂ] F) (z : ℂ)
    (hscale : 0 < operatorAffineScale (some center)
      profile.orderedResetWeight M)
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (atom : Measure ℂ))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(atom : Measure ℂ) ≤ 1) :
    let radius := fun η : Fin (d + 2) → ℂ =>
      ‖operatorAffine profile.orderedResetWeight
        (paperOperatorAffineAtoms d η) M z (M (some center))‖
    let scale := operatorAffineScale (some center)
      profile.orderedResetWeight M
    iidMeasure (atom : Measure ℂ) (d + 2) {η | radius η = 0} = 0 ∧
      MemLp (fun η => |Real.log (radius η) - Real.log scale|)
        2 (iidMeasure (atom : Measure ℂ) (d + 2)) ∧
      ∫ η, |Real.log (radius η) - Real.log scale| ^ 2
          ∂iidMeasure (atom : Measure ℂ) (d + 2) ≤
        2 * oneSidedLogSecondMomentBound
            ((4 * L) /
              ((1 / 2 : ℝ) * Real.sqrt (c₀ / (d + 2 : ℝ)))) 1 +
          2 * (3 * (Real.log (d + 2 : ℝ)) ^ 2 + 3 + 3 * ‖z‖ ^ 2) := by
  have h := complex_paperIndicator_operatorAffineFin_absLog_L2_directional
    atom phase L hdir hL profile hc₀ hsqrt center M z hscale
      hsecondInt hsecond
  simpa only [operatorAffine_paperOperatorAffineAtoms,
    paperOperatorAffineFamilyFin_center,
    paperOperatorAffineScaleFin_eq] using h

end CircularLawSection4
