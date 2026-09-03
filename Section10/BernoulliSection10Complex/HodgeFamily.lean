import BernoulliSection10Complex.HodgeEnvelope

/-!
# Simultaneous exterior-degree Hodge control

This file packages every exterior degree of a one-site cleared transfer into
one finite dependent product.  Its sup norm is the maximum of the individual
Frobenius norms.  Applying Corollary 10.3 once to this family avoids the extra
factor `2W+1` that would result from summing the separate first-moment bounds.
-/

open scoped BigOperators Matrix ENNReal NNReal Matrix.Norms.Frobenius
open MeasureTheory

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open Matrix Set Set.powersetCard
open BernoulliLinearAlgebra

set_option maxHeartbeats 800000

/-- The dependent finite family of all one-site cleared exterior operators. -/
abbrev OneSiteClearedFamily (W : ℕ) :=
  (r : Fin (2 * W + 1)) →
    Matrix (powersetCard (Fin W ⊕ Fin W) r.1)
      (powersetCard (Fin W ⊕ Fin W) r.1) ℂ

/-- All exterior degrees, in recursive row coordinates. -/
def oneSiteClearedFamilyRecursiveFunction (W : ℕ) (z : ℂ) :
    MultiAffineRows (List.replicate (1 * W) (3 * W)) →
      OneSiteClearedFamily W := fun y r ↦
  intervalClearedProduct W 1 z
    (multiAffineRowsToFinRows (3 * W) (1 * W) y) r

/-- The concrete canonical coefficient tensor of the simultaneous family. -/
def oneSiteClearedFamilyTensor (W : ℕ) (z : ℂ) :=
  multiAffineTensorOfFunction (oneSiteClearedFamilyRecursiveFunction W z)

theorem oneSiteClearedFamilyRecursiveFunction_isMultiAffine
    (W : ℕ) (z : ℂ) :
    IsMultiAffine (oneSiteClearedFamilyRecursiveFunction W z) := by
  apply isMultiAffine_comp_multiAffineRowsToFinRows
    (p := 3 * W) (n := 1 * W)
    (F := fun x r ↦ intervalClearedProduct W 1 z x r)
  intro x i u v t
  funext r
  exact intervalClearedProduct_update_line W 1 z x r i u v t

theorem oneSiteClearedFamilyRecursiveFunction_ne_zero
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    oneSiteClearedFamilyRecursiveFunction W z ≠ 0 := by
  intro hzero
  let r₀ : Fin (2 * W + 1) := ⟨0, by omega⟩
  have hvalue := congrFun hzero (identityMultiAffineRows W 1)
  have hr := congrFun hvalue r₀
  exact identityMultiAffineRows_product_ne_zero W 1 hW z r₀ hr

/-- Corollary 10.3 applied once to all exterior degrees simultaneously. -/
theorem oneSiteClearedFamily_log_deviation_recursive
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ y, ENNReal.ofReal
        |Real.log ‖oneSiteClearedFamilyRecursiveFunction W z y‖ -
          Real.log ‖oneSiteClearedFamilyTensor W z‖|
        ∂multiAffineRowLaw μ (List.replicate (1 * W) (3 * W))) ≤
        multiAffineLogCost L (List.replicate (1 * W) (3 * W)) ∧
      ∀ᵐ y ∂multiAffineRowLaw μ (List.replicate (1 * W) (3 * W)),
        oneSiteClearedFamilyRecursiveFunction W z y ≠ 0 := by
  have hpos : ∀ p ∈ List.replicate (1 * W) (3 * W), 0 < p := by
    intro p hp
    simp only [List.mem_replicate] at hp
    omega
  simpa only [oneSiteClearedFamilyTensor] using
    corollary_10_3 hμ
      (oneSiteClearedFamilyRecursiveFunction_isMultiAffine W z) hpos
      (oneSiteClearedFamilyRecursiveFunction_ne_zero W hW z)

/-- All exterior degrees, in the paper's flat physical-row coordinates. -/
def oneSiteClearedFamily (W : ℕ) (z : ℂ)
    (x : IntervalRows W 1) : OneSiteClearedFamily W :=
  oneSiteClearedFamilyRecursiveFunction W z
    (finRowsToMultiAffineRows (3 * W) (1 * W) x)

theorem oneSiteClearedFamily_log_deviation
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal
        |Real.log ‖oneSiteClearedFamily W z x‖ -
          Real.log ‖oneSiteClearedFamilyTensor W z‖|
        ∂intervalRowsLaw W 1 μ) ≤
        multiAffineLogCost L (List.replicate (1 * W) (3 * W)) ∧
      ∀ᵐ x ∂intervalRowsLaw W 1 μ,
        oneSiteClearedFamily W z x ≠ 0 := by
  letI := hμ.toIsProbabilityMeasure
  let e := finRowsMultiAffineRowsMeasurableEquiv (3 * W) (1 * W)
  have hmp : MeasurePreserving e (intervalRowsLaw W 1 μ)
      (multiAffineRowLaw μ (List.replicate (1 * W) (3 * W))) := by
    simpa only [intervalRowsLaw, physicalRowLaw] using
      finRowsMultiAffineRows_measurePreserving μ (3 * W) (1 * W)
  have hrec := oneSiteClearedFamily_log_deviation_recursive hμ W hW z
  constructor
  · have heq := hmp.lintegral_comp_emb e.measurableEmbedding
      (fun y ↦ ENNReal.ofReal
        |Real.log ‖oneSiteClearedFamilyRecursiveFunction W z y‖ -
          Real.log ‖oneSiteClearedFamilyTensor W z‖|)
    calc
      (∫⁻ x, ENNReal.ofReal
          |Real.log ‖oneSiteClearedFamily W z x‖ -
            Real.log ‖oneSiteClearedFamilyTensor W z‖|
          ∂intervalRowsLaw W 1 μ) =
          ∫⁻ y, ENNReal.ofReal
            |Real.log ‖oneSiteClearedFamilyRecursiveFunction W z y‖ -
              Real.log ‖oneSiteClearedFamilyTensor W z‖|
            ∂multiAffineRowLaw μ (List.replicate (1 * W) (3 * W)) := by
        simpa only [oneSiteClearedFamily, e,
          finRowsMultiAffineRowsMeasurableEquiv_apply] using heq
      _ ≤ multiAffineLogCost L (List.replicate (1 * W) (3 * W)) := hrec.1
  · have hrecMap : ∀ᵐ y ∂Measure.map e (intervalRowsLaw W 1 μ),
        oneSiteClearedFamilyRecursiveFunction W z y ≠ 0 := by
      rw [hmp.map_eq]
      exact hrec.2
    have hflat := e.measurableEmbedding.ae_map_iff.mp hrecMap
    simpa only [oneSiteClearedFamily, e,
      finRowsMultiAffineRowsMeasurableEquiv_apply] using hflat

/-- The sharp-in-the-number-of-degrees forward envelope.  Its remaining
deterministic datum is one simultaneous coefficient-tensor norm, rather than
a sum of `2W+1` separate tensor norms. -/
def oneSiteForwardMaxIntegralBound (L : ℝ) (W : ℕ) (z : ℂ) : ℝ≥0∞ :=
  multiAffineLogCost L (List.replicate (1 * W) (3 * W)) +
    ENNReal.ofReal (Real.posLog ‖oneSiteClearedFamilyTensor W z‖)

theorem oneSiteClearedFamily_posLog_lintegral_le
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal
        (Real.posLog ‖oneSiteClearedFamily W z x‖)
        ∂intervalRowsLaw W 1 μ) ≤
      oneSiteForwardMaxIntegralBound L W z := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (intervalRowsLaw W 1 μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  have hdev := oneSiteClearedFamily_log_deviation hμ W hW z
  have hpoint (x : IntervalRows W 1) :
      ENNReal.ofReal (Real.posLog ‖oneSiteClearedFamily W z x‖) ≤
        ENNReal.ofReal
            |Real.log ‖oneSiteClearedFamily W z x‖ -
              Real.log ‖oneSiteClearedFamilyTensor W z‖| +
          ENNReal.ofReal
            (Real.posLog ‖oneSiteClearedFamilyTensor W z‖) := by
    calc
      ENNReal.ofReal (Real.posLog ‖oneSiteClearedFamily W z x‖) ≤
          ENNReal.ofReal
            (|Real.log ‖oneSiteClearedFamily W z x‖ -
                Real.log ‖oneSiteClearedFamilyTensor W z‖| +
              Real.posLog ‖oneSiteClearedFamilyTensor W z‖) :=
        ENNReal.ofReal_le_ofReal
          (posLog_le_abs_log_sub_log_add_posLog
            ‖oneSiteClearedFamily W z x‖
            ‖oneSiteClearedFamilyTensor W z‖)
      _ = _ := ENNReal.ofReal_add (abs_nonneg _)
        (Real.posLog_nonneg
          (x := ‖oneSiteClearedFamilyTensor W z‖))
  calc
    (∫⁻ x, ENNReal.ofReal
        (Real.posLog ‖oneSiteClearedFamily W z x‖)
        ∂intervalRowsLaw W 1 μ) ≤
        ∫⁻ x, (ENNReal.ofReal
            |Real.log ‖oneSiteClearedFamily W z x‖ -
              Real.log ‖oneSiteClearedFamilyTensor W z‖| +
          ENNReal.ofReal
            (Real.posLog ‖oneSiteClearedFamilyTensor W z‖))
          ∂intervalRowsLaw W 1 μ := lintegral_mono hpoint
    _ = (∫⁻ x, ENNReal.ofReal
          |Real.log ‖oneSiteClearedFamily W z x‖ -
            Real.log ‖oneSiteClearedFamilyTensor W z‖|
          ∂intervalRowsLaw W 1 μ) +
        ENNReal.ofReal
          (Real.posLog ‖oneSiteClearedFamilyTensor W z‖) := by
      rw [lintegral_add_right _ measurable_const]
      simp
    _ ≤ oneSiteForwardMaxIntegralBound L W z := by
      exact add_le_add hdev.1 le_rfl

/-- Every exterior degree is controlled by the simultaneous sup norm. -/
theorem oneSiteCleared_posLog_le_family
    (W : ℕ) (z : ℂ) (x : IntervalRows W 1)
    (r : Fin (2 * W + 1)) :
    Real.posLog ‖intervalClearedProduct W 1 z x r‖ ≤
      Real.posLog ‖oneSiteClearedFamily W z x‖ := by
  apply Real.posLog_le_posLog (norm_nonneg _)
  change ‖intervalClearedProduct W 1 z x r‖ ≤
    ‖oneSiteClearedFamily W z x‖
  have hx : oneSiteClearedFamily W z x r =
      intervalClearedProduct W 1 z x r := by
    unfold oneSiteClearedFamily oneSiteClearedFamilyRecursiveFunction
    rw [multiAffineRowsToFinRows_leftInverse]
  rw [← hx]
  exact norm_le_pi_norm (oneSiteClearedFamily W z x) r

theorem continuous_oneSiteClearedFamily (W : ℕ) (z : ℂ) :
    Continuous (oneSiteClearedFamily W z) := by
  apply continuous_pi
  intro r
  have h := continuous_intervalClearedProduct W 1 z r
  simpa only [oneSiteClearedFamily,
    oneSiteClearedFamilyRecursiveFunction,
    multiAffineRowsToFinRows_leftInverse] using h

/-- The maximum, rather than the sum, of the forward exterior-degree losses. -/
def oneSiteForwardMaxLoss (W : ℕ) (z : ℂ)
    (x : IntervalRows W 1) : ℝ :=
  Real.posLog ‖oneSiteClearedFamily W z x‖

theorem measurable_oneSiteForwardMaxLoss (W : ℕ) (z : ℂ) :
    Measurable (oneSiteForwardMaxLoss W z) := by
  exact Real.continuous_posLog.measurable.comp
    (continuous_oneSiteClearedFamily W z).norm.measurable

/-- A simultaneous one-site Hodge envelope whose forward term pays for all
exterior degrees only once. -/
def oneSiteMaxHodgeEnvelope (W : ℕ) (z : ℂ)
    (x : IntervalRows W 1) : ℝ :=
  2 * oneSiteForwardMaxLoss W z x +
    Real.posLog ‖oneSiteBDet W z x‖⁻¹ +
    Real.posLog ‖oneSiteCDet W z x‖⁻¹

theorem oneSiteMaxHodgeEnvelope_nonneg
    (W : ℕ) (z : ℂ) (x : IntervalRows W 1) :
    0 ≤ oneSiteMaxHodgeEnvelope W z x := by
  unfold oneSiteMaxHodgeEnvelope oneSiteForwardMaxLoss
  exact add_nonneg
    (add_nonneg (mul_nonneg (by norm_num) Real.posLog_nonneg)
      Real.posLog_nonneg)
    Real.posLog_nonneg

theorem measurable_oneSiteMaxHodgeEnvelope (W : ℕ) (z : ℂ) :
    Measurable (oneSiteMaxHodgeEnvelope W z) := by
  unfold oneSiteMaxHodgeEnvelope
  have hB : Measurable (oneSiteBDet W z) :=
    (continuous_intervalSiteB W 1 z 0).matrix_det.measurable
  have hC : Measurable (oneSiteCDet W z) :=
    (continuous_intervalSiteC W 1 z 0).matrix_det.measurable
  exact ((measurable_const.mul (measurable_oneSiteForwardMaxLoss W z)).add
    (Real.continuous_posLog.measurable.comp hB.norm.inv)).add
      (Real.continuous_posLog.measurable.comp hC.norm.inv)

/-- Deterministic Hodge control using the simultaneous exterior family. -/
theorem oneSiteMaxHodgeEnvelope_controls
    (W : ℕ) (z : ℂ) (x : IntervalRows W 1)
    (hB : IsUnit (oneSiteBDet W z x))
    (hC : IsUnit (oneSiteCDet W z x))
    (r : Fin (2 * W + 1)) :
    Real.posLog ‖clearedStepCompound r.1 (intervalSiteBlocks z x 0).B
        (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C‖ +
      Real.posLog ‖(clearedStepCompound r.1 (intervalSiteBlocks z x 0).B
        (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C)⁻¹‖ ≤
      oneSiteMaxHodgeEnvelope W z x := by
  let X := intervalSiteBlocks z x 0
  let F := oneSiteForwardMaxLoss W z x
  let dB := Real.posLog ‖oneSiteBDet W z x‖⁻¹
  let dC := Real.posLog ‖oneSiteCDet W z x‖⁻¹
  have hr : r.1 ≤ Fintype.card (Fin W ⊕ Fin W) := by
    simp
    omega
  have hcard : Fintype.card (Fin W ⊕ Fin W) = 2 * W := by
    simp
    omega
  have hinv := clearedStepCompound_inverse_norm_eq_complement
    r.1 hr X.B X.D X.C hB hC
  rw [hcard] at hinv
  have hfwd : Real.posLog ‖clearedStepCompound r.1 X.B X.D X.C‖ ≤ F := by
    change Real.posLog ‖clearedStepCompound r.1
      (intervalSiteBlocks z x 0).B (intervalSiteBlocks z x 0).D
      (intervalSiteBlocks z x 0).C‖ ≤
        oneSiteForwardMaxLoss W z x
    have hfamily := oneSiteCleared_posLog_le_family W z x r
    rw [intervalClearedProduct_one] at hfamily
    simpa only [intervalClearedStep, oneSiteForwardMaxLoss] using hfamily
  let rc : Fin (2 * W + 1) := ⟨2 * W - r.1, by omega⟩
  have hcomp :
      Real.posLog ‖clearedStepCompound (2 * W - r.1) X.B X.D X.C‖ ≤ F := by
    change Real.posLog ‖clearedStepCompound rc.1
      (intervalSiteBlocks z x 0).B (intervalSiteBlocks z x 0).D
      (intervalSiteBlocks z x 0).C‖ ≤
        oneSiteForwardMaxLoss W z x
    have hfamily := oneSiteCleared_posLog_le_family W z x rc
    rw [intervalClearedProduct_one] at hfamily
    simpa only [intervalClearedStep, oneSiteForwardMaxLoss] using hfamily
  have hdet :
      Real.posLog ‖X.B.det * X.C.det‖⁻¹ ≤ dB + dC := by
    have hmul := Real.posLog_mul (x := ‖X.B.det‖⁻¹) (y := ‖X.C.det‖⁻¹)
    simpa only [norm_mul, mul_inv, X, dB, dC, oneSiteBDet,
      oneSiteCDet] using hmul
  have hinvloss :
      Real.posLog ‖(clearedStepCompound r.1 X.B X.D X.C)⁻¹‖ ≤
        F + dB + dC := by
    rw [hinv, div_eq_mul_inv]
    calc
      Real.posLog
          (‖clearedStepCompound (2 * W - r.1) X.B X.D X.C‖ *
            ‖X.B.det * X.C.det‖⁻¹) ≤
          Real.posLog ‖clearedStepCompound (2 * W - r.1) X.B X.D X.C‖ +
            Real.posLog ‖X.B.det * X.C.det‖⁻¹ := Real.posLog_mul
      _ ≤ F + (dB + dC) := add_le_add hcomp hdet
      _ = F + dB + dC := by ring
  change Real.posLog ‖clearedStepCompound r.1 X.B X.D X.C‖ +
      Real.posLog ‖(clearedStepCompound r.1 X.B X.D X.C)⁻¹‖ ≤ _
  calc
    _ ≤ F + (F + dB + dC) := add_le_add hfwd hinvloss
    _ = 2 * F + dB + dC := by ring
    _ = oneSiteMaxHodgeEnvelope W z x := by rfl

def oneSiteMaxHodgeIntegralBound (L : ℝ) (W : ℕ) (z : ℂ) : ℝ≥0∞ :=
  2 * oneSiteForwardMaxIntegralBound L W z +
    2 * oneSiteInterfaceDetIntegralBound L W

/-- First moment of the simultaneous one-site Hodge envelope. -/
theorem oneSiteMaxHodgeEnvelope_lintegral_le
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal (oneSiteMaxHodgeEnvelope W z x)
        ∂intervalRowsLaw W 1 μ) ≤
      oneSiteMaxHodgeIntegralBound L W z := by
  let F : IntervalRows W 1 → ℝ := oneSiteForwardMaxLoss W z
  let b : IntervalRows W 1 → ℝ := fun x ↦
    Real.posLog ‖oneSiteBDet W z x‖⁻¹
  let c : IntervalRows W 1 → ℝ := fun x ↦
    Real.posLog ‖oneSiteCDet W z x‖⁻¹
  let FE : IntervalRows W 1 → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (F x)
  let bE : IntervalRows W 1 → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (b x)
  let cE : IntervalRows W 1 → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (c x)
  have hF (x : IntervalRows W 1) : 0 ≤ F x := Real.posLog_nonneg
  have hb (x : IntervalRows W 1) : 0 ≤ b x := Real.posLog_nonneg
  have hc (x : IntervalRows W 1) : 0 ≤ c x := Real.posLog_nonneg
  have hFE : Measurable FE :=
    (measurable_oneSiteForwardMaxLoss W z).ennreal_ofReal
  have hbE : Measurable bE := by
    unfold bE b
    have hdet : Measurable (oneSiteBDet W z) :=
      (continuous_intervalSiteB W 1 z 0).matrix_det.measurable
    exact (Real.continuous_posLog.measurable.comp hdet.norm.inv).ennreal_ofReal
  have hcE : Measurable cE := by
    unfold cE c
    have hdet : Measurable (oneSiteCDet W z) :=
      (continuous_intervalSiteC W 1 z 0).matrix_det.measurable
    exact (Real.continuous_posLog.measurable.comp hdet.norm.inv).ennreal_ofReal
  have hsplit (x : IntervalRows W 1) :
      ENNReal.ofReal (oneSiteMaxHodgeEnvelope W z x) =
        2 * FE x + bE x + cE x := by
    change ENNReal.ofReal (2 * F x + b x + c x) =
      2 * ENNReal.ofReal (F x) + ENNReal.ofReal (b x) +
        ENNReal.ofReal (c x)
    calc
      ENNReal.ofReal (2 * F x + b x + c x) =
          ENNReal.ofReal (2 * F x + b x) + ENNReal.ofReal (c x) :=
        ENNReal.ofReal_add
          (add_nonneg (mul_nonneg (by norm_num) (hF x)) (hb x)) (hc x)
      _ = (ENNReal.ofReal (2 * F x) + ENNReal.ofReal (b x)) +
          ENNReal.ofReal (c x) := by
        rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) (hF x)) (hb x)]
      _ = 2 * ENNReal.ofReal (F x) + ENNReal.ofReal (b x) +
          ENNReal.ofReal (c x) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  have hforward := oneSiteClearedFamily_posLog_lintegral_le hμ W hW z
  have hB := oneSiteBDet_posLog_inv_lintegral_explicit_le hμ W hW z
  have hC := oneSiteCDet_posLog_inv_lintegral_explicit_le hμ W hW z
  calc
    (∫⁻ x, ENNReal.ofReal (oneSiteMaxHodgeEnvelope W z x)
        ∂intervalRowsLaw W 1 μ) =
        ∫⁻ x, (2 * FE x + bE x + cE x)
          ∂intervalRowsLaw W 1 μ := lintegral_congr hsplit
    _ = 2 * (∫⁻ x, FE x ∂intervalRowsLaw W 1 μ) +
          (∫⁻ x, bE x ∂intervalRowsLaw W 1 μ) +
          (∫⁻ x, cE x ∂intervalRowsLaw W 1 μ) := by
      rw [lintegral_add_right (fun x ↦ 2 * FE x + bE x) hcE,
        lintegral_add_right (fun x ↦ 2 * FE x) hbE,
        lintegral_const_mul 2 hFE]
    _ ≤ 2 * oneSiteForwardMaxIntegralBound L W z +
          oneSiteInterfaceDetIntegralBound L W +
          oneSiteInterfaceDetIntegralBound L W := by
      apply add_le_add
      · apply add_le_add
        · gcongr
          simpa only [FE, F, oneSiteForwardMaxLoss] using hforward
        · simpa only [bE, b, oneSiteInterfaceDetIntegralBound] using hB
      · simpa only [cE, c, oneSiteInterfaceDetIntegralBound] using hC
    _ = oneSiteMaxHodgeIntegralBound L W z := by
      unfold oneSiteMaxHodgeIntegralBound
      ring

/-- The logarithm of the simultaneous exterior-family norm has finite second
moment in recursive row coordinates. -/
theorem oneSiteClearedFamilyLog_recursive_memLp_two
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    MemLp (fun y : MultiAffineRows (List.replicate (1 * W) (3 * W)) ↦
        Real.log ‖oneSiteClearedFamilyRecursiveFunction W z y‖) 2
      (multiAffineRowLaw μ (List.replicate (1 * W) (3 * W))) := by
  letI := hμ.toIsProbabilityMeasure
  let c := oneSiteClearedFamilyTensor W z
  have hpos : ∀ p ∈ List.replicate (1 * W) (3 * W), 0 < p := by
    intro p hp
    simp only [List.mem_replicate] at hp
    omega
  have hcenter : MemLp (fun y ↦
      Real.log ‖multiAffineEval c y‖ - Real.log ‖c‖) 2
      (multiAffineRowLaw μ (List.replicate (1 * W) (3 * W))) :=
    multiAffineEval_log_memLp_two hμ hpos c
  have hconst : MemLp (fun _ :
      MultiAffineRows (List.replicate (1 * W) (3 * W)) ↦ Real.log ‖c‖) 2
      (multiAffineRowLaw μ (List.replicate (1 * W) (3 * W))) :=
    memLp_const _
  have hfull := hcenter.add hconst
  apply MemLp.ae_eq _ hfull
  filter_upwards [] with y
  change (Real.log ‖multiAffineEval c y‖ - Real.log ‖c‖) +
      Real.log ‖c‖ =
        Real.log ‖oneSiteClearedFamilyRecursiveFunction W z y‖
  rw [sub_add_cancel]
  exact congrArg (fun q ↦ Real.log ‖q‖)
    (congrFun
      (oneSiteClearedFamilyRecursiveFunction_isMultiAffine W z).eval_tensorOfFunction y)

theorem oneSiteClearedFamilyLog_memLp_two
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    MemLp (fun x : IntervalRows W 1 ↦
        Real.log ‖oneSiteClearedFamily W z x‖) 2
      (intervalRowsLaw W 1 μ) := by
  letI := hμ.toIsProbabilityMeasure
  let e := finRowsMultiAffineRowsMeasurableEquiv (3 * W) (1 * W)
  have hmp : MeasurePreserving e (intervalRowsLaw W 1 μ)
      (multiAffineRowLaw μ (List.replicate (1 * W) (3 * W))) := by
    simpa only [intervalRowsLaw, physicalRowLaw] using
      finRowsMultiAffineRows_measurePreserving μ (3 * W) (1 * W)
  have hflat :=
    (oneSiteClearedFamilyLog_recursive_memLp_two hμ W hW z).comp_measurePreserving hmp
  apply MemLp.ae_eq _ hflat
  filter_upwards [] with x
  simp only [oneSiteClearedFamily, Function.comp_apply, e,
    finRowsMultiAffineRowsMeasurableEquiv_apply]

theorem oneSiteForwardMaxLoss_memLp_two
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    MemLp (oneSiteForwardMaxLoss W z) 2 (intervalRowsLaw W 1 μ) := by
  have h := (oneSiteClearedFamilyLog_memLp_two hμ W hW z).pos_part
  apply MemLp.ae_eq _ h
  filter_upwards [] with x
  simp only [oneSiteForwardMaxLoss, Real.posLog_apply, max_comm]

theorem oneSiteMaxHodgeEnvelope_memLp_two
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    MemLp (oneSiteMaxHodgeEnvelope W z) 2 (intervalRowsLaw W 1 μ) := by
  unfold oneSiteMaxHodgeEnvelope
  exact (((oneSiteForwardMaxLoss_memLp_two hμ W hW z).const_mul 2).add
    (oneSiteBDet_posLog_inv_memLp_two hμ W z)).add
      (oneSiteCDet_posLog_inv_memLp_two hμ W z)

theorem oneSiteMaxHodgeEnvelope_integrable
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    Integrable (oneSiteMaxHodgeEnvelope W z) (intervalRowsLaw W 1 μ) := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (intervalRowsLaw W 1 μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  exact (oneSiteMaxHodgeEnvelope_memLp_two hμ W hW z).integrable one_le_two

/-- Almost-sure simultaneous Hodge domination with no caller-supplied
nonvanishing certificate. -/
theorem oneSiteMaxHodgeEnvelope_controls_ae
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    ∀ᵐ x ∂intervalRowsLaw W 1 μ, ∀ r : Fin (2 * W + 1),
      Real.posLog ‖clearedStepCompound r.1 (intervalSiteBlocks z x 0).B
          (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C‖ +
        Real.posLog ‖(clearedStepCompound r.1 (intervalSiteBlocks z x 0).B
          (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C)⁻¹‖ ≤
        oneSiteMaxHodgeEnvelope W z x := by
  filter_upwards [oneSiteInterfaceDets_isUnit_ae hμ W hW z] with x hx
  intro r
  exact oneSiteMaxHodgeEnvelope_controls W z x hx.1 hx.2 r

end BernoulliSection10Complex
