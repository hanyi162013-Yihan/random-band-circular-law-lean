import BernoulliSection10.EndpointExteriorGrowth

open scoped BigOperators Matrix ENNReal NNReal Matrix.Norms.Frobenius
open MeasureTheory

noncomputable section

namespace BernoulliSection10

open Matrix Set Set.powersetCard
open BernoulliLinearAlgebra

local instance endpointConditioningGrowthSumLinearOrder (W : ℕ) :
    LinearOrder (Fin W ⊕ Fin W) :=
  LinearOrder.lift' (fun x : Fin W ⊕ Fin W ↦ (toLex x : Fin W ⊕ₗ Fin W))
    (fun _ _ h ↦ toLex.injective h)

theorem exactExteriorConditioningConstant_normalizedEndpointFactor_le
    (W : ℕ) (x : EndpointBlockPair W)
    (hE : IsUnit (normalizedEndpointFactor W x).det) :
    exactExteriorConditioningConstant (normalizedEndpointFactor W x) ≤
      1 + (2 * W + 1 : ℝ) *
        (‖endpointForwardFamily W x‖ +
          ‖(normalizedEndpointFactor W x).det‖⁻¹ *
            ‖endpointForwardFamily W x‖) := by
  let E := normalizedEndpointFactor W x
  let F := ‖endpointForwardFamily W x‖
  have hcard : Fintype.card (Fin W ⊕ Fin W) = 2 * W := by
    simp
    omega
  have hterm : ∀ k ∈ Finset.range (2 * W + 1),
      ‖compound k E‖ + ‖compound k E⁻¹‖ ≤
        F + ‖E.det‖⁻¹ * F := by
    intro k hk
    have hk' : k ≤ 2 * W := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    let q : Fin (2 * W + 1) := ⟨k, Finset.mem_range.mp hk⟩
    let qc : Fin (2 * W + 1) := ⟨2 * W - k, by omega⟩
    have hfwd : ‖compound k E‖ ≤ F := by
      change ‖endpointForwardFamily W x q‖ ≤ _
      exact norm_le_pi_norm _ q
    have hcomp : ‖compound (2 * W - k) E‖ ≤ F := by
      change ‖endpointForwardFamily W x qc‖ ≤ _
      exact norm_le_pi_norm _ qc
    have hinv : ‖compound k E⁻¹‖ ≤ ‖E.det‖⁻¹ * F := by
      rw [compound_inverse_norm_eq_of_isUnit E hE k (by simpa [hcard] using hk')]
      rw [hcard]
      exact mul_le_mul_of_nonneg_left hcomp
        (inv_nonneg.mpr (norm_nonneg E.det))
    exact add_le_add hfwd hinv
  unfold exactExteriorConditioningConstant
  rw [hcard]
  calc
    1 + ∑ k ∈ Finset.range (2 * W + 1),
        (‖compound k E‖ + ‖compound k E⁻¹‖) ≤
        1 + ∑ _k ∈ Finset.range (2 * W + 1),
          (F + ‖E.det‖⁻¹ * F) := by
      exact add_le_add le_rfl
        (Finset.sum_le_sum fun k hk => hterm k hk)
    _ = 1 + (2 * W + 1 : ℝ) * (F + ‖E.det‖⁻¹ * F) := by
      simp
      ring
    _ = _ := rfl

theorem exactExteriorConditioningConstant_normalizedEndpointFactor_le_coarse
    (W : ℕ) (x : EndpointBlockPair W)
    (hE : IsUnit (normalizedEndpointFactor W x).det) :
    exactExteriorConditioningConstant (normalizedEndpointFactor W x) ≤
      (4 * W + 3 : ℝ) * max 1 ‖endpointForwardFamily W x‖ *
        max 1 ‖(normalizedEndpointFactor W x).det‖⁻¹ := by
  let F := ‖endpointForwardFamily W x‖
  let D := ‖(normalizedEndpointFactor W x).det‖⁻¹
  let MF := max 1 F
  let MD := max 1 D
  have hF0 : 0 ≤ F := norm_nonneg _
  have hD0 : 0 ≤ D := inv_nonneg.mpr (norm_nonneg _)
  have hMF0 : 0 ≤ MF := le_trans zero_le_one (le_max_left _ _)
  have hMD0 : 0 ≤ MD := le_trans zero_le_one (le_max_left _ _)
  have hMF1 : 1 ≤ MF := le_max_left _ _
  have hMD1 : 1 ≤ MD := le_max_left _ _
  have hF : F ≤ MF := le_max_right _ _
  have hD : D ≤ MD := le_max_right _ _
  have hFMD : F ≤ MF * MD := by
    calc
      F ≤ MF := hF
      _ = MF * 1 := by ring
      _ ≤ MF * MD := mul_le_mul_of_nonneg_left hMD1 hMF0
  have hDF : D * F ≤ MF * MD := by
    calc
      D * F ≤ MD * MF := mul_le_mul hD hF hF0 hMD0
      _ = MF * MD := by ring
  have hsum : F + D * F ≤ 2 * (MF * MD) := by linarith
  have hprod : 1 ≤ MF * MD := by
    simpa only [one_mul] using
      (mul_le_mul hMF1 hMD1 zero_le_one hMF0)
  have hn : 0 ≤ (2 * W + 1 : ℝ) := by positivity
  calc
    exactExteriorConditioningConstant (normalizedEndpointFactor W x) ≤
        1 + (2 * W + 1 : ℝ) * (F + D * F) := by
      simpa only [F, D] using
        exactExteriorConditioningConstant_normalizedEndpointFactor_le W x hE
    _ ≤ 1 + (2 * W + 1 : ℝ) * (2 * (MF * MD)) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hn)
    _ ≤ MF * MD + (2 * W + 1 : ℝ) * (2 * (MF * MD)) :=
      add_le_add hprod le_rfl
    _ = (4 * W + 3 : ℝ) * MF * MD := by
      push_cast
      ring
    _ = _ := rfl

theorem log_exactExteriorConditioningConstant_normalizedEndpointFactor_le
    (W : ℕ) (x : EndpointBlockPair W)
    (hE : IsUnit (normalizedEndpointFactor W x).det) :
    Real.log
        (exactExteriorConditioningConstant (normalizedEndpointFactor W x)) ≤
      Real.posLog (4 * W + 3 : ℝ) +
        Real.posLog ‖endpointForwardFamily W x‖ +
        Real.posLog ‖(normalizedEndpointFactor W x).det‖⁻¹ := by
  let K := exactExteriorConditioningConstant (normalizedEndpointFactor W x)
  let F := ‖endpointForwardFamily W x‖
  let D := ‖(normalizedEndpointFactor W x).det‖⁻¹
  let MF := max 1 F
  let MD := max 1 D
  let C : ℝ := 4 * W + 3
  have hK1 : 1 ≤ K := one_le_exactExteriorConditioningConstant _
  have hK0 : 0 ≤ K := zero_le_one.trans hK1
  have hF0 : 0 ≤ F := norm_nonneg _
  have hD0 : 0 ≤ D := inv_nonneg.mpr (norm_nonneg _)
  have hMF0 : 0 ≤ MF := le_trans zero_le_one (le_max_left _ _)
  have hMD0 : 0 ≤ MD := le_trans zero_le_one (le_max_left _ _)
  have hMF1 : 1 ≤ MF := le_max_left _ _
  have hMD1 : 1 ≤ MD := le_max_left _ _
  have hcoarse : K ≤ C * MF * MD := by
    simpa only [K, C, MF, MD, F, D] using
      exactExteriorConditioningConstant_normalizedEndpointFactor_le_coarse
        W x hE
  have hmono : Real.posLog K ≤ Real.posLog (C * MF * MD) :=
    Real.posLog_le_posLog hK0 hcoarse
  have houter := Real.posLog_mul (x := C) (y := MF * MD)
  have hinner := Real.posLog_mul (x := MF) (y := MD)
  have hMFlog : Real.posLog MF = Real.posLog F := by
    rw [Real.posLog_eq_log (by
      rw [abs_of_nonneg hMF0]
      exact hMF1)]
    exact (Real.posLog_eq_log_max_one hF0).symm
  have hMDlog : Real.posLog MD = Real.posLog D := by
    rw [Real.posLog_eq_log (by
      rw [abs_of_nonneg hMD0]
      exact hMD1)]
    exact (Real.posLog_eq_log_max_one hD0).symm
  have hKlog : Real.posLog K = Real.log K := by
    apply Real.posLog_eq_log
    rw [abs_of_nonneg hK0]
    exact hK1
  dsimp only [C, F, D] at *
  rw [hKlog] at hmono
  rw [mul_assoc] at hmono
  rw [hMFlog, hMDlog] at hinner
  linarith

theorem measurable_endpointDeterminantLoss (W : ℕ) :
    Measurable (endpointDeterminantLoss W) := by
  unfold endpointDeterminantLoss
  exact ((measurable_blockDetLoss W).comp measurable_fst).add
    ((measurable_blockDetLoss W).comp measurable_snd)

def endpointExteriorLogIntegralBound (L : ℝ) (W : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.posLog (4 * W + 3 : ℝ)) +
    endpointForwardWLogIntegralBound L W +
    2 * (multiAffineLogCost L (List.replicate W W) +
      ENNReal.ofReal
        (Real.posLog ((2 : ℝ) ^ W * |blockNormalization W|⁻¹ ^ W)))

theorem endpointExteriorConstant_log_lintegral_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) :
    (∫⁻ x, ENNReal.ofReal
        (Real.log (exactExteriorConditioningConstant
          (normalizedEndpointFactor W x)))
        ∂endpointBlockPairLaw W μ) ≤
      endpointExteriorLogIntegralBound L W := by
  letI := hμ.toIsProbabilityMeasure
  let m := endpointBlockPairLaw W μ
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.posLog (4 * W + 3 : ℝ))
  let f : EndpointBlockPair W → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.posLog ‖endpointForwardFamily W x‖)
  let d : EndpointBlockPair W → ℝ≥0∞ := endpointDeterminantLoss W
  haveI : IsProbabilityMeasure m := by
    dsimp only [m, endpointBlockPairLaw, blockAtomRowsLaw]
    infer_instance
  have hd : Measurable d := by
    simpa only [d] using measurable_endpointDeterminantLoss W
  have hunit := normalizedEndpointFactor_det_isUnit_ae hμ W hW
  have hpoint : ∀ᵐ x ∂m,
      ENNReal.ofReal
          (Real.log (exactExteriorConditioningConstant
            (normalizedEndpointFactor W x))) ≤
        c + f x + d x := by
    filter_upwards [hunit] with x hx
    have hlog :=
      log_exactExteriorConditioningConstant_normalizedEndpointFactor_le
        W x hx
    calc
      ENNReal.ofReal
          (Real.log (exactExteriorConditioningConstant
            (normalizedEndpointFactor W x))) ≤
          ENNReal.ofReal
            (Real.posLog (4 * W + 3 : ℝ) +
              Real.posLog ‖endpointForwardFamily W x‖ +
              Real.posLog ‖(normalizedEndpointFactor W x).det‖⁻¹) :=
        ENNReal.ofReal_le_ofReal hlog
      _ = c + f x + ENNReal.ofReal
          (Real.posLog ‖(normalizedEndpointFactor W x).det‖⁻¹) := by
        rw [ENNReal.ofReal_add
          (add_nonneg Real.posLog_nonneg Real.posLog_nonneg)
          Real.posLog_nonneg,
          ENNReal.ofReal_add Real.posLog_nonneg Real.posLog_nonneg]
      _ ≤ c + f x + d x := by
        simpa only [d] using
          add_le_add (show c + f x ≤ c + f x from le_rfl)
            (normalizedEndpointFactor_detLoss_le W x)
  have hforward := endpointForwardFamily_posLog_lintegral_le hμ W hW
  have hdet := endpointDeterminantLoss_lintegral_le hμ W hW
  calc
    (∫⁻ x, ENNReal.ofReal
        (Real.log (exactExteriorConditioningConstant
          (normalizedEndpointFactor W x))) ∂m) ≤
        ∫⁻ x, c + (f x + d x) ∂m := by
      apply lintegral_mono_ae
      filter_upwards [hpoint] with x hx
      simpa only [add_assoc] using hx
    _ = c + (∫⁻ x, f x ∂m) + ∫⁻ x, d x ∂m := by
      rw [lintegral_add_left measurable_const]
      rw [lintegral_add_right _ hd]
      simp
      rw [add_assoc]
    _ ≤ c + endpointForwardWLogIntegralBound L W +
        2 * (multiAffineLogCost L (List.replicate W W) +
          ENNReal.ofReal
            (Real.posLog
              ((2 : ℝ) ^ W * |blockNormalization W|⁻¹ ^ W))) := by
      exact add_le_add (add_le_add le_rfl (by simpa only [f, m] using hforward))
        (by simpa only [d, m] using hdet)
    _ = endpointExteriorLogIntegralBound L W := rfl

end BernoulliSection10
