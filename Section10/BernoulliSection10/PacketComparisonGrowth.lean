import BernoulliSection10.EndpointConditioningScale

open scoped BigOperators Matrix ENNReal NNReal Matrix.Norms.Frobenius
open MeasureTheory

noncomputable section

namespace BernoulliSection10

open BernoulliLinearAlgebra

local instance packetComparisonGrowthSumLinearOrder (W : ℕ) :
    LinearOrder (Fin W ⊕ Fin W) :=
  LinearOrder.lift' (fun x : Fin W ⊕ Fin W ↦ (toLex x : Fin W ⊕ₗ Fin W))
    (fun _ _ h ↦ toLex.injective h)

def packetZeroLogConstant : ℝ :=
  Real.posLog 2 + 3 * Real.posLog 4 + 3

theorem packetZeroLogConstant_nonneg : 0 ≤ packetZeroLogConstant := by
  unfold packetZeroLogConstant
  exact add_nonneg
    (add_nonneg Real.posLog_nonneg
      (mul_nonneg (by norm_num) Real.posLog_nonneg)) (by norm_num)

theorem log_threeBlockZeroComparisonConstant_fin_le_W_log_eW
    (W : ℕ) (hW : 0 < W) :
    Real.log (threeBlockZeroComparisonConstant (w := Fin W)) ≤
      packetZeroLogConstant * W * Real.log (Real.exp 1 * W) := by
  have hW1Nat : 1 ≤ W := by omega
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1Nat
  have hW0 : (0 : ℝ) ≤ W := by positivity
  have hWne : (W : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hW)
  let t := Real.posLog (W : ℝ)
  let P : ℝ := (3 * W + 1 : ℝ) ^ (3 * W)
  have hcast : ((((3 * W + 1) ^ (3 * W) : ℕ) : ℝ)) = P := by
    dsimp only [P]
    push_cast
    rfl
  have hbase1 : (1 : ℝ) ≤ 3 * W + 1 := by
    push_cast
    nlinarith
  have hP1 : 1 ≤ P := one_le_pow₀ hbase1
  have hPpos : 0 < P := zero_lt_one.trans_le hP1
  have hsum : 1 + ((((3 * W + 1) ^ (3 * W) : ℕ) : ℝ)) ≤ 2 * P := by
    rw [hcast]
    linarith
  have hlogsum :
      Real.log (1 + ((((3 * W + 1) ^ (3 * W) : ℕ) : ℝ))) ≤
        Real.log 2 + (3 * W : ℝ) * Real.log (3 * W + 1 : ℝ) := by
    calc
      Real.log (1 + ((((3 * W + 1) ^ (3 * W) : ℕ) : ℝ))) ≤
          Real.log (2 * P) :=
        Real.log_le_log (by positivity) hsum
      _ = Real.log 2 + Real.log P := by
        rw [Real.log_mul (by norm_num) hPpos.ne']
      _ = Real.log 2 + (3 * W : ℝ) * Real.log (3 * W + 1 : ℝ) := by
        dsimp only [P]
        rw [Real.log_pow]
        push_cast
        rfl
  have hbase : (3 * W + 1 : ℝ) ≤ 4 * W := by
    push_cast
    nlinarith
  have hlogbase : Real.log (3 * W + 1 : ℝ) ≤ Real.posLog 4 + t := by
    calc
      Real.log (3 * W + 1 : ℝ) ≤ Real.log (4 * W : ℝ) :=
        Real.log_le_log (by positivity) hbase
      _ = Real.log 4 + Real.log (W : ℝ) := by
        rw [Real.log_mul (by norm_num) hWne]
      _ = Real.posLog 4 + t := by
        dsimp only [t]
        rw [Real.posLog_eq_log (by norm_num),
          Real.posLog_eq_log (by
            rw [abs_of_nonneg hW0]
            exact hW1)]
  have hlog2 : Real.log (2 : ℝ) = Real.posLog 2 := by
    rw [Real.posLog_eq_log (by norm_num)]
  have hraw :
      Real.log (threeBlockZeroComparisonConstant (w := Fin W)) ≤
        Real.posLog 2 + (3 * W : ℝ) * (Real.posLog 4 + t) := by
    calc
      Real.log (threeBlockZeroComparisonConstant (w := Fin W)) ≤
          Real.log (1 + ((((3 * W + 1) ^ (3 * W) : ℕ) : ℝ))) :=
        log_threeBlockZeroComparisonConstant_fin_le W
      _ ≤ Real.log 2 + (3 * W : ℝ) * Real.log (3 * W + 1 : ℝ) := hlogsum
      _ ≤ Real.posLog 2 + (3 * W : ℝ) * (Real.posLog 4 + t) := by
        rw [hlog2]
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hlogbase
            (show 0 ≤ (3 * W : ℝ) by positivity))
  have ht : 0 ≤ t := Real.posLog_nonneg
  have h2 : 0 ≤ Real.posLog (2 : ℝ) := Real.posLog_nonneg
  have h4 : 0 ≤ Real.posLog (4 : ℝ) := Real.posLog_nonneg
  have habsorb : Real.posLog 2 + (3 * W : ℝ) * (Real.posLog 4 + t) ≤
      (W : ℝ) * (Real.posLog 2 + 3 * Real.posLog 4 + 3 * t) := by
    have htwoW : Real.posLog 2 ≤ W * Real.posLog 2 := by
      nlinarith [mul_nonneg h2 (sub_nonneg.mpr hW1)]
    push_cast
    nlinarith
  have hinner : Real.posLog 2 + 3 * Real.posLog 4 + 3 * t ≤
      packetZeroLogConstant * (1 + t) := by
    unfold packetZeroLogConstant
    nlinarith [mul_nonneg h2 ht, mul_nonneg h4 ht]
  calc
    Real.log (threeBlockZeroComparisonConstant (w := Fin W)) ≤
        Real.posLog 2 + (3 * W : ℝ) * (Real.posLog 4 + t) := hraw
    _ ≤ W * (Real.posLog 2 + 3 * Real.posLog 4 + 3 * t) := habsorb
    _ ≤ W * (packetZeroLogConstant * (1 + t)) :=
      mul_le_mul_of_nonneg_left hinner hW0
    _ = packetZeroLogConstant * W * Real.log (Real.exp 1 * W) := by
      rw [← one_add_posLog_nat_eq_log_e_mul W hW]
      ring

def packetTranslationLogConstant (z : ℂ) : ℝ :=
  3 * Real.posLog (1 + ‖z‖)

theorem packetTranslationLogConstant_nonneg (z : ℂ) :
    0 ≤ packetTranslationLogConstant z := by
  unfold packetTranslationLogConstant
  exact mul_nonneg (by norm_num) Real.posLog_nonneg

theorem log_threeBlockTranslationFactor_fin_le_W_log_eW
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    Real.log (threeBlockTranslationFactor (w := Fin W) z) ≤
      packetTranslationLogConstant z * W *
        Real.log (Real.exp 1 * W) := by
  have hcard : Fintype.card (ThreeBlockIndex (Fin W)) = 3 * W := by
    simp [ThreeBlockIndex, ThreeBlockOuter]
    omega
  have heq := log_threeBlockTranslationFactor_eq (W := Fin W) z
  rw [hcard] at heq
  have hbase1 : 1 ≤ 1 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg z)
  have hbase0 : 0 ≤ 1 + ‖z‖ := zero_le_one.trans hbase1
  have hposlog : Real.log (1 + ‖z‖) = Real.posLog (1 + ‖z‖) := by
    symm
    apply Real.posLog_eq_log
    rw [abs_of_nonneg hbase0]
    exact hbase1
  have hscale : 1 ≤ Real.log (Real.exp 1 * W) := by
    rw [← one_add_posLog_nat_eq_log_e_mul W hW]
    exact le_add_of_nonneg_right Real.posLog_nonneg
  have hcoef : 0 ≤ packetTranslationLogConstant z * W := by
    exact mul_nonneg (packetTranslationLogConstant_nonneg z) (by positivity)
  calc
    Real.log (threeBlockTranslationFactor (w := Fin W) z) =
        packetTranslationLogConstant z * W := by
      rw [heq, hposlog]
      unfold packetTranslationLogConstant
      push_cast
      ring
    _ = packetTranslationLogConstant z * W * 1 := by ring
    _ ≤ packetTranslationLogConstant z * W *
        Real.log (Real.exp 1 * W) :=
      mul_le_mul_of_nonneg_left hscale hcoef

def packetDeterministicLogConstant (z : ℂ) : ℝ :=
  packetZeroLogConstant + packetTranslationLogConstant z

theorem packetDeterministicLogConstant_nonneg (z : ℂ) :
    0 ≤ packetDeterministicLogConstant z :=
  add_nonneg packetZeroLogConstant_nonneg
    (packetTranslationLogConstant_nonneg z)

theorem log_threeBlockConcreteComparisonConstant_fin_le_W_log_eW
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    Real.log (threeBlockConcreteComparisonConstant (W := Fin W) z) ≤
      packetDeterministicLogConstant z * W *
        Real.log (Real.exp 1 * W) := by
  have hzero :=
    log_threeBlockZeroComparisonConstant_fin_le_W_log_eW W hW
  have htranslation :=
    log_threeBlockTranslationFactor_fin_le_W_log_eW W hW z
  have hzeroPos : 0 < threeBlockZeroComparisonConstant (w := Fin W) :=
    zero_lt_one.trans_le
      (threeBlockZeroComparisonConstant_one_le (w := Fin W))
  have htranslationPos : 0 < threeBlockTranslationFactor (w := Fin W) z :=
    zero_lt_one.trans_le
      (threeBlockTranslationFactor_one_le (w := Fin W) z)
  unfold threeBlockConcreteComparisonConstant
  rw [Real.log_mul hzeroPos.ne' htranslationPos.ne']
  calc
    Real.log (threeBlockZeroComparisonConstant (w := Fin W)) +
        Real.log (threeBlockTranslationFactor (w := Fin W) z) ≤
      packetZeroLogConstant * W * Real.log (Real.exp 1 * W) +
        packetTranslationLogConstant z * W *
          Real.log (Real.exp 1 * W) := add_le_add hzero htranslation
    _ = packetDeterministicLogConstant z * W *
        Real.log (Real.exp 1 * W) := by
      unfold packetDeterministicLogConstant
      ring

def packetProposition108WLogConstant (L : ℝ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (packetDeterministicLogConstant z) +
    endpointExteriorWLogConstant L

theorem proposition_10_8_integrated_endpoint_comparison
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (hTheta : IsUnit Theta.det) :
    (∫⁻ x, ENNReal.ofReal
        |Real.log (packetBoundaryCoefficientNorm z
            (normalizedBlockMatrix W x.1) (normalizedBlockMatrix W x.2)
            Theta) -
          (1 / 2 : ℝ) * Real.log (gramEnergy Theta)|
        ∂endpointBlockPairLaw W μ) ≤
      packetProposition108WLogConstant L z * oneSiteWLogScale W := by
  letI := hμ.toIsProbabilityMeasure
  let m := endpointBlockPairLaw W μ
  let c : ℝ≥0∞ := ENNReal.ofReal
    (Real.log (threeBlockConcreteComparisonConstant (W := Fin W) z))
  let g : EndpointBlockPair W → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.log (exactExteriorConditioningConstant
      (normalizedEndpointFactor W x)))
  haveI : IsProbabilityMeasure m := by
    dsimp only [m, endpointBlockPairLaw, blockAtomRowsLaw]
    infer_instance
  have hunit := normalizedEndpointFactor_det_isUnit_ae hμ W hW
  have hpoint : ∀ᵐ x ∂m,
      ENNReal.ofReal
          |Real.log (packetBoundaryCoefficientNorm z
              (normalizedBlockMatrix W x.1) (normalizedBlockMatrix W x.2)
              Theta) -
            (1 / 2 : ℝ) * Real.log (gramEnergy Theta)| ≤
        c + g x := by
    filter_upwards [hunit] with x hx
    have hprod : IsUnit
        (normalizedBlockDet W x.1 * normalizedBlockDet W x.2) := by
      simpa only [normalizedEndpointFactor_det] using hx
    have hprodNe : normalizedBlockDet W x.1 * normalizedBlockDet W x.2 ≠ 0 :=
      isUnit_iff_ne_zero.mp hprod
    have hparts := mul_ne_zero_iff.mp hprodNe
    have hCL : IsUnit (normalizedBlockMatrix W x.1).det := by
      exact isUnit_iff_ne_zero.mpr hparts.1
    have hBR : IsUnit (normalizedBlockMatrix W x.2).det := by
      exact isUnit_iff_ne_zero.mpr hparts.2
    have hpath := packetCoefficient_log_gramEnergy_pathwise
      z (normalizedBlockMatrix W x.1) (normalizedBlockMatrix W x.2)
      hCL hBR Theta hTheta
    have hthreeOne : 1 ≤
        threeBlockConcreteComparisonConstant (W := Fin W) z :=
      one_le_threeBlockConcreteComparisonConstant (W := Fin W) z
    have hextOne : 1 ≤ exactExteriorConditioningConstant
        (normalizedEndpointFactor W x) :=
      one_le_exactExteriorConditioningConstant _
    have hthreePos : 0 <
        threeBlockConcreteComparisonConstant (W := Fin W) z :=
      zero_lt_one.trans_le hthreeOne
    have hextPos : 0 < exactExteriorConditioningConstant
        (normalizedEndpointFactor W x) := zero_lt_one.trans_le hextOne
    have hsplit : Real.log (packetEndpointComparisonConstant z
          (normalizedBlockMatrix W x.1) (normalizedBlockMatrix W x.2)) =
        Real.log (threeBlockConcreteComparisonConstant (W := Fin W) z) +
          Real.log (exactExteriorConditioningConstant
            (normalizedEndpointFactor W x)) := by
      have hextPos' : 0 < exactExteriorConditioningConstant
          (endpointFactor (normalizedBlockMatrix W x.1)
            (normalizedBlockMatrix W x.2)) := by
        simpa only [normalizedEndpointFactor] using hextPos
      unfold packetEndpointComparisonConstant endpointExteriorConstant
        normalizedEndpointFactor
      exact Real.log_mul hthreePos.ne' hextPos'.ne'
    calc
      ENNReal.ofReal
          |Real.log (packetBoundaryCoefficientNorm z
              (normalizedBlockMatrix W x.1) (normalizedBlockMatrix W x.2)
              Theta) -
            (1 / 2 : ℝ) * Real.log (gramEnergy Theta)| ≤
          ENNReal.ofReal (Real.log (packetEndpointComparisonConstant z
            (normalizedBlockMatrix W x.1) (normalizedBlockMatrix W x.2))) :=
        ENNReal.ofReal_le_ofReal hpath
      _ = c + g x := by
        rw [hsplit, ENNReal.ofReal_add
          (Real.log_nonneg hthreeOne) (Real.log_nonneg hextOne)]
  have hdeterministic : c ≤
      ENNReal.ofReal (packetDeterministicLogConstant z) *
        oneSiteWLogScale W := by
    have h := ENNReal.ofReal_le_ofReal
      (log_threeBlockConcreteComparisonConstant_fin_le_W_log_eW W hW z)
    rw [show packetDeterministicLogConstant z * (W : ℝ) *
        Real.log (Real.exp 1 * W) = packetDeterministicLogConstant z *
          ((W : ℝ) * Real.log (Real.exp 1 * W)) by ring,
      ENNReal.ofReal_mul (packetDeterministicLogConstant_nonneg z)] at h
    exact h
  have hexterior := endpointExteriorConstant_log_lintegral_le_W_log_eW
    hμ W hW
  calc
    (∫⁻ x, ENNReal.ofReal
        |Real.log (packetBoundaryCoefficientNorm z
            (normalizedBlockMatrix W x.1) (normalizedBlockMatrix W x.2)
            Theta) -
          (1 / 2 : ℝ) * Real.log (gramEnergy Theta)| ∂m) ≤
        ∫⁻ x, c + g x ∂m := lintegral_mono_ae hpoint
    _ = c + ∫⁻ x, g x ∂m := by
      rw [lintegral_add_left measurable_const]
      simp
    _ ≤ ENNReal.ofReal (packetDeterministicLogConstant z) *
          oneSiteWLogScale W +
        endpointExteriorWLogConstant L * oneSiteWLogScale W := by
      exact add_le_add hdeterministic (by simpa only [g, m] using hexterior)
    _ = packetProposition108WLogConstant L z * oneSiteWLogScale W := by
      unfold packetProposition108WLogConstant
      rw [add_mul]

end BernoulliSection10
