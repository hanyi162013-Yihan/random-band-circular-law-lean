/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Proposition34Uniform.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.ConcreteEtaNet
import Vendor.Arxiv2410.V3.McDiarmidArithmetic
import Vendor.Arxiv2410.V3.RateArithmetic
import Vendor.Arxiv2410.V3.TraceMeasurability

/-!
# The common `eta` event in v3 Proposition 3.4

This file combines the explicit net in `ConcreteEtaNet.lean` with the proved resolvent
Lipschitz estimate and the internal McDiarmid theorem.  The constant `C_D = 16` used elsewhere
in the reconstruction actually gives a pointwise four-tail bound `4 n⁻³²`.  The net below has
cardinality at most `n¹⁴`; hence the complete finite union still costs at most `n⁻¹⁰`.

Thus neither existence of a net nor a finite-union probability budget is an input.
-/

namespace Arxiv2410V3

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory Matrix.Norms.L2Operator

noncomputable section

/-- Mesh used for v3 Proposition 3.4.  At this mesh, the resolvent-continuity loss is `1/2`. -/
def etaUniformMesh (v0 : ℝ) : ℝ := v0 ^ 2 / 4

theorem etaUniformMesh_pos {v0 : ℝ} (hv0 : 0 < v0) :
    0 < etaUniformMesh v0 := by
  simp only [etaUniformMesh]
  positivity

/-- The explicit net used in the uniform proposition. -/
noncomputable def proposition34EtaNet (v0 : ℝ) (hv0 : 0 < v0) :
    FiniteEtaNet (EtaGridIndex v0 (etaUniformMesh v0)) (EtaDomainAtScale v0) :=
  concreteEtaNet v0 (etaUniformMesh v0) hv0 (etaUniformMesh_pos hv0)

/-- The lower imaginary cutoff written in v3 Proposition 3.4. -/
def proposition34EtaScale (n : ℕ) (B cPrime : ℝ) : ℝ :=
  Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n cPrime

/-- The fully explicit centre-index type at the v3 scale. -/
abbrev Proposition34EtaGridIndex (n : ℕ) (B cPrime : ℝ) :=
  EtaGridIndex (proposition34EtaScale n B cPrime)
    (etaUniformMesh (proposition34EtaScale n B cPrime))

/-- The fully explicit v3 net, with its scale positivity derived from `B > 0` and `n > 0`. -/
noncomputable def proposition34PaperEtaNet
    (n : ℕ) (B cPrime : ℝ) (hB : 0 < B) (hn : 0 < n) :
    FiniteEtaNet (Proposition34EtaGridIndex n B cPrime)
      (EtaDomainAtScale (proposition34EtaScale n B cPrime)) :=
  proposition34EtaNet (proposition34EtaScale n B cPrime)
    (corollary35_scale_pos hB (by exact_mod_cast hn))

/-- At the chosen mesh, `v0⁻² * radius = 1/2`. -/
theorem proposition34EtaNet_lipschitz_margin
    {v0 : ℝ} (hv0 : 0 < v0) :
    v0⁻¹ ^ 2 * (proposition34EtaNet v0 hv0).radius = 1 / 2 := by
  change v0⁻¹ ^ 2 * (2 * (v0 ^ 2 / 4)) = 1 / 2
  field_simp [hv0.ne']
  ring

/-- Deterministic v3 `(3.10)` closure for the explicit net. -/
theorem proposition34_gridGood_subset_uniformTraceGood
    {Omega : Type*} {n : ℕ} [NeZero n]
    (matrix : Omega → Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {v0 C : ℝ} (hv0 : 0 < v0) :
    (proposition34EtaNet v0 hv0).gridGood
        (fun omega eta ↦ stieltjesTrace (matrix omega) z eta) C ⊆
      UniformEtaGood (EtaDomainAtScale v0)
        (fun omega eta ↦ stieltjesTrace (matrix omega) z eta) (C + 1 / 2) := by
  have h := stieltjesTrace_gridGood_subset_uniformEtaGood
    (proposition34EtaNet v0 hv0) matrix z hv0
    (fun eta heta ↦ heta.2.2) (C := C)
  rwa [proposition34EtaNet_lipschitz_margin hv0] at h

/-- Coarse scale fact used only in the cardinality ledger.  It follows from `B <= n` and
`c' >= 0`; no asymptotics are involved. -/
theorem one_le_nat_mul_proposition34_scale
    {n : ℕ} (hn : 1 ≤ n) {B cPrime : ℝ}
    (hB : 0 < B) (hBn : B ≤ n) (hcPrime : 0 ≤ cPrime) :
    1 ≤ (n : ℝ) *
      (Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n cPrime) := by
  have hnPos : (0 : ℝ) < n := by positivity
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hneg : -(1 / 8 : ℝ) < 0 := by norm_num
  have hpowReverse :
      Real.rpow (n : ℝ) (-(1 / 8 : ℝ)) ≤
        Real.rpow B (-(1 / 8 : ℝ)) :=
    (Real.rpow_le_rpow_iff_of_neg hnPos hB hneg).2 (by exact_mod_cast hBn)
  have hnSevenEighth : 1 ≤ Real.rpow (n : ℝ) (7 / 8 : ℝ) :=
    Real.one_le_rpow hnOne (by norm_num)
  have hnTimesNegative :
      1 ≤ (n : ℝ) * Real.rpow (n : ℝ) (-(1 / 8 : ℝ)) := by
    calc
      1 ≤ Real.rpow (n : ℝ) (7 / 8 : ℝ) := hnSevenEighth
      _ = (n : ℝ) * Real.rpow (n : ℝ) (-(1 / 8 : ℝ)) := by
        calc
          Real.rpow (n : ℝ) (7 / 8 : ℝ) =
              Real.rpow (n : ℝ) (1 + (-(1 / 8 : ℝ))) := by norm_num
          _ = Real.rpow (n : ℝ) 1 *
              Real.rpow (n : ℝ) (-(1 / 8 : ℝ)) := Real.rpow_add hnPos _ _
          _ = (n : ℝ) * Real.rpow (n : ℝ) (-(1 / 8 : ℝ)) := by
            simp
  have hbase :
      1 ≤ (n : ℝ) * Real.rpow B (-(1 / 8 : ℝ)) := by
    calc
      1 ≤ (n : ℝ) * Real.rpow (n : ℝ) (-(1 / 8 : ℝ)) := hnTimesNegative
      _ ≤ (n : ℝ) * Real.rpow B (-(1 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpowReverse hnPos.le
  have hcPow : 1 ≤ Real.rpow (n : ℝ) cPrime :=
    Real.one_le_rpow hnOne hcPrime
  calc
    1 = 1 * 1 := by ring
    _ ≤ ((n : ℝ) * Real.rpow B (-(1 / 8 : ℝ))) *
        Real.rpow n cPrime := mul_le_mul hbase hcPow zero_le_one (by positivity)
    _ = (n : ℝ) *
        (Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n cPrime) := by ring

/-- The explicit two-dimensional net has polynomial size.  The deliberately loose exponent
`14` leaves ample room for the final `n⁻¹⁰` union bound. -/
theorem etaGridIndex_uniformMesh_card_le_pow_fourteen
    {n : ℕ} (hn : 2 ≤ n) {v0 : ℝ} (hv0 : 0 < v0)
    (hcoarse : 1 ≤ (n : ℝ) * v0) :
    (Fintype.card (EtaGridIndex v0 (etaUniformMesh v0)) : ℝ) ≤
      (n : ℝ) ^ 14 := by
  have hnPos : (0 : ℝ) < n := by positivity
  have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := one_le_two.trans hnTwo
  have hv0sq : 0 < v0 ^ 2 := sq_pos_of_pos hv0
  have hmulSq : 1 ≤ (n : ℝ) ^ 2 * v0 ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) * v0 - 1),
      pow_le_pow_left₀ zero_le_one hcoarse 2]
  have hratio : 5 / etaUniformMesh v0 ≤ 20 * (n : ℝ) ^ 2 := by
    rw [etaUniformMesh]
    have hid : 5 / (v0 ^ 2 / 4) = 20 / v0 ^ 2 := by
      field_simp [hv0.ne']
      ring
    rw [hid]
    apply (div_le_iff₀ hv0sq).2
    nlinarith
  have hratio0 : 0 ≤ 5 / etaUniformMesh v0 :=
    div_nonneg (by norm_num) (etaUniformMesh_pos hv0).le
  have hceil := Nat.ceil_lt_add_one hratio0
  have hsteps :
      (etaGridSteps (etaUniformMesh v0) : ℝ) ≤ 21 * (n : ℝ) ^ 2 := by
    have hstepslt :
        (etaGridSteps (etaUniformMesh v0) : ℝ) < 21 * (n : ℝ) ^ 2 := by
      calc
        (etaGridSteps (etaUniformMesh v0) : ℝ) =
            (Nat.ceil (5 / etaUniformMesh v0) : ℝ) + 1 := by
          simp [etaGridSteps]
        _ < 5 / etaUniformMesh v0 + 2 := by linarith
        _ ≤ 20 * (n : ℝ) ^ 2 + 2 := by linarith
        _ < 21 * (n : ℝ) ^ 2 := by nlinarith
    exact hstepslt.le
  have hcardNat := etaGridIndex_card_le v0 (etaUniformMesh v0)
  have hcard :
      (Fintype.card (EtaGridIndex v0 (etaUniformMesh v0)) : ℝ) ≤
        2 * (etaGridSteps (etaUniformMesh v0) : ℝ) ^ 2 := by
    exact_mod_cast hcardNat
  have hcardPolynomial :
      (Fintype.card (EtaGridIndex v0 (etaUniformMesh v0)) : ℝ) ≤
        882 * (n : ℝ) ^ 4 := by
    calc
      (Fintype.card (EtaGridIndex v0 (etaUniformMesh v0)) : ℝ) ≤
          2 * (etaGridSteps (etaUniformMesh v0) : ℝ) ^ 2 := hcard
      _ ≤ 2 * (21 * (n : ℝ) ^ 2) ^ 2 := by gcongr
      _ = 882 * (n : ℝ) ^ 4 := by ring
  have h882 : (882 : ℝ) ≤ (n : ℝ) ^ 10 := by
    calc
      (882 : ℝ) ≤ 2 ^ 10 := by norm_num
      _ ≤ (n : ℝ) ^ 10 := pow_le_pow_left₀ (by norm_num) hnTwo 10
  calc
    (Fintype.card (EtaGridIndex v0 (etaUniformMesh v0)) : ℝ) ≤
        882 * (n : ℝ) ^ 4 := hcardPolynomial
    _ ≤ (n : ℝ) ^ 10 * (n : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_right h882 (pow_nonneg hnPos.le 4)
    _ = (n : ℝ) ^ 14 := by rw [← pow_add]

/-- Specialization of the preceding exact cardinality proof to the v3 scale
`B⁻¹/⁸ n^(c')`. -/
theorem proposition34EtaGrid_card_le_pow_fourteen
    {n : ℕ} (hn : 2 ≤ n) {B cPrime : ℝ}
    (hB : 0 < B) (hBn : B ≤ n) (hcPrime : 0 ≤ cPrime) :
    (Fintype.card (EtaGridIndex
      (Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n cPrime)
      (etaUniformMesh
        (Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n cPrime))) : ℝ) ≤
      (n : ℝ) ^ 14 := by
  have hnOne : 1 ≤ n := by omega
  have hv0 : 0 < Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n cPrime :=
    corollary35_scale_pos hB (by positivity)
  exact etaGridIndex_uniformMesh_card_le_pow_fourteen hn hv0
    (one_le_nat_mul_proposition34_scale hnOne hB hBn hcPrime)

/-- The exponent arithmetic behind `C_D = 16`, before discarding its large slack. -/
theorem four_exp_mcdiarmid_threshold_sixteen_le_four_mul_zpow_neg32
    {n : ℕ} (hn : 2 ≤ n) {v : ℝ} (hv : 0 < v) {c : ℕ → ℝ≥0}
    (hc : ∀ i < n, (c i : ℝ) ≤ 2 / ((n : ℝ) * v))
    (hpos : ∃ i < n, 0 < c i) :
    4 * exp
      (-((16 * sqrt (log (n : ℝ)) / (sqrt (n : ℝ) * v)) / 2) ^ 2 /
        (2 * (((∑ i ∈ Finset.range n, (c i / 2) ^ 2 : ℝ≥0)) : ℝ))) ≤
      4 * (n : ℝ) ^ (-32 : ℤ) := by
  have hnNat : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hnOne : (1 : ℝ) ≤ n := by
    exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 0 ≤ log (n : ℝ) := log_nonneg hnOne
  have hsqrtn : 0 < sqrt (n : ℝ) := sqrt_pos.2 hnR
  have hnv2 : 0 < (n : ℝ) * v ^ 2 := mul_pos hnR (sq_pos_of_pos hv)
  let S : ℝ := (((∑ i ∈ Finset.range n, (c i / 2) ^ 2 : ℝ≥0)) : ℝ)
  have hSpos : 0 < S := mcdiarmid_proxy_sum_pos_of_one_pos hpos
  have hSle : S ≤ 1 / ((n : ℝ) * v ^ 2) :=
    mcdiarmid_proxy_sum_le_of_row_sensitivity hnNat hv hc
  have hnumerator :
      ((16 * sqrt (log (n : ℝ)) / (sqrt (n : ℝ) * v)) / 2) ^ 2 =
        64 * log (n : ℝ) / ((n : ℝ) * v ^ 2) := by
    field_simp [hsqrtn.ne', hv.ne', hnR.ne']
    nlinarith [sq_sqrt hlog, sq_sqrt hnR.le]
  have hnum_nonneg : 0 ≤ 64 * log (n : ℝ) / ((n : ℝ) * v ^ 2) := by positivity
  have hquotient :
      32 * log (n : ℝ) ≤
        ((16 * sqrt (log (n : ℝ)) / (sqrt (n : ℝ) * v)) / 2) ^ 2 /
          (2 * S) := by
    rw [hnumerator]
    calc
      32 * log (n : ℝ) =
          (64 * log (n : ℝ) / ((n : ℝ) * v ^ 2)) /
            (2 / ((n : ℝ) * v ^ 2)) := by
        field_simp [hnv2.ne']
        ring
      _ ≤ (64 * log (n : ℝ) / ((n : ℝ) * v ^ 2)) / (2 * S) := by
        apply div_le_div_of_nonneg_left hnum_nonneg (by positivity)
        calc
          2 * S ≤ 2 * (1 / ((n : ℝ) * v ^ 2)) :=
            mul_le_mul_of_nonneg_left hSle (by norm_num)
          _ = 2 / ((n : ℝ) * v ^ 2) := by ring
  have hexp :
      exp
          (-((16 * sqrt (log (n : ℝ)) / (sqrt (n : ℝ) * v)) / 2) ^ 2 /
            (2 * S)) ≤ exp (-(32 * log (n : ℝ))) := by
    exact exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hquotient)
  have hexpPower : exp (-(32 * log (n : ℝ))) = (n : ℝ) ^ (-32 : ℤ) := by
    rw [show -(32 * log (n : ℝ)) = log ((n : ℝ) ^ (-32 : ℤ)) by
      rw [log_zpow]
      norm_num]
    exact exp_log (zpow_pos hnR _)
  change 4 * exp
      (-((16 * sqrt (log (n : ℝ)) / (sqrt (n : ℝ) * v)) / 2) ^ 2 /
        (2 * S)) ≤ 4 * (n : ℝ) ^ (-32 : ℤ)
  calc
    4 * exp
        (-((16 * sqrt (log (n : ℝ)) / (sqrt (n : ℝ) * v)) / 2) ^ 2 /
          (2 * S)) ≤ 4 * exp (-(32 * log (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = 4 * (n : ℝ) ^ (-32 : ℤ) := by rw [hexpPower]

/-- The explicit net cardinality can be paid from the `n⁻³²` pointwise tail. -/
theorem card_mul_four_zpow_neg32_le_zpow_neg10
    {n : ℕ} (hn : 2 ≤ n) {K : ℕ} (hK : (K : ℝ) ≤ (n : ℝ) ^ 18) :
    (K : ℝ) * (4 * (n : ℝ) ^ (-32 : ℤ)) ≤ (n : ℝ) ^ (-10 : ℤ) := by
  have hnR : (0 : ℝ) < n := by positivity
  have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hfour : (4 : ℝ) ≤ (n : ℝ) ^ 4 := by
    calc
      (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnTwo 2
      _ ≤ (n : ℝ) ^ 4 :=
        pow_le_pow_right₀ (one_le_two.trans hnTwo) (by norm_num)
  rw [show (-32 : ℤ) = -(32 : ℤ) by norm_num,
    show (-10 : ℤ) = -(10 : ℤ) by norm_num, zpow_neg, zpow_neg]
  rw [inv_eq_one_div, inv_eq_one_div]
  calc
    (K : ℝ) * (4 * (1 / (n : ℝ) ^ 32)) =
        ((K : ℝ) * 4) / (n : ℝ) ^ 32 := by ring
    _ ≤ 1 / (n : ℝ) ^ 10 := by
      apply (div_le_div_iff₀ (pow_pos hnR 32) (pow_pos hnR 10)).2
      calc
        (K : ℝ) * 4 * (n : ℝ) ^ 10 ≤
            (n : ℝ) ^ 18 * (n : ℝ) ^ 4 * (n : ℝ) ^ 10 := by
          gcongr
        _ = 1 * (n : ℝ) ^ 32 := by rw [one_mul, ← pow_add, ← pow_add]

/-- Convert a probability lower bound into the corresponding failure upper bound. -/
theorem measure_compl_le_of_probabilityAtLeast_one_sub
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {good : Set Omega} (hmeas : MeasurableSet good)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hprob : ProbabilityAtLeast mu good (1 - q)) :
    mu goodᶜ ≤ ENNReal.ofReal q := by
  have hprobReal :=
    (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (by finiteness)).mpr hprob
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hq1)] at hprobReal
  change 1 - q ≤ mu.real good at hprobReal
  apply (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hq0]
  change mu.real goodᶜ ≤ q
  rw [probReal_compl_eq_one_sub hmeas]
  linarith

/-- A pointwise row-McDiarmid certificate gives the unrelaxed `4 n⁻³²` failure estimate. -/
theorem measure_compl_complexConcentrationGood_le_four_zpow_neg32
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {filtration : Filtration ℕ mOmega}
    {trace : Omega → ℂ} (htraceMeasurable : Measurable trace)
    (htraceIntegrable : Integrable trace mu)
    {n : ℕ} (hn : 2 ≤ n) {v : ℝ} (hv : 0 < v)
    {sensitivity : ℕ → ℝ≥0}
    (hsensitivity : ∀ i < n,
      (sensitivity i : ℝ) ≤ 2 / ((n : ℝ) * v))
    (hsensitivityPos : ∃ i < n, 0 < sensitivity i)
    (hre : DoobIntervalCertificate (filtration := filtration) (mu := mu)
      (fun omega ↦ (trace omega).re) n sensitivity)
    (him : DoobIntervalCertificate (filtration := filtration) (mu := mu)
      (fun omega ↦ (trace omega).im) n sensitivity) :
    mu (ComplexConcentrationGood trace (∫ omega, trace omega ∂mu)
      (16 * sqrt (log (n : ℝ)) / (sqrt (n : ℝ) * v)))ᶜ ≤
        ENNReal.ofReal (4 * (n : ℝ) ^ (-32 : ℤ)) := by
  let bound : ℝ := 16 * sqrt (log (n : ℝ)) / (sqrt (n : ℝ) * v)
  let tail : ℝ := 4 * exp (-(bound / 2) ^ 2 /
    (2 * (((∑ i ∈ Finset.range n,
      (sensitivity i / 2) ^ 2 : ℝ≥0)) : ℝ)))
  have hbase := probabilityAtLeast_complexConcentrationGood_of_boundedDoobDifferences
    htraceMeasurable htraceIntegrable hre.toBoundedDoobDifferences
      him.toBoundedDoobDifferences (bound := bound) (by
        dsimp only [bound]
        positivity)
  have htail : tail ≤ 4 * (n : ℝ) ^ (-32 : ℤ) := by
    exact four_exp_mcdiarmid_threshold_sixteen_le_four_mul_zpow_neg32
      hn hv hsensitivity hsensitivityPos
  have hq0 : 0 ≤ 4 * (n : ℝ) ^ (-32 : ℤ) := by positivity
  have hq10 : 4 * (n : ℝ) ^ (-32 : ℤ) ≤ (n : ℝ) ^ (-10 : ℤ) :=
    by
      have hnOne : (1 : ℝ) ≤ n := by
        exact_mod_cast (by omega : 1 ≤ n)
      have h := card_mul_four_zpow_neg32_le_zpow_neg10 hn (K := 1)
        (by simpa using (one_le_pow₀ hnOne : (1 : ℝ) ≤ (n : ℝ) ^ 18))
      simpa using h
  have hq1 : 4 * (n : ℝ) ^ (-32 : ℤ) ≤ 1 := by
    have hnR : (0 : ℝ) < n := by positivity
    have hnOne : (1 : ℝ) ≤ n := by
      exact_mod_cast (by omega : 1 ≤ n)
    have hzpow : (n : ℝ) ^ (-10 : ℤ) ≤ 1 := by
      rw [show (-10 : ℤ) = -(10 : ℤ) by norm_num, zpow_neg]
      exact (inv_le_one₀ (pow_pos hnR 10)).2 (one_le_pow₀ hnOne)
    exact hq10.trans hzpow
  have hprob : ProbabilityAtLeast mu
      (ComplexConcentrationGood trace (∫ omega, trace omega ∂mu) bound)
      (1 - 4 * (n : ℝ) ^ (-32 : ℤ)) := by
    apply (ENNReal.ofReal_le_ofReal ?_).trans hbase
    dsimp only [tail] at htail
    linarith
  exact measure_compl_le_of_probabilityAtLeast_one_sub
    (measurableSet_complexConcentrationGood htraceMeasurable _ _)
    hq0 hq1 hprob

/-- `4 n⁻³²` at every centre plus the proved cardinality bound gives one common event of
probability at least `1-n⁻¹⁰`. -/
theorem probabilityAtLeast_iInter_of_n32_failure_of_card_le_n18
    {kappa Omega : Type*} [Fintype kappa] [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {n : ℕ} (hn : 2 ≤ n) (good : kappa → Set Omega)
    (hmeas : ∀ i, MeasurableSet (good i))
    (hcard : (Fintype.card kappa : ℝ) ≤ (n : ℝ) ^ 18)
    (hpoint : ∀ i,
      mu (good i)ᶜ ≤ ENNReal.ofReal (4 * (n : ℝ) ^ (-32 : ℤ))) :
    ProbabilityAtLeast mu (⋂ i, good i) (1 - (n : ℝ) ^ (-10 : ℤ)) := by
  apply probabilityAtLeast_iInter_of_finite_failure_bounds mu good hmeas
    (ENNReal.ofReal (4 * (n : ℝ) ^ (-32 : ℤ)))
    (by positivity) hpoint
  rw [← ENNReal.ofReal_nsmul]
  exact ENNReal.ofReal_le_ofReal (by
    simpa only [nsmul_eq_mul] using
      (card_mul_four_zpow_neg32_le_zpow_neg10 hn hcard))

/-- Concentration-independent, end-to-end uniformization at the exact v3 scale.

This is the core theorem intended for the direct product-McDiarmid route.  Its only stochastic
input is the explicit `4 n⁻³²` failure estimate at each *concretely enumerated* centre.  It then
proves the net cardinality, the finite union bound, the `eta`-continuity extension, and the final
`1-n⁻¹⁰` common-event probability.  No Doob certificate and no external uniformization or
good-event interface occurs in the statement. -/
theorem proposition34_uniformTrace_probability_from_center_failures
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {n : ℕ} (hn : 2 ≤ n)
    {B cPrime C : ℝ} (hB : 0 < B) (hBn : B ≤ n) (hcPrime : 0 ≤ cPrime)
    (matrix : Omega → Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (good : EtaGridIndex (proposition34EtaScale n B cPrime)
      (etaUniformMesh (proposition34EtaScale n B cPrime)) → Set Omega)
    (hmeas : ∀ k, MeasurableSet (good k))
    (hpoint : ∀ k,
      mu (good k)ᶜ ≤ ENNReal.ofReal (4 * (n : ℝ) ^ (-32 : ℤ)))
    (hcenter : ∀ k omega, omega ∈ good k →
      ‖stieltjesTrace (matrix omega) z
        ((proposition34PaperEtaNet n B cPrime hB (by omega)).center k)‖ ≤ C) :
    ProbabilityAtLeast mu
      (Proposition34UniformTraceGood
        (fun omega eta ↦ stieltjesTrace (matrix omega) z eta)
        n B cPrime (C + 1 / 2))
      (1 - (n : ℝ) ^ (-10 : ℤ)) := by
  let _ : NeZero n := ⟨by omega⟩
  let v0 : ℝ := proposition34EtaScale n B cPrime
  have hv0 : 0 < v0 := corollary35_scale_pos hB (by positivity)
  let net := proposition34PaperEtaNet n B cPrime hB (by omega)
  let trace : Omega → ℂ → ℂ :=
    fun omega eta ↦ stieltjesTrace (matrix omega) z eta
  have hcard14 :
      (Fintype.card (EtaGridIndex (proposition34EtaScale n B cPrime)
        (etaUniformMesh (proposition34EtaScale n B cPrime))) : ℝ) ≤
        (n : ℝ) ^ 14 := by
    have hraw := proposition34EtaGrid_card_le_pow_fourteen hn hB hBn hcPrime
    rw [← Nat.card_eq_fintype_card] at hraw ⊢
    simpa only [proposition34EtaScale] using hraw
  have hcard18 :
      (Fintype.card (EtaGridIndex (proposition34EtaScale n B cPrime)
        (etaUniformMesh (proposition34EtaScale n B cPrime))) : ℝ) ≤
        (n : ℝ) ^ 18 := by
    have hnOne : (1 : ℝ) ≤ n := by
      exact_mod_cast (by omega : 1 ≤ n)
    exact hcard14.trans (pow_le_pow_right₀ hnOne (by norm_num))
  have hcommon : ProbabilityAtLeast mu (⋂ k, good k)
      (1 - (n : ℝ) ^ (-10 : ℤ)) :=
    probabilityAtLeast_iInter_of_n32_failure_of_card_le_n18
      mu hn good hmeas hcard18 hpoint
  have hinterGrid : (⋂ k, good k) ⊆ net.gridGood trace C := by
    intro omega homega k
    exact hcenter k omega (Set.mem_iInter.mp homega k)
  have hgridUniform : net.gridGood trace C ⊆
      UniformEtaGood (EtaDomainAtScale v0) trace (C + 1 / 2) := by
    simpa only [net, v0, proposition34PaperEtaNet] using
      (proposition34_gridGood_subset_uniformTraceGood matrix z hv0 (C := C))
  have huniformEq :
      UniformEtaGood (EtaDomainAtScale v0) trace (C + 1 / 2) =
        Proposition34UniformTraceGood trace n B cPrime (C + 1 / 2) := by
    ext omega
    simp only [UniformEtaGood, Proposition34UniformTraceGood, mem_ofPred_eq]
    constructor
    · intro h eta heta
      apply h eta
      simpa only [v0, proposition34EtaScale] using
        ((proposition34EtaDomain_iff_mem_etaDomainAtScale
          n B cPrime eta).mp heta)
    · intro h eta heta
      apply h eta
      exact (proposition34EtaDomain_iff_mem_etaDomainAtScale
        n B cPrime eta).mpr (by
          simpa only [v0, proposition34EtaScale] using heta)
  rw [← huniformEq]
  exact hcommon.trans (measure_mono (hinterGrid.trans hgridUniform))

end

end Arxiv2410V3

