import BernoulliSection10.PhysicalAffinity
import BernoulliSection10.FinitePressure
import BernoulliSection8.ClippedLog
import Mathlib.Probability.Moments.SubGaussian

/-!
# Independent clipped-cell concentration

The zero norm is sent to the lower clipping endpoint, as required by
(8.30)--(8.32). All estimates use the original finite product law. No
interface-good event, density assumption, or concentration certificate is
assumed. The final concrete theorem applies to IID physical cores.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Matrix.Norms.L2Operator

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace BernoulliSection8

theorem clippedLog_mem_Icc (A : ℝ≥0) (x : ℝ) :
    clippedLog A x ∈ Set.Icc (-(A : ℝ)) A :=
  ⟨neg_le_clippedLog A.2 x, clippedLog_le _ _⟩

theorem measurable_clippedLog (A : ℝ≥0) : Measurable (clippedLog A) :=
  (continuous_clippedLog A).measurable

section BoundedConcentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem bounded_centered_subgaussian (A : ℝ≥0) {Y : Ω → ℝ}
    (hY : AEMeasurable Y μ) (hbound : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (-(A : ℝ)) A) :
    HasSubgaussianMGF (fun ω => Y ω - ∫ x, Y x ∂μ) (A ^ 2) μ := by
  have h := hasSubgaussianMGF_of_mem_Icc hY hbound
  have hA : ‖(A : ℝ) - (-(A : ℝ))‖₊ / 2 = A := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm]
    rw [Real.norm_eq_abs]
    have hnonneg : 0 ≤ (A : ℝ) - (-(A : ℝ)) := by
      rw [sub_neg_eq_add]
      positivity
    rw [abs_of_nonneg hnonneg]
    ring
  simpa only [hA] using h

theorem bounded_centered_sum_subgaussian {K : ℕ} (A : ℝ≥0)
    (Y : Fin K → Ω → ℝ) (hY : ∀ k, AEMeasurable (Y k) μ)
    (hindep : iIndepFun Y μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, Y k ω ∈ Set.Icc (-(A : ℝ)) A) :
    HasSubgaussianMGF (fun ω => ∑ k, (Y k ω - ∫ x, Y k x ∂μ))
      ((K : ℝ≥0) * A ^ 2) μ := by
  have hi := hindep.comp (fun k y => y - ∫ x, Y k x ∂μ)
    (fun _ => measurable_id.sub_const _)
  have h := HasSubgaussianMGF.sum_of_iIndepFun (s := Finset.univ) hi
    (fun k _ => bounded_centered_subgaussian A (hY k) (hbound k))
  simpa only [Function.comp_def, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using h

theorem subgaussian_abs_tail {Y : Ω → ℝ} {c : ℝ≥0}
    (hY : HasSubgaussianMGF Y c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |Y ω|} ≤ 2 * Real.exp (-t ^ 2 / (2 * c)) := by
  have hs : {ω | t ≤ |Y ω|} = {ω | t ≤ Y ω} ∪ {ω | t ≤ -Y ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union]
    by_cases h : 0 ≤ Y ω
    · rw [abs_of_nonneg h]
      constructor
      · exact Or.inl
      · rintro (h' | h')
        · exact h'
        · linarith
    · rw [abs_of_neg (lt_of_not_ge h)]
      constructor
      · exact Or.inr
      · rintro (h' | h')
        · linarith
        · exact h'
  rw [hs]
  have h1 := hY.measure_ge_le ht
  have h2 := hY.neg.measure_ge_le ht
  simp only [Pi.neg_apply] at h2
  exact (measureReal_union_le _ _).trans (by linarith)

/-- Simultaneous two-sided Hoeffding bound. Independence is required only
between cells at each fixed degree; degrees need not be independent. -/
theorem bounded_cells_max_tail {K d : ℕ} (A : ℝ≥0)
    (Y : Fin (d + 1) → Fin K → Ω → ℝ)
    (hY : ∀ r k, AEMeasurable (Y r k) μ)
    (hindep : ∀ r, iIndepFun (Y r) μ)
    (hbound : ∀ r k, ∀ᵐ ω ∂μ, Y r k ω ∈ Set.Icc (-(A : ℝ)) A)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t < BernoulliSection10.finitePressureMax
      (fun r => |∑ k, (Y r k ω - ∫ x, Y r k x ∂μ)|)} ≤
      2 * (d + 1 : ℕ) * Real.exp (-t ^ 2 / (2 * (K : ℝ) * (A : ℝ) ^ 2)) := by
  let E : Fin (d + 1) → Set Ω := fun r =>
    {ω | t ≤ |∑ k, (Y r k ω - ∫ x, Y r k x ∂μ)|}
  have hsub : {ω | t < BernoulliSection10.finitePressureMax
      (fun r => |∑ k, (Y r k ω - ∫ x, Y r k x ∂μ)|)} ⊆ ⋃ r, E r := by
    intro ω hω
    obtain ⟨r, hr⟩ := BernoulliSection10.finitePressureMax_attained
      (fun r => |∑ k, (Y r k ω - ∫ x, Y r k x ∂μ)|)
    exact Set.mem_iUnion.mpr ⟨r, by dsimp [E]; simpa only [hr] using hω.le⟩
  have he (r : Fin (d + 1)) : μ.real (E r) ≤
      2 * Real.exp (-t ^ 2 / (2 * (K : ℝ) * (A : ℝ) ^ 2)) := by
    have h := subgaussian_abs_tail
      (bounded_centered_sum_subgaussian A (Y r) (hY r) (hindep r) (hbound r)) ht
    simpa only [E, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, mul_assoc] using h
  calc
    _ ≤ μ.real (⋃ r, E r) := measureReal_mono hsub
    _ ≤ ∑ r, μ.real (E r) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _r : Fin (d + 1),
        2 * Real.exp (-t ^ 2 / (2 * (K : ℝ) * (A : ℝ) ^ 2)) :=
      Finset.sum_le_sum (fun r _ => he r)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]; ring

end BoundedConcentration

/-- Clipped core log of the literal polynomial cleared physical product. -/
def clippedCoreLog (A : ℝ≥0) (W s : ℕ) (z : ℂ)
    (r : Fin (2 * W + 1)) (x : BernoulliSection10.IntervalRows W s) : ℝ :=
  clippedLog A ‖BernoulliSection10.intervalClearedProduct W s z x r‖

theorem measurable_clippedCoreLog (A : ℝ≥0) (W s : ℕ) (z : ℂ)
    (r : Fin (2 * W + 1)) : Measurable (clippedCoreLog A W s z r) :=
  (measurable_clippedLog A).comp
    (BernoulliSection10.continuous_intervalClearedProduct W s z r).norm.measurable

theorem clippedCoreLog_mem_Icc (A : ℝ≥0) (W s : ℕ) (z : ℂ)
    (r : Fin (2 * W + 1)) (x : BernoulliSection10.IntervalRows W s) :
    clippedCoreLog A W s z r x ∈ Set.Icc (-(A : ℝ)) A := clippedLog_mem_Icc _ _

/-- Deterministic pressure under the original physical core product law. -/
def clippedCorePressure (μ : Measure ℝ) (A : ℝ≥0) (W s : ℕ) (z : ℂ)
    (r : Fin (2 * W + 1)) : ℝ :=
  ∫ x, clippedCoreLog A W s z r x ∂BernoulliSection10.intervalRowsLaw W s μ

/-- The deterministic maximum of the actual clipped core expectations. -/
def clippedMaxCorePressure (μ : Measure ℝ) (A : ℝ≥0) (W s : ℕ) (z : ℂ) : ℝ :=
  BernoulliSection10.finitePressureMax (clippedCorePressure μ A W s z)

/-- The least maximizing degree is chosen from the law before sampling. -/
def clippedCoreOptimizingDegree (μ : Measure ℝ) (A : ℝ≥0) (W s : ℕ) (z : ℂ) :
    Fin (2 * W + 1) :=
  BernoulliSection10.pressureOptimizingDegree (clippedCorePressure μ A W s z)

theorem clippedCoreOptimizingDegree_maximizes
    (μ : Measure ℝ) (A : ℝ≥0) (W s : ℕ) (z : ℂ) :
    clippedCorePressure μ A W s z (clippedCoreOptimizingDegree μ A W s z) =
      clippedMaxCorePressure μ A W s z :=
  BernoulliSection10.pressureOptimizingDegree_maximizes _

theorem clippedCoreOptimizingDegree_minimal
    (μ : Measure ℝ) (A : ℝ≥0) (W s : ℕ) (z : ℂ) {r : Fin (2 * W + 1)}
    (hr : clippedCorePressure μ A W s z r = clippedMaxCorePressure μ A W s z) :
    clippedCoreOptimizingDegree μ A W s z ≤ r :=
  BernoulliSection10.pressureOptimizingDegree_le _ hr

theorem integrable_clippedCoreLog (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (A : ℝ≥0) (W s : ℕ) (z : ℂ) (r : Fin (2 * W + 1)) :
    Integrable (clippedCoreLog A W s z r) (BernoulliSection10.intervalRowsLaw W s μ) := by
  letI : IsProbabilityMeasure (BernoulliSection10.intervalRowsLaw W s μ) := by
    unfold BernoulliSection10.intervalRowsLaw BernoulliSection10.physicalRowLaw
    infer_instance
  exact Integrable.of_mem_Icc (-(A : ℝ)) A (measurable_clippedCoreLog A W s z r).aemeasurable
    (ae_of_all _ (clippedCoreLog_mem_Icc A W s z r))

theorem clippedCorePressure_mem_Icc (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (A : ℝ≥0) (W s : ℕ) (z : ℂ) (r : Fin (2 * W + 1)) :
    clippedCorePressure μ A W s z r ∈ Set.Icc (-(A : ℝ)) A := by
  letI : IsProbabilityMeasure (BernoulliSection10.intervalRowsLaw W s μ) := by
    unfold BernoulliSection10.intervalRowsLaw BernoulliSection10.physicalRowLaw
    infer_instance
  have hlo := integral_mono (μ := BernoulliSection10.intervalRowsLaw W s μ)
    (integrable_const (-(A : ℝ))) (integrable_clippedCoreLog μ A W s z r)
    (fun x => (clippedCoreLog_mem_Icc A W s z r x).1)
  have hhi := integral_mono (μ := BernoulliSection10.intervalRowsLaw W s μ)
    (integrable_clippedCoreLog μ A W s z r) (integrable_const (A : ℝ))
    (fun x => (clippedCoreLog_mem_Icc A W s z r x).2)
  exact ⟨by simpa only [integral_const, probReal_univ, one_smul,
    clippedCorePressure] using hlo,
    by simpa only [integral_const, probReal_univ, one_smul,
      clippedCorePressure] using hhi⟩

theorem abs_clippedMaxCorePressure_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (A : ℝ≥0) (W s : ℕ) (z : ℂ) : |clippedMaxCorePressure μ A W s z| ≤ A := by
  rw [← clippedCoreOptimizingDegree_maximizes μ A W s z]
  exact abs_le.mpr (clippedCorePressure_mem_Icc μ A W s z _)

/-- The sample maximum of sums is compared with `K` times the maximum
mean, without paying the degree count a second time. -/
theorem abs_coreSumMax_sub_pressure_le
    (μ : Measure ℝ) (A : ℝ≥0) (W s K : ℕ) (z : ℂ)
    (x : Fin K → BernoulliSection10.IntervalRows W s) :
    |BernoulliSection10.finitePressureMax
        (fun r => ∑ k, clippedCoreLog A W s z r (x k)) -
      (K : ℝ) * clippedMaxCorePressure μ A W s z| ≤
      BernoulliSection10.finitePressureMax
        (fun r => |∑ k, (clippedCoreLog A W s z r (x k) - clippedCorePressure μ A W s z r)|) := by
  have h := BernoulliSection10.abs_finitePressureMax_sub_le_max_deviation
    (fun r => ∑ k, clippedCoreLog A W s z r (x k))
    (fun r => (K : ℝ) * clippedCorePressure μ A W s z r)
  rw [BernoulliSection10.finitePressureMax_mul_nonneg _ (by positivity)] at h
  simpa only [clippedMaxCorePressure, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

/-- The unconditioned product law of `K` independent physical cores. -/
def independentCoreLaw (μ : Measure ℝ) (W s K : ℕ) :
    Measure (Fin K → BernoulliSection10.IntervalRows W s) :=
  Measure.pi fun _ : Fin K => BernoulliSection10.intervalRowsLaw W s μ

instance independentCoreLaw_isProbabilityMeasure
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (W s K : ℕ) :
    IsProbabilityMeasure (independentCoreLaw μ W s K) := by
  unfold independentCoreLaw BernoulliSection10.intervalRowsLaw BernoulliSection10.physicalRowLaw
  infer_instance

theorem integral_clippedCoreLog_eval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (A : ℝ≥0) (W s K : ℕ) (z : ℂ) (r : Fin (2 * W + 1)) (k : Fin K) :
    (∫ x, clippedCoreLog A W s z r (x k) ∂independentCoreLaw μ W s K) =
      clippedCorePressure μ A W s z r := by
  letI : IsProbabilityMeasure (BernoulliSection10.intervalRowsLaw W s μ) := by
    unfold BernoulliSection10.intervalRowsLaw BernoulliSection10.physicalRowLaw
    infer_instance
  have hp := measurePreserving_eval
    (fun _ : Fin K => BernoulliSection10.intervalRowsLaw W s μ) k
  have h := integral_map (μ := independentCoreLaw μ W s K) hp.measurable.aemeasurable
    (measurable_clippedCoreLog A W s z r).aestronglyMeasurable
  simpa only [hp.map_eq, independentCoreLaw, clippedCorePressure] using h.symm

/-- Concrete independent-cell Hoeffding bound: the functions, their
independence, and their common pressure are all constructed internally.
There is no density hypothesis and no conditioning on interface events. -/
theorem independent_clippedCore_max_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : ℝ≥0)
    (W s K : ℕ) (z : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    (independentCoreLaw μ W s K).real {x | t < BernoulliSection10.finitePressureMax
      (fun r => |∑ k, (clippedCoreLog A W s z r (x k) - clippedCorePressure μ A W s z r)|)} ≤
      2 * (2 * W + 1 : ℕ) *
        Real.exp (-t ^ 2 / (2 * (K : ℝ) * (A : ℝ) ^ 2)) := by
  letI : IsProbabilityMeasure (BernoulliSection10.intervalRowsLaw W s μ) := by
    unfold BernoulliSection10.intervalRowsLaw BernoulliSection10.physicalRowLaw
    infer_instance
  have hi (r : Fin (2 * W + 1)) :
      iIndepFun (fun k (x : Fin K → BernoulliSection10.IntervalRows W s) =>
        clippedCoreLog A W s z r (x k)) (independentCoreLaw μ W s K) :=
    iIndepFun_pi (fun _ => (measurable_clippedCoreLog A W s z r).aemeasurable)
  have h := bounded_cells_max_tail A
    (fun r k (x : Fin K → BernoulliSection10.IntervalRows W s) =>
      clippedCoreLog A W s z r (x k))
    (fun r k => ((measurable_clippedCoreLog A W s z r).comp
      (measurable_pi_apply k)).aemeasurable) hi
    (fun r k => ae_of_all _ fun x => clippedCoreLog_mem_Icc A W s z r (x k)) ht
  simpa only [integral_clippedCoreLog_eval] using h

/-- Exact simultaneous Hoeffding threshold before absorbing the finite
degree count into a constant times `log W`. -/
def cellHoeffdingThreshold (A : ℝ≥0) (W K : ℕ) (u : ℝ) : ℝ :=
  (A : ℝ) * Real.sqrt (2 * (K : ℝ) * (Real.log (2 * W + 1 : ℕ) + u))

theorem independent_clippedCore_concentration
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : ℝ≥0) (hA : 0 < A)
    (W s K : ℕ) (hK : 0 < K) (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    (independentCoreLaw μ W s K).real {x |
      cellHoeffdingThreshold A W K u < BernoulliSection10.finitePressureMax
        (fun r => |∑ k, (clippedCoreLog A W s z r (x k) - clippedCorePressure μ A W s z r)|)} ≤
      2 * Real.exp (-u) := by
  have hD : (0 : ℝ) < (2 * W + 1 : ℕ) := by positivity
  have hlog : 0 ≤ Real.log (2 * W + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast
    (show 1 ≤ 2 * W + 1 by omega))
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hA0 : (A : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  have hrad : 0 ≤ 2 * (K : ℝ) * (Real.log (2 * W + 1 : ℕ) + u) := by positivity
  have hsq : (cellHoeffdingThreshold A W K u) ^ 2 =
      (A : ℝ) ^ 2 * (2 * (K : ℝ) * (Real.log (2 * W + 1 : ℕ) + u)) := by
    rw [cellHoeffdingThreshold, mul_pow, Real.sq_sqrt hrad]
  have hexp : -(cellHoeffdingThreshold A W K u) ^ 2 /
      (2 * (K : ℝ) * (A : ℝ) ^ 2) = -(Real.log (2 * W + 1 : ℕ) + u) := by
    rw [hsq]
    field_simp
    <;> ring
  have h := independent_clippedCore_max_tail μ A W s K z
    (show 0 ≤ cellHoeffdingThreshold A W K u by unfold cellHoeffdingThreshold; positivity)
  rw [hexp] at h
  convert h using 1
  rw [neg_add, Real.exp_add, Real.exp_neg (Real.log (2 * W + 1 : ℕ)), Real.exp_log hD]
  field_simp

/-- The source's degree count is logarithmic in width, uniformly from
`W=2` onward. This finite comparison avoids a hidden `log(2W+1)` premise. -/
theorem log_degreeCount_le_three_log {W : ℕ} (hW : 2 ≤ W) :
    Real.log (2 * W + 1 : ℕ) ≤ 3 * Real.log W := by
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
  have hsq : (4 : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
  have hcube : 2 * (W : ℝ) + 1 ≤ (W : ℝ) ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ W)
    nlinarith
  have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 * W + 1 : ℕ))
    (show ((2 * W + 1 : ℕ) : ℝ) ≤ (W : ℝ) ^ 3 by exact_mod_cast hcube)
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem cellHoeffdingThreshold_le {W K : ℕ} (hW : 2 ≤ W)
    (A : ℝ≥0) {u : ℝ} (hu : 0 ≤ u) :
    cellHoeffdingThreshold A W K u ≤
      3 * (A : ℝ) * Real.sqrt ((K : ℝ) * (Real.log W + u)) := by
  have hlog := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ W) : (1 : ℝ) ≤ W)
  have hinside : 2 * (K : ℝ) * (Real.log (2 * W + 1 : ℕ) + u) ≤
      9 * ((K : ℝ) * (Real.log W + u)) := by
    have h := log_degreeCount_le_three_log hW
    have hmul := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * (K : ℝ))
    have hrest : 0 ≤ (K : ℝ) * Real.log W := mul_nonneg (by positivity) hlog
    have hrest' : 0 ≤ (K : ℝ) * u := mul_nonneg (by positivity) hu
    nlinarith
  have hroot : Real.sqrt (2 * (K : ℝ) * (Real.log (2 * W + 1 : ℕ) + u)) ≤
      3 * Real.sqrt ((K : ℝ) * (Real.log W + u)) := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    norm_num
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hinside
  calc
    cellHoeffdingThreshold A W K u =
        (A : ℝ) * Real.sqrt (2 * (K : ℝ) * (Real.log (2 * W + 1 : ℕ) + u)) := rfl
    _ ≤ (A : ℝ) * (3 * Real.sqrt ((K : ℝ) * (Real.log W + u))) :=
      mul_le_mul_of_nonneg_left hroot A.2
    _ = 3 * (A : ℝ) * Real.sqrt ((K : ℝ) * (Real.log W + u)) := by ring

/-- Lemma 8.1 with the explicit constant `3`: take
`A = C_(K,z) * ell_W * log W` and `s = coreSites W` for its literal scales.
All core variables, their common mean, and independence are internal. -/
theorem lemma_8_1_independent_cores
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : ℝ≥0) (hA : 0 < A)
    (W s K : ℕ) (hW : 2 ≤ W) (hK : 0 < K) (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    (independentCoreLaw μ W s K).real {x |
      3 * (A : ℝ) * Real.sqrt ((K : ℝ) * (Real.log W + u)) <
        BernoulliSection10.finitePressureMax
          (fun r => |∑ k, (clippedCoreLog A W s z r (x k) - clippedCorePressure μ A W s z r)|)} ≤
      2 * Real.exp (-u) := by
  refine le_trans (measureReal_mono ?_)
    (independent_clippedCore_concentration μ A hA W s K hK z hu)
  intro x hx
  exact lt_of_le_of_lt (cellHoeffdingThreshold_le hW A hu) hx

end BernoulliSection8
