import BernoulliSection8.CellCoordinates
import BernoulliSection8.MesoscopicScales
import BernoulliSection10.PhysicalProbabilityInstances
import BernoulliSection10.ProbabilityLimits

/-! # The actual clipped core pressure law of large numbers -/

open Filter MeasureTheory
open scoped Topology BigOperators NNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace BernoulliSection8

open BernoulliSection10 BernoulliSection10.ProbabilityLimits

/-- Literal cap `C ell_W log W`; it is nonnegative even at `W=0,1`. -/
def cellClipBound (C : ℝ≥0) (W : ℕ) : ℝ≥0 :=
  ⟨(C : ℝ) * cellLength W * Real.log W,
    mul_nonneg (mul_nonneg C.2 (Nat.cast_nonneg _)) (Real.log_natCast_nonneg W)⟩

/-- The simultaneous centered core fluctuation used on both sides of
the actual pressure sandwich. -/
def completeCellCoreFluctuation (μ : Measure ℝ) (A : ℝ≥0) (W s K : ℕ) (z : ℂ)
    (x : Fin K → IntervalRows W (3 + s)) : ℝ :=
  finitePressureMax (fun r => |∑ k,
    (clippedCoreLog A W s z r (completeCellCore W s (x k)) - clippedCorePressure μ A W s z r)|)

theorem completeCellCoreFluctuation_nonneg (μ : Measure ℝ) (A : ℝ≥0) (W s K : ℕ) (z : ℂ)
    (x : Fin K → IntervalRows W (3 + s)) : 0 ≤ completeCellCoreFluctuation μ A W s K z x := by
  unfold completeCellCoreFluctuation
  refine le_trans ?_ (le_finitePressureMax _ (0 : Fin (2 * W + 1)))
  exact abs_nonneg _

theorem cellClipBound_pos {C : ℝ≥0} (hC : 0 < C) {W : ℕ} (hW : 2 ≤ W) :
    0 < cellClipBound C W := by
  change 0 < (C : ℝ) * cellLength W * Real.log W
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hLpos : (0 : ℝ) < cellLength W := by
    exact_mod_cast (cellLength_pos (by omega : 0 < W))
  have hlog : 0 < Real.log W :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < W))
  exact mul_pos (mul_pos hCpos hLpos) hlog

/-- The normalized deviation of the maximal sum of actual core logs
from its deterministic maximal pressure. Reset losses are separate. -/
def mesoscopicCorePressureError (μ : Measure ℝ) (C : ℝ≥0) (W K : ℕ) (z : ℂ)
    (x : IntervalRows W (K * (3 + coreSites W))) : ℝ :=
  (finitePressureMax (fun r => ∑ k,
      clippedCoreLog (cellClipBound C W) W (coreSites W) z r
        (completeCellCore W (coreSites W)
          (unflattenCompleteCells W (3 + coreSites W) K x k))) -
    (K : ℝ) * clippedMaxCorePressure μ (cellClipBound C W) W (coreSites W) z) /
      ((K : ℝ) * cellLength W)

/-- Explicit normalization of the source's Hoeffding threshold at
`u=log W`. The remaining rate is exactly that of (8.51). -/
theorem normalized_cell_threshold_le {W K : ℕ} (hW : 2 ≤ W) (hK : 0 < K)
    (C : ℝ≥0) :
    (3 * (cellClipBound C W : ℝ) *
      Real.sqrt ((K : ℝ) * (Real.log W + Real.log W))) /
      ((K : ℝ) * cellLength W) ≤
      6 * (C : ℝ) * ((Real.log W) ^ (3 / 2 : ℝ) / Real.sqrt K) := by
  have hW0 : 0 < W := by omega
  have hlog : 0 < Real.log W :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < W))
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hLpos : (0 : ℝ) < cellLength W := by exact_mod_cast cellLength_pos hW0
  have hroot : (0 : ℝ) < Real.sqrt K := Real.sqrt_pos.2 hKpos
  have hrootSq : (Real.sqrt K) ^ 2 = (K : ℝ) := Real.sq_sqrt hKpos.le
  have hlogpow : Real.log W * Real.sqrt (Real.log W) = (Real.log W) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hlog, Real.rpow_one]
  have hlogroot : Real.sqrt (Real.log W + Real.log W) ≤
      2 * Real.sqrt (Real.log W) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hlog.le]
    nlinarith
  calc
    _ = 3 * (C : ℝ) * Real.log W *
        Real.sqrt (Real.log W + Real.log W) / Real.sqrt K := by
      rw [Real.sqrt_mul hKpos.le]
      change (3 * ((C : ℝ) * cellLength W * Real.log W) *
        (Real.sqrt K * Real.sqrt (Real.log W + Real.log W))) /
        ((K : ℝ) * cellLength W) = _
      rw [show (K : ℝ) * cellLength W = (Real.sqrt K) ^ 2 * cellLength W by
        rw [hrootSq]]
      field_simp [hroot.ne', hLpos.ne']
      <;> ring
    _ ≤ 3 * (C : ℝ) * Real.log W *
        (2 * Real.sqrt (Real.log W)) / Real.sqrt K := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogroot (by positivity)) hroot.le
    _ = _ := by rw [← hlogpow]; ring

/-- The exact simultaneous fluctuation in the sandwich, normalized by
the scalar size of all complete cells, vanishes under their actual law. -/
theorem completeCellCoreFluctuation_tendsto
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (C : ℝ≥0) (hC : 0 < C)
    (W K : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hK : ∀ᶠ n in atTop, coreSites (W n) ≤ K n) (z : ℂ) :
    TendstoInProbabilityTri
      (fun n => independentCoreLaw μ (W n) (3 + coreSites (W n)) (K n))
      (fun n x => completeCellCoreFluctuation μ (cellClipBound C (W n))
        (W n) (coreSites (W n)) (K n) z x / ((K n : ℝ) * cellLength (W n))) 0 := by
  intro ε hε
  have hRate : Tendsto (fun n => 6 * (C : ℝ) *
      ((Real.log (W n)) ^ (3 / 2 : ℝ) / Real.sqrt (K n))) atTop (𝓝 0) := by
    simpa using (tendsto_cellConcentrationOverhead hW hK).const_mul (6 * (C : ℝ))
  have hprob : ∀ᶠ n in atTop,
      (independentCoreLaw μ (W n) (3 + coreSites (W n)) (K n)).real
        {x | ε ≤ |completeCellCoreFluctuation μ (cellClipBound C (W n))
          (W n) (coreSites (W n)) (K n) z x / ((K n : ℝ) * cellLength (W n)) - 0|} ≤
      2 / (W n : ℝ) := by
    filter_upwards [hW.eventually (eventually_ge_atTop 2), hK,
      hRate.eventually (Iio_mem_nhds hε)] with n hWn hKn hsmall
    have hWp : 0 < W n := by omega
    have hKp : 0 < K n := lt_of_lt_of_le (coreSites_pos hWp) hKn
    have hden : (0 : ℝ) < (K n : ℝ) * cellLength (W n) :=
      mul_pos (by exact_mod_cast hKp) (by exact_mod_cast cellLength_pos hWp)
    have hbound : (independentCoreLaw μ (W n) (3 + coreSites (W n)) (K n)).real
        {x | 3 * (cellClipBound C (W n) : ℝ) *
          Real.sqrt ((K n : ℝ) * (Real.log (W n) + Real.log (W n))) <
          completeCellCoreFluctuation μ (cellClipBound C (W n))
            (W n) (coreSites (W n)) (K n) z x} ≤ 2 * Real.exp (-Real.log (W n)) := by
      exact (measurePreserving_real_preimage_le
        (completeCellsCores_measurePreserving μ (W n) (coreSites (W n)) (K n)) _).trans
          (lemma_8_1_independent_cores μ (cellClipBound C (W n)) (cellClipBound_pos hC hWn)
            (W n) (coreSites (W n)) (K n) hWn hKp z (Real.log_natCast_nonneg (W n)))
    have hsub : {x | ε ≤ |completeCellCoreFluctuation μ (cellClipBound C (W n))
        (W n) (coreSites (W n)) (K n) z x / ((K n : ℝ) * cellLength (W n)) - 0|} ⊆
        {x | 3 * (cellClipBound C (W n) : ℝ) *
          Real.sqrt ((K n : ℝ) * (Real.log (W n) + Real.log (W n))) <
          completeCellCoreFluctuation μ (cellClipBound C (W n))
            (W n) (coreSites (W n)) (K n) z x} := by
      intro x hx
      have ht := (div_lt_iff₀ hden).1
        ((normalized_cell_threshold_le hWn hKp C).trans_lt hsmall)
      have hnonneg := completeCellCoreFluctuation_nonneg μ (cellClipBound C (W n))
        (W n) (coreSites (W n)) (K n) z x
      have hx' : ε ≤ completeCellCoreFluctuation μ (cellClipBound C (W n))
          (W n) (coreSites (W n)) (K n) z x / ((K n : ℝ) * cellLength (W n)) := by
        simpa only [Set.mem_ofPred_eq, sub_zero, abs_div, abs_of_pos hden,
          abs_of_nonneg hnonneg] using hx
      exact ht.trans_le ((le_div_iff₀ hden).1 hx')
    have h := (measureReal_mono hsub).trans hbound
    simpa only [Real.exp_neg, Real.exp_log (by exact_mod_cast hWp : (0 : ℝ) < W n),
      div_eq_mul_inv] using h
  have hzero : Tendsto (fun n => 2 / (W n : ℝ)) atTop (𝓝 0) := by
    have hcast : Tendsto (fun n => (W n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hW
    simpa only [div_eq_mul_inv, Function.comp_def, mul_zero] using
      (tendsto_inv_atTop_zero.comp hcast).const_mul (2 : ℝ)
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg) hprob hzero

/-- Concrete LLN for the actual clipped core sums in a complete-cell
interval. It applies both to the independent anchor and to every longer
target because only `K >= K_W` is needed, and that inequality is proved
from the exact target dimension in `MesoscopicScales`. -/
theorem mesoscopicCorePressureError_tendsto
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (C : ℝ≥0) (hC : 0 < C)
    (W K : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hK : ∀ᶠ n in atTop, coreSites (W n) ≤ K n) (z : ℂ) :
    TendstoInProbabilityTri
      (fun n => intervalRowsLaw (W n) (K n * (3 + coreSites (W n))) μ)
      (fun n => mesoscopicCorePressureError μ C (W n) (K n) z) 0 := by
  intro ε hε
  have hRate : Tendsto (fun n => 6 * (C : ℝ) *
      ((Real.log (W n)) ^ (3 / 2 : ℝ) / Real.sqrt (K n))) atTop (𝓝 0) := by
    simpa using (tendsto_cellConcentrationOverhead hW hK).const_mul (6 * (C : ℝ))
  have hSmall := hRate.eventually (Iio_mem_nhds hε)
  have hprob : ∀ᶠ n in atTop,
      (intervalRowsLaw (W n) (K n * (3 + coreSites (W n))) μ).real
        {x | ε ≤ |mesoscopicCorePressureError μ C (W n) (K n) z x - 0|} ≤
      2 / (W n : ℝ) := by
    filter_upwards [hW.eventually (eventually_ge_atTop 2), hK, hSmall] with n hWn hKn hsmall
    have hWp : 0 < W n := by omega
    have hKp : 0 < K n := lt_of_lt_of_le (coreSites_pos hWp) hKn
    have hden : (0 : ℝ) < (K n : ℝ) * cellLength (W n) :=
      mul_pos (by exact_mod_cast hKp) (by exact_mod_cast cellLength_pos hWp)
    have hbound := lemma_8_1_interval_cells μ (cellClipBound C (W n))
      (cellClipBound_pos hC hWn) (W n) (coreSites (W n)) (K n) hWn hKp z
      (Real.log_natCast_nonneg (W n))
    have hsub : {x | ε ≤ |mesoscopicCorePressureError μ C (W n) (K n) z x - 0|} ⊆
        {x | 3 * (cellClipBound C (W n) : ℝ) *
          Real.sqrt ((K n : ℝ) * (Real.log (W n) + Real.log (W n))) <
          finitePressureMax (fun r => |∑ k,
            (clippedCoreLog (cellClipBound C (W n)) (W n) (coreSites (W n)) z r
              (completeCellCore (W n) (coreSites (W n))
                (unflattenCompleteCells (W n) (3 + coreSites (W n)) (K n) x k)) -
              clippedCorePressure μ (cellClipBound C (W n)) (W n) (coreSites (W n)) z r)|)} := by
      intro x hx
      have hmax := abs_coreSumMax_sub_pressure_le μ (cellClipBound C (W n))
        (W n) (coreSites (W n)) (K n) z
        (completeCellsCores (W n) (coreSites (W n)) (K n)
          (unflattenCompleteCells (W n) (3 + coreSites (W n)) (K n) x))
      have hthreshold := (normalized_cell_threshold_le hWn hKp C).trans_lt hsmall
      have hthreshold' := (div_lt_iff₀ hden).1 hthreshold
      simp only [mesoscopicCorePressureError, sub_zero, abs_div, abs_of_pos hden] at hx
      have hx' := (le_div_iff₀ hden).1 hx
      exact lt_of_lt_of_le hthreshold' (hx'.trans hmax)
    have h := (measureReal_mono hsub).trans hbound
    simpa only [Real.exp_neg, Real.exp_log (by exact_mod_cast hWp : (0 : ℝ) < W n),
      div_eq_mul_inv] using h
  have hzero : Tendsto (fun n => 2 / (W n : ℝ)) atTop (𝓝 0) := by
    have hcast : Tendsto (fun n => (W n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hW
    simpa only [div_eq_mul_inv, Function.comp_def, mul_zero] using
      (tendsto_inv_atTop_zero.comp hcast).const_mul (2 : ℝ)
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg) hprob hzero

/-- Pullback of a probability limit under literal law-preserving maps.
The outer-measure inequality avoids an unnecessary observability premise. -/
theorem tendstoInProbabilityTri_comp_measurePreserving
    {Ω Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (μ : ∀ n, Measure (Ω n)) (ν : ∀ n, Measure (Ξ n))
    [∀ n, IsFiniteMeasure (μ n)] [∀ n, IsFiniteMeasure (ν n)]
    (f : ∀ n, Ω n → Ξ n) (hf : ∀ n, MeasurePreserving (f n) (μ n) (ν n))
    (X : ∀ n, Ξ n → ℝ) (u : ℝ) (hX : TendstoInProbabilityTri ν X u) :
    TendstoInProbabilityTri μ (fun n x => X n (f n x)) u := by
  intro ε hε
  apply squeeze_zero (fun _ => measureReal_nonneg) _ (hX ε hε)
  intro n
  exact measurePreserving_real_preimage_le (hf n) {x | ε ≤ |X n x - u|}

/-- Any actual interval containing the complete cells inherits their
proved LLN by restriction of IID rows. -/
theorem mesoscopicCorePressureError_embedded_tendsto
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (C : ℝ≥0) (hC : 0 < C)
    (W K m : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hK : ∀ᶠ n in atTop, coreSites (W n) ≤ K n)
    (e : ∀ n, Fin (K n * (3 + coreSites (W n))) ↪ Fin (m n)) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (m n) μ)
      (fun n x => mesoscopicCorePressureError μ C (W n) (K n) z
        (intervalRestriction (W := W n) (e n) x)) 0 := by
  apply tendstoInProbabilityTri_comp_measurePreserving _ _
    (fun n => intervalRestriction (W := W n) (e n))
    (fun n => physicalRestriction_measurePreserving μ (e n)) _ 0
  exact mesoscopicCorePressureError_tendsto μ C hC W K hW hK z

/-- The exact anchor has its complete cells before the final three sites. -/
def anchorCompleteCellsEmbedding (W : ℕ) :
    Fin (anchorCells W * (3 + coreSites W)) ↪ Fin (anchorSites W) :=
  Fin.castLEEmb (by
    simp only [anchorSites, cellSites, Nat.add_comm 3 (coreSites W)]
    omega)

def anchorCorePressureError (μ : Measure ℝ) (C : ℝ≥0) (W : ℕ) (z : ℂ)
    (x : IntervalRows W (anchorSites W)) : ℝ :=
  mesoscopicCorePressureError μ C W (anchorCells W) z
    (intervalRestriction (anchorCompleteCellsEmbedding W) x)

theorem anchorCorePressureError_tendsto
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (C : ℝ≥0) (hC : 0 < C)
    (W : ℕ → ℕ) (hW : Tendsto W atTop atTop) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (anchorSites (W n)) μ)
      (fun n => anchorCorePressureError μ C (W n) z) 0 :=
  mesoscopicCorePressureError_embedded_tendsto μ C hC W
    (fun n => anchorCells (W n)) (fun n => anchorSites (W n)) hW
    (Filter.Eventually.of_forall fun _ => le_rfl)
    (fun n => anchorCompleteCellsEmbedding (W n)) z

/-- Every target contains its computed number of complete cells, even at
the unused small indices where `m < 3`. -/
def targetCompleteCellsEmbedding (W m : ℕ) :
    Fin (targetCells m W * (3 + coreSites W)) ↪ Fin m :=
  Fin.castLEEmb (by
    have h := Nat.div_mul_le_self (m - 3) (cellSites W)
    have h' : targetCells m W * (3 + coreSites W) ≤ m - 3 := by
      simpa only [targetCells, cellSites, Nat.add_comm] using h
    exact h'.trans (Nat.sub_le m 3))

/-- The actual long target's core pressure LLN, with all cell geometry
and independence discharged by the exact target length. -/
theorem targetCorePressureError_tendsto
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (C : ℝ≥0) (hC : 0 < C)
    (W m : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, anchorSize (W n) ≤ m n * W n) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (m n) μ)
      (fun n x => mesoscopicCorePressureError μ C (W n) (targetCells (m n) (W n)) z
        (intervalRestriction (targetCompleteCellsEmbedding (W n) (m n)) x)) 0 := by
  apply mesoscopicCorePressureError_embedded_tendsto μ C hC W
    (fun n => targetCells (m n) (W n)) m hW _
    (fun n => targetCompleteCellsEmbedding (W n) (m n)) z
  filter_upwards [hW.eventually (eventually_gt_atTop 0), hlong] with n hWn hn
  exact anchorCells_le_targetCells hWn hn

/-- The long branch's core error, filled by zero at unused short indices. -/
def longBranchCorePressureError (μ : Measure ℝ) (C : ℝ≥0) (W m : ℕ) (z : ℂ)
    (x : IntervalRows W m) : ℝ :=
  if anchorSize W ≤ m * W then
    mesoscopicCorePressureError μ C W (targetCells m W) z
      (intervalRestriction (targetCompleteCellsEmbedding W m) x)
  else 0

/-- Arbitrarily alternating long targets still have a vanishing clipped
core error on their own row spaces. Larger independent cell arrays fill
the unused indices only inside the proof. -/
theorem longBranchCorePressureError_tendsto
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (C : ℝ≥0) (hC : 0 < C)
    (W m : ℕ → ℕ) (hW : Tendsto W atTop atTop) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (m n) μ)
      (fun n => longBranchCorePressureError μ C (W n) (m n) z) 0 := by
  let K : ℕ → ℕ := fun n => max (coreSites (W n)) (targetCells (m n) (W n))
  have h := mesoscopicCorePressureError_tendsto μ C hC W K hW
    (Filter.Eventually.of_forall fun n => le_max_left _ _) z
  intro ε hε
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg) _ (h ε hε)
  filter_upwards [hW.eventually (eventually_gt_atTop 0)] with n hWn
  by_cases hn : anchorSize (W n) ≤ m n * W n
  · have hCells : coreSites (W n) ≤ targetCells (m n) (W n) :=
      anchorCells_le_targetCells hWn hn
    have hKn : K n = targetCells (m n) (W n) := Nat.max_eq_right hCells
    let F : ℕ → ℝ := fun k =>
      (intervalRowsLaw (W n) (k * (3 + coreSites (W n))) μ).real
        {x | ε ≤ |mesoscopicCorePressureError μ C (W n) k z x - 0|}
    have hPull := measurePreserving_real_preimage_le
      (physicalRestriction_measurePreserving μ (targetCompleteCellsEmbedding (W n) (m n)))
      {x | ε ≤ |mesoscopicCorePressureError μ C (W n) (targetCells (m n) (W n)) z x - 0|}
    simp only [longBranchCorePressureError, if_pos hn]
    exact hPull.trans_eq (congrArg F hKn).symm
  · simp only [longBranchCorePressureError, if_neg hn, sub_self, abs_zero]
    have he : {x : IntervalRows (W n) (m n) | ε ≤ (0 : ℝ)} = ∅ := by
      ext x
      simp [not_le_of_gt hε]
    rw [he, measureReal_empty]
    exact measureReal_nonneg

end BernoulliSection8
