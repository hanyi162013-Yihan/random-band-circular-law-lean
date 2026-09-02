import BernoulliSection10.RemainderControl
import BernoulliSection10.IntervalRestriction
import BernoulliSection10.AsymptoticErrors

/-!
# Removing the actual residual interval

Equations (10.46)--(10.49): the observable is the difference between the
maximum degree-log of the full physical interval and of its literal
prefix. Invertibility, the suffix marginal law, and the common envelope
are proved internally; no incoming-product or probability certificate is
an assumption of the final estimate.
-/

open MeasureTheory Filter Set Topology
open scoped BigOperators Matrix Matrix.Norms.L2Operator ENNReal

noncomputable section

namespace BernoulliSection10

open BernoulliLinearAlgebra

/-- The finite manuscript constant, now in real rather than extended-real
form, for use in probability and limit estimates. -/
def remainderHodgeConstant (L : ℝ) (z : ℂ) : ℝ :=
  (oneSiteMaxHodgeWLogConstant L z).toReal

theorem remainderHodgeConstant_nonneg (L : ℝ) (z : ℂ) :
    0 ≤ remainderHodgeConstant L z := ENNReal.toReal_nonneg

theorem oneSiteMaxHodgeWLogConstant_ne_top (L : ℝ) (z : ℂ) :
    oneSiteMaxHodgeWLogConstant L z ≠ ⊤ := by
  unfold oneSiteMaxHodgeWLogConstant
  finiteness

theorem intervalMaxHodgeEnvelope_nonneg (W s : ℕ) (z : ℂ)
    (x : IntervalRows W s) : 0 ≤ intervalMaxHodgeEnvelope W s z x :=
  Finset.sum_nonneg fun _ _ => oneSiteMaxHodgeEnvelope_nonneg W z _

def intervalRemainderMaxDifference (W p q : ℕ) (z : ℂ)
    (x : IntervalRows W (p + q)) : ℝ :=
  finitePressureMax (fun r => intervalDegreeLog W (p + q) z r x) -
    finitePressureMax (fun r => intervalDegreeLog W p z r
      (intervalRestriction (Fin.castAddEmb q) x))

theorem intervalRemainderMaxDifference_le_ae
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W p q : ℕ) (hW : 0 < W) (z : ℂ) :
    ∀ᵐ x ∂intervalRowsLaw W (p + q) μ,
      |intervalRemainderMaxDifference W p q z x| ≤
        intervalMaxHodgeEnvelope W q z
          (intervalRestriction (Fin.natAddEmb p) x) := by
  have hprefix := (intervalRestriction_measurePreserving hμ
    (W := W) (Fin.castAddEmb q)).quasiMeasurePreserving.ae
      (intervalClearedProduct_det_isUnit_ae hμ W p hW z)
  have hsuffix := (intervalRestriction_measurePreserving hμ
    (W := W) (Fin.natAddEmb p)).quasiMeasurePreserving.ae
      (interval_remainder_max_change_le_ae hμ W q hW z)
  filter_upwards [hprefix, hsuffix] with x hp hq
  have hn (r : Fin (2 * W + 1)) :
      intervalClearedProduct W p z
        (intervalRestriction (Fin.castAddEmb q) x) r ≠ 0 := by
    letI : Nonempty (powersetCard (Fin W ⊕ Fin W) r.1) := by
      rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
      apply Nat.choose_pos
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    exact ((Matrix.isUnit_iff_isUnit_det _).mpr (hp r)).ne_zero
  have h := hq (fun r => intervalClearedProduct W p z
    (intervalRestriction (Fin.castAddEmb q) x) r) hn
  simpa only [intervalRemainderMaxDifference, intervalDegreeLog,
    intervalClearedProduct_split] using h

/-- The expected suffix envelope has the literal suffix length, even
though it is integrated on the whole physical interval. -/
theorem suffixHodgeEnvelope_integral_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W p q : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫ x, intervalMaxHodgeEnvelope W q z
      (intervalRestriction (Fin.natAddEmb p) x)
        ∂intervalRowsLaw W (p + q) μ) ≤
      (q : ℝ) * remainderHodgeConstant L z * W * densityLogScale W := by
  have hmp := intervalRestriction_measurePreserving hμ
    (W := W) (t := q) (Fin.natAddEmb p)
  have hmeas := (measurable_intervalMaxHodgeEnvelope hμ W q z).comp hmp.measurable
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => intervalMaxHodgeEnvelope_nonneg W q z _)
    hmeas.aestronglyMeasurable]
  rw [hmp.lintegral_comp (measurable_intervalMaxHodgeEnvelope hμ W q z).ennreal_ofReal]
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness)
      (oneSiteMaxHodgeWLogConstant_ne_top L z)) ENNReal.ofReal_ne_top)
    (intervalMaxHodgeEnvelope_lintegral_le_W_log_eW hμ W q hW z)
  have hnonneg : 0 ≤ (W : ℝ) * densityLogScale W :=
    mul_nonneg (Nat.cast_nonneg _) (densityLogScale_nonneg hW)
  simp only [densityLogScale] at hnonneg
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, oneSiteWLogScale,
    densityLogScale, ENNReal.toReal_ofReal hnonneg, remainderHodgeConstant,
    mul_assoc] using h

/-- A dominated version of Markov's inequality. The bound can hold only
almost surely; no modification of the concrete observable is necessary. -/
theorem measureReal_abs_ge_le_of_ae_bound
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν]
    (X H : Ω → ℝ) (hX : ∀ᵐ x ∂ν, |X x| ≤ H x)
    (hH : Integrable H ν) (hH0 : ∀ᵐ x ∂ν, 0 ≤ H x)
    {ε : ℝ} (hε : 0 < ε) :
    ν.real {x | ε ≤ |X x|} ≤ (∫ x, H x ∂ν) / ε := by
  have hmono : ν.real {x | ε ≤ |X x|} ≤ ν.real {x | ε ≤ H x} :=
    ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono_ae (hX.mono fun x hx => fun h => h.trans hx))
  apply hmono.trans
  apply (le_div_iff₀ hε).2
  simpa only [mul_comm] using mul_meas_ge_le_integral_of_nonneg hH0 hH ε

/-- The probability estimate (10.48) for actual interval products. -/
theorem intervalRemainderMaxDifference_markov
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W p q : ℕ) (hW : 0 < W) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (intervalRowsLaw W (p + q) μ).real
      {x | ε ≤ |intervalRemainderMaxDifference W p q z x|} ≤
        ((q : ℝ) * remainderHodgeConstant L z * W * densityLogScale W) / ε := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (intervalRowsLaw W (p + q) μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  have hmp := intervalRestriction_measurePreserving hμ
    (W := W) (t := q) (Fin.natAddEmb p)
  have hi := hmp.integrable_comp_of_integrable
    (intervalMaxHodgeEnvelope_integrable hμ W q hW z)
  exact (measureReal_abs_ge_le_of_ae_bound _ _ _
    (intervalRemainderMaxDifference_le_ae hμ W p q hW z) hi
    (Eventually.of_forall fun x => intervalMaxHodgeEnvelope_nonneg W q z _) hε).trans
      (div_le_div_of_nonneg_right
        (suffixHodgeEnvelope_integral_le hμ W p q hW z) hε.le)

theorem intervalRemainderMaxDifference_normalized_markov
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W p q N : ℕ) (hW : 0 < W) (hN : 0 < N)
    (hq : q ≤ densityCellSites W) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (intervalRowsLaw W (p + q) μ).real
      {x | ε ≤ |intervalRemainderMaxDifference W p q z x / N|} ≤
        (remainderHodgeConstant L z / ε) *
          ((densityAnchorSize W : ℝ) * densityLogScale W / N) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hset : {x : IntervalRows W (p + q) |
      ε ≤ |intervalRemainderMaxDifference W p q z x / N|} =
      {x | ε * (N : ℝ) ≤ |intervalRemainderMaxDifference W p q z x|} := by
    ext x
    simp only [mem_setOf_eq, abs_div, abs_of_pos hNr, le_div_iff₀ hNr]
  rw [hset]
  calc
    _ ≤ ((q : ℝ) * remainderHodgeConstant L z * W * densityLogScale W) /
        (ε * N) :=
      intervalRemainderMaxDifference_markov hμ W p q hW z (mul_pos hε hNr)
    _ ≤ ((densityCellSites W : ℝ) * remainderHodgeConstant L z * W *
        densityLogScale W) / (ε * N) := by
      apply div_le_div_of_nonneg_right _ (mul_pos hε hNr).le
      apply mul_le_mul_of_nonneg_right _ (densityLogScale_nonneg hW)
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg W)
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hq)
        (remainderHodgeConstant_nonneg L z)
    _ = _ := by
      simp only [densityAnchorSize, Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
      ring

/-- Equation (10.49), on the literal varying finite product spaces.
The only size inputs say that the residual interval is shorter than a
cell and that the target is in the long-ring branch. -/
theorem intervalRemainderMaxDifference_normalized_tendsto
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {W p q N : ℕ → ℕ} (hW : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, (W n : ℝ) ^ (101 / 100 : ℝ) ≤ N n)
    (hq : ∀ᶠ n in atTop, q n ≤ densityCellSites (W n))
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (intervalRowsLaw (W n) (p n + q n) μ).real
      {x | ε ≤ |intervalRemainderMaxDifference (W n) (p n) (q n) z x / N n|})
      atTop (𝓝 0) := by
  have hpos : ∀ᶠ n in atTop, 0 < W n :=
    hW.eventually (eventually_gt_atTop 0)
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_
    (show Tendsto (fun n => (remainderHodgeConstant L z / ε) *
      ((densityAnchorSize (W n) : ℝ) * densityLogScale (W n) / N n))
      atTop (𝓝 0) from by
        simpa using (tendsto_densityRemainderErrorScale hW hlong).const_mul
          (remainderHodgeConstant L z / ε))
  filter_upwards [hpos, hlong, hq] with n hn hl hqn
  have hN : 0 < N n := by
    apply (Nat.cast_pos (α := ℝ)).mp
    exact (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _).trans_le hl
  exact intervalRemainderMaxDifference_normalized_markov hμ
    (W n) (p n) (q n) (N n) hn hN hqn z hε

/-- The paper's actual floor/modulus decomposition instantiates the
residual-length condition automatically. -/
theorem densityRemainder_normalized_tendsto
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {W m : ℕ → ℕ} (hW : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, (W n : ℝ) ^ (101 / 100 : ℝ) ≤ m n * W n)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (intervalRowsLaw (W n)
      (densityCellCount (m n) (W n) * densityCellSites (W n) +
        densityRemainderSites (m n) (W n)) μ).real
      {x | ε ≤ |intervalRemainderMaxDifference (W n)
        (densityCellCount (m n) (W n) * densityCellSites (W n))
        (densityRemainderSites (m n) (W n)) z x / (m n * W n)|})
      atTop (𝓝 0) := by
  have hl : ∀ᶠ n in atTop,
      (W n : ℝ) ^ (101 / 100 : ℝ) ≤ ((m n * W n : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul] using hlong
  simpa only [Nat.cast_mul] using
    (intervalRemainderMaxDifference_normalized_tendsto hμ (W := W)
      (p := fun n => densityCellCount (m n) (W n) * densityCellSites (W n))
      (q := fun n => densityRemainderSites (m n) (W n))
      (N := fun n => m n * W n) hW hl
      (Eventually.of_forall fun n => (densityRemainderSites_lt (m n) (W n)).le) z hε)

end BernoulliSection10
