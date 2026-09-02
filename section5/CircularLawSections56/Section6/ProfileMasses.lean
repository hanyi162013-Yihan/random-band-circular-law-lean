import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Profile masses and normalized compact cores

This file contains the deterministic part of the Riemann-mass argument in Section 6.
The two genuinely analytic statements--convergence of the full and truncated BV mesh
sums--are ordinary hypotheses of `normalizedCoreMass_tendsto_of_riemannSums`.  The
quotient limit, complementary tail limit, exhaustion in the radius, and all finite
normalization calculations are proved here.
-/

open Filter Topology
open scoped BigOperators

namespace CircularLawSections56.Section6

section RiemannMassRatios

/-- The fraction of the total sampled profile mass lying in a fixed core. -/
noncomputable def normalizedCoreMass
    (coreRawMass normalizer : ℕ → ℝ) (n : ℕ) : ℝ :=
  coreRawMass n / normalizer n

/-- The normalized tail is defined as the complementary core mass. -/
noncomputable def normalizedTailMass
    (coreRawMass normalizer : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 - normalizedCoreMass coreRawMass normalizer n

@[simp]
theorem normalizedTailMass_eq_one_sub
    (coreRawMass normalizer : ℕ → ℝ) (n : ℕ) :
    normalizedTailMass coreRawMass normalizer n =
      1 - normalizedCoreMass coreRawMass normalizer n :=
  rfl

/-- Nonnegative raw core mass below a positive normalizer gives a normalized core mass
in `[0,1]`. -/
theorem normalizedCoreMass_mem_unitInterval
    (coreRawMass normalizer : ℕ → ℝ) (n : ℕ)
    (hNormalizer : 0 < normalizer n)
    (hCoreNonneg : 0 ≤ coreRawMass n)
    (hCoreLe : coreRawMass n ≤ normalizer n) :
    0 ≤ normalizedCoreMass coreRawMass normalizer n ∧
      normalizedCoreMass coreRawMass normalizer n ≤ 1 := by
  constructor
  · exact div_nonneg hCoreNonneg hNormalizer.le
  · exact (div_le_one hNormalizer).2 hCoreLe

/-- The complementary normalized tail inherits the unit-interval bounds. -/
theorem normalizedTailMass_mem_unitInterval
    (coreRawMass normalizer : ℕ → ℝ) (n : ℕ)
    (hNormalizer : 0 < normalizer n)
    (hCoreNonneg : 0 ≤ coreRawMass n)
    (hCoreLe : coreRawMass n ≤ normalizer n) :
    0 ≤ normalizedTailMass coreRawMass normalizer n ∧
      normalizedTailMass coreRawMass normalizer n ≤ 1 := by
  have hCore := normalizedCoreMass_mem_unitInterval
    coreRawMass normalizer n hNormalizer hCoreNonneg hCoreLe
  constructor
  · exact sub_nonneg.2 hCore.2
  · exact sub_le_self 1 hCore.1

/-- The quotient step in the Riemann-masses lemma.

In the application, `bandwidth n = W_n`, `normalizer n = Z_{N,W}`, and
`coreRawMass n` is the unnormalized sum over `|s| ≤ ⌊R W_n⌋`.  Thus the two
`Tendsto` assumptions are precisely the external full and truncated BV Riemann-sum
theorems. -/
theorem normalizedCoreMass_tendsto_of_riemannSums
    (coreRawMass normalizer bandwidth : ℕ → ℝ) (v : ℝ)
    (hBandwidth : ∀ n, bandwidth n ≠ 0)
    (hNormalizerRiemann :
      Tendsto (fun n ↦ normalizer n / bandwidth n) atTop (𝓝 1))
    (hCoreRiemann :
      Tendsto (fun n ↦ coreRawMass n / bandwidth n) atTop (𝓝 v)) :
    Tendsto (normalizedCoreMass coreRawMass normalizer) atTop (𝓝 v) := by
  have hRatio := hCoreRiemann.div hNormalizerRiemann one_ne_zero
  have hCancel :
      ((fun n ↦ coreRawMass n / bandwidth n) /
          (fun n ↦ normalizer n / bandwidth n)) =
        normalizedCoreMass coreRawMass normalizer := by
    funext n
    exact div_div_div_cancel_right₀ (hBandwidth n) _ _
  rw [hCancel] at hRatio
  simpa using hRatio

/-- Once the normalized core converges, its complementary tail converges to the
complementary limiting mass. -/
theorem normalizedTailMass_tendsto
    (coreRawMass normalizer : ℕ → ℝ) (v : ℝ)
    (hCore :
      Tendsto (normalizedCoreMass coreRawMass normalizer) atTop (𝓝 v)) :
    Tendsto (normalizedTailMass coreRawMass normalizer) atTop (𝓝 (1 - v)) := by
  change Tendsto
    (fun n ↦ 1 - normalizedCoreMass coreRawMass normalizer n)
    atTop (𝓝 (1 - v))
  have hOne : Tendsto (fun _n : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  exact hOne.sub hCore

/-- The normalized core and tail conclusions of the Riemann-masses lemma, with the BV
Riemann-sum inputs kept visible as theorem hypotheses. -/
theorem normalizedCoreTailMass_tendsto_of_riemannSums
    (coreRawMass normalizer bandwidth : ℕ → ℝ) (v : ℝ)
    (hBandwidth : ∀ n, bandwidth n ≠ 0)
    (hNormalizerRiemann :
      Tendsto (fun n ↦ normalizer n / bandwidth n) atTop (𝓝 1))
    (hCoreRiemann :
      Tendsto (fun n ↦ coreRawMass n / bandwidth n) atTop (𝓝 v)) :
    Tendsto (normalizedCoreMass coreRawMass normalizer) atTop (𝓝 v) ∧
      Tendsto (normalizedTailMass coreRawMass normalizer) atTop (𝓝 (1 - v)) := by
  have hCore := normalizedCoreMass_tendsto_of_riemannSums
    coreRawMass normalizer bandwidth v hBandwidth hNormalizerRiemann hCoreRiemann
  exact ⟨hCore, normalizedTailMass_tendsto coreRawMass normalizer v hCore⟩

/-- If raw core and tail sums partition the normalizer, normalized raw tail mass really
is `1 - normalized core mass`.  The nonzero assumption is necessary because division
by zero in `ℝ` is totalized. -/
theorem normalized_rawTail_eq_one_sub_core
    {coreRawMass tailRawMass normalizer : ℝ}
    (hNormalizer : normalizer ≠ 0)
    (hPartition : coreRawMass + tailRawMass = normalizer) :
    tailRawMass / normalizer = 1 - coreRawMass / normalizer := by
  have hTail : tailRawMass = normalizer - coreRawMass := by
    apply (eq_sub_iff_add_eq).2
    simpa [add_comm] using hPartition
  rw [hTail, sub_div, div_self hNormalizer]

/-- Sequence form of `normalized_rawTail_eq_one_sub_core`. -/
theorem normalized_rawTail_tendsto
    (coreRawMass tailRawMass normalizer : ℕ → ℝ) (v : ℝ)
    (hNormalizer : ∀ n, normalizer n ≠ 0)
    (hPartition : ∀ n, coreRawMass n + tailRawMass n = normalizer n)
    (hCore : Tendsto
      (fun n ↦ coreRawMass n / normalizer n) atTop (𝓝 v)) :
    Tendsto (fun n ↦ tailRawMass n / normalizer n) atTop (𝓝 (1 - v)) := by
  have hComplement :
      (fun n ↦ tailRawMass n / normalizer n) =
        (fun n ↦ 1 - coreRawMass n / normalizer n) := by
    funext n
    exact normalized_rawTail_eq_one_sub_core
      (hNormalizer n) (hPartition n)
  rw [hComplement]
  simpa using tendsto_const_nhds.sub hCore

/-- Full paper-facing ratio statement: external BV Riemann-sum convergence for the
normalizer and raw core implies convergence of both the raw core and raw tail ratios. -/
theorem rawCoreTailMass_tendsto_of_riemannSums
    (coreRawMass tailRawMass normalizer bandwidth : ℕ → ℝ) (v : ℝ)
    (hBandwidth : ∀ n, bandwidth n ≠ 0)
    (hNormalizer : ∀ n, normalizer n ≠ 0)
    (hPartition : ∀ n, coreRawMass n + tailRawMass n = normalizer n)
    (hNormalizerRiemann :
      Tendsto (fun n ↦ normalizer n / bandwidth n) atTop (𝓝 1))
    (hCoreRiemann :
      Tendsto (fun n ↦ coreRawMass n / bandwidth n) atTop (𝓝 v)) :
    Tendsto (fun n ↦ coreRawMass n / normalizer n) atTop (𝓝 v) ∧
      Tendsto (fun n ↦ tailRawMass n / normalizer n) atTop (𝓝 (1 - v)) := by
  have hCore := normalizedCoreMass_tendsto_of_riemannSums
    coreRawMass normalizer bandwidth v hBandwidth
    hNormalizerRiemann hCoreRiemann
  have hCoreRatio : Tendsto
      (fun n ↦ coreRawMass n / normalizer n) atTop (𝓝 v) := by
    change Tendsto (normalizedCoreMass coreRawMass normalizer) atTop (𝓝 v)
    exact hCore
  exact ⟨hCoreRatio, normalized_rawTail_tendsto
    coreRawMass tailRawMass normalizer v hNormalizer hPartition hCoreRatio⟩

end RiemannMassRatios

section RadiusExhaustion

/-- The limiting tail mass associated with a limiting core mass `v_R`. -/
noncomputable def limitingTailMass (coreMass : ℕ → ℝ) (R : ℕ) : ℝ :=
  1 - coreMass R

@[simp]
theorem coreMass_add_limitingTailMass (coreMass : ℕ → ℝ) (R : ℕ) :
    coreMass R + limitingTailMass coreMass R = 1 := by
  simp [limitingTailMass]

/-- Expanding cores have nondecreasing limiting mass.  This finite-sum form isolates
the only order fact needed for `v_R ↑ 1`. -/
theorem coreWeightMass_monotone_of_nested
    {ι : Type*}
    (core : ℕ → Finset ι) (weight : ι → ℝ)
    (hNested : Monotone core) (hWeight : ∀ i, 0 ≤ weight i) :
    Monotone (fun R ↦ ∑ i ∈ core R, weight i) := by
  intro R S hRS
  exact Finset.sum_le_sum_of_subset_of_nonneg (hNested hRS)
    (fun i _ _ ↦ hWeight i)

/-- Complementation turns increasing core masses into decreasing tail masses. -/
theorem limitingTailMass_antitone_of_core_monotone
    (coreMass : ℕ → ℝ) (hCoreMonotone : Monotone coreMass) :
    Antitone (limitingTailMass coreMass) := by
  intro R S hRS
  exact sub_le_sub_left (hCoreMonotone hRS) 1

/-- If `v_R → 1`, then `t_R = 1 - v_R → 0`. -/
theorem limitingTailMass_tendsto_zero
    (coreMass : ℕ → ℝ)
    (hCoreOne : Tendsto coreMass atTop (𝓝 1)) :
    Tendsto (limitingTailMass coreMass) atTop (𝓝 0) := by
  change Tendsto (fun R ↦ 1 - coreMass R) atTop (𝓝 0)
  have hOne : Tendsto (fun _R : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  simpa using hOne.sub hCoreOne

/-- A deterministic vanishing upper bound is enough to prove `t_R → 0`.  This is the
quantitative interface for the integrable-tail estimate in the profile application. -/
theorem limitingTailMass_tendsto_zero_of_bound
    (coreMass error : ℕ → ℝ)
    (hTailNonneg : ∀ R, 0 ≤ limitingTailMass coreMass R)
    (hTailLe : ∀ R, limitingTailMass coreMass R ≤ error R)
    (hErrorZero : Tendsto error atTop (𝓝 0)) :
    Tendsto (limitingTailMass coreMass) atTop (𝓝 0) := by
  exact squeeze_zero hTailNonneg hTailLe hErrorZero

/-- A vanishing quantitative tail bound also proves `v_R → 1`. -/
theorem coreMass_tendsto_one_of_tail_bound
    (coreMass error : ℕ → ℝ)
    (hTailNonneg : ∀ R, 0 ≤ limitingTailMass coreMass R)
    (hTailLe : ∀ R, limitingTailMass coreMass R ≤ error R)
    (hErrorZero : Tendsto error atTop (𝓝 0)) :
    Tendsto coreMass atTop (𝓝 1) := by
  have hTailZero := limitingTailMass_tendsto_zero_of_bound
    coreMass error hTailNonneg hTailLe hErrorZero
  have hOne : Tendsto (fun _R : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hDifference : Tendsto
      (fun R ↦ 1 - limitingTailMass coreMass R) atTop (𝓝 1) := by
    simpa using hOne.sub hTailZero
  simpa [limitingTailMass] using hDifference

/-- The exact `v_R ↑ 1`, `t_R ↓ 0` package used by the sparse mean squeeze. -/
theorem coreTailMass_monotone_tendsto
    (coreMass : ℕ → ℝ)
    (hCoreMonotone : Monotone coreMass)
    (hCoreOne : Tendsto coreMass atTop (𝓝 1)) :
    Monotone coreMass ∧
      Antitone (limitingTailMass coreMass) ∧
      Tendsto coreMass atTop (𝓝 1) ∧
      Tendsto (limitingTailMass coreMass) atTop (𝓝 0) := by
  exact ⟨hCoreMonotone,
    limitingTailMass_antitone_of_core_monotone coreMass hCoreMonotone,
    hCoreOne, limitingTailMass_tendsto_zero coreMass hCoreOne⟩

/-- Quantitative version of `coreTailMass_monotone_tendsto`: an explicit vanishing
tail majorant supplies both limiting statements. -/
theorem coreTailMass_monotone_tendsto_of_tail_bound
    (coreMass error : ℕ → ℝ)
    (hCoreMonotone : Monotone coreMass)
    (hTailNonneg : ∀ R, 0 ≤ limitingTailMass coreMass R)
    (hTailLe : ∀ R, limitingTailMass coreMass R ≤ error R)
    (hErrorZero : Tendsto error atTop (𝓝 0)) :
    Monotone coreMass ∧
      Antitone (limitingTailMass coreMass) ∧
      Tendsto coreMass atTop (𝓝 1) ∧
      Tendsto (limitingTailMass coreMass) atTop (𝓝 0) := by
  have hTailZero := limitingTailMass_tendsto_zero_of_bound
    coreMass error hTailNonneg hTailLe hErrorZero
  have hCoreOne := coreMass_tendsto_one_of_tail_bound
    coreMass error hTailNonneg hTailLe hErrorZero
  exact ⟨hCoreMonotone,
    limitingTailMass_antitone_of_core_monotone coreMass hCoreMonotone,
    hCoreOne, hTailZero⟩

/-- Core bounds transport to complementary tail bounds. -/
theorem limitingTailMass_mem_unitInterval
    (coreMass : ℕ → ℝ) (R : ℕ)
    (hCoreNonneg : 0 ≤ coreMass R) (hCoreLeOne : coreMass R ≤ 1) :
    0 ≤ limitingTailMass coreMass R ∧ limitingTailMass coreMass R ≤ 1 := by
  constructor
  · exact sub_nonneg.2 hCoreLeOne
  · exact sub_le_self 1 hCoreNonneg

/-- Quantitative equivalence between small tail mass and core mass close to one. -/
theorem limitingTailMass_le_iff
    (coreMass : ℕ → ℝ) (R : ℕ) (error : ℝ) :
    limitingTailMass coreMass R ≤ error ↔ 1 - error ≤ coreMass R := by
  simp only [limitingTailMass]
  constructor
  · intro h
    have h' : 1 ≤ error + coreMass R :=
      (sub_le_iff_le_add).1 h
    exact (sub_le_iff_le_add).2 (by simpa [add_comm] using h')
  · intro h
    have h' : 1 ≤ coreMass R + error :=
      (sub_le_iff_le_add).1 h
    exact (sub_le_iff_le_add).2 (by simpa [add_comm] using h')

end RadiusExhaustion

section NormalizedCoreWeights

variable {ι : Type*}

/-- Total raw weight of a finite core. -/
noncomputable def coreWeightMass (core : Finset ι) (weight : ι → ℝ) : ℝ :=
  ∑ i ∈ core, weight i

/-- The profile weights after restricting to a core and renormalizing there. -/
noncomputable def normalizedCoreWeights
    (core : Finset ι) (weight : ι → ℝ) (i : ι) : ℝ :=
  weight i / coreWeightMass core weight

theorem coreWeightMass_nonneg
    (core : Finset ι) (weight : ι → ℝ)
    (hWeight : ∀ i ∈ core, 0 ≤ weight i) :
    0 ≤ coreWeightMass core weight := by
  exact Finset.sum_nonneg hWeight

/-- A positive weight at one active offset makes the whole core mass positive. -/
theorem coreWeightMass_pos
    (core : Finset ι) (weight : ι → ℝ) (i₀ : ι)
    (hWeight : ∀ i ∈ core, 0 ≤ weight i)
    (hi₀ : i₀ ∈ core) (hPositive : 0 < weight i₀) :
    0 < coreWeightMass core weight := by
  exact Finset.sum_pos' hWeight ⟨i₀, hi₀, hPositive⟩

/-- Core renormalization gives total mass one. -/
theorem normalizedCoreWeights_sum_eq_one
    (core : Finset ι) (weight : ι → ℝ)
    (hMass : coreWeightMass core weight ≠ 0) :
    ∑ i ∈ core, normalizedCoreWeights core weight i = 1 := by
  unfold normalizedCoreWeights
  rw [← Finset.sum_div]
  exact div_self hMass

theorem normalizedCoreWeights_nonneg
    (core : Finset ι) (weight : ι → ℝ) (i : ι)
    (hWeight : 0 ≤ weight i) (hMass : 0 ≤ coreWeightMass core weight) :
    0 ≤ normalizedCoreWeights core weight i := by
  exact div_nonneg hWeight hMass

/-- Every active normalized core weight lies in `[0,1]`. -/
theorem normalizedCoreWeights_mem_unitInterval
    (core : Finset ι) (weight : ι → ℝ) (i : ι)
    (hi : i ∈ core) (hWeight : ∀ j ∈ core, 0 ≤ weight j)
    (hMass : 0 < coreWeightMass core weight) :
    0 ≤ normalizedCoreWeights core weight i ∧
      normalizedCoreWeights core weight i ≤ 1 := by
  have hPointLeMass : weight i ≤ coreWeightMass core weight :=
    Finset.single_le_sum hWeight hi
  constructor
  · exact div_nonneg (hWeight i hi) hMass.le
  · exact (div_le_one hMass).2 hPointLeMass

/-- Summing weights after division by a global profile normalizer divides their core
mass by the same normalizer. -/
theorem coreWeightMass_div_normalizer
    (core : Finset ι) (weight : ι → ℝ) (normalizer : ℝ) :
    coreWeightMass core (fun i ↦ weight i / normalizer) =
      coreWeightMass core weight / normalizer := by
  exact (Finset.sum_div core weight normalizer).symm

/-- Global normalization cancels when the core is normalized a second time. -/
theorem normalizedCoreWeights_div_normalizer
    (core : Finset ι) (weight : ι → ℝ) (normalizer : ℝ) (i : ι)
    (hNormalizer : normalizer ≠ 0) :
    normalizedCoreWeights core (fun j ↦ weight j / normalizer) i =
      normalizedCoreWeights core weight i := by
  unfold normalizedCoreWeights
  rw [coreWeightMass_div_normalizer]
  exact div_div_div_cancel_right₀ hNormalizer _ _

/-- Pointwise and total-mass bounds transport through core normalization. -/
theorem normalizedCoreWeights_bounds
    (core : Finset ι) (weight : ι → ℝ) (i : ι)
    {pointLower pointUpper massLower massUpper : ℝ}
    (hPointLowerNonneg : 0 ≤ pointLower)
    (hPointLower : pointLower ≤ weight i)
    (hPointUpper : weight i ≤ pointUpper)
    (hMassLower : 0 < massLower)
    (hMassLowerLe : massLower ≤ coreWeightMass core weight)
    (hMassUpper : coreWeightMass core weight ≤ massUpper) :
    pointLower / massUpper ≤ normalizedCoreWeights core weight i ∧
      normalizedCoreWeights core weight i ≤ pointUpper / massLower := by
  have hWeightNonneg : 0 ≤ weight i := hPointLowerNonneg.trans hPointLower
  have hMassPositive : 0 < coreWeightMass core weight :=
    hMassLower.trans_le hMassLowerLe
  constructor
  · exact div_le_div₀ hWeightNonneg hPointLower hMassPositive hMassUpper
  · exact div_le_div₀ (hWeightNonneg.trans hPointUpper) hPointUpper
      hMassLower hMassLowerLe

/-- The comparable-weight form used for a fixed compact core.  If the raw profile is
between `pointLower` and `pointUpper`, while its core sum is between fixed multiples of
the bandwidth, then normalized core weights are between fixed multiples of `1/W`. -/
theorem normalizedCore_weights_comparable
    (core : Finset ι) (weight : ι → ℝ) (i : ι)
    {bandwidth pointLower pointUpper coreLower coreUpper : ℝ}
    (hBandwidth : 0 < bandwidth)
    (hPointLowerNonneg : 0 ≤ pointLower)
    (hPointLower : pointLower ≤ weight i)
    (hPointUpper : weight i ≤ pointUpper)
    (hCoreLower : 0 < coreLower)
    (hCoreLowerMass :
      coreLower * bandwidth ≤ coreWeightMass core weight)
    (hCoreUpperMass :
      coreWeightMass core weight ≤ coreUpper * bandwidth) :
    (pointLower / coreUpper) / bandwidth ≤
        normalizedCoreWeights core weight i ∧
      normalizedCoreWeights core weight i ≤
        (pointUpper / coreLower) / bandwidth := by
  have hBounds := normalizedCoreWeights_bounds core weight i
    hPointLowerNonneg hPointLower hPointUpper
    (mul_pos hCoreLower hBandwidth) hCoreLowerMass
    hCoreUpperMass
  simpa only [div_div] using hBounds

/-- Uniform-on-the-core wrapper for `normalizedCore_weights_comparable`. -/
theorem normalizedCore_weights_comparable_on
    (core : Finset ι) (weight : ι → ℝ)
    {bandwidth pointLower pointUpper coreLower coreUpper : ℝ}
    (hBandwidth : 0 < bandwidth)
    (hPointLowerNonneg : 0 ≤ pointLower)
    (hPointLower : ∀ i ∈ core, pointLower ≤ weight i)
    (hPointUpper : ∀ i ∈ core, weight i ≤ pointUpper)
    (hCoreLower : 0 < coreLower)
    (hCoreLowerMass :
      coreLower * bandwidth ≤ coreWeightMass core weight)
    (hCoreUpperMass :
      coreWeightMass core weight ≤ coreUpper * bandwidth) :
    ∀ i ∈ core,
      (pointLower / coreUpper) / bandwidth ≤
          normalizedCoreWeights core weight i ∧
        normalizedCoreWeights core weight i ≤
          (pointUpper / coreLower) / bandwidth := by
  intro i hi
  exact normalizedCore_weights_comparable core weight i
    hBandwidth hPointLowerNonneg (hPointLower i hi) (hPointUpper i hi)
    hCoreLower hCoreLowerMass hCoreUpperMass

end NormalizedCoreWeights

end CircularLawSections56.Section6
