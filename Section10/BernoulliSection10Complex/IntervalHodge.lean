import BernoulliSection10Complex.HodgeFamily
import BernoulliSection10Complex.ProductMarginal

/-!
# Interval Hodge control

This module upgrades the concrete one-site envelope to products along a
nonempty interval.  It isolates the deterministic submultiplicativity and
inverse-product argument used in the second half of Lemma 10.6.
-/

open scoped BigOperators Matrix ENNReal Matrix.Norms.Frobenius
open MeasureTheory

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open Matrix Set Set.powersetCard
open BernoulliLinearAlgebra

set_option maxHeartbeats 800000

/-! ## Generic products of nonsingular matrices -/

/-- The simultaneous forward/inverse positive-log loss of a square matrix. -/
def matrixHodgeLoss {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ℝ :=
  Real.posLog ‖A‖ + Real.posLog ‖A⁻¹‖

/-- Frobenius submultiplicativity, together with reversal of a nonsingular
inverse product, makes the Hodge loss subadditive. -/
theorem matrixHodgeLoss_mul_le {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : IsUnit A.det) (hB : IsUnit B.det) :
    matrixHodgeLoss (A * B) ≤ matrixHodgeLoss A + matrixHodgeLoss B := by
  have hf : Real.posLog ‖A * B‖ ≤
      Real.posLog ‖A‖ + Real.posLog ‖B‖ := by
    exact (Real.posLog_le_posLog (norm_nonneg _)
      (Matrix.frobenius_norm_mul A B)).trans Real.posLog_mul
  have hinv : (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
    apply Matrix.inv_eq_left_inv
    calc
      (B⁻¹ * A⁻¹) * (A * B) = B⁻¹ * ((A⁻¹ * A) * B) := by
        noncomm_ring
      _ = B⁻¹ * B := by rw [Matrix.nonsing_inv_mul A hA, Matrix.one_mul]
      _ = 1 := Matrix.nonsing_inv_mul B hB
  have hi : Real.posLog ‖(A * B)⁻¹‖ ≤
      Real.posLog ‖A⁻¹‖ + Real.posLog ‖B⁻¹‖ := by
    rw [hinv]
    have h := (Real.posLog_le_posLog (norm_nonneg _)
      (Matrix.frobenius_norm_mul B⁻¹ A⁻¹)).trans Real.posLog_mul
    linarith
  unfold matrixHodgeLoss
  linarith

theorem list_prod_det_isUnit {n : Type*} [Fintype n] [DecidableEq n]
    (l : List (Matrix n n ℂ))
    (h : ∀ A ∈ l, IsUnit A.det) : IsUnit l.prod.det := by
  induction l with
  | nil => simp
  | cons A l ih =>
      rw [List.prod_cons, Matrix.det_mul]
      exact (h A (by simp)).mul (ih (by
        intro B hB
        exact h B (by simp [hB])))

/-- A nonempty product has Hodge loss at most the sum of the factor losses.
The nonempty hypothesis avoids an artificial Frobenius loss for the identity
matrix. -/
theorem matrixHodgeLoss_list_prod_le {n : Type*} [Fintype n] [DecidableEq n]
    (l : List (Matrix n n ℂ)) (hne : l ≠ [])
    (h : ∀ A ∈ l, IsUnit A.det) :
    matrixHodgeLoss l.prod ≤ (l.map matrixHodgeLoss).sum := by
  induction l with
  | nil => contradiction
  | cons A l ih =>
      cases l with
      | nil => simp
      | cons B l =>
          rw [List.prod_cons, List.map_cons, List.sum_cons]
          calc
            matrixHodgeLoss (A * (B :: l).prod) ≤
                matrixHodgeLoss A + matrixHodgeLoss (B :: l).prod :=
              matrixHodgeLoss_mul_le A (B :: l).prod
                (h A (by simp))
                (list_prod_det_isUnit (B :: l) (by
                  intro C hC
                  exact h C (by simp [hC])))
            _ ≤ matrixHodgeLoss A +
                ((B :: l).map matrixHodgeLoss).sum := by
              gcongr
              exact ih (by simp) (by
                intro C hC
                exact h C (by simp [hC]))

/-! ## The concrete interval envelope -/

/-- Restrict an interval configuration to the physical rows at one site. -/
def intervalSiteRestriction (W s : ℕ) (x : IntervalRows W s) (j : Fin s) :
    IntervalRows W 1 := fun i =>
  x (intervalRowIndex j (finProdFinEquiv.symm i).2)

/-- The injective coordinate map underlying restriction to a fixed site. -/
def intervalSiteRowEmbedding (W s : ℕ) (j : Fin s) :
    Fin (1 * W) ↪ Fin (s * W) where
  toFun i := intervalRowIndex j (finProdFinEquiv.symm i).2
  inj' := by
    intro i k hik
    apply finProdFinEquiv.symm.injective
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · have hp := finProdFinEquiv.injective hik
      exact (Prod.mk.inj hp).2

/-- The rows at any fixed site have exactly the one-site product law. -/
theorem intervalSiteRestriction_measurePreserving
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (j : Fin s) :
    MeasurePreserving (fun x : IntervalRows W s =>
        intervalSiteRestriction W s x j)
      (intervalRowsLaw W s μ) (intervalRowsLaw W 1 μ) := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (physicalRowLaw W μ) := by
    unfold physicalRowLaw
    infer_instance
  have h := measurePreserving_pi_restrict_embedding
    (physicalRowLaw W μ) (intervalSiteRowEmbedding W s j)
  change MeasurePreserving (fun x : IntervalRows W s =>
      intervalSiteRestriction W s x j)
    (Measure.pi fun _ : Fin (s * W) => physicalRowLaw W μ)
    (Measure.pi fun _ : Fin (1 * W) => physicalRowLaw W μ)
  convert h using 1
  ext x i
  rfl

theorem intervalSiteBlocks_restriction (W s : ℕ) (z : ℂ)
    (x : IntervalRows W s) (j : Fin s) :
    intervalSiteBlocks z (intervalSiteRestriction W s x j) 0 =
      intervalSiteBlocks z x j := by
  apply PhysicalBlocks.ext <;> ext a c <;>
    simp [intervalSiteBlocks, intervalPhysicalRow, intervalSiteRestriction,
      intervalRowIndex]

/-- Sum of the literal one-site envelopes over an interval. -/
def intervalHodgeEnvelope (W s : ℕ) (z : ℂ) (x : IntervalRows W s) : ℝ :=
  ∑ j : Fin s, oneSiteHodgeEnvelope W z (intervalSiteRestriction W s x j)

theorem measurable_intervalSiteHodgeEnvelope
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (z : ℂ) (j : Fin s) :
    Measurable (fun x : IntervalRows W s =>
      oneSiteHodgeEnvelope W z (intervalSiteRestriction W s x j)) :=
  (measurable_oneSiteHodgeEnvelope W z).comp
    (intervalSiteRestriction_measurePreserving hμ W s j).measurable

theorem measurable_intervalHodgeEnvelope
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (z : ℂ) :
    Measurable (intervalHodgeEnvelope W s z) := by
  unfold intervalHodgeEnvelope
  apply Finset.measurable_fun_sum
  intro j _hj
  exact measurable_intervalSiteHodgeEnvelope hμ W s z j

/-- Pulling the one-site second-moment estimate through a site marginal is
lossless. -/
theorem intervalSiteHodgeEnvelope_memLp_two
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) (j : Fin s) :
    MemLp (fun x : IntervalRows W s =>
      oneSiteHodgeEnvelope W z (intervalSiteRestriction W s x j)) 2
      (intervalRowsLaw W s μ) := by
  have h := (oneSiteHodgeEnvelope_memLp_two hμ W hW z).comp_measurePreserving
    (intervalSiteRestriction_measurePreserving hμ W s j)
  change MemLp (oneSiteHodgeEnvelope W z ∘
      fun x : IntervalRows W s => intervalSiteRestriction W s x j) 2
    (intervalRowsLaw W s μ)
  exact h

/-- The sum of one-site envelopes over a finite interval has finite second
moment. -/
theorem intervalHodgeEnvelope_memLp_two
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    MemLp (intervalHodgeEnvelope W s z) 2 (intervalRowsLaw W s μ) := by
  unfold intervalHodgeEnvelope
  exact memLp_finsetSum Finset.univ fun j _hj =>
    intervalSiteHodgeEnvelope_memLp_two hμ W s hW z j

theorem intervalHodgeEnvelope_integrable
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    Integrable (intervalHodgeEnvelope W s z) (intervalRowsLaw W s μ) := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (intervalRowsLaw W s μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  exact (intervalHodgeEnvelope_memLp_two hμ W s hW z).integrable one_le_two

/-- The interval envelope has expectation at most `s` times the explicit
one-site bound.  No independence certificate is exposed to callers. -/
theorem intervalHodgeEnvelope_lintegral_le
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal (intervalHodgeEnvelope W s z x)
        ∂intervalRowsLaw W s μ) ≤
      (s : ℝ≥0∞) * oneSiteHodgeIntegralBound L W z := by
  let f : Fin s → IntervalRows W s → ℝ := fun j x =>
    oneSiteHodgeEnvelope W z (intervalSiteRestriction W s x j)
  have hf_nonneg (j : Fin s) (x : IntervalRows W s) : 0 ≤ f j x :=
    oneSiteHodgeEnvelope_nonneg W z _
  have hf_meas (j : Fin s) : Measurable (fun x => ENNReal.ofReal (f j x)) :=
    (measurable_intervalSiteHodgeEnvelope hμ W s z j).ennreal_ofReal
  have hsite (j : Fin s) :
      (∫⁻ x, ENNReal.ofReal (f j x) ∂intervalRowsLaw W s μ) ≤
        oneSiteHodgeIntegralBound L W z := by
    have hmap := (intervalSiteRestriction_measurePreserving hμ W s j).lintegral_comp
      (measurable_oneSiteHodgeEnvelope W z).ennreal_ofReal
    rw [hmap]
    exact oneSiteHodgeEnvelope_lintegral_le hμ W hW z
  calc
    (∫⁻ x, ENNReal.ofReal (intervalHodgeEnvelope W s z x)
        ∂intervalRowsLaw W s μ) =
        ∫⁻ x, ∑ j : Fin s, ENNReal.ofReal (f j x)
          ∂intervalRowsLaw W s μ := by
      congr 1
      funext x
      unfold intervalHodgeEnvelope
      exact ENNReal.ofReal_sum_of_nonneg
        (fun j _hj => hf_nonneg j x)
    _ = ∑ j : Fin s,
        ∫⁻ x, ENNReal.ofReal (f j x) ∂intervalRowsLaw W s μ := by
      rw [lintegral_finsetSum Finset.univ]
      intro j _hj
      exact hf_meas j
    _ ≤ ∑ _j : Fin s, oneSiteHodgeIntegralBound L W z := by
      exact Finset.sum_le_sum fun j _hj => hsite j
    _ = (s : ℝ≥0∞) * oneSiteHodgeIntegralBound L W z := by
      simp [nsmul_eq_mul]

/-- All interface determinants in a finite interval are nonsingular almost
surely. -/
theorem intervalInterfaceDets_isUnit_ae
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    ∀ᵐ x ∂intervalRowsLaw W s μ, ∀ j : Fin s,
      IsUnit (intervalSiteBlocks z x j).B.det ∧
        IsUnit (intervalSiteBlocks z x j).C.det := by
  rw [ae_all_iff]
  intro j
  have h := (intervalSiteRestriction_measurePreserving hμ W s j).quasiMeasurePreserving.ae
    (oneSiteInterfaceDets_isUnit_ae hμ W hW z)
  simpa only [oneSiteBDet, oneSiteCDet, intervalSiteBlocks_restriction] using h

/-- Deterministic interval part of Lemma 10.6: on the nonsingular interface
locus, the forward and inverse loss of every exterior-degree product is
bounded by the sum of the concrete one-site envelopes. -/
theorem intervalClearedProduct_hodgeLoss_le
    (W s : ℕ) (hs : 0 < s) (z : ℂ) (x : IntervalRows W s)
    (hB : ∀ j : Fin s, IsUnit (intervalSiteBlocks z x j).B.det)
    (hC : ∀ j : Fin s, IsUnit (intervalSiteBlocks z x j).C.det)
    (r : Fin (2 * W + 1)) :
    matrixHodgeLoss (intervalClearedProduct W s z x r) ≤
      intervalHodgeEnvelope W s z x := by
  let M : Fin s → Matrix (powersetCard (Fin W ⊕ Fin W) r.1)
      (powersetCard (Fin W ⊕ Fin W) r.1) ℂ := fun j =>
    intervalClearedStep W z x r j
  let l := List.ofFn fun j : Fin s => M j.rev
  have hl : l ≠ [] := by
    intro heq
    have hlen := congrArg List.length heq
    have : s = 0 := by
      simpa only [l, List.length_ofFn, List.length_nil] using hlen
    omega
  have hr : r.1 ≤ Fintype.card (Fin W ⊕ Fin W) := by simp; omega
  have hunit : ∀ A ∈ l, IsUnit A.det := by
    intro A hA
    simp only [l, List.mem_ofFn] at hA
    obtain ⟨j, rfl⟩ := hA
    unfold M intervalClearedStep
    exact clearedStepCompound_det_isUnit r.1 hr _ _ _ (hB j.rev) (hC j.rev)
  have hprod := matrixHodgeLoss_list_prod_le l hl hunit
  change matrixHodgeLoss l.prod ≤ _
  calc
    matrixHodgeLoss l.prod ≤ (l.map matrixHodgeLoss).sum := hprod
    _ = ∑ j : Fin s, matrixHodgeLoss (M j.rev) := by
      simp only [l, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
    _ ≤ ∑ j : Fin s,
        oneSiteHodgeEnvelope W z (intervalSiteRestriction W s x j.rev) := by
      apply Finset.sum_le_sum
      intro j _hj
      have h := oneSiteHodgeEnvelope_controls W z
        (intervalSiteRestriction W s x j.rev)
        (by simpa only [oneSiteBDet, intervalSiteBlocks_restriction] using hB j.rev)
        (by simpa only [oneSiteCDet, intervalSiteBlocks_restriction] using hC j.rev) r
      simpa only [matrixHodgeLoss, M, intervalClearedStep,
        intervalSiteBlocks_restriction] using h
    _ = intervalHodgeEnvelope W s z x := by
      unfold intervalHodgeEnvelope
      let g : Fin s → ℝ := fun j =>
        oneSiteHodgeEnvelope W z (intervalSiteRestriction W s x j)
      have hrev : (∑ j : Fin s, g (Fin.revPerm j)) = ∑ j : Fin s, g j :=
        Equiv.sum_comp Fin.revPerm g
      simpa only [g, Fin.revPerm_apply] using hrev

/-- Almost-sure interval form of the second display in Lemma 10.6, before
the final manuscript-specific simplification of the explicit constant. -/
theorem intervalClearedProduct_hodgeLoss_le_ae
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (hs : 0 < s) (z : ℂ) :
    ∀ᵐ x ∂intervalRowsLaw W s μ, ∀ r : Fin (2 * W + 1),
      matrixHodgeLoss (intervalClearedProduct W s z x r) ≤
        intervalHodgeEnvelope W s z x := by
  filter_upwards [intervalInterfaceDets_isUnit_ae hμ W s hW z] with x hx
  intro r
  exact intervalClearedProduct_hodgeLoss_le W s hs z x
    (fun j => (hx j).1) (fun j => (hx j).2) r

/-! ## Sharp simultaneous-degree interval envelope -/

/-- Sum over sites of the one-site maximum-over-degrees envelope. -/
def intervalMaxHodgeEnvelope (W s : ℕ) (z : ℂ)
    (x : IntervalRows W s) : ℝ :=
  ∑ j : Fin s,
    oneSiteMaxHodgeEnvelope W z (intervalSiteRestriction W s x j)

theorem measurable_intervalSiteMaxHodgeEnvelope
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (z : ℂ) (j : Fin s) :
    Measurable (fun x : IntervalRows W s ↦
      oneSiteMaxHodgeEnvelope W z (intervalSiteRestriction W s x j)) :=
  (measurable_oneSiteMaxHodgeEnvelope W z).comp
    (intervalSiteRestriction_measurePreserving hμ W s j).measurable

theorem measurable_intervalMaxHodgeEnvelope
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (z : ℂ) :
    Measurable (intervalMaxHodgeEnvelope W s z) := by
  unfold intervalMaxHodgeEnvelope
  apply Finset.measurable_fun_sum
  intro j _hj
  exact measurable_intervalSiteMaxHodgeEnvelope hμ W s z j

theorem intervalSiteMaxHodgeEnvelope_memLp_two
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) (j : Fin s) :
    MemLp (fun x : IntervalRows W s ↦
      oneSiteMaxHodgeEnvelope W z (intervalSiteRestriction W s x j)) 2
      (intervalRowsLaw W s μ) := by
  have h :=
    (oneSiteMaxHodgeEnvelope_memLp_two hμ W hW z).comp_measurePreserving
      (intervalSiteRestriction_measurePreserving hμ W s j)
  change MemLp (oneSiteMaxHodgeEnvelope W z ∘
      fun x : IntervalRows W s ↦ intervalSiteRestriction W s x j) 2
    (intervalRowsLaw W s μ)
  exact h

theorem intervalMaxHodgeEnvelope_memLp_two
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    MemLp (intervalMaxHodgeEnvelope W s z) 2
      (intervalRowsLaw W s μ) := by
  unfold intervalMaxHodgeEnvelope
  exact memLp_finsetSum Finset.univ fun j _hj ↦
    intervalSiteMaxHodgeEnvelope_memLp_two hμ W s hW z j

theorem intervalMaxHodgeEnvelope_integrable
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    Integrable (intervalMaxHodgeEnvelope W s z)
      (intervalRowsLaw W s μ) := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (intervalRowsLaw W s μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  exact (intervalMaxHodgeEnvelope_memLp_two hμ W s hW z).integrable one_le_two

/-- The simultaneous-degree interval envelope has a first moment linear in
the interval length and pays the Corollary 10.3 row cost only once per site. -/
theorem intervalMaxHodgeEnvelope_lintegral_le
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal (intervalMaxHodgeEnvelope W s z x)
        ∂intervalRowsLaw W s μ) ≤
      (s : ℝ≥0∞) * oneSiteMaxHodgeIntegralBound L W z := by
  let f : Fin s → IntervalRows W s → ℝ := fun j x ↦
    oneSiteMaxHodgeEnvelope W z (intervalSiteRestriction W s x j)
  have hf_nonneg (j : Fin s) (x : IntervalRows W s) : 0 ≤ f j x :=
    oneSiteMaxHodgeEnvelope_nonneg W z _
  have hf_meas (j : Fin s) : Measurable (fun x ↦ ENNReal.ofReal (f j x)) :=
    (measurable_intervalSiteMaxHodgeEnvelope hμ W s z j).ennreal_ofReal
  have hsite (j : Fin s) :
      (∫⁻ x, ENNReal.ofReal (f j x) ∂intervalRowsLaw W s μ) ≤
        oneSiteMaxHodgeIntegralBound L W z := by
    have hmap :=
      (intervalSiteRestriction_measurePreserving hμ W s j).lintegral_comp
        (measurable_oneSiteMaxHodgeEnvelope W z).ennreal_ofReal
    rw [hmap]
    exact oneSiteMaxHodgeEnvelope_lintegral_le hμ W hW z
  calc
    (∫⁻ x, ENNReal.ofReal (intervalMaxHodgeEnvelope W s z x)
        ∂intervalRowsLaw W s μ) =
        ∫⁻ x, ∑ j : Fin s, ENNReal.ofReal (f j x)
          ∂intervalRowsLaw W s μ := by
      congr 1
      funext x
      unfold intervalMaxHodgeEnvelope
      exact ENNReal.ofReal_sum_of_nonneg
        (fun j _hj ↦ hf_nonneg j x)
    _ = ∑ j : Fin s,
        ∫⁻ x, ENNReal.ofReal (f j x) ∂intervalRowsLaw W s μ := by
      rw [lintegral_finsetSum Finset.univ]
      intro j _hj
      exact hf_meas j
    _ ≤ ∑ _j : Fin s, oneSiteMaxHodgeIntegralBound L W z := by
      exact Finset.sum_le_sum fun j _hj ↦ hsite j
    _ = (s : ℝ≥0∞) * oneSiteMaxHodgeIntegralBound L W z := by
      simp [nsmul_eq_mul]

/-- Deterministic interval Hodge control with the simultaneous-degree
one-site envelope. -/
theorem intervalClearedProduct_hodgeLoss_le_maxEnvelope
    (W s : ℕ) (hs : 0 < s) (z : ℂ) (x : IntervalRows W s)
    (hB : ∀ j : Fin s, IsUnit (intervalSiteBlocks z x j).B.det)
    (hC : ∀ j : Fin s, IsUnit (intervalSiteBlocks z x j).C.det)
    (r : Fin (2 * W + 1)) :
    matrixHodgeLoss (intervalClearedProduct W s z x r) ≤
      intervalMaxHodgeEnvelope W s z x := by
  let M : Fin s → Matrix (powersetCard (Fin W ⊕ Fin W) r.1)
      (powersetCard (Fin W ⊕ Fin W) r.1) ℂ := fun j ↦
    intervalClearedStep W z x r j
  let l := List.ofFn fun j : Fin s ↦ M j.rev
  have hl : l ≠ [] := by
    intro heq
    have hlen := congrArg List.length heq
    have : s = 0 := by
      simpa only [l, List.length_ofFn, List.length_nil] using hlen
    omega
  have hr : r.1 ≤ Fintype.card (Fin W ⊕ Fin W) := by simp; omega
  have hunit : ∀ A ∈ l, IsUnit A.det := by
    intro A hA
    simp only [l, List.mem_ofFn] at hA
    obtain ⟨j, rfl⟩ := hA
    unfold M intervalClearedStep
    exact clearedStepCompound_det_isUnit r.1 hr _ _ _
      (hB j.rev) (hC j.rev)
  have hprod := matrixHodgeLoss_list_prod_le l hl hunit
  change matrixHodgeLoss l.prod ≤ _
  calc
    matrixHodgeLoss l.prod ≤ (l.map matrixHodgeLoss).sum := hprod
    _ = ∑ j : Fin s, matrixHodgeLoss (M j.rev) := by
      simp only [l, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
    _ ≤ ∑ j : Fin s,
        oneSiteMaxHodgeEnvelope W z
          (intervalSiteRestriction W s x j.rev) := by
      apply Finset.sum_le_sum
      intro j _hj
      have h := oneSiteMaxHodgeEnvelope_controls W z
        (intervalSiteRestriction W s x j.rev)
        (by simpa only [oneSiteBDet, intervalSiteBlocks_restriction] using
          hB j.rev)
        (by simpa only [oneSiteCDet, intervalSiteBlocks_restriction] using
          hC j.rev) r
      simpa only [matrixHodgeLoss, M, intervalClearedStep,
        intervalSiteBlocks_restriction] using h
    _ = intervalMaxHodgeEnvelope W s z x := by
      unfold intervalMaxHodgeEnvelope
      let g : Fin s → ℝ := fun j ↦
        oneSiteMaxHodgeEnvelope W z
          (intervalSiteRestriction W s x j)
      have hrev : (∑ j : Fin s, g (Fin.revPerm j)) = ∑ j : Fin s, g j :=
        Equiv.sum_comp Fin.revPerm g
      simpa only [g, Fin.revPerm_apply] using hrev

/-- Almost-sure interval form of Lemma 10.6 with the improved simultaneous
exterior-degree envelope. -/
theorem intervalClearedProduct_hodgeLoss_le_maxEnvelope_ae
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (hs : 0 < s) (z : ℂ) :
    ∀ᵐ x ∂intervalRowsLaw W s μ, ∀ r : Fin (2 * W + 1),
      matrixHodgeLoss (intervalClearedProduct W s z x r) ≤
        intervalMaxHodgeEnvelope W s z x := by
  filter_upwards [intervalInterfaceDets_isUnit_ae hμ W s hW z] with x hx
  intro r
  exact intervalClearedProduct_hodgeLoss_le_maxEnvelope W s hs z x
    (fun j ↦ (hx j).1) (fun j ↦ (hx j).2) r

end BernoulliSection10Complex
