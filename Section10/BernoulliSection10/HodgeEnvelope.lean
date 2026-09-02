import BernoulliSection10.HodgeIntegrability
import BernoulliSection10.PositiveLog

/-!
# Concrete integrated Hodge envelopes

This module builds the probabilistic envelope in Lemma 10.6 from the literal
one-site cleared exterior matrices.  The coefficient tensors and all
nonvanishing facts are constructed from the physical-row model.
-/

open scoped BigOperators Matrix ENNReal NNReal Matrix.Norms.Frobenius
open MeasureTheory

noncomputable section

namespace BernoulliSection10

open Matrix Set Set.powersetCard
open BernoulliLinearAlgebra

set_option maxHeartbeats 800000

/-! ## A deterministic tensor evaluation bound -/

/-- A row-multiaffine tensor evaluated on rows whose `ℓ¹` norms are at most
`M` grows by at most `(1+M)` per row. -/
theorem norm_multiAffineEval_replicate_le_of_l1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℕ) (M : ℝ) (hM : 0 ≤ M) : ∀ (n : ℕ)
      (c : MultiAffineTensor E (List.replicate n p))
      (x : MultiAffineRows (List.replicate n p)),
      (∀ i : Fin n,
        ∑ a : Fin p, |multiAffineRowsToFinRows p n x i a| ≤ M) →
      ‖multiAffineEval c x‖ ≤ (1 + M) ^ n * ‖c‖ := by
  intro n
  induction n with
  | zero =>
      intro c x hx
      change ‖c‖ ≤ (1 + M) ^ 0 * ‖c‖
      simp
  | succ n ih =>
      intro c x hx
      let c' := multiAffineHeadEval c x.1
      have hhead : ∑ a : Fin p, |x.1 a| ≤ M := by
        simpa [multiAffineRowsToFinRows] using hx 0
      have hc0 : ‖multiAffineTensorHead c 0‖ ≤ ‖c‖ := by
        exact PiLp.norm_apply_le
          (show PiLp 2 (fun _ : Fin (p + 1) =>
            MultiAffineTensor E (List.replicate n p)) from c) 0
      have hci (a : Fin p) : ‖multiAffineTensorHead c a.succ‖ ≤ ‖c‖ := by
        exact PiLp.norm_apply_le
          (show PiLp 2 (fun _ : Fin (p + 1) =>
            MultiAffineTensor E (List.replicate n p)) from c) a.succ
      have hc' : ‖c'‖ ≤ (1 + M) * ‖c‖ := by
        calc
          ‖c'‖ ≤ ‖multiAffineTensorHead c 0‖ +
              ‖∑ a : Fin p, x.1 a • multiAffineTensorHead c a.succ‖ := by
            exact norm_add_le _ _
          _ ≤ ‖c‖ + ∑ a : Fin p,
              ‖x.1 a • multiAffineTensorHead c a.succ‖ := by
            gcongr
            exact norm_sum_le _ _
          _ ≤ ‖c‖ + ∑ a : Fin p, |x.1 a| * ‖c‖ := by
            gcongr with a
            rw [norm_smul]
            exact mul_le_mul_of_nonneg_left (hci a) (abs_nonneg _)
          _ = ‖c‖ + (∑ a : Fin p, |x.1 a|) * ‖c‖ := by
            rw [Finset.sum_mul]
          _ ≤ ‖c‖ + M * ‖c‖ := by gcongr
          _ = (1 + M) * ‖c‖ := by ring
      have htail : ∀ i : Fin n,
          ∑ a : Fin p,
            |multiAffineRowsToFinRows p n x.2 i a| ≤ M := by
        intro i
        simpa [multiAffineRowsToFinRows] using hx i.succ
      have hi := ih c' x.2 htail
      change ‖multiAffineEval c' x.2‖ ≤ (1 + M) ^ (n + 1) * ‖c‖
      calc
        ‖multiAffineEval c' x.2‖ ≤ (1 + M) ^ n * ‖c'‖ := hi
        _ ≤ (1 + M) ^ n * ((1 + M) * ‖c‖) := by gcongr
        _ = (1 + M) ^ (n + 1) * ‖c‖ := by
          rw [pow_succ]
          ring

/-! ## Forward exterior growth from the concrete coefficient tensor -/

def intervalClearedRecursiveFunction (W s : ℕ) (z : ℂ)
    (r : Fin (2 * W + 1)) :
    MultiAffineRows (List.replicate (s * W) (3 * W)) →
      Matrix (powersetCard (Fin W ⊕ Fin W) r.1)
        (powersetCard (Fin W ⊕ Fin W) r.1) ℂ := fun y ↦
  intervalClearedProduct W s z
    (multiAffineRowsToFinRows (3 * W) (s * W) y) r

def intervalClearedTensor (W s : ℕ) (z : ℂ)
    (r : Fin (2 * W + 1)) :=
  multiAffineTensorOfFunction (intervalClearedRecursiveFunction W s z r)

theorem intervalClearedRecursiveFunction_isMultiAffine
    (W s : ℕ) (z : ℂ) (r : Fin (2 * W + 1)) :
    IsMultiAffine (intervalClearedRecursiveFunction W s z r) := by
  exact intervalClearedProduct_isMultiAffine W s z r

theorem intervalClearedRecursiveFunction_ne_zero
    (W s : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1)) :
    intervalClearedRecursiveFunction W s z r ≠ 0 := by
  intro hzero
  have hvalue := congrFun hzero (identityMultiAffineRows W s)
  exact identityMultiAffineRows_product_ne_zero W s hW z r hvalue

theorem intervalCleared_log_deviation_recursive
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ)
    (r : Fin (2 * W + 1)) :
    (∫⁻ y, ENNReal.ofReal
        |Real.log ‖intervalClearedRecursiveFunction W s z r y‖ -
          Real.log ‖intervalClearedTensor W s z r‖|
        ∂multiAffineRowLaw μ (List.replicate (s * W) (3 * W))) ≤
        multiAffineLogCost L (List.replicate (s * W) (3 * W)) ∧
      ∀ᵐ y ∂multiAffineRowLaw μ (List.replicate (s * W) (3 * W)),
        intervalClearedRecursiveFunction W s z r y ≠ 0 := by
  have hpos : ∀ p ∈ List.replicate (s * W) (3 * W), 0 < p := by
    intro p hp
    simp only [List.mem_replicate] at hp
    omega
  simpa only [intervalClearedTensor] using
    corollary_10_3 hμ
      (intervalClearedRecursiveFunction_isMultiAffine W s z r) hpos
      (intervalClearedRecursiveFunction_ne_zero W s hW z r)

theorem intervalCleared_log_deviation
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ)
    (r : Fin (2 * W + 1)) :
    (∫⁻ x, ENNReal.ofReal
        |Real.log ‖intervalClearedProduct W s z x r‖ -
          Real.log ‖intervalClearedTensor W s z r‖|
        ∂intervalRowsLaw W s μ) ≤
        multiAffineLogCost L (List.replicate (s * W) (3 * W)) ∧
      ∀ᵐ x ∂intervalRowsLaw W s μ,
        intervalClearedProduct W s z x r ≠ 0 := by
  letI := hμ.toIsProbabilityMeasure
  let e := finRowsMultiAffineRowsMeasurableEquiv (3 * W) (s * W)
  have hmp : MeasurePreserving e (intervalRowsLaw W s μ)
      (multiAffineRowLaw μ (List.replicate (s * W) (3 * W))) := by
    simpa only [intervalRowsLaw, physicalRowLaw] using
      finRowsMultiAffineRows_measurePreserving μ (3 * W) (s * W)
  have hrec := intervalCleared_log_deviation_recursive hμ W s hW z r
  constructor
  · have heq := hmp.lintegral_comp_emb e.measurableEmbedding
      (fun y ↦ ENNReal.ofReal
        |Real.log ‖intervalClearedRecursiveFunction W s z r y‖ -
          Real.log ‖intervalClearedTensor W s z r‖|)
    calc
      (∫⁻ x, ENNReal.ofReal
          |Real.log ‖intervalClearedProduct W s z x r‖ -
            Real.log ‖intervalClearedTensor W s z r‖|
          ∂intervalRowsLaw W s μ) =
          ∫⁻ y, ENNReal.ofReal
            |Real.log ‖intervalClearedRecursiveFunction W s z r y‖ -
              Real.log ‖intervalClearedTensor W s z r‖|
            ∂multiAffineRowLaw μ (List.replicate (s * W) (3 * W)) := by
        simpa only [intervalClearedRecursiveFunction, e,
          finRowsMultiAffineRowsMeasurableEquiv_apply,
          multiAffineRowsToFinRows_leftInverse] using heq
      _ ≤ multiAffineLogCost L (List.replicate (s * W) (3 * W)) := hrec.1
  · have hrecMap : ∀ᵐ y ∂Measure.map e (intervalRowsLaw W s μ),
        intervalClearedRecursiveFunction W s z r y ≠ 0 := by
      rw [hmp.map_eq]
      exact hrec.2
    have hflat := e.measurableEmbedding.ae_map_iff.mp hrecMap
    simpa only [intervalClearedRecursiveFunction, e,
      finRowsMultiAffineRowsMeasurableEquiv_apply,
      multiAffineRowsToFinRows_leftInverse] using hflat

/-- Forward positive-log growth in an arbitrary interval, with the concrete
coefficient tensor constructed internally. -/
theorem intervalCleared_posLog_lintegral_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ)
    (r : Fin (2 * W + 1)) :
    (∫⁻ x, ENNReal.ofReal
        (Real.posLog ‖intervalClearedProduct W s z x r‖)
        ∂intervalRowsLaw W s μ) ≤
      multiAffineLogCost L (List.replicate (s * W) (3 * W)) +
        ENNReal.ofReal (Real.posLog ‖intervalClearedTensor W s z r‖) := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (intervalRowsLaw W s μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  have hdev := intervalCleared_log_deviation hμ W s hW z r
  have hpoint (x : IntervalRows W s) :
      ENNReal.ofReal
          (Real.posLog ‖intervalClearedProduct W s z x r‖) ≤
        ENNReal.ofReal
            |Real.log ‖intervalClearedProduct W s z x r‖ -
              Real.log ‖intervalClearedTensor W s z r‖| +
          ENNReal.ofReal
            (Real.posLog ‖intervalClearedTensor W s z r‖) := by
    calc
      ENNReal.ofReal
          (Real.posLog ‖intervalClearedProduct W s z x r‖) ≤
          ENNReal.ofReal
            (|Real.log ‖intervalClearedProduct W s z x r‖ -
                Real.log ‖intervalClearedTensor W s z r‖| +
              Real.posLog ‖intervalClearedTensor W s z r‖) :=
        ENNReal.ofReal_le_ofReal
          (posLog_le_abs_log_sub_log_add_posLog
            ‖intervalClearedProduct W s z x r‖
            ‖intervalClearedTensor W s z r‖)
      _ = _ := ENNReal.ofReal_add (abs_nonneg _)
        (Real.posLog_nonneg (x := ‖intervalClearedTensor W s z r‖))
  calc
    (∫⁻ x, ENNReal.ofReal
        (Real.posLog ‖intervalClearedProduct W s z x r‖)
        ∂intervalRowsLaw W s μ) ≤
        ∫⁻ x, (ENNReal.ofReal
            |Real.log ‖intervalClearedProduct W s z x r‖ -
              Real.log ‖intervalClearedTensor W s z r‖| +
          ENNReal.ofReal
            (Real.posLog ‖intervalClearedTensor W s z r‖))
          ∂intervalRowsLaw W s μ := lintegral_mono hpoint
    _ = (∫⁻ x, ENNReal.ofReal
          |Real.log ‖intervalClearedProduct W s z x r‖ -
            Real.log ‖intervalClearedTensor W s z r‖|
          ∂intervalRowsLaw W s μ) +
        ENNReal.ofReal
          (Real.posLog ‖intervalClearedTensor W s z r‖) := by
      rw [lintegral_add_right _ measurable_const]
      simp
    _ ≤ multiAffineLogCost L (List.replicate (s * W) (3 * W)) +
        ENNReal.ofReal
          (Real.posLog ‖intervalClearedTensor W s z r‖) := by
      exact add_le_add hdev.1 le_rfl

/-! ## The two one-site interface determinants on physical rows -/

def oneSiteBDet (W : ℕ) (z : ℂ) (x : IntervalRows W 1) : ℂ :=
  (intervalSiteBlocks z x 0).B.det

def oneSiteCDet (W : ℕ) (z : ℂ) (x : IntervalRows W 1) : ℂ :=
  (intervalSiteBlocks z x 0).C.det

theorem oneSiteBDet_update_line
    (W : ℕ) (z : ℂ) (x : IntervalRows W 1)
    (i : Fin (1 * W)) (u v : PhysicalRowAtoms W) (t : ℝ) :
    oneSiteBDet W z (Function.update x i ((1 - t) • u + t • v)) =
      (1 - t) • oneSiteBDet W z (Function.update x i u) +
        t • oneSiteBDet W z (Function.update x i v) := by
  let ja : Fin 1 × Fin W := finProdFinEquiv.symm i
  let a : Fin W := ja.2
  have hj : ja.1 = 0 := Subsingleton.elim _ _
  have hi : intervalRowIndex (0 : Fin 1) a = i := by
    have hpair : ((0 : Fin 1), a) = ja := Prod.ext hj.symm rfl
    change finProdFinEquiv (0, a) = i
    rw [hpair, finProdFinEquiv.apply_symm_apply]
  rw [← hi]
  simp only [oneSiteBDet, intervalSiteBlocks_update_same]
  change ((intervalSiteBlocks z x 0).B.updateRow a
      (physicalRowGroupOfAtoms W z a ((1 - t) • u + t • v)).B).det = _
  have hrow :
      (physicalRowGroupOfAtoms W z a ((1 - t) • u + t • v)).B =
        fun b => (1 - (t : ℂ)) * (physicalRowGroupOfAtoms W z a u).B b +
          (t : ℂ) * (physicalRowGroupOfAtoms W z a v).B b := by
    funext b
    simp [physicalRowGroupOfAtoms, normalizedPhysicalAtom]
    push_cast
    ring
  rw [hrow]
  simpa [PhysicalBlocks.replaceRow, smul_eq_mul] using
    det_updateRow_interpolate (intervalSiteBlocks z x 0).B a
      (physicalRowGroupOfAtoms W z a u).B
      (physicalRowGroupOfAtoms W z a v).B (t : ℂ)

theorem oneSiteCDet_update_line
    (W : ℕ) (z : ℂ) (x : IntervalRows W 1)
    (i : Fin (1 * W)) (u v : PhysicalRowAtoms W) (t : ℝ) :
    oneSiteCDet W z (Function.update x i ((1 - t) • u + t • v)) =
      (1 - t) • oneSiteCDet W z (Function.update x i u) +
        t • oneSiteCDet W z (Function.update x i v) := by
  let ja : Fin 1 × Fin W := finProdFinEquiv.symm i
  let a : Fin W := ja.2
  have hj : ja.1 = 0 := Subsingleton.elim _ _
  have hi : intervalRowIndex (0 : Fin 1) a = i := by
    have hpair : ((0 : Fin 1), a) = ja := Prod.ext hj.symm rfl
    change finProdFinEquiv (0, a) = i
    rw [hpair, finProdFinEquiv.apply_symm_apply]
  rw [← hi]
  simp only [oneSiteCDet, intervalSiteBlocks_update_same]
  change ((intervalSiteBlocks z x 0).C.updateRow a
      (physicalRowGroupOfAtoms W z a ((1 - t) • u + t • v)).C).det = _
  have hrow :
      (physicalRowGroupOfAtoms W z a ((1 - t) • u + t • v)).C =
        fun b => (1 - (t : ℂ)) * (physicalRowGroupOfAtoms W z a u).C b +
          (t : ℂ) * (physicalRowGroupOfAtoms W z a v).C b := by
    funext b
    simp [physicalRowGroupOfAtoms, normalizedPhysicalAtom]
    push_cast
    ring
  rw [hrow]
  simpa [PhysicalBlocks.replaceRow, smul_eq_mul] using
    det_updateRow_interpolate (intervalSiteBlocks z x 0).C a
      (physicalRowGroupOfAtoms W z a u).C
      (physicalRowGroupOfAtoms W z a v).C (t : ℂ)

def oneSiteBDetRecursive (W : ℕ) (z : ℂ) :
    MultiAffineRows (List.replicate (1 * W) (3 * W)) → ℂ := fun y =>
  oneSiteBDet W z (multiAffineRowsToFinRows (3 * W) (1 * W) y)

def oneSiteCDetRecursive (W : ℕ) (z : ℂ) :
    MultiAffineRows (List.replicate (1 * W) (3 * W)) → ℂ := fun y =>
  oneSiteCDet W z (multiAffineRowsToFinRows (3 * W) (1 * W) y)

theorem oneSiteBDetRecursive_isMultiAffine (W : ℕ) (z : ℂ) :
    IsMultiAffine (oneSiteBDetRecursive W z) := by
  apply isMultiAffine_comp_multiAffineRowsToFinRows
  intro x i u v t
  exact oneSiteBDet_update_line W z x i u v t

theorem oneSiteCDetRecursive_isMultiAffine (W : ℕ) (z : ℂ) :
    IsMultiAffine (oneSiteCDetRecursive W z) := by
  apply isMultiAffine_comp_multiAffineRowsToFinRows
  intro x i u v t
  exact oneSiteCDet_update_line W z x i u v t

theorem oneSiteBDetRecursive_ne_zero (W : ℕ) (hW : 0 < W) (z : ℂ) :
    oneSiteBDetRecursive W z ≠ 0 := by
  intro hzero
  have hvalue := congrFun hzero (identityMultiAffineRows W 1)
  simp only [oneSiteBDetRecursive, identityMultiAffineRows_toFinRows,
    oneSiteBDet, identityIntervalRows_siteB W 1 hW z 0, Matrix.det_one]
    at hvalue
  exact one_ne_zero hvalue

theorem oneSiteCDetRecursive_ne_zero (W : ℕ) (hW : 0 < W) (z : ℂ) :
    oneSiteCDetRecursive W z ≠ 0 := by
  intro hzero
  have hvalue := congrFun hzero (identityMultiAffineRows W 1)
  simp only [oneSiteCDetRecursive, identityMultiAffineRows_toFinRows,
    oneSiteCDet, identityIntervalRows_siteC W 1 hW z 0, Matrix.det_one]
    at hvalue
  exact one_ne_zero hvalue

def oneSiteBDetTensor (W : ℕ) (z : ℂ) :=
  multiAffineTensorOfFunction (oneSiteBDetRecursive W z)

def oneSiteCDetTensor (W : ℕ) (z : ℂ) :=
  multiAffineTensorOfFunction (oneSiteCDetRecursive W z)

/-! The identity configuration provides a uniform concrete lower bound on
the coefficient tensors.  This removes the coefficient-norm certificate from
the inverse-determinant estimates below. -/

theorem identityMultiAffineRows_l1_le (W : ℕ) (i : Fin (1 * W)) :
    ∑ a : Fin (3 * W),
        |multiAffineRowsToFinRows (3 * W) (1 * W)
          (identityMultiAffineRows W 1) i a| ≤
      (3 * W : ℝ) * |(blockNormalization W)⁻¹| := by
  rw [identityMultiAffineRows_toFinRows]
  calc
    (∑ a : Fin (3 * W), |identityIntervalRows W 1 i a|) ≤
        ∑ _a : Fin (3 * W), |(blockNormalization W)⁻¹| := by
      apply Finset.sum_le_sum
      intro a ha
      simp only [identityIntervalRows, identityPhysicalRowAtoms]
      by_cases h :
          ((a.divNat = 0 ∨ a.divNat = 2) ∧ a.modNat = i.modNat)
      · simp [h]
      · simp [h]
    _ = (3 * W : ℝ) * |(blockNormalization W)⁻¹| := by simp

def oneSiteDetTensorGrowth (W : ℕ) : ℝ :=
  (1 + (3 * W : ℝ) * |(blockNormalization W)⁻¹|) ^ W

theorem oneSiteBDetTensor_lower (W : ℕ) (hW : 0 < W) (z : ℂ) :
    1 ≤ oneSiteDetTensorGrowth W * ‖oneSiteBDetTensor W z‖ := by
  let M : ℝ := (3 * W : ℝ) * |(blockNormalization W)⁻¹|
  have hM : 0 ≤ M := by positivity
  have hbound := norm_multiAffineEval_replicate_le_of_l1
    (E := ℂ) (3 * W) M hM (1 * W) (oneSiteBDetTensor W z)
      (identityMultiAffineRows W 1) (identityMultiAffineRows_l1_le W)
  have heval := congrFun
    (oneSiteBDetRecursive_isMultiAffine W z).eval_tensorOfFunction
      (identityMultiAffineRows W 1)
  rw [oneSiteBDetTensor, heval] at hbound
  have hone : oneSiteBDetRecursive W z (identityMultiAffineRows W 1) = 1 := by
    simp [oneSiteBDetRecursive, oneSiteBDet,
      identityIntervalRows_siteB W 1 hW z 0]
  rw [hone, norm_one] at hbound
  simpa only [oneSiteDetTensorGrowth, oneSiteBDetTensor, M, one_mul] using hbound

theorem oneSiteCDetTensor_lower (W : ℕ) (hW : 0 < W) (z : ℂ) :
    1 ≤ oneSiteDetTensorGrowth W * ‖oneSiteCDetTensor W z‖ := by
  let M : ℝ := (3 * W : ℝ) * |(blockNormalization W)⁻¹|
  have hM : 0 ≤ M := by positivity
  have hbound := norm_multiAffineEval_replicate_le_of_l1
    (E := ℂ) (3 * W) M hM (1 * W) (oneSiteCDetTensor W z)
      (identityMultiAffineRows W 1) (identityMultiAffineRows_l1_le W)
  have heval := congrFun
    (oneSiteCDetRecursive_isMultiAffine W z).eval_tensorOfFunction
      (identityMultiAffineRows W 1)
  rw [oneSiteCDetTensor, heval] at hbound
  have hone : oneSiteCDetRecursive W z (identityMultiAffineRows W 1) = 1 := by
    simp [oneSiteCDetRecursive, oneSiteCDet,
      identityIntervalRows_siteC W 1 hW z 0]
  rw [hone, norm_one] at hbound
  simpa only [oneSiteDetTensorGrowth, oneSiteCDetTensor, M, one_mul] using hbound

theorem posLog_inv_oneSiteBDetTensor_le
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    Real.posLog ‖oneSiteBDetTensor W z‖⁻¹ ≤
      Real.posLog (oneSiteDetTensorGrowth W) := by
  let Γ : ℝ := ‖oneSiteBDetTensor W z‖
  let b : ℝ := oneSiteDetTensorGrowth W
  have hb : 0 < b := by
    unfold b oneSiteDetTensorGrowth
    positivity
  have hlower : 1 ≤ b * Γ := by
    simpa only [b, Γ] using oneSiteBDetTensor_lower W hW z
  have hΓ : 0 < Γ := by
    by_contra h
    have hzero : Γ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hzero, mul_zero] at hlower
    norm_num at hlower
  have hinv : Γ⁻¹ ≤ b := by
    rw [← one_mul Γ⁻¹, mul_inv_le_iff₀ hΓ]
    simpa only [one_mul] using hlower
  simpa only [Γ, b] using
    Real.posLog_le_posLog (inv_nonneg.mpr hΓ.le) hinv

theorem posLog_inv_oneSiteCDetTensor_le
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    Real.posLog ‖oneSiteCDetTensor W z‖⁻¹ ≤
      Real.posLog (oneSiteDetTensorGrowth W) := by
  let Γ : ℝ := ‖oneSiteCDetTensor W z‖
  let b : ℝ := oneSiteDetTensorGrowth W
  have hb : 0 < b := by
    unfold b oneSiteDetTensorGrowth
    positivity
  have hlower : 1 ≤ b * Γ := by
    simpa only [b, Γ] using oneSiteCDetTensor_lower W hW z
  have hΓ : 0 < Γ := by
    by_contra h
    have hzero : Γ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hzero, mul_zero] at hlower
    norm_num at hlower
  have hinv : Γ⁻¹ ≤ b := by
    rw [← one_mul Γ⁻¹, mul_inv_le_iff₀ hΓ]
    simpa only [one_mul] using hlower
  simpa only [Γ, b] using
    Real.posLog_le_posLog (inv_nonneg.mpr hΓ.le) hinv

theorem oneSiteBDet_log_deviation_recursive
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ y, ENNReal.ofReal
        |Real.log ‖oneSiteBDetRecursive W z y‖ -
          Real.log ‖oneSiteBDetTensor W z‖|
        ∂multiAffineRowLaw μ (List.replicate (1 * W) (3 * W))) ≤
        multiAffineLogCost L (List.replicate (1 * W) (3 * W)) ∧
      ∀ᵐ y ∂multiAffineRowLaw μ (List.replicate (1 * W) (3 * W)),
        oneSiteBDetRecursive W z y ≠ 0 := by
  have hpos : ∀ p ∈ List.replicate (1 * W) (3 * W), 0 < p := by
    intro p hp
    simp only [List.mem_replicate] at hp
    omega
  simpa only [oneSiteBDetTensor] using
    corollary_10_3 hμ (oneSiteBDetRecursive_isMultiAffine W z) hpos
      (oneSiteBDetRecursive_ne_zero W hW z)

theorem oneSiteCDet_log_deviation_recursive
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ y, ENNReal.ofReal
        |Real.log ‖oneSiteCDetRecursive W z y‖ -
          Real.log ‖oneSiteCDetTensor W z‖|
        ∂multiAffineRowLaw μ (List.replicate (1 * W) (3 * W))) ≤
        multiAffineLogCost L (List.replicate (1 * W) (3 * W)) ∧
      ∀ᵐ y ∂multiAffineRowLaw μ (List.replicate (1 * W) (3 * W)),
        oneSiteCDetRecursive W z y ≠ 0 := by
  have hpos : ∀ p ∈ List.replicate (1 * W) (3 * W), 0 < p := by
    intro p hp
    simp only [List.mem_replicate] at hp
    omega
  simpa only [oneSiteCDetTensor] using
    corollary_10_3 hμ (oneSiteCDetRecursive_isMultiAffine W z) hpos
      (oneSiteCDetRecursive_ne_zero W hW z)

theorem oneSiteBDet_log_deviation
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal
        |Real.log ‖oneSiteBDet W z x‖ - Real.log ‖oneSiteBDetTensor W z‖|
        ∂intervalRowsLaw W 1 μ) ≤
        multiAffineLogCost L (List.replicate (1 * W) (3 * W)) ∧
      ∀ᵐ x ∂intervalRowsLaw W 1 μ, oneSiteBDet W z x ≠ 0 := by
  letI := hμ.toIsProbabilityMeasure
  let e := finRowsMultiAffineRowsMeasurableEquiv (3 * W) (1 * W)
  have hmp : MeasurePreserving e (intervalRowsLaw W 1 μ)
      (multiAffineRowLaw μ (List.replicate (1 * W) (3 * W))) := by
    simpa only [intervalRowsLaw, physicalRowLaw] using
      finRowsMultiAffineRows_measurePreserving μ (3 * W) (1 * W)
  have hrec := oneSiteBDet_log_deviation_recursive hμ W hW z
  constructor
  · have heq := hmp.lintegral_comp_emb e.measurableEmbedding
      (fun y => ENNReal.ofReal
        |Real.log ‖oneSiteBDetRecursive W z y‖ -
          Real.log ‖oneSiteBDetTensor W z‖|)
    calc
      _ = ∫⁻ y, ENNReal.ofReal
            |Real.log ‖oneSiteBDetRecursive W z y‖ -
              Real.log ‖oneSiteBDetTensor W z‖|
            ∂multiAffineRowLaw μ (List.replicate (1 * W) (3 * W)) := by
        simpa only [oneSiteBDetRecursive, e,
          finRowsMultiAffineRowsMeasurableEquiv_apply,
          multiAffineRowsToFinRows_leftInverse] using heq
      _ ≤ _ := hrec.1
  · have hrecMap : ∀ᵐ y ∂Measure.map e (intervalRowsLaw W 1 μ),
        oneSiteBDetRecursive W z y ≠ 0 := by
      rw [hmp.map_eq]
      exact hrec.2
    have hflat := e.measurableEmbedding.ae_map_iff.mp hrecMap
    simpa only [oneSiteBDetRecursive, e,
      finRowsMultiAffineRowsMeasurableEquiv_apply,
      multiAffineRowsToFinRows_leftInverse] using hflat

theorem oneSiteCDet_log_deviation
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal
        |Real.log ‖oneSiteCDet W z x‖ - Real.log ‖oneSiteCDetTensor W z‖|
        ∂intervalRowsLaw W 1 μ) ≤
        multiAffineLogCost L (List.replicate (1 * W) (3 * W)) ∧
      ∀ᵐ x ∂intervalRowsLaw W 1 μ, oneSiteCDet W z x ≠ 0 := by
  letI := hμ.toIsProbabilityMeasure
  let e := finRowsMultiAffineRowsMeasurableEquiv (3 * W) (1 * W)
  have hmp : MeasurePreserving e (intervalRowsLaw W 1 μ)
      (multiAffineRowLaw μ (List.replicate (1 * W) (3 * W))) := by
    simpa only [intervalRowsLaw, physicalRowLaw] using
      finRowsMultiAffineRows_measurePreserving μ (3 * W) (1 * W)
  have hrec := oneSiteCDet_log_deviation_recursive hμ W hW z
  constructor
  · have heq := hmp.lintegral_comp_emb e.measurableEmbedding
      (fun y => ENNReal.ofReal
        |Real.log ‖oneSiteCDetRecursive W z y‖ -
          Real.log ‖oneSiteCDetTensor W z‖|)
    calc
      _ = ∫⁻ y, ENNReal.ofReal
            |Real.log ‖oneSiteCDetRecursive W z y‖ -
              Real.log ‖oneSiteCDetTensor W z‖|
            ∂multiAffineRowLaw μ (List.replicate (1 * W) (3 * W)) := by
        simpa only [oneSiteCDetRecursive, e,
          finRowsMultiAffineRowsMeasurableEquiv_apply,
          multiAffineRowsToFinRows_leftInverse] using heq
      _ ≤ _ := hrec.1
  · have hrecMap : ∀ᵐ y ∂Measure.map e (intervalRowsLaw W 1 μ),
        oneSiteCDetRecursive W z y ≠ 0 := by
      rw [hmp.map_eq]
      exact hrec.2
    have hflat := e.measurableEmbedding.ae_map_iff.mp hrecMap
    simpa only [oneSiteCDetRecursive, e,
      finRowsMultiAffineRowsMeasurableEquiv_apply,
      multiAffineRowsToFinRows_leftInverse] using hflat

theorem oneSiteBDet_posLog_inv_lintegral_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal (Real.posLog ‖oneSiteBDet W z x‖⁻¹)
        ∂intervalRowsLaw W 1 μ) ≤
      multiAffineLogCost L (List.replicate (1 * W) (3 * W)) +
        ENNReal.ofReal (Real.posLog ‖oneSiteBDetTensor W z‖⁻¹) := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (intervalRowsLaw W 1 μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  have hdev := oneSiteBDet_log_deviation hμ W hW z
  have hpoint (x : IntervalRows W 1) :
      ENNReal.ofReal (Real.posLog ‖oneSiteBDet W z x‖⁻¹) ≤
        ENNReal.ofReal
            |Real.log ‖oneSiteBDet W z x‖ -
              Real.log ‖oneSiteBDetTensor W z‖| +
          ENNReal.ofReal (Real.posLog ‖oneSiteBDetTensor W z‖⁻¹) := by
    calc
      _ ≤ ENNReal.ofReal
          (|Real.log ‖oneSiteBDet W z x‖ -
              Real.log ‖oneSiteBDetTensor W z‖| +
            Real.posLog ‖oneSiteBDetTensor W z‖⁻¹) :=
        ENNReal.ofReal_le_ofReal
          (posLog_inv_le_abs_log_sub_log_add_posLog_inv
            ‖oneSiteBDet W z x‖ ‖oneSiteBDetTensor W z‖)
      _ = _ := ENNReal.ofReal_add (abs_nonneg _)
        (Real.posLog_nonneg (x := ‖oneSiteBDetTensor W z‖⁻¹))
  calc
    _ ≤ ∫⁻ x, (ENNReal.ofReal
          |Real.log ‖oneSiteBDet W z x‖ -
            Real.log ‖oneSiteBDetTensor W z‖| +
        ENNReal.ofReal (Real.posLog ‖oneSiteBDetTensor W z‖⁻¹))
        ∂intervalRowsLaw W 1 μ := lintegral_mono hpoint
    _ = (∫⁻ x, ENNReal.ofReal
          |Real.log ‖oneSiteBDet W z x‖ -
            Real.log ‖oneSiteBDetTensor W z‖|
          ∂intervalRowsLaw W 1 μ) +
        ENNReal.ofReal (Real.posLog ‖oneSiteBDetTensor W z‖⁻¹) := by
      rw [lintegral_add_right _ measurable_const]
      simp
    _ ≤ _ := add_le_add hdev.1 le_rfl

theorem oneSiteCDet_posLog_inv_lintegral_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal (Real.posLog ‖oneSiteCDet W z x‖⁻¹)
        ∂intervalRowsLaw W 1 μ) ≤
      multiAffineLogCost L (List.replicate (1 * W) (3 * W)) +
        ENNReal.ofReal (Real.posLog ‖oneSiteCDetTensor W z‖⁻¹) := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (intervalRowsLaw W 1 μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  have hdev := oneSiteCDet_log_deviation hμ W hW z
  have hpoint (x : IntervalRows W 1) :
      ENNReal.ofReal (Real.posLog ‖oneSiteCDet W z x‖⁻¹) ≤
        ENNReal.ofReal
            |Real.log ‖oneSiteCDet W z x‖ -
              Real.log ‖oneSiteCDetTensor W z‖| +
          ENNReal.ofReal (Real.posLog ‖oneSiteCDetTensor W z‖⁻¹) := by
    calc
      _ ≤ ENNReal.ofReal
          (|Real.log ‖oneSiteCDet W z x‖ -
              Real.log ‖oneSiteCDetTensor W z‖| +
            Real.posLog ‖oneSiteCDetTensor W z‖⁻¹) :=
        ENNReal.ofReal_le_ofReal
          (posLog_inv_le_abs_log_sub_log_add_posLog_inv
            ‖oneSiteCDet W z x‖ ‖oneSiteCDetTensor W z‖)
      _ = _ := ENNReal.ofReal_add (abs_nonneg _)
        (Real.posLog_nonneg (x := ‖oneSiteCDetTensor W z‖⁻¹))
  calc
    _ ≤ ∫⁻ x, (ENNReal.ofReal
          |Real.log ‖oneSiteCDet W z x‖ -
            Real.log ‖oneSiteCDetTensor W z‖| +
        ENNReal.ofReal (Real.posLog ‖oneSiteCDetTensor W z‖⁻¹))
        ∂intervalRowsLaw W 1 μ := lintegral_mono hpoint
    _ = (∫⁻ x, ENNReal.ofReal
          |Real.log ‖oneSiteCDet W z x‖ -
            Real.log ‖oneSiteCDetTensor W z‖|
          ∂intervalRowsLaw W 1 μ) +
        ENNReal.ofReal (Real.posLog ‖oneSiteCDetTensor W z‖⁻¹) := by
      rw [lintegral_add_right _ measurable_const]
      simp
    _ ≤ _ := add_le_add hdev.1 le_rfl

/-- The one-site `B` determinant inverse loss with every tensor datum
eliminated in favor of the concrete width-dependent growth factor. -/
theorem oneSiteBDet_posLog_inv_lintegral_explicit_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal (Real.posLog ‖oneSiteBDet W z x‖⁻¹)
        ∂intervalRowsLaw W 1 μ) ≤
      multiAffineLogCost L (List.replicate (1 * W) (3 * W)) +
        ENNReal.ofReal (Real.posLog (oneSiteDetTensorGrowth W)) := by
  calc
    _ ≤ multiAffineLogCost L (List.replicate (1 * W) (3 * W)) +
        ENNReal.ofReal (Real.posLog ‖oneSiteBDetTensor W z‖⁻¹) :=
      oneSiteBDet_posLog_inv_lintegral_le hμ W hW z
    _ ≤ _ := add_le_add le_rfl
      (ENNReal.ofReal_le_ofReal (posLog_inv_oneSiteBDetTensor_le W hW z))

/-- The one-site `C` determinant inverse loss with every tensor datum
eliminated in favor of the concrete width-dependent growth factor. -/
theorem oneSiteCDet_posLog_inv_lintegral_explicit_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal (Real.posLog ‖oneSiteCDet W z x‖⁻¹)
        ∂intervalRowsLaw W 1 μ) ≤
      multiAffineLogCost L (List.replicate (1 * W) (3 * W)) +
        ENNReal.ofReal (Real.posLog (oneSiteDetTensorGrowth W)) := by
  calc
    _ ≤ multiAffineLogCost L (List.replicate (1 * W) (3 * W)) +
        ENNReal.ofReal (Real.posLog ‖oneSiteCDetTensor W z‖⁻¹) :=
      oneSiteCDet_posLog_inv_lintegral_le hμ W hW z
    _ ≤ _ := add_le_add le_rfl
      (ENNReal.ofReal_le_ofReal (posLog_inv_oneSiteCDetTensor_le W hW z))

theorem oneSiteInterfaceDets_isUnit_ae
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    ∀ᵐ x ∂intervalRowsLaw W 1 μ,
      IsUnit (oneSiteBDet W z x) ∧ IsUnit (oneSiteCDet W z x) := by
  filter_upwards [(oneSiteBDet_log_deviation hμ W hW z).2,
    (oneSiteCDet_log_deviation hμ W hW z).2] with x hB hC
  exact ⟨isUnit_iff_ne_zero.mpr hB, isUnit_iff_ne_zero.mpr hC⟩

/-! ## A simultaneous one-site Hodge envelope -/

theorem intervalClearedProduct_one
    (W : ℕ) (z : ℂ) (x : IntervalRows W 1)
    (r : Fin (2 * W + 1)) :
    intervalClearedProduct W 1 z x r = intervalClearedStep W z x r 0 := by
  simp [intervalClearedProduct, reverseMatrixProduct]

/-- Sum of the positive logarithms of all forward one-site exterior
degrees.  The natural-number indexing avoids transporting matrix norm
instances across proof fields in complementary `Fin` indices. -/
def oneSiteForwardLoss (W : ℕ) (z : ℂ) (x : IntervalRows W 1) : ℝ :=
  ∑ k ∈ Finset.range (2 * W + 1),
    Real.posLog ‖clearedStepCompound k (intervalSiteBlocks z x 0).B
      (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C‖

/-- A concrete simultaneous envelope for all one-site forward and inverse
exterior degrees. -/
def oneSiteHodgeEnvelope (W : ℕ) (z : ℂ) (x : IntervalRows W 1) : ℝ :=
  2 * oneSiteForwardLoss W z x +
    Real.posLog ‖oneSiteBDet W z x‖⁻¹ +
    Real.posLog ‖oneSiteCDet W z x‖⁻¹

theorem oneSiteHodgeEnvelope_nonneg
    (W : ℕ) (z : ℂ) (x : IntervalRows W 1) :
    0 ≤ oneSiteHodgeEnvelope W z x := by
  unfold oneSiteHodgeEnvelope oneSiteForwardLoss
  have hsum : 0 ≤ ∑ k ∈ Finset.range (2 * W + 1),
      Real.posLog ‖clearedStepCompound k (intervalSiteBlocks z x 0).B
        (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C‖ := by
    exact Finset.sum_nonneg fun k _hk => Real.posLog_nonneg
  exact add_nonneg
    (add_nonneg (mul_nonneg (by norm_num) hsum) Real.posLog_nonneg)
    Real.posLog_nonneg

/-- Deterministic Hodge control on the nonsingular interface locus. -/
theorem oneSiteHodgeEnvelope_controls
    (W : ℕ) (z : ℂ) (x : IntervalRows W 1)
    (hB : IsUnit (oneSiteBDet W z x))
    (hC : IsUnit (oneSiteCDet W z x))
    (r : Fin (2 * W + 1)) :
    Real.posLog ‖clearedStepCompound r.1 (intervalSiteBlocks z x 0).B
        (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C‖ +
      Real.posLog ‖(clearedStepCompound r.1 (intervalSiteBlocks z x 0).B
        (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C)⁻¹‖ ≤
      oneSiteHodgeEnvelope W z x := by
  let X := intervalSiteBlocks z x 0
  let F := oneSiteForwardLoss W z x
  let dB := Real.posLog ‖oneSiteBDet W z x‖⁻¹
  let dC := Real.posLog ‖oneSiteCDet W z x‖⁻¹
  have hr : r.1 ≤ Fintype.card (Fin W ⊕ Fin W) := by
    simp
    omega
  have hcard : Fintype.card (Fin W ⊕ Fin W) = 2 * W := by simp; omega
  have hinv := clearedStepCompound_inverse_norm_eq_complement
    r.1 hr X.B X.D X.C hB hC
  rw [hcard] at hinv
  have hfwd : Real.posLog ‖clearedStepCompound r.1 X.B X.D X.C‖ ≤ F := by
    unfold F oneSiteForwardLoss X
    exact Finset.single_le_sum
      (s := Finset.range (2 * W + 1))
      (f := fun k => Real.posLog
        ‖clearedStepCompound k (intervalSiteBlocks z x 0).B
          (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C‖)
      (fun k _hk => Real.posLog_nonneg)
      (Finset.mem_range.mpr r.isLt)
  have hcomp :
      Real.posLog ‖clearedStepCompound (2 * W - r.1) X.B X.D X.C‖ ≤ F := by
    unfold F oneSiteForwardLoss X
    have hlt : 2 * W - r.1 < 2 * W + 1 := by omega
    exact Finset.single_le_sum
      (s := Finset.range (2 * W + 1))
      (f := fun k => Real.posLog
        ‖clearedStepCompound k (intervalSiteBlocks z x 0).B
          (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C‖)
      (fun k _hk => Real.posLog_nonneg)
      (Finset.mem_range.mpr hlt)
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
    _ = oneSiteHodgeEnvelope W z x := by rfl

theorem oneSiteCleared_posLog_lintegral_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) (k : ℕ) (hk : k < 2 * W + 1) :
    (∫⁻ x, ENNReal.ofReal
        (Real.posLog ‖clearedStepCompound k (intervalSiteBlocks z x 0).B
          (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C‖)
        ∂intervalRowsLaw W 1 μ) ≤
      multiAffineLogCost L (List.replicate (1 * W) (3 * W)) +
        ENNReal.ofReal
          (Real.posLog ‖intervalClearedTensor W 1 z ⟨k, hk⟩‖) := by
  have h := intervalCleared_posLog_lintegral_le hμ W 1 hW z ⟨k, hk⟩
  simpa only [intervalClearedProduct_one, intervalClearedStep] using h

theorem measurable_oneSiteForwardLoss (W : ℕ) (z : ℂ) :
    Measurable (oneSiteForwardLoss W z) := by
  unfold oneSiteForwardLoss
  apply Finset.measurable_fun_sum
  intro k hk
  have hlt : k < 2 * W + 1 := Finset.mem_range.mp hk
  have hc := continuous_intervalClearedStep W 1 z ⟨k, hlt⟩ 0
  have hraw : Continuous (fun x : IntervalRows W 1 =>
      clearedStepCompound k (intervalSiteBlocks z x 0).B
        (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C) := by
    simpa only [intervalClearedStep] using hc
  exact Real.continuous_posLog.measurable.comp hraw.norm.measurable

theorem measurable_oneSiteHodgeEnvelope (W : ℕ) (z : ℂ) :
    Measurable (oneSiteHodgeEnvelope W z) := by
  unfold oneSiteHodgeEnvelope
  have hB : Measurable (oneSiteBDet W z) := by
    exact (continuous_intervalSiteB W 1 z 0).matrix_det.measurable
  have hC : Measurable (oneSiteCDet W z) := by
    exact (continuous_intervalSiteC W 1 z 0).matrix_det.measurable
  have hBloss : Measurable (fun x : IntervalRows W 1 =>
      Real.posLog ‖oneSiteBDet W z x‖⁻¹) :=
    Real.continuous_posLog.measurable.comp hB.norm.inv
  have hCloss : Measurable (fun x : IntervalRows W 1 =>
      Real.posLog ‖oneSiteCDet W z x‖⁻¹) :=
    Real.continuous_posLog.measurable.comp hC.norm.inv
  exact ((measurable_const.mul (measurable_oneSiteForwardLoss W z)).add
    hBloss).add hCloss

def oneSiteForwardIntegralBound (L : ℝ) (W : ℕ) (z : ℂ) : ℝ≥0∞ :=
  ∑ r : Fin (2 * W + 1),
    (multiAffineLogCost L (List.replicate (1 * W) (3 * W)) +
      ENNReal.ofReal (Real.posLog ‖intervalClearedTensor W 1 z r‖))

theorem oneSiteForwardLoss_lintegral_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal (oneSiteForwardLoss W z x)
        ∂intervalRowsLaw W 1 μ) ≤
      oneSiteForwardIntegralBound L W z := by
  let f : ℕ → IntervalRows W 1 → ℝ := fun k x =>
    Real.posLog ‖clearedStepCompound k (intervalSiteBlocks z x 0).B
      (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C‖
  have hf_nonneg (k : ℕ) (x : IntervalRows W 1) : 0 ≤ f k x :=
    Real.posLog_nonneg
  have hf_meas (r : Fin (2 * W + 1)) :
      Measurable (fun x => ENNReal.ofReal (f r.1 x)) := by
    have hc := continuous_intervalClearedStep W 1 z r 0
    have hraw : Continuous (fun x : IntervalRows W 1 =>
        clearedStepCompound r.1 (intervalSiteBlocks z x 0).B
          (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C) := by
      simpa only [intervalClearedStep] using hc
    exact (Real.continuous_posLog.measurable.comp hraw.norm.measurable).ennreal_ofReal
  calc
    (∫⁻ x, ENNReal.ofReal (oneSiteForwardLoss W z x)
        ∂intervalRowsLaw W 1 μ) =
        ∫⁻ x, ∑ r : Fin (2 * W + 1),
          ENNReal.ofReal (f r.1 x) ∂intervalRowsLaw W 1 μ := by
      congr 1
      funext x
      have hsum : oneSiteForwardLoss W z x =
          ∑ r : Fin (2 * W + 1), f r.1 x := by
        unfold oneSiteForwardLoss
        simpa only [f] using
          (Fin.sum_univ_eq_sum_range (fun k => f k x) (2 * W + 1)).symm
      rw [hsum]
      exact ENNReal.ofReal_sum_of_nonneg
        (fun r _hr => hf_nonneg r.1 x)
    _ = ∑ r : Fin (2 * W + 1),
        ∫⁻ x, ENNReal.ofReal (f r.1 x) ∂intervalRowsLaw W 1 μ := by
      rw [lintegral_finsetSum Finset.univ]
      intro r _hr
      exact hf_meas r
    _ ≤ ∑ r : Fin (2 * W + 1),
        (multiAffineLogCost L (List.replicate (1 * W) (3 * W)) +
          ENNReal.ofReal
            (Real.posLog ‖intervalClearedTensor W 1 z r‖)) := by
      apply Finset.sum_le_sum
      intro r _hr
      simpa only [f] using
        oneSiteCleared_posLog_lintegral_le hμ W hW z r.1 r.isLt
    _ = oneSiteForwardIntegralBound L W z := rfl

def oneSiteInterfaceDetIntegralBound (L : ℝ) (W : ℕ) : ℝ≥0∞ :=
  multiAffineLogCost L (List.replicate (1 * W) (3 * W)) +
    ENNReal.ofReal (Real.posLog (oneSiteDetTensorGrowth W))

def oneSiteHodgeIntegralBound (L : ℝ) (W : ℕ) (z : ℂ) : ℝ≥0∞ :=
  2 * oneSiteForwardIntegralBound L W z +
    2 * oneSiteInterfaceDetIntegralBound L W

/-- Caller-facing one-site envelope estimate.  Every quantity on the
right is constructed from the concrete paper objects. -/
theorem oneSiteHodgeEnvelope_lintegral_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫⁻ x, ENNReal.ofReal (oneSiteHodgeEnvelope W z x)
        ∂intervalRowsLaw W 1 μ) ≤
      oneSiteHodgeIntegralBound L W z := by
  let F : IntervalRows W 1 → ℝ := oneSiteForwardLoss W z
  let b : IntervalRows W 1 → ℝ := fun x =>
    Real.posLog ‖oneSiteBDet W z x‖⁻¹
  let c : IntervalRows W 1 → ℝ := fun x =>
    Real.posLog ‖oneSiteCDet W z x‖⁻¹
  let FE : IntervalRows W 1 → ℝ≥0∞ := fun x => ENNReal.ofReal (F x)
  let bE : IntervalRows W 1 → ℝ≥0∞ := fun x => ENNReal.ofReal (b x)
  let cE : IntervalRows W 1 → ℝ≥0∞ := fun x => ENNReal.ofReal (c x)
  have hF (x : IntervalRows W 1) : 0 ≤ F x := by
    unfold F oneSiteForwardLoss
    exact Finset.sum_nonneg fun k _hk => Real.posLog_nonneg
  have hb (x : IntervalRows W 1) : 0 ≤ b x := Real.posLog_nonneg
  have hc (x : IntervalRows W 1) : 0 ≤ c x := Real.posLog_nonneg
  have hFE : Measurable FE :=
    (measurable_oneSiteForwardLoss W z).ennreal_ofReal
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
      ENNReal.ofReal (oneSiteHodgeEnvelope W z x) =
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
  have hforward := oneSiteForwardLoss_lintegral_le hμ W hW z
  have hB := oneSiteBDet_posLog_inv_lintegral_explicit_le hμ W hW z
  have hC := oneSiteCDet_posLog_inv_lintegral_explicit_le hμ W hW z
  calc
    (∫⁻ x, ENNReal.ofReal (oneSiteHodgeEnvelope W z x)
        ∂intervalRowsLaw W 1 μ) =
        ∫⁻ x, (2 * FE x + bE x + cE x)
          ∂intervalRowsLaw W 1 μ := lintegral_congr hsplit
    _ = 2 * (∫⁻ x, FE x ∂intervalRowsLaw W 1 μ) +
          (∫⁻ x, bE x ∂intervalRowsLaw W 1 μ) +
          (∫⁻ x, cE x ∂intervalRowsLaw W 1 μ) := by
      rw [lintegral_add_right (fun x => 2 * FE x + bE x) hcE,
        lintegral_add_right (fun x => 2 * FE x) hbE,
        lintegral_const_mul 2 hFE]
    _ ≤ 2 * oneSiteForwardIntegralBound L W z +
          oneSiteInterfaceDetIntegralBound L W +
          oneSiteInterfaceDetIntegralBound L W := by
      apply add_le_add
      · apply add_le_add
        · gcongr
        · simpa only [bE, b, oneSiteInterfaceDetIntegralBound] using hB
      · simpa only [cE, c, oneSiteInterfaceDetIntegralBound] using hC
    _ = oneSiteHodgeIntegralBound L W z := by
      unfold oneSiteHodgeIntegralBound
      ring

/-- The simultaneous Hodge domination holds almost surely under precisely
the paper's atom-law assumptions. -/
theorem oneSiteHodgeEnvelope_controls_ae
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    ∀ᵐ x ∂intervalRowsLaw W 1 μ, ∀ r : Fin (2 * W + 1),
      Real.posLog ‖clearedStepCompound r.1 (intervalSiteBlocks z x 0).B
          (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C‖ +
        Real.posLog ‖(clearedStepCompound r.1 (intervalSiteBlocks z x 0).B
          (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C)⁻¹‖ ≤
        oneSiteHodgeEnvelope W z x := by
  filter_upwards [oneSiteInterfaceDets_isUnit_ae hμ W hW z] with x hx
  intro r
  exact oneSiteHodgeEnvelope_controls W z x hx.1 hx.2 r

/-! ## Finite second moment of the concrete envelope -/

theorem oneSiteBDetRecursive_log_memLp_two
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (z : ℂ) :
    MemLp (fun y : MultiAffineRows (List.replicate (1 * W) (3 * W)) =>
        Real.log ‖oneSiteBDetRecursive W z y‖) 2
      (multiAffineRowLaw μ (List.replicate (1 * W) (3 * W))) := by
  letI := hμ.toIsProbabilityMeasure
  let c := oneSiteBDetTensor W z
  have hpos : ∀ p ∈ List.replicate (1 * W) (3 * W), 0 < p := by
    intro p hp
    simp only [List.mem_replicate] at hp
    omega
  have hcenter : MemLp (fun y =>
      Real.log ‖multiAffineEval c y‖ - Real.log ‖c‖) 2
      (multiAffineRowLaw μ (List.replicate (1 * W) (3 * W))) :=
    multiAffineEval_log_memLp_two hμ hpos c
  have hconst : MemLp (fun _ :
      MultiAffineRows (List.replicate (1 * W) (3 * W)) => Real.log ‖c‖) 2
      (multiAffineRowLaw μ (List.replicate (1 * W) (3 * W))) :=
    memLp_const _
  have hfull := hcenter.add hconst
  apply MemLp.ae_eq _ hfull
  filter_upwards [] with y
  change (Real.log ‖multiAffineEval c y‖ - Real.log ‖c‖) +
      Real.log ‖c‖ = Real.log ‖oneSiteBDetRecursive W z y‖
  rw [sub_add_cancel]
  exact congrArg (fun q : ℂ => Real.log ‖q‖)
    (congrFun (oneSiteBDetRecursive_isMultiAffine W z).eval_tensorOfFunction y)

theorem oneSiteCDetRecursive_log_memLp_two
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (z : ℂ) :
    MemLp (fun y : MultiAffineRows (List.replicate (1 * W) (3 * W)) =>
        Real.log ‖oneSiteCDetRecursive W z y‖) 2
      (multiAffineRowLaw μ (List.replicate (1 * W) (3 * W))) := by
  letI := hμ.toIsProbabilityMeasure
  let c := oneSiteCDetTensor W z
  have hpos : ∀ p ∈ List.replicate (1 * W) (3 * W), 0 < p := by
    intro p hp
    simp only [List.mem_replicate] at hp
    omega
  have hcenter : MemLp (fun y =>
      Real.log ‖multiAffineEval c y‖ - Real.log ‖c‖) 2
      (multiAffineRowLaw μ (List.replicate (1 * W) (3 * W))) :=
    multiAffineEval_log_memLp_two hμ hpos c
  have hconst : MemLp (fun _ :
      MultiAffineRows (List.replicate (1 * W) (3 * W)) => Real.log ‖c‖) 2
      (multiAffineRowLaw μ (List.replicate (1 * W) (3 * W))) :=
    memLp_const _
  have hfull := hcenter.add hconst
  apply MemLp.ae_eq _ hfull
  filter_upwards [] with y
  change (Real.log ‖multiAffineEval c y‖ - Real.log ‖c‖) +
      Real.log ‖c‖ = Real.log ‖oneSiteCDetRecursive W z y‖
  rw [sub_add_cancel]
  exact congrArg (fun q : ℂ => Real.log ‖q‖)
    (congrFun (oneSiteCDetRecursive_isMultiAffine W z).eval_tensorOfFunction y)

theorem oneSiteBDet_log_memLp_two
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (z : ℂ) :
    MemLp (fun x : IntervalRows W 1 => Real.log ‖oneSiteBDet W z x‖) 2
      (intervalRowsLaw W 1 μ) := by
  letI := hμ.toIsProbabilityMeasure
  let e := finRowsMultiAffineRowsMeasurableEquiv (3 * W) (1 * W)
  have hmp : MeasurePreserving e (intervalRowsLaw W 1 μ)
      (multiAffineRowLaw μ (List.replicate (1 * W) (3 * W))) := by
    simpa only [intervalRowsLaw, physicalRowLaw] using
      finRowsMultiAffineRows_measurePreserving μ (3 * W) (1 * W)
  have hflat :=
    (oneSiteBDetRecursive_log_memLp_two hμ W z).comp_measurePreserving hmp
  apply MemLp.ae_eq _ hflat
  filter_upwards [] with x
  change Real.log ‖oneSiteBDet W z
      (multiAffineRowsToFinRows (3 * W) (1 * W)
        (finRowsToMultiAffineRows (3 * W) (1 * W) x))‖ = _
  rw [multiAffineRowsToFinRows_leftInverse]

theorem oneSiteCDet_log_memLp_two
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (z : ℂ) :
    MemLp (fun x : IntervalRows W 1 => Real.log ‖oneSiteCDet W z x‖) 2
      (intervalRowsLaw W 1 μ) := by
  letI := hμ.toIsProbabilityMeasure
  let e := finRowsMultiAffineRowsMeasurableEquiv (3 * W) (1 * W)
  have hmp : MeasurePreserving e (intervalRowsLaw W 1 μ)
      (multiAffineRowLaw μ (List.replicate (1 * W) (3 * W))) := by
    simpa only [intervalRowsLaw, physicalRowLaw] using
      finRowsMultiAffineRows_measurePreserving μ (3 * W) (1 * W)
  have hflat :=
    (oneSiteCDetRecursive_log_memLp_two hμ W z).comp_measurePreserving hmp
  apply MemLp.ae_eq _ hflat
  filter_upwards [] with x
  change Real.log ‖oneSiteCDet W z
      (multiAffineRowsToFinRows (3 * W) (1 * W)
        (finRowsToMultiAffineRows (3 * W) (1 * W) x))‖ = _
  rw [multiAffineRowsToFinRows_leftInverse]

theorem oneSiteBDet_posLog_inv_memLp_two
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (z : ℂ) :
    MemLp (fun x : IntervalRows W 1 =>
        Real.posLog ‖oneSiteBDet W z x‖⁻¹) 2
      (intervalRowsLaw W 1 μ) := by
  have h := (oneSiteBDet_log_memLp_two hμ W z).neg.pos_part
  simpa only [Pi.neg_apply, Real.posLog_apply, Real.log_inv, neg_neg,
    max_comm] using h

theorem oneSiteCDet_posLog_inv_memLp_two
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (z : ℂ) :
    MemLp (fun x : IntervalRows W 1 =>
        Real.posLog ‖oneSiteCDet W z x‖⁻¹) 2
      (intervalRowsLaw W 1 μ) := by
  have h := (oneSiteCDet_log_memLp_two hμ W z).neg.pos_part
  simpa only [Pi.neg_apply, Real.posLog_apply, Real.log_inv, neg_neg,
    max_comm] using h

/-- Frobenius-norm version of the interval logarithmic `L²` theorem.  This
is separate from `intervalDegreeLog_memLp_two`, whose public observable uses
the operator norm. -/
theorem intervalClearedFrobeniusLog_recursive_memLp_two
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1)) :
    MemLp (fun y : MultiAffineRows (List.replicate (s * W) (3 * W)) =>
        Real.log ‖intervalClearedRecursiveFunction W s z r y‖) 2
      (multiAffineRowLaw μ (List.replicate (s * W) (3 * W))) := by
  letI := hμ.toIsProbabilityMeasure
  let c := intervalClearedTensor W s z r
  have hpos : ∀ p ∈ List.replicate (s * W) (3 * W), 0 < p := by
    intro p hp
    simp only [List.mem_replicate] at hp
    omega
  have hcenter : MemLp (fun y =>
      Real.log ‖multiAffineEval c y‖ - Real.log ‖c‖) 2
      (multiAffineRowLaw μ (List.replicate (s * W) (3 * W))) :=
    multiAffineEval_log_memLp_two hμ hpos c
  have hconst : MemLp (fun _ :
      MultiAffineRows (List.replicate (s * W) (3 * W)) => Real.log ‖c‖) 2
      (multiAffineRowLaw μ (List.replicate (s * W) (3 * W))) :=
    memLp_const _
  have hfull := hcenter.add hconst
  apply MemLp.ae_eq _ hfull
  filter_upwards [] with y
  change (Real.log ‖multiAffineEval c y‖ - Real.log ‖c‖) +
      Real.log ‖c‖ = Real.log ‖intervalClearedRecursiveFunction W s z r y‖
  rw [sub_add_cancel]
  exact congrArg (fun q => Real.log ‖q‖)
    (congrFun
      (intervalClearedRecursiveFunction_isMultiAffine W s z r).eval_tensorOfFunction y)

theorem intervalClearedFrobeniusLog_memLp_two
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1)) :
    MemLp (fun x : IntervalRows W s =>
        Real.log ‖intervalClearedProduct W s z x r‖) 2
      (intervalRowsLaw W s μ) := by
  letI := hμ.toIsProbabilityMeasure
  let e := finRowsMultiAffineRowsMeasurableEquiv (3 * W) (s * W)
  have hmp : MeasurePreserving e (intervalRowsLaw W s μ)
      (multiAffineRowLaw μ (List.replicate (s * W) (3 * W))) := by
    simpa only [intervalRowsLaw, physicalRowLaw] using
      finRowsMultiAffineRows_measurePreserving μ (3 * W) (s * W)
  have hflat :=
    (intervalClearedFrobeniusLog_recursive_memLp_two
      hμ W s hW z r).comp_measurePreserving hmp
  apply MemLp.ae_eq _ hflat
  filter_upwards [] with x
  change Real.log ‖intervalClearedProduct W s z
      (multiAffineRowsToFinRows (3 * W) (s * W)
        (finRowsToMultiAffineRows (3 * W) (s * W) x)) r‖ = _
  rw [multiAffineRowsToFinRows_leftInverse]

theorem oneSiteForwardLoss_memLp_two
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    MemLp (oneSiteForwardLoss W z) 2 (intervalRowsLaw W 1 μ) := by
  let f : Fin (2 * W + 1) → IntervalRows W 1 → ℝ := fun r x =>
    Real.posLog ‖clearedStepCompound r.1 (intervalSiteBlocks z x 0).B
      (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C‖
  have hf (r : Fin (2 * W + 1)) :
      MemLp (f r) 2 (intervalRowsLaw W 1 μ) := by
    have h :=
      (intervalClearedFrobeniusLog_memLp_two hμ W 1 hW z r).pos_part
    simpa only [f, intervalDegreeLog, Real.posLog_apply, max_comm,
      intervalClearedProduct_one, intervalClearedStep] using h
  have hsum : MemLp (fun x => ∑ r : Fin (2 * W + 1), f r x) 2
      (intervalRowsLaw W 1 μ) :=
    memLp_finsetSum Finset.univ (fun r _hr => hf r)
  apply MemLp.ae_eq _ hsum
  filter_upwards [] with x
  unfold oneSiteForwardLoss
  simpa only [f] using
    (Fin.sum_univ_eq_sum_range (fun k =>
      Real.posLog ‖clearedStepCompound k (intervalSiteBlocks z x 0).B
        (intervalSiteBlocks z x 0).D (intervalSiteBlocks z x 0).C‖)
      (2 * W + 1))

/-- The concrete simultaneous envelope has the finite second moment asserted
in Lemma 10.6. -/
theorem oneSiteHodgeEnvelope_memLp_two
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    MemLp (oneSiteHodgeEnvelope W z) 2 (intervalRowsLaw W 1 μ) := by
  unfold oneSiteHodgeEnvelope
  exact (((oneSiteForwardLoss_memLp_two hμ W hW z).const_mul 2).add
    (oneSiteBDet_posLog_inv_memLp_two hμ W z)).add
      (oneSiteCDet_posLog_inv_memLp_two hμ W z)

theorem oneSiteHodgeEnvelope_integrable
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) (z : ℂ) :
    Integrable (oneSiteHodgeEnvelope W z) (intervalRowsLaw W 1 μ) := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (intervalRowsLaw W 1 μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  exact (oneSiteHodgeEnvelope_memLp_two hμ W hW z).integrable one_le_two

end BernoulliSection10
