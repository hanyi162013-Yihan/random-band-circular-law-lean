import BernoulliSection10Complex.HodgeIntegrability
import BernoulliSection10.PositiveLog
import BernoulliLinearAlgebra.ConcreteConditioning

/-!
# Endpoint determinant logarithms

This module formalizes the determinant small-ball component of Lemma 10.6.
Rows are kept as the literal normalized atom rows, and Corollary 10.3 supplies
the logarithmic deviation without a nonvanishing certificate.
-/

open scoped BigOperators Matrix ENNReal NNReal
open MeasureTheory

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open Matrix

set_option maxHeartbeats 800000

/-! ## A coefficient-tensor lower bound from one-hot evaluation -/

/-- Recursive rows in which each group is a standard coordinate vector. -/
def replicatedOneHotRows (p : ℕ) :
    (n : ℕ) → (Fin n → Fin p) → MultiAffineRows (List.replicate n p)
  | 0, _ => PUnit.unit
  | n + 1, i =>
      (Pi.single (i 0) 1, replicatedOneHotRows p n (Fin.tail i))

/-- Every one-hot evaluation is bounded by `2^n` times the Euclidean tensor
norm.  The deliberately elementary constant is sufficient for the sharp
`O(W log(eW))` determinant loss. -/
theorem norm_multiAffineEval_replicatedOneHotRows_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) : ∀ (n : ℕ)
      (c : MultiAffineTensor E (List.replicate n p))
      (i : Fin n → Fin p),
      ‖multiAffineEval c (replicatedOneHotRows p n i)‖ ≤
        (2 : ℝ) ^ n * ‖c‖ := by
  intro n
  induction n with
  | zero =>
      intro c i
      have hrows : replicatedOneHotRows p 0 i = PUnit.unit := rfl
      rw [hrows]
      change E at c
      change ‖c‖ ≤ (2 : ℝ) ^ 0 * ‖c‖
      norm_num
  | succ n ih =>
      intro c i
      let c0 := multiAffineTensorHead c 0
      let ci := multiAffineTensorHead c (i 0).succ
      have hc0 : ‖c0‖ ≤ ‖c‖ := by
        exact PiLp.norm_apply_le
          (show PiLp 2 (fun _ : Fin (p + 1) =>
            MultiAffineTensor E (List.replicate n p)) from c) 0
      have hci : ‖ci‖ ≤ ‖c‖ := by
        exact PiLp.norm_apply_le
          (show PiLp 2 (fun _ : Fin (p + 1) =>
            MultiAffineTensor E (List.replicate n p)) from c) (i 0).succ
      have hhead :
          affineValue (multiAffineTensorHead c 0)
              (fun a : Fin p => multiAffineTensorHead c a.succ)
              (Pi.single (i 0) 1) = c0 + ci := by
        classical
        simp [affineValue, c0, ci, Pi.single_apply]
      have htail := ih (c0 + ci) (Fin.tail i)
      change ‖multiAffineEval
          (affineValue (multiAffineTensorHead c 0)
            (fun a : Fin p => multiAffineTensorHead c a.succ)
            (Pi.single (i 0) 1))
          (replicatedOneHotRows p n (Fin.tail i))‖ ≤
        (2 : ℝ) ^ (n + 1) * ‖c‖
      rw [hhead]
      calc
        ‖multiAffineEval (c0 + ci)
            (replicatedOneHotRows p n (Fin.tail i))‖ ≤
            (2 : ℝ) ^ n * ‖c0 + ci‖ := htail
        _ ≤ (2 : ℝ) ^ n * (2 * ‖c‖) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            ‖c0 + ci‖ ≤ ‖c0‖ + ‖ci‖ := norm_add_le _ _
            _ ≤ ‖c‖ + ‖c‖ := add_le_add hc0 hci
            _ = 2 * ‖c‖ := by ring
        _ = (2 : ℝ) ^ (n + 1) * ‖c‖ := by
          rw [pow_succ]
          ring

/-! ## The normalized random endpoint block -/

abbrev BlockAtomRows (W : ℕ) := Fin W → Fin W → ℂ

def blockAtomRowsLaw (W : ℕ) (μ : Measure ℂ) : Measure (BlockAtomRows W) :=
  Measure.pi fun _ : Fin W ↦ Measure.pi fun _ : Fin W ↦ μ

/-- A physical `W × W` block with the paper's `(3W)⁻¹/²`
normalization. -/
def normalizedBlockMatrix (W : ℕ) (x : BlockAtomRows W) :
    Matrix (Fin W) (Fin W) ℂ := fun a b ↦
  ((blockNormalization W : ℂ) * x a b)

def normalizedBlockDet (W : ℕ) (x : BlockAtomRows W) : ℂ :=
  (normalizedBlockMatrix W x).det

theorem normalizedBlockMatrix_update
    (W : ℕ) (x : BlockAtomRows W) (i : Fin W) (u : Fin W → ℂ) :
    normalizedBlockMatrix W (Function.update x i u) =
      (normalizedBlockMatrix W x).updateRow i
        (fun b ↦ ((blockNormalization W : ℂ) * u b)) := by
  ext a b
  by_cases hai : a = i
  · subst a
    simp [normalizedBlockMatrix, Matrix.updateRow_apply]
  · simp [normalizedBlockMatrix, Matrix.updateRow_apply, hai]

/-- Determinant affinity in one complete endpoint row. -/
theorem normalizedBlockDet_update_line
    (W : ℕ) (x : BlockAtomRows W) (i : Fin W)
    (u v : Fin W → ℂ) (t : ℂ) :
    normalizedBlockDet W
        (Function.update x i ((1 - t) • u + t • v)) =
      (1 - t) • normalizedBlockDet W (Function.update x i u) +
        t • normalizedBlockDet W (Function.update x i v) := by
  rw [normalizedBlockDet, normalizedBlockDet, normalizedBlockDet,
    normalizedBlockMatrix_update, normalizedBlockMatrix_update,
    normalizedBlockMatrix_update]
  let A := normalizedBlockMatrix W x
  let ru : Fin W → ℂ := fun b ↦
    (blockNormalization W : ℂ) * u b
  let rv : Fin W → ℂ := fun b ↦
    (blockNormalization W : ℂ) * v b
  have hrow :
      (fun b : Fin W ↦
        (blockNormalization W : ℂ) *
          (((1 - t) • u + t • v) b)) =
        (fun b ↦ (1 - (t : ℂ)) * ru b + (t : ℂ) * rv b) := by
    funext b
    simp [ru, rv]
    push_cast
    ring
  have hdet := det_updateRow_interpolate A i ru rv (t : ℂ)
  rw [← hrow] at hdet
  simpa [A, ru, rv, smul_eq_mul] using hdet

def normalizedBlockDetRecursive (W : ℕ) :
    MultiAffineRows (List.replicate W W) → ℂ := fun y ↦
  normalizedBlockDet W (multiAffineRowsToFinRows W W y)

theorem normalizedBlockDetRecursive_isMultiAffine (W : ℕ) :
    IsMultiAffine (normalizedBlockDetRecursive W) := by
  apply isMultiAffine_comp_multiAffineRowsToFinRows
  intro x i u v t
  exact normalizedBlockDet_update_line W x i u v t

theorem replicatedOneHotRows_eq_finRowsToMultiAffineRows
    (p : ℕ) : ∀ (n : ℕ) (i : Fin n → Fin p),
    replicatedOneHotRows p n i =
      finRowsToMultiAffineRows p n
        (fun a ↦ (Pi.single (i a) 1 : Fin p → ℂ)) := by
  intro n
  induction n with
  | zero => intro i; rfl
  | succ n ih =>
      intro i
      change (Pi.single (i 0) 1, replicatedOneHotRows p n (Fin.tail i)) =
        (Pi.single (i 0) 1,
          finRowsToMultiAffineRows p n
            (Fin.tail (fun a ↦ (Pi.single (i a) 1 : Fin p → ℂ))))
      congr 1
      rw [ih]
      congr 1

theorem normalizedBlockDetRecursive_oneHot (W : ℕ) :
    normalizedBlockDetRecursive W (replicatedOneHotRows W W id) =
      (blockNormalization W : ℂ) ^ W := by
  have hflat :
      multiAffineRowsToFinRows W W (replicatedOneHotRows W W id) =
        fun a ↦ Pi.single a 1 := by
    rw [replicatedOneHotRows_eq_finRowsToMultiAffineRows,
      multiAffineRowsToFinRows_leftInverse]
    rfl
  have hmatrix :
      normalizedBlockMatrix W (fun a ↦ Pi.single a 1) =
        (blockNormalization W : ℂ) •
          (1 : Matrix (Fin W) (Fin W) ℂ) := by
    classical
    ext a b
    by_cases hab : a = b
    · subst b
      simp [normalizedBlockMatrix, Pi.single_apply]
    · simp [normalizedBlockMatrix, Pi.single_apply, hab,
        Matrix.one_apply]
  rw [normalizedBlockDetRecursive, hflat, normalizedBlockDet, hmatrix,
    Matrix.det_smul, Matrix.det_one, mul_one]
  simp

theorem blockNormalization_pos (W : ℕ) (hW : 0 < W) :
    0 < blockNormalization W := by
  unfold blockNormalization
  exact inv_pos.mpr (Real.sqrt_pos.2 (by positivity))

/-- A concrete quantitative lower bound for the canonical determinant
coefficient tensor. -/
theorem normalizedBlockDetTensor_lower
    (W : ℕ) :
    |blockNormalization W| ^ W ≤
      (2 : ℝ) ^ W *
        ‖multiAffineTensorOfFunction (normalizedBlockDetRecursive W)‖ := by
  let c := multiAffineTensorOfFunction (normalizedBlockDetRecursive W)
  have hbound := norm_multiAffineEval_replicatedOneHotRows_le
    (E := ℂ) W W c id
  have heval := congrFun
    (normalizedBlockDetRecursive_isMultiAffine W).eval_tensorOfFunction
      (replicatedOneHotRows W W id)
  rw [heval, normalizedBlockDetRecursive_oneHot, norm_pow,
    Complex.norm_real] at hbound
  exact hbound

theorem normalizedBlockDetTensor_pos (W : ℕ) (hW : 0 < W) :
    0 < ‖multiAffineTensorOfFunction (normalizedBlockDetRecursive W)‖ := by
  have hlower := normalizedBlockDetTensor_lower W
  have hc : 0 < |blockNormalization W| ^ W := by
    exact pow_pos (abs_pos.mpr (ne_of_gt (blockNormalization_pos W hW))) _
  have htwo : 0 < (2 : ℝ) ^ W := by positivity
  nlinarith

/-! ## Determinant logarithmic expectation -/

def normalizedBlockDetTensor (W : ℕ) :
    MultiAffineTensor ℂ (List.replicate W W) :=
  multiAffineTensorOfFunction (normalizedBlockDetRecursive W)

theorem normalizedBlockDetRecursive_ne_zero (W : ℕ) (hW : 0 < W) :
    normalizedBlockDetRecursive W ≠ 0 := by
  intro hzero
  have hvalue := congrFun hzero (replicatedOneHotRows W W id)
  rw [normalizedBlockDetRecursive_oneHot] at hvalue
  have hc : (blockNormalization W : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (blockNormalization_pos W hW)
  exact (pow_ne_zero W hc) hvalue

theorem normalizedBlockDet_log_deviation_recursive
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) :
    (∫⁻ y, ENNReal.ofReal
        |Real.log ‖normalizedBlockDetRecursive W y‖ -
          Real.log ‖normalizedBlockDetTensor W‖|
        ∂multiAffineRowLaw μ (List.replicate W W)) ≤
        multiAffineLogCost L (List.replicate W W) ∧
      ∀ᵐ y ∂multiAffineRowLaw μ (List.replicate W W),
        normalizedBlockDetRecursive W y ≠ 0 := by
  have hpos : ∀ p ∈ List.replicate W W, 0 < p := by
    intro p hp
    simp only [List.mem_replicate] at hp
    omega
  simpa only [normalizedBlockDetTensor] using
    corollary_10_3 hμ
      (normalizedBlockDetRecursive_isMultiAffine W) hpos
      (normalizedBlockDetRecursive_ne_zero W hW)

theorem normalizedBlockDet_log_deviation
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) :
    (∫⁻ x, ENNReal.ofReal
        |Real.log ‖normalizedBlockDet W x‖ -
          Real.log ‖normalizedBlockDetTensor W‖|
        ∂blockAtomRowsLaw W μ) ≤
        multiAffineLogCost L (List.replicate W W) ∧
      ∀ᵐ x ∂blockAtomRowsLaw W μ,
        normalizedBlockDet W x ≠ 0 := by
  letI := hμ.toIsProbabilityMeasure
  let e := finRowsMultiAffineRowsMeasurableEquiv W W
  have hmp : MeasurePreserving e (blockAtomRowsLaw W μ)
      (multiAffineRowLaw μ (List.replicate W W)) := by
    simpa only [blockAtomRowsLaw] using
      finRowsMultiAffineRows_measurePreserving μ W W
  have hrec := normalizedBlockDet_log_deviation_recursive hμ W hW
  constructor
  · have heq := hmp.lintegral_comp_emb e.measurableEmbedding
      (fun y ↦ ENNReal.ofReal
        |Real.log ‖normalizedBlockDetRecursive W y‖ -
          Real.log ‖normalizedBlockDetTensor W‖|)
    calc
      (∫⁻ x, ENNReal.ofReal
          |Real.log ‖normalizedBlockDet W x‖ -
            Real.log ‖normalizedBlockDetTensor W‖|
          ∂blockAtomRowsLaw W μ) =
          ∫⁻ y, ENNReal.ofReal
            |Real.log ‖normalizedBlockDetRecursive W y‖ -
              Real.log ‖normalizedBlockDetTensor W‖|
            ∂multiAffineRowLaw μ (List.replicate W W) := by
        simpa only [normalizedBlockDetRecursive, e,
          finRowsMultiAffineRowsMeasurableEquiv_apply,
          multiAffineRowsToFinRows_leftInverse] using heq
      _ ≤ multiAffineLogCost L (List.replicate W W) := hrec.1
  · have hrecMap : ∀ᵐ y ∂Measure.map e (blockAtomRowsLaw W μ),
        normalizedBlockDetRecursive W y ≠ 0 := by
      rw [hmp.map_eq]
      exact hrec.2
    have hflat := e.measurableEmbedding.ae_map_iff.mp hrecMap
    simpa only [normalizedBlockDetRecursive, e,
      finRowsMultiAffineRowsMeasurableEquiv_apply,
      multiAffineRowsToFinRows_leftInverse] using hflat

/-- Explicit deterministic upper bound for the normalized determinant
tensor's inverse logarithm. -/
theorem posLog_inv_normalizedBlockDetTensor_le
    (W : ℕ) (hW : 0 < W) :
    Real.posLog ‖normalizedBlockDetTensor W‖⁻¹ ≤
      Real.posLog ((2 : ℝ) ^ W * |blockNormalization W|⁻¹ ^ W) := by
  let Γ : ℝ := ‖normalizedBlockDetTensor W‖
  let a : ℝ := |blockNormalization W| ^ W
  let b : ℝ := (2 : ℝ) ^ W
  have hΓ : 0 < Γ := by
    simpa only [Γ, normalizedBlockDetTensor] using
      normalizedBlockDetTensor_pos W hW
  have ha : 0 < a := by
    exact pow_pos (abs_pos.mpr (ne_of_gt (blockNormalization_pos W hW))) _
  have hb : 0 < b := by positivity
  have hlower : a ≤ b * Γ := by
    simpa only [a, b, Γ, normalizedBlockDetTensor] using
      normalizedBlockDetTensor_lower W
  have hinv : Γ⁻¹ ≤ b * a⁻¹ := by
    rw [← one_mul Γ⁻¹, mul_inv_le_iff₀ hΓ]
    calc
      1 = a * a⁻¹ := (mul_inv_cancel₀ ha.ne').symm
      _ ≤ (b * Γ) * a⁻¹ :=
        mul_le_mul_of_nonneg_right hlower (inv_nonneg.mpr ha.le)
      _ = (b * a⁻¹) * Γ := by ring
  have hposlog := Real.posLog_le_posLog (inv_nonneg.mpr hΓ.le) hinv
  simpa only [Γ, a, b, inv_pow] using hposlog

/-- The determinant estimate needed in Lemma 10.6, with a fully explicit
`O(W log(eW))` right-hand side. -/
theorem normalizedBlockDet_posLog_inv_lintegral_le
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) :
    (∫⁻ x, ENNReal.ofReal (Real.posLog ‖normalizedBlockDet W x‖⁻¹)
        ∂blockAtomRowsLaw W μ) ≤
      multiAffineLogCost L (List.replicate W W) +
        ENNReal.ofReal
          (Real.posLog ((2 : ℝ) ^ W * |blockNormalization W|⁻¹ ^ W)) := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (blockAtomRowsLaw W μ) := by
    unfold blockAtomRowsLaw
    infer_instance
  have heval := normalizedBlockDet_log_deviation hμ W hW
  let Γ : ℝ := ‖normalizedBlockDetTensor W‖
  have hpoint (x : BlockAtomRows W) :
      ENNReal.ofReal (Real.posLog ‖normalizedBlockDet W x‖⁻¹) ≤
        ENNReal.ofReal
            |Real.log ‖normalizedBlockDet W x‖ - Real.log Γ| +
          ENNReal.ofReal (Real.posLog Γ⁻¹) := by
    calc
      ENNReal.ofReal (Real.posLog ‖normalizedBlockDet W x‖⁻¹) ≤
          ENNReal.ofReal
            (|Real.log ‖normalizedBlockDet W x‖ - Real.log Γ| +
              Real.posLog Γ⁻¹) :=
        ENNReal.ofReal_le_ofReal
          (posLog_inv_le_abs_log_sub_log_add_posLog_inv
            ‖normalizedBlockDet W x‖ Γ)
      _ = _ := ENNReal.ofReal_add (abs_nonneg _)
        (Real.posLog_nonneg (x := Γ⁻¹))
  calc
    (∫⁻ x, ENNReal.ofReal (Real.posLog ‖normalizedBlockDet W x‖⁻¹)
        ∂blockAtomRowsLaw W μ) ≤
        ∫⁻ x, (ENNReal.ofReal
            |Real.log ‖normalizedBlockDet W x‖ - Real.log Γ| +
          ENNReal.ofReal (Real.posLog Γ⁻¹))
          ∂blockAtomRowsLaw W μ := lintegral_mono hpoint
    _ = (∫⁻ x, ENNReal.ofReal
            |Real.log ‖normalizedBlockDet W x‖ - Real.log Γ|
          ∂blockAtomRowsLaw W μ) +
        ENNReal.ofReal (Real.posLog Γ⁻¹) := by
      rw [lintegral_add_right _ measurable_const]
      simp
    _ ≤ multiAffineLogCost L (List.replicate W W) +
        ENNReal.ofReal (Real.posLog Γ⁻¹) := by
      have h := add_le_add_left heval.1
        (ENNReal.ofReal (Real.posLog Γ⁻¹))
      simpa only [Γ, add_comm] using h
    _ ≤ multiAffineLogCost L (List.replicate W W) +
        ENNReal.ofReal
          (Real.posLog ((2 : ℝ) ^ W * |blockNormalization W|⁻¹ ^ W)) := by
      have hloss := ENNReal.ofReal_le_ofReal
        (posLog_inv_normalizedBlockDetTensor_le W hW)
      have hadd := add_le_add_left hloss
        (multiAffineLogCost L (List.replicate W W))
      simpa only [add_comm] using hadd

/-! ## The two endpoint blocks used by Lemma 10.6 -/

theorem measurable_normalizedBlockDet (W : ℕ) :
    Measurable (normalizedBlockDet W) := by
  apply Continuous.measurable
  unfold normalizedBlockDet
  apply Continuous.matrix_det
  unfold normalizedBlockMatrix
  fun_prop

theorem measurable_blockDetLoss (W : ℕ) :
    Measurable (fun x : BlockAtomRows W =>
      ENNReal.ofReal (Real.posLog ‖normalizedBlockDet W x‖⁻¹)) := by
  exact (Real.continuous_posLog.measurable.comp
    ((measurable_normalizedBlockDet W).norm.inv)).ennreal_ofReal

/-- The independent left and right endpoint blocks. -/
abbrev EndpointBlockPair (W : ℕ) := BlockAtomRows W × BlockAtomRows W

def endpointBlockPairLaw (W : ℕ) (μ : Measure ℂ) :
    Measure (EndpointBlockPair W) :=
  (blockAtomRowsLaw W μ).prod (blockAtomRowsLaw W μ)

/-- The two determinant losses appearing in the inverse exterior-power
estimate for a single interval. -/
def endpointDeterminantLoss (W : ℕ) (x : EndpointBlockPair W) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.posLog ‖normalizedBlockDet W x.1‖⁻¹) +
    ENNReal.ofReal (Real.posLog ‖normalizedBlockDet W x.2‖⁻¹)

/-- Caller-facing two-endpoint determinant estimate for Lemma 10.6.  All
nonvanishing information is discharged by the concrete block determinant,
and independence is expressed by the literal product law. -/
theorem endpointDeterminantLoss_lintegral_le
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) :
    (∫⁻ x, endpointDeterminantLoss W x ∂endpointBlockPairLaw W μ) ≤
      2 * (multiAffineLogCost L (List.replicate W W) +
        ENNReal.ofReal
          (Real.posLog ((2 : ℝ) ^ W * |blockNormalization W|⁻¹ ^ W))) := by
  letI := hμ.toIsProbabilityMeasure
  let m := blockAtomRowsLaw W μ
  let f : BlockAtomRows W → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.posLog ‖normalizedBlockDet W x‖⁻¹)
  let C := multiAffineLogCost L (List.replicate W W) +
    ENNReal.ofReal
      (Real.posLog ((2 : ℝ) ^ W * |blockNormalization W|⁻¹ ^ W))
  haveI : IsProbabilityMeasure m := by
    dsimp only [m, blockAtomRowsLaw]
    infer_instance
  have hf : Measurable f := by
    simpa only [f] using measurable_blockDetLoss W
  have hsingle : (∫⁻ x, f x ∂m) ≤ C := by
    simpa only [f, m, C] using
      normalizedBlockDet_posLog_inv_lintegral_le hμ W hW
  have hfst : (∫⁻ z, f z.1 ∂m.prod m) = ∫⁻ x, f x ∂m := by
    calc
      _ = ∫⁻ x, ∫⁻ y, f (x, y).1 ∂m ∂m :=
        MeasureTheory.lintegral_prod _
          (hf.comp measurable_fst).aemeasurable
      _ = _ := by simp
  have hsnd : (∫⁻ z, f z.2 ∂m.prod m) = ∫⁻ x, f x ∂m := by
    calc
      _ = ∫⁻ x, ∫⁻ y, f (x, y).2 ∂m ∂m :=
        MeasureTheory.lintegral_prod _
          (hf.comp measurable_snd).aemeasurable
      _ = _ := by simp
  calc
    (∫⁻ x, endpointDeterminantLoss W x ∂endpointBlockPairLaw W μ) =
        (∫⁻ z, f z.1 ∂m.prod m) +
          (∫⁻ z, f z.2 ∂m.prod m) := by
      have hadd := lintegral_add_left (μ := m.prod m)
        (hf.comp measurable_fst) (fun z : EndpointBlockPair W => f z.2)
      simpa only [endpointDeterminantLoss, endpointBlockPairLaw, f, m,
        Function.comp_apply] using hadd
    _ = (∫⁻ x, f x ∂m) + ∫⁻ x, f x ∂m := by rw [hfst, hsnd]
    _ ≤ C + C := add_le_add hsingle hsingle
    _ = 2 * C := by ring
    _ = 2 * (multiAffineLogCost L (List.replicate W W) +
        ENNReal.ofReal
          (Real.posLog ((2 : ℝ) ^ W * |blockNormalization W|⁻¹ ^ W))) := rfl

/-! ## The actual endpoint factor -/

open BernoulliLinearAlgebra

/-- The paper's block-diagonal endpoint matrix, specialized to the two
normalized random blocks. -/
def normalizedEndpointFactor (W : ℕ) (x : EndpointBlockPair W) :
    Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ :=
  endpointFactor (normalizedBlockMatrix W x.1)
    (normalizedBlockMatrix W x.2)

theorem normalizedEndpointFactor_det (W : ℕ) (x : EndpointBlockPair W) :
    (normalizedEndpointFactor W x).det =
      normalizedBlockDet W x.1 * normalizedBlockDet W x.2 := by
  simp [normalizedEndpointFactor, normalizedBlockDet, endpointFactor_det]

/-- The determinant inverse loss of the actual endpoint factor is bounded
pointwise by the sum of the two block losses. -/
theorem normalizedEndpointFactor_detLoss_le
    (W : ℕ) (x : EndpointBlockPair W) :
    ENNReal.ofReal (Real.posLog ‖(normalizedEndpointFactor W x).det‖⁻¹) ≤
      endpointDeterminantLoss W x := by
  rw [normalizedEndpointFactor_det, norm_mul, mul_inv]
  calc
    ENNReal.ofReal
        (Real.posLog (‖normalizedBlockDet W x.1‖⁻¹ *
          ‖normalizedBlockDet W x.2‖⁻¹)) ≤
        ENNReal.ofReal
          (Real.posLog ‖normalizedBlockDet W x.1‖⁻¹ +
            Real.posLog ‖normalizedBlockDet W x.2‖⁻¹) :=
      ENNReal.ofReal_le_ofReal Real.posLog_mul
    _ = endpointDeterminantLoss W x := by
      rw [ENNReal.ofReal_add
        (Real.posLog_nonneg (x := ‖normalizedBlockDet W x.1‖⁻¹))
        (Real.posLog_nonneg (x := ‖normalizedBlockDet W x.2‖⁻¹))]
      rfl

/-- The two-block estimate rewritten for the determinant of the actual
endpoint factor consumed by the Hodge--Jacobi comparison. -/
theorem normalizedEndpointFactor_detLoss_lintegral_le
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) :
    (∫⁻ x, ENNReal.ofReal
        (Real.posLog ‖(normalizedEndpointFactor W x).det‖⁻¹)
        ∂endpointBlockPairLaw W μ) ≤
      2 * (multiAffineLogCost L (List.replicate W W) +
        ENNReal.ofReal
          (Real.posLog ((2 : ℝ) ^ W * |blockNormalization W|⁻¹ ^ W))) := by
  exact (lintegral_mono (normalizedEndpointFactor_detLoss_le W)).trans
    (endpointDeterminantLoss_lintegral_le hμ W hW)

/-- The concrete endpoint factor is nonsingular almost surely.  This is
deduced from the two concrete determinant polynomials, so callers do not
supply endpoint invertibility certificates. -/
theorem normalizedEndpointFactor_det_isUnit_ae
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) :
    ∀ᵐ x ∂endpointBlockPairLaw W μ,
      IsUnit (normalizedEndpointFactor W x).det := by
  letI := hμ.toIsProbabilityMeasure
  let m := blockAtomRowsLaw W μ
  haveI : IsProbabilityMeasure m := by
    dsimp only [m, blockAtomRowsLaw]
    infer_instance
  have hblock : ∀ᵐ x ∂m, normalizedBlockDet W x ≠ 0 := by
    simpa only [m] using
      (normalizedBlockDet_log_deviation hμ W hW).2
  have hleft : ∀ᵐ x ∂m.prod m, normalizedBlockDet W x.1 ≠ 0 :=
    (measurePreserving_fst (μ := m) (ν := m)).quasiMeasurePreserving.ae hblock
  have hright : ∀ᵐ x ∂m.prod m, normalizedBlockDet W x.2 ≠ 0 :=
    (measurePreserving_snd (μ := m) (ν := m)).quasiMeasurePreserving.ae hblock
  filter_upwards [hleft, hright] with x hx hy
  rw [normalizedEndpointFactor_det]
  exact (isUnit_iff_ne_zero.mpr hx).mul (isUnit_iff_ne_zero.mpr hy)

end BernoulliSection10Complex
