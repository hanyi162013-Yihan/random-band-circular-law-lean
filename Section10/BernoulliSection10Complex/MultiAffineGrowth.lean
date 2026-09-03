import BernoulliSection10Complex.HodgeIntegrability

open scoped BigOperators

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

set_option maxHeartbeats 800000

theorem multiAffineHeadEval_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : ℕ} {ps : List ℕ}
    (c d : MultiAffineTensor E (p :: ps)) (x : Fin p → ℂ) :
    multiAffineHeadEval (c + d) x =
      multiAffineHeadEval c x + multiAffineHeadEval d x := by
  change
    affineValue
        (multiAffineTensorHead c 0 + multiAffineTensorHead d 0)
        (fun s ↦ multiAffineTensorHead c s.succ +
          multiAffineTensorHead d s.succ) x = _
  unfold multiAffineHeadEval
  simp only [affineValue, smul_add, Finset.sum_add_distrib]
  abel

theorem multiAffineHeadEval_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : ℕ} {ps : List ℕ}
    (c : MultiAffineTensor E (p :: ps)) (x : Fin p → ℂ) :
    multiAffineHeadEval (-c) x = -multiAffineHeadEval c x := by
  change affineValue (-multiAffineTensorHead c 0)
    (fun s ↦ -multiAffineTensorHead c s.succ) x = _
  unfold multiAffineHeadEval
  simp only [affineValue, smul_neg, Finset.sum_neg_distrib]
  abel

theorem multiAffineHeadEval_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : ℕ} {ps : List ℕ}
    (t : ℂ) (c : MultiAffineTensor E (p :: ps)) (x : Fin p → ℂ) :
    multiAffineHeadEval (t • c) x = t • multiAffineHeadEval c x := by
  change affineValue (t • multiAffineTensorHead c 0)
    (fun s ↦ t • multiAffineTensorHead c s.succ) x = _
  unfold multiAffineHeadEval
  simp only [affineValue, smul_add, Finset.smul_sum, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

theorem multiAffineEval_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ∀ {ps : List ℕ} (c d : MultiAffineTensor E ps)
      (x : MultiAffineRows ps),
      multiAffineEval (c + d) x =
        multiAffineEval c x + multiAffineEval d x := by
  intro ps
  induction ps with
  | nil =>
      intro c d x
      rfl
  | cons p ps ih =>
      intro c d x
      rw [multiAffineEval_cons_eq_headEval,
        multiAffineHeadEval_add, ih,
        multiAffineEval_cons_eq_headEval,
        multiAffineEval_cons_eq_headEval]

theorem multiAffineEval_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ∀ {ps : List ℕ} (c : MultiAffineTensor E ps)
      (x : MultiAffineRows ps),
      multiAffineEval (-c) x = -multiAffineEval c x := by
  intro ps
  induction ps with
  | nil =>
      intro c x
      rfl
  | cons p ps ih =>
      intro c x
      rw [multiAffineEval_cons_eq_headEval,
        multiAffineHeadEval_neg, ih,
        multiAffineEval_cons_eq_headEval]

theorem multiAffineEval_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ∀ {ps : List ℕ} (t : ℂ) (c : MultiAffineTensor E ps)
      (x : MultiAffineRows ps),
      multiAffineEval (t • c) x = t • multiAffineEval c x := by
  intro ps
  induction ps with
  | nil =>
      intro t c x
      rfl
  | cons p ps ih =>
      intro t c x
      rw [multiAffineEval_cons_eq_headEval,
        multiAffineHeadEval_smul, ih,
        multiAffineEval_cons_eq_headEval]

theorem multiAffineEval_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ps : List ℕ} (c d : MultiAffineTensor E ps)
    (x : MultiAffineRows ps) :
    multiAffineEval (c - d) x =
      multiAffineEval c x - multiAffineEval d x := by
  rw [sub_eq_add_neg, multiAffineEval_add, multiAffineEval_neg, sub_eq_add_neg]

/-- A row-multiaffine tensor grows by at most one affine factor for each
physical row when every atom in that row is uniformly bounded. -/
theorem norm_multiAffineEval_finRows_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℕ) (R : ℝ) (hR : 0 ≤ R) : ∀ (n : ℕ)
      (c : MultiAffineTensor E (List.replicate n p))
      (x : Fin n → Fin p → ℂ),
      (∀ i j, ‖x i j‖ ≤ R) →
      ‖multiAffineEval c (finRowsToMultiAffineRows p n x)‖ ≤
        (1 + (p : ℝ) * R) ^ n * ‖c‖ := by
  intro n
  induction n with
  | zero =>
      intro c x hx
      change ‖c‖ ≤ (1 + (p : ℝ) * R) ^ 0 * ‖c‖
      simp
  | succ n ih =>
      intro c x hx
      let c0 := multiAffineTensorHead c 0
      let ci : Fin p → MultiAffineTensor E (List.replicate n p) :=
        fun j ↦ multiAffineTensorHead c j.succ
      let cnext := affineValue c0 ci (x 0)
      have hc0 : ‖c0‖ ≤ ‖c‖ := by
        exact PiLp.norm_apply_le
          (show PiLp 2 (fun _ : Fin (p + 1) ↦
            MultiAffineTensor E (List.replicate n p)) from c) 0
      have hci (j : Fin p) : ‖ci j‖ ≤ ‖c‖ := by
        exact PiLp.norm_apply_le
          (show PiLp 2 (fun _ : Fin (p + 1) ↦
            MultiAffineTensor E (List.replicate n p)) from c) j.succ
      have hnext : ‖cnext‖ ≤ (1 + (p : ℝ) * R) * ‖c‖ := by
        calc
          ‖cnext‖ ≤ ‖c0‖ + ∑ j : Fin p, ‖x 0 j‖ * ‖ci j‖ := by
            exact norm_affineValue_le c0 ci (x 0)
          _ ≤ ‖c‖ + ∑ _j : Fin p, R * ‖c‖ := by
            apply add_le_add hc0
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul (hx 0 j) (hci j) (norm_nonneg _) hR
          _ = (1 + (p : ℝ) * R) * ‖c‖ := by
            simp [Finset.card_univ]
            ring
      have htail : ∀ (i : Fin n) (j : Fin p), ‖Fin.tail x i j‖ ≤ R := by
        intro i j
        exact hx i.succ j
      have hind := ih cnext (Fin.tail x) htail
      change ‖multiAffineEval cnext
          (finRowsToMultiAffineRows p n (Fin.tail x))‖ ≤
        (1 + (p : ℝ) * R) ^ (n + 1) * ‖c‖
      calc
        ‖multiAffineEval cnext
            (finRowsToMultiAffineRows p n (Fin.tail x))‖ ≤
            (1 + (p : ℝ) * R) ^ n * ‖cnext‖ := hind
        _ ≤ (1 + (p : ℝ) * R) ^ n *
              ((1 + (p : ℝ) * R) * ‖c‖) := by
            exact mul_le_mul_of_nonneg_left hnext (by positivity)
        _ = (1 + (p : ℝ) * R) ^ (n + 1) * ‖c‖ := by
            rw [pow_succ]
            ring

end BernoulliSection10Complex
