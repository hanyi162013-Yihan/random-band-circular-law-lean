import BernoulliSection10Complex.BoundedDensity
import BernoulliSection10.AffineLog

/-!
# Random affine logarithms

This file proves the continuous-density input called Lemma 10.2 in the paper.
The random vector is represented by the canonical finite product measure, so
independence is present in the statement itself rather than hidden behind a
certificate.  The internal normalized density bound is constructed from the raw planar
hypotheses. The measure-theoretic layer-cake bounds are imported unchanged
from the real Section 10 library.
-/

open scoped ENNReal NNReal Topology BigOperators
open Set MeasureTheory

noncomputable section

namespace BernoulliSection10Complex

/-- The affine map occurring in Lemma 10.2. -/
def affineValue {p : ℕ} {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (v₀ : E) (v : Fin p → E) (x : Fin p → ℂ) : E :=
  v₀ + ∑ i, x i • v i

/-- The coefficient ℓ2 scale from the second assertion of Lemma 10.2. -/
def affineRho {p : ℕ} {E : Type*} [NormedAddCommGroup E]
    (v₀ : E) (v : Fin p → E) : ℝ :=
  Real.sqrt (‖v₀‖ ^ 2 + ∑ i, ‖v i‖ ^ 2)

/-- The auxiliary scale used in the proof.  The norm on the finite Pi-space
is the maximum coefficient norm. -/
def affineLambda {p : ℕ} {E : Type*} [NormedAddCommGroup E]
    (v₀ : E) (v : Fin p → E) : ℝ :=
  max ‖v₀‖ ((p : ℝ) * ‖v‖)

/-- An explicit density-dependent constant.  It is intentionally generous;
its role is to make the dimension dependence exactly `log² (e p)`. -/
def affineLogConstant (L : ℝ) : ℝ :=
  1024 * (1 + Real.log (16 * (1 + L))) ^ 2

/-- A single explicit constant used by the caller-facing forms of Lemma 10.2. -/
def lemma10_2Constant (L : ℝ) : ℝ :=
  8 * (affineLogConstant L + 1)

section Deterministic

variable {p : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem continuous_affineValue (v₀ : E) (v : Fin p → E) :
    Continuous (affineValue v₀ v) := by
  unfold affineValue
  fun_prop

theorem measurable_affineValue (v₀ : E) (v : Fin p → E) :
    Measurable fun x ↦ ‖affineValue v₀ v x‖ :=
  (continuous_norm.comp (continuous_affineValue v₀ v)).measurable

theorem affineLambda_nonneg (v₀ : E) (v : Fin p → E) :
    0 ≤ affineLambda v₀ v := by
  exact le_trans (norm_nonneg v₀) (le_max_left _ _)

theorem affineRho_nonneg (v₀ : E) (v : Fin p → E) :
    0 ≤ affineRho v₀ v := Real.sqrt_nonneg _

theorem affineRho_sq (v₀ : E) (v : Fin p → E) :
    affineRho v₀ v ^ 2 = ‖v₀‖ ^ 2 + ∑ i, ‖v i‖ ^ 2 := by
  rw [affineRho, Real.sq_sqrt]
  positivity

theorem norm_affineValue_le (v₀ : E) (v : Fin p → E) (x : Fin p → ℂ) :
    ‖affineValue v₀ v x‖ ≤ ‖v₀‖ + ∑ i, ‖x i‖ * ‖v i‖ := by
  calc
    ‖affineValue v₀ v x‖ ≤ ‖v₀‖ + ‖∑ i, x i • v i‖ := norm_add_le _ _
    _ ≤ ‖v₀‖ + ∑ i, ‖x i • v i‖ :=
      add_le_add (le_refl _) (norm_sum_le _ _)
    _ = ‖v₀‖ + ∑ i, ‖x i‖ * ‖v i‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp [norm_smul, Real.norm_eq_abs]

theorem norm_affineValue_le_piNorm (v₀ : E) (v : Fin p → E) (x : Fin p → ℂ) :
    ‖affineValue v₀ v x‖ ≤ ‖v₀‖ + (∑ i, ‖x i‖) * ‖v‖ := by
  refine (norm_affineValue_le v₀ v x).trans (add_le_add (le_refl _) ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (norm_nonneg _)

theorem norm_affineValue_le_sup (v₀ : E) (v : Fin p → E) (x : Fin p → ℂ) :
    ‖affineValue v₀ v x‖ ≤ ‖v₀‖ + (p : ℝ) * ‖x‖ * ‖v‖ := by
  refine (norm_affineValue_le_piNorm v₀ v x).trans (add_le_add (le_refl _) ?_)
  have hsum : ∑ i, ‖x i‖ ≤ (p : ℝ) * ‖x‖ := by
    simpa [Real.norm_eq_abs, nsmul_eq_mul] using Pi.sum_norm_apply_le_norm x
  exact mul_le_mul_of_nonneg_right hsum (norm_nonneg v)

theorem norm_affineValue_le_lambda_mul (v₀ : E) (v : Fin p → E) (x : Fin p → ℂ) :
    ‖affineValue v₀ v x‖ ≤ affineLambda v₀ v * (1 + ‖x‖) := by
  have hb : ‖v₀‖ ≤ affineLambda v₀ v := le_max_left _ _
  have hv : (p : ℝ) * ‖v‖ ≤ affineLambda v₀ v := le_max_right _ _
  calc
    ‖affineValue v₀ v x‖ ≤ ‖v₀‖ + (p : ℝ) * ‖x‖ * ‖v‖ :=
      norm_affineValue_le_sup v₀ v x
    _ ≤ affineLambda v₀ v + affineLambda v₀ v * ‖x‖ := by
      apply add_le_add hb
      calc
        (p : ℝ) * ‖x‖ * ‖v‖ = ((p : ℝ) * ‖v‖) * ‖x‖ := by ring
        _ ≤ affineLambda v₀ v * ‖x‖ :=
          mul_le_mul_of_nonneg_right hv (norm_nonneg x)
    _ = affineLambda v₀ v * (1 + ‖x‖) := by ring

theorem affineValue_eq_const_of_piNorm_eq_zero (v₀ : E) (v : Fin p → E)
    (hv : ‖v‖ = 0) : affineValue v₀ v = fun _ => v₀ := by
  have hvzero : v = 0 := norm_eq_zero.mp hv
  subst v
  funext x
  simp [affineValue]

theorem norm_v₀_le_affineRho (v₀ : E) (v : Fin p → E) :
    ‖v₀‖ ≤ affineRho v₀ v := by
  have hsum : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hrho := affineRho_sq v₀ v
  have hrnonneg := affineRho_nonneg v₀ v
  nlinarith [sq_nonneg ‖v₀‖]

theorem norm_pi_le_affineRho {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E) :
    ‖v‖ ≤ affineRho v₀ v := by
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm v).1
  have hterm : ‖v i‖ ^ 2 ≤ ∑ j, ‖v j‖ ^ 2 := by
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖v j‖) (Finset.mem_univ i)
  have hrho := affineRho_sq v₀ v
  have hrnonneg := affineRho_nonneg v₀ v
  have hinonneg := norm_nonneg (v i)
  have hi' : ‖v i‖ = ‖v‖ := hi
  rw [hi'] at hterm hinonneg
  nlinarith [sq_nonneg ‖v₀‖]

theorem affineRho_pos_of_nonzero {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E)
    (hG : v₀ ≠ 0 ∨ v ≠ 0) : 0 < affineRho v₀ v := by
  rcases hG with hv₀ | hv
  · exact (norm_pos_iff.mpr hv₀).trans_le (norm_v₀_le_affineRho v₀ v)
  · exact (norm_pos_iff.mpr hv).trans_le (norm_pi_le_affineRho v₀ v)

theorem affineLambda_le_card_mul_affineRho {n : ℕ}
    (v₀ : E) (v : Fin (n + 1) → E) :
    affineLambda v₀ v ≤ (n + 1 : ℝ) * affineRho v₀ v := by
  have hp : 1 ≤ (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hrho_nonneg := affineRho_nonneg v₀ v
  rw [affineLambda, max_le_iff]
  constructor
  · exact (norm_v₀_le_affineRho v₀ v).trans
      (by nlinarith [hrho_nonneg])
  · norm_num [Nat.cast_add, Nat.cast_one]
    exact mul_le_mul_of_nonneg_left (norm_pi_le_affineRho v₀ v) (by positivity)

theorem affineRho_le_two_mul_affineLambda {n : ℕ}
    (v₀ : E) (v : Fin (n + 1) → E) :
    affineRho v₀ v ≤ 2 * affineLambda v₀ v := by
  let q : ℝ := n + 1
  have hq : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hsum : ∑ i, ‖v i‖ ^ 2 ≤ q * ‖v‖ ^ 2 := by
    calc
      ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin (n + 1), ‖v‖ ^ 2 := by
        exact Finset.sum_le_sum fun i _ ↦
          (sq_le_sq₀ (norm_nonneg (v i)) (norm_nonneg v)).2 (norm_le_pi_norm v i)
      _ = q * ‖v‖ ^ 2 := by simp [q, nsmul_eq_mul]
  have hq_sq : q * ‖v‖ ^ 2 ≤ (q * ‖v‖) ^ 2 := by
    have hv2 : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) hv2]
  have hb : ‖v₀‖ ≤ affineLambda v₀ v := le_max_left _ _
  have hv : q * ‖v‖ ≤ affineLambda v₀ v := by
    dsimp [q, affineLambda]
    norm_num [Nat.cast_add, Nat.cast_one]
  have hb_sq := (sq_le_sq₀ (norm_nonneg v₀) (affineLambda_nonneg v₀ v)).2 hb
  have hv_sq := (sq_le_sq₀ (mul_nonneg (by positivity) (norm_nonneg v))
    (affineLambda_nonneg v₀ v)).2 hv
  have hrho := affineRho_sq v₀ v
  have hrnonneg := affineRho_nonneg v₀ v
  have hlambda_nonneg := affineLambda_nonneg v₀ v
  apply le_of_sq_le_sq _ (mul_nonneg (by norm_num) hlambda_nonneg)
  nlinarith

theorem abs_log_affineLambda_sub_log_affineRho_le {n : ℕ}
    (v₀ : E) (v : Fin (n + 1) → E) (hv : ‖v‖ ≠ 0) :
    |Real.log (affineLambda v₀ v) - Real.log (affineRho v₀ v)| ≤
      Real.log (Real.exp 1 * (n + 1 : ℝ)) := by
  let q : ℝ := n + 1
  have hq : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hlambda_pos : 0 < affineLambda v₀ v := by
    have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    have hp : 0 < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    exact (mul_pos hp hvpos).trans_le (le_max_right _ _)
  have hrho_pos : 0 < affineRho v₀ v :=
    affineRho_pos_of_nonzero v₀ v (Or.inr (norm_ne_zero_iff.mp hv))
  have hu := Real.log_le_log hlambda_pos (affineLambda_le_card_mul_affineRho v₀ v)
  have hl := Real.log_le_log hrho_pos (affineRho_le_two_mul_affineLambda v₀ v)
  have hu' : Real.log (affineLambda v₀ v) - Real.log (affineRho v₀ v) ≤
      Real.log q := by
    rw [Real.log_mul hqpos.ne' hrho_pos.ne'] at hu
    linarith
  have hl' : -(Real.log q + 1) ≤
      Real.log (affineLambda v₀ v) - Real.log (affineRho v₀ v) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlambda_pos.ne'] at hl
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      exact h
    have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
    linarith
  have hell : Real.log (Real.exp 1 * (n + 1 : ℝ)) = 1 + Real.log q := by
    dsimp [q]
    rw [Real.log_mul (Real.exp_ne_zero 1) hqpos.ne', Real.log_exp]
  rw [hell]
  apply abs_le.2
  constructor
  · simpa [add_comm] using hl'
  · have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
    linarith

end Deterministic

section ProductSmallBall

variable {μ : Measure ℂ} {L : ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Conditional one-coordinate small-ball estimate on the canonical product
law.  This is the precise Fubini step in the proof of Lemma 10.2. -/
theorem measure_pi_norm_affineValue_le (hμ : IsBoundedDensityAtom μ L)
    {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E) (i : Fin (n + 1))
    (hvi : v i ≠ 0) (r : ℝ) (hr : 0 ≤ r) :
    (Measure.pi fun _ : Fin (n + 1) => μ)
        {x : Fin (n + 1) → ℂ | ‖affineValue v₀ v x‖ ≤ r} ≤
      ENNReal.ofReal (2 * L * r / ‖v i‖) := by
  letI := hμ.toIsProbabilityMeasure
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) i
  let ν : Measure (Fin n → ℂ) := Measure.pi fun _ : Fin n => μ
  let A : Set (ℂ × (Fin n → ℂ)) :=
    {z | ‖affineValue v₀ v (e.symm z)‖ ≤ r}
  have hA : MeasurableSet A := by
    exact measurableSet_le
      ((measurable_affineValue v₀ v).comp e.symm.measurable)
      measurable_const
  have hevent :
      {x : Fin (n + 1) → ℂ | ‖affineValue v₀ v x‖ ≤ r} = e ⁻¹' A := by
    ext x
    change ‖affineValue v₀ v x‖ ≤ r ↔
      ‖affineValue v₀ v (e.symm (e x))‖ ≤ r
    rw [e.symm_apply_apply]
  have hpush := congrArg (fun m : Measure (ℂ × (Fin n → ℂ)) => m A)
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i).map_eq
  rw [Measure.map_apply
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i).measurable hA] at hpush
  rw [hevent, hpush, Measure.prod_apply_symm hA]
  calc
    (∫⁻ y, μ ((fun x : ℂ => (x, y)) ⁻¹' A) ∂ν) ≤
        ∫⁻ _y, ENNReal.ofReal (2 * L * r / ‖v i‖) ∂ν := by
      apply lintegral_mono
      intro y
      let a : E := affineValue v₀ v (e.symm (0, y))
      have hfiber :
          (fun x : ℂ => (x, y)) ⁻¹' A =
            {x : ℂ | ‖a + x • v i‖ ≤ r} := by
        ext x
        change ‖affineValue v₀ v (e.symm (x, y))‖ ≤ r ↔
          ‖affineValue v₀ v (e.symm (0, y)) + x • v i‖ ≤ r
        congr 2
        unfold affineValue
        rw [Fin.sum_univ_succAbove (fun j ↦ (e.symm (x, y)) j • v j) i,
          Fin.sum_univ_succAbove (fun j ↦ (e.symm (0, y)) j • v j) i]
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
          add_assoc, add_left_comm, add_comm]
      change μ ((fun x : ℂ => (x, y)) ⁻¹' A) ≤
        ENNReal.ofReal (2 * L * r / ‖v i‖)
      rw [hfiber]
      exact hμ.measure_norm_add_smul_le a (v i) hvi r hr
    _ = ENNReal.ofReal (2 * L * r / ‖v i‖) := by simp [ν]

/-- The same conditional estimate, written with the maximal Pi norm. -/
theorem measure_pi_norm_affineValue_le_max (hμ : IsBoundedDensityAtom μ L)
    {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E) (i : Fin (n + 1))
    (hi : ‖v i‖ = ‖v‖) (hv : ‖v‖ ≠ 0) (r : ℝ) (hr : 0 ≤ r) :
    (Measure.pi fun _ : Fin (n + 1) => μ)
        {x : Fin (n + 1) → ℂ | ‖affineValue v₀ v x‖ ≤ r} ≤
      ENNReal.ofReal (2 * L * r / ‖v‖) := by
  have hvi : v i ≠ 0 := by
    intro hzero
    apply hv
    simpa [hzero] using hi.symm
  simpa [hi] using measure_pi_norm_affineValue_le hμ v₀ v i hvi r hr

end ProductSmallBall

section LowerTail

variable {μ : Measure ℂ} {L : ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem exists_maximal_coefficient {n : ℕ} (v : Fin (n + 1) → E) :
    ∃ i : Fin (n + 1), ‖v i‖ = ‖v‖ := by
  simpa only [mem_range] using (IsGreatest.pi_norm v).1

private theorem sqrt_exp_half (s : ℝ) :
    Real.sqrt (Real.exp s) = Real.exp (s / 2) := by
  have h₁ : Real.sqrt (Real.exp s) ^ 2 = Real.exp s :=
    Real.sq_sqrt (Real.exp_pos s).le
  have h₂ : Real.exp (s / 2) ^ 2 = Real.exp s := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  nlinarith [Real.sqrt_nonneg (Real.exp s), Real.exp_pos (s / 2)]

theorem affineLambda_pos {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E)
    (hv : ‖v‖ ≠ 0) : 0 < affineLambda v₀ v := by
  have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
  have hp : 0 < (n + 1 : ℝ) := by positivity
  have hmax : ((n + 1 : ℕ) : ℝ) * ‖v‖ ≤ affineLambda v₀ v := by
    exact le_max_right _ _
  exact (mul_pos hp hvpos).trans_le (by simpa using hmax)

theorem measure_affineValue_small_center_le (hμ : IsBoundedDensityAtom μ L)
    {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E) (hv : ‖v‖ ≠ 0)
    (hcenter : ‖v₀‖ ≤ 2 * (n + 1 : ℝ) * ‖v‖)
    (u : ℝ) (hu : 0 ≤ u) :
    (Measure.pi fun _ : Fin (n + 1) => μ)
        {x | ‖affineValue v₀ v x‖ ≤ u * affineLambda v₀ v} ≤
      ENNReal.ofReal (4 * L * (n + 1 : ℝ) * u) := by
  obtain ⟨i, hi⟩ := exists_maximal_coefficient v
  have hlambda_nonneg := affineLambda_nonneg v₀ v
  have hlambda : affineLambda v₀ v ≤ 2 * (n + 1 : ℝ) * ‖v‖ := by
    rw [affineLambda, max_le_iff]
    exact ⟨hcenter, by
      norm_num [Nat.cast_add, Nat.cast_one]
      nlinarith [norm_nonneg v]⟩
  refine (measure_pi_norm_affineValue_le_max hμ v₀ v i hi hv
    (u * affineLambda v₀ v) (mul_nonneg hu hlambda_nonneg)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
  have hL2 : 0 ≤ 2 * L := mul_nonneg (by norm_num) hμ.nonneg
  apply (div_le_iff₀ hvpos).2
  calc
    2 * L * (u * affineLambda v₀ v) ≤
        2 * L * (u * (2 * (n + 1 : ℝ) * ‖v‖)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlambda hu) hL2
    _ = 4 * L * (n + 1 : ℝ) * u * ‖v‖ := by ring

/-- In the large-center regime, a small affine value forces at least one
scalar atom to be large.  The resulting estimate is the paper's Markov bound,
with a harmless extra factor `p` from a coordinate union bound. -/
theorem measure_affineValue_large_center_markov_le (hμ : IsBoundedDensityAtom μ L)
    {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E) (hv : ‖v‖ ≠ 0)
    (hcenter : 2 * (n + 1 : ℝ) * ‖v‖ < ‖v₀‖)
    (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1 / 2) :
    (Measure.pi fun _ : Fin (n + 1) => μ)
        {x | ‖affineValue v₀ v x‖ ≤ u * ‖v₀‖} ≤
      ENNReal.ofReal
        (4 * (n + 1 : ℝ) * (((n + 1 : ℝ) * ‖v‖ / ‖v₀‖) ^ 2)) := by
  let p : ℝ := n + 1
  let b : ℝ := ‖v₀‖
  let ν : ℝ := ‖v‖
  have hp : 0 < p := by
    dsimp [p]
    exact_mod_cast Nat.succ_pos n
  have hν : 0 < ν := by
    dsimp [ν]
    exact lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
  have hb : 0 < b := by
    dsimp [b]
    have hpos : 0 < 2 * (n + 1 : ℝ) * ‖v‖ := by
      have hp' : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
      exact mul_pos (mul_pos (by norm_num) hp')
        (lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv))
    exact hpos.trans hcenter
  have hpν : 0 < 2 * p * ν := mul_pos (mul_pos (by positivity) hp) hν
  have hthreshold : 0 < b / (2 * p * ν) := div_pos hb hpν
  have hsubset :
      {x : Fin (n + 1) → ℂ | ‖affineValue v₀ v x‖ ≤ u * b} ⊆
        {x : Fin (n + 1) → ℂ | b / (2 * p * ν) ≤ ‖x‖} := by
    intro x hx
    have hnoise : ‖∑ i, x i • v i‖ ≤ p * ‖x‖ * ν := by
      simpa [p, ν, affineValue] using norm_affineValue_le_sup (0 : E) v x
    have hbtri : b ≤ ‖affineValue v₀ v x‖ + ‖∑ i, x i • v i‖ := by
      dsimp [b]
      calc
        ‖v₀‖ = ‖affineValue v₀ v x - ∑ i, x i • v i‖ := by
          congr 1
          simp [affineValue]
        _ ≤ ‖affineValue v₀ v x‖ + ‖∑ i, x i • v i‖ := norm_sub_le _ _
    change ‖affineValue v₀ v x‖ ≤ u * b at hx
    have haff : ‖affineValue v₀ v x‖ ≤ b / 2 := by
      refine hx.trans ?_
      calc
        u * b ≤ (1 / 2 : ℝ) * b := mul_le_mul_of_nonneg_right hu' hb.le
        _ = b / 2 := by ring
    have hhalf : b / 2 ≤ ‖∑ i, x i • v i‖ := by
      linarith
    apply (div_le_iff₀ hpν).2
    nlinarith
  refine (measure_mono hsubset).trans ?_
  refine (hμ.measure_pi_norm_ge_le (b / (2 * p * ν)) hthreshold).trans ?_
  apply ENNReal.ofReal_le_ofReal
  dsimp [p, b, ν]
  field_simp
  norm_num [Nat.cast_add, Nat.cast_one]

theorem measure_affineValue_large_center_density_le (hμ : IsBoundedDensityAtom μ L)
    {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E) (hv : ‖v‖ ≠ 0)
    (u : ℝ) (hu : 0 ≤ u) :
    (Measure.pi fun _ : Fin (n + 1) => μ)
        {x | ‖affineValue v₀ v x‖ ≤ u * ‖v₀‖} ≤
      ENNReal.ofReal
        (2 * L * (n + 1 : ℝ) * u /
          ((n + 1 : ℝ) * ‖v‖ / ‖v₀‖)) := by
  obtain ⟨i, hi⟩ := exists_maximal_coefficient v
  have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
  by_cases hv₀ : v₀ = 0
  · simpa [hv₀] using
      (measure_pi_norm_affineValue_le_max hμ v₀ v i hi hv 0 le_rfl)
  have hbpos : 0 < ‖v₀‖ := norm_pos_iff.mpr hv₀
  refine (measure_pi_norm_affineValue_le_max hμ v₀ v i hi hv
    (u * ‖v₀‖) (mul_nonneg hu hbpos.le)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  field_simp
  ring_nf
  exact le_rfl

/-- Uniform square-root lower-tail estimate in the large-center regime. -/
theorem measure_affineValue_large_center_le (hμ : IsBoundedDensityAtom μ L)
    {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E) (hv : ‖v‖ ≠ 0)
    (hcenter : 2 * (n + 1 : ℝ) * ‖v‖ < ‖v₀‖)
    (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1 / 2) :
    (Measure.pi fun _ : Fin (n + 1) => μ)
        {x | ‖affineValue v₀ v x‖ ≤ u * ‖v₀‖} ≤
      ENNReal.ofReal ((4 + 2 * L) * (n + 1 : ℝ) * Real.sqrt u) := by
  let δ : ℝ := (n + 1 : ℝ) * ‖v‖ / ‖v₀‖
  have hδ : 0 < δ := by
    dsimp [δ]
    have hp : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    have hbpos : 0 < ‖v₀‖ := by
      exact (mul_pos (mul_pos (by norm_num) hp) hvpos).trans hcenter
    exact div_pos (mul_pos hp hvpos) hbpos
  have hsqrt : 0 ≤ Real.sqrt u := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
  have hu_one : u ≤ 1 := hu'.trans (by norm_num)
  have hsqrt_one : Real.sqrt u ≤ 1 := by nlinarith
  have hu_sqrt : u ≤ Real.sqrt u := by nlinarith
  by_cases hcase : δ ^ 2 ≤ u
  · refine (measure_affineValue_large_center_markov_le hμ v₀ v hv hcenter u hu hu').trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hp : 0 ≤ (n + 1 : ℝ) := by positivity
    have h₁ : 4 * (n + 1 : ℝ) * δ ^ 2 ≤ 4 * (n + 1 : ℝ) * u := by
      gcongr
    have h₂ : 4 * (n + 1 : ℝ) * u ≤
        4 * (n + 1 : ℝ) * Real.sqrt u := by
      gcongr
    have h₃ : 4 * (n + 1 : ℝ) * Real.sqrt u ≤
        (4 + 2 * L) * (n + 1 : ℝ) * Real.sqrt u := by
      have : 4 ≤ 4 + 2 * L := by linarith [hμ.nonneg]
      gcongr
    simpa [δ] using h₁.trans (h₂.trans h₃)
  · refine (measure_affineValue_large_center_density_le hμ v₀ v hv u hu).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hsqrt_lt : Real.sqrt u < δ := by
      have : u < δ ^ 2 := lt_of_not_ge hcase
      nlinarith
    have hdiv : u / δ ≤ Real.sqrt u := by
      apply (div_le_iff₀ hδ).2
      nlinarith
    have hp : 0 ≤ (n + 1 : ℝ) := by positivity
    have hcoef : 0 ≤ 2 * L * (n + 1 : ℝ) := by
      exact mul_nonneg (mul_nonneg (by norm_num) hμ.nonneg) hp
    calc
      2 * L * (n + 1 : ℝ) * u / δ =
          (2 * L * (n + 1 : ℝ)) * (u / δ) := by ring
      _ ≤ (2 * L * (n + 1 : ℝ)) * Real.sqrt u :=
        mul_le_mul_of_nonneg_left hdiv hcoef
      _ ≤ (4 + 2 * L) * (n + 1 : ℝ) * Real.sqrt u := by
        have : 2 * L ≤ 4 + 2 * L := by linarith
        gcongr

/-- The two center regimes combine into one exponential lower tail. -/
theorem measure_affineValue_lower_le (hμ : IsBoundedDensityAtom μ L)
    {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E) (hv : ‖v‖ ≠ 0)
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin (n + 1) => μ)
        {x | ‖affineValue v₀ v x‖ ≤
          Real.exp (-t) * affineLambda v₀ v} ≤
      ENNReal.ofReal
        (8 * (1 + L) * (n + 1 : ℝ) * Real.exp (-t / 2)) := by
  letI := hμ.toIsProbabilityMeasure
  by_cases hcenter : ‖v₀‖ ≤ 2 * (n + 1 : ℝ) * ‖v‖
  · refine (measure_affineValue_small_center_le hμ v₀ v hv hcenter
      (Real.exp (-t)) (Real.exp_pos _).le).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hexp : Real.exp (-t) ≤ Real.exp (-t / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hp : 0 ≤ (n + 1 : ℝ) := by positivity
    have he : 0 ≤ Real.exp (-t / 2) := (Real.exp_pos _).le
    have hcoef : 4 * L ≤ 8 * (1 + L) := by linarith [hμ.nonneg]
    have hfac : 0 ≤ 4 * L * (n + 1 : ℝ) := by
      exact mul_nonneg (mul_nonneg (by positivity) hμ.nonneg) hp
    calc
      4 * L * (n + 1 : ℝ) * Real.exp (-t) ≤
          4 * L * (n + 1 : ℝ) * Real.exp (-t / 2) := by
        exact mul_le_mul_of_nonneg_left hexp hfac
      _ ≤ 8 * (1 + L) * (n + 1 : ℝ) * Real.exp (-t / 2) := by
        gcongr
  · have hcenter' : 2 * (n + 1 : ℝ) * ‖v‖ < ‖v₀‖ := lt_of_not_ge hcenter
    have hlambda : affineLambda v₀ v = ‖v₀‖ := by
      rw [affineLambda, max_eq_left]
      norm_num [Nat.cast_add, Nat.cast_one]
      have hpν : 0 ≤ (n + 1 : ℝ) * ‖v‖ := by positivity
      nlinarith
    by_cases htlog : t < Real.log 2
    · calc
        (Measure.pi fun _ : Fin (n + 1) => μ)
            {x | ‖affineValue v₀ v x‖ ≤
              Real.exp (-t) * affineLambda v₀ v} ≤ 1 := by
          calc
            (Measure.pi fun _ : Fin (n + 1) => μ)
                {x | ‖affineValue v₀ v x‖ ≤
                  Real.exp (-t) * affineLambda v₀ v} ≤
                (Measure.pi fun _ : Fin (n + 1) => μ) univ := measure_mono (subset_univ _)
            _ = 1 := measure_univ
        _ ≤ ENNReal.ofReal
            (8 * (1 + L) * (n + 1 : ℝ) * Real.exp (-t / 2)) := by
          rw [← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          have hexp : (1 : ℝ) / 2 < Real.exp (-t / 2) := by
            calc
              (1 : ℝ) / 2 = Real.exp (-Real.log 2) := by
                rw [Real.exp_neg, Real.exp_log (by norm_num)]
                norm_num
              _ < Real.exp (-t / 2) := by
                apply Real.exp_lt_exp.mpr
                nlinarith
          have hp : (1 : ℝ) ≤ n + 1 := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          have honeL : 1 ≤ 1 + L := by linarith [hμ.nonneg]
          calc
            (1 : ℝ) ≤ 8 * 1 * 1 * ((1 : ℝ) / 2) := by norm_num
            _ ≤ 8 * (1 + L) * (n + 1 : ℝ) * Real.exp (-t / 2) := by
              gcongr <;> linarith
    · have htlog' : Real.log 2 ≤ t := le_of_not_gt htlog
      have hu : Real.exp (-t) ≤ 1 / 2 := by
        calc
          Real.exp (-t) ≤ Real.exp (-Real.log 2) := by
            apply Real.exp_le_exp.mpr
            linarith
          _ = 1 / 2 := by
            rw [Real.exp_neg, Real.exp_log (by norm_num)]
            norm_num
      rw [hlambda]
      refine (measure_affineValue_large_center_le hμ v₀ v hv hcenter'
        (Real.exp (-t)) (Real.exp_pos _).le hu).trans ?_
      apply ENNReal.ofReal_le_ofReal
      rw [sqrt_exp_half]
      have hp : 0 ≤ (n + 1 : ℝ) := by positivity
      have he : 0 ≤ Real.exp (-t / 2) := (Real.exp_pos _).le
      have hcoef : 4 + 2 * L ≤ 8 * (1 + L) := by linarith [hμ.nonneg]
      gcongr

end LowerTail

section UpperTail

variable {μ : Measure ℂ} {L : ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Exponential upper tail at the auxiliary scale.  A coordinate union bound
and the variance-one hypothesis suffice. -/
theorem measure_affineValue_upper_le (hμ : IsBoundedDensityAtom μ L)
    {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E) (hv : ‖v‖ ≠ 0)
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin (n + 1) => μ)
        {x | Real.exp t * affineLambda v₀ v < ‖affineValue v₀ v x‖} ≤
      ENNReal.ofReal (4 * (n + 1 : ℝ) * Real.exp (-t / 2)) := by
  letI := hμ.toIsProbabilityMeasure
  have hlambda_pos := affineLambda_pos v₀ v hv
  by_cases hsmall : t ≤ Real.log 4
  · calc
      (Measure.pi fun _ : Fin (n + 1) => μ)
          {x | Real.exp t * affineLambda v₀ v < ‖affineValue v₀ v x‖} ≤ 1 := by
        calc
          (Measure.pi fun _ : Fin (n + 1) => μ)
              {x | Real.exp t * affineLambda v₀ v < ‖affineValue v₀ v x‖} ≤
              (Measure.pi fun _ : Fin (n + 1) => μ) univ := measure_mono (subset_univ _)
          _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal (4 * (n + 1 : ℝ) * Real.exp (-t / 2)) := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        have hexp : (1 : ℝ) / 4 ≤ Real.exp (-t / 2) := by
          calc
            (1 : ℝ) / 4 = Real.exp (-Real.log 4) := by
              rw [Real.exp_neg, Real.exp_log (by norm_num)]
              norm_num
            _ ≤ Real.exp (-t / 2) := by
              apply Real.exp_le_exp.mpr
              nlinarith
        have hp : (1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        nlinarith
  · have hlog : Real.log 4 < t := lt_of_not_ge hsmall
    have hexp_four : 4 < Real.exp t := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      exact Real.exp_lt_exp.mpr hlog
    have hsubset :
        {x : Fin (n + 1) → ℂ |
            Real.exp t * affineLambda v₀ v < ‖affineValue v₀ v x‖} ⊆
          {x : Fin (n + 1) → ℂ | Real.exp t / 2 ≤ ‖x‖} := by
      intro x hx
      have hdet := norm_affineValue_le_lambda_mul v₀ v x
      have hdiv : Real.exp t < 1 + ‖x‖ := by
        apply (mul_lt_mul_iff_of_pos_left hlambda_pos).mp
        simpa [mul_comm] using hx.trans_le hdet
      have hexp_two : 2 < Real.exp t := (by norm_num : (2 : ℝ) < 4).trans hexp_four
      have hhalf : Real.exp t / 2 < Real.exp t - 1 := by linarith
      have hxnorm : Real.exp t - 1 < ‖x‖ := by linarith
      exact (hhalf.trans hxnorm).le
    refine (measure_mono hsubset).trans ?_
    refine (hμ.measure_pi_norm_ge_le (Real.exp t / 2) (by positivity)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hexpmono : Real.exp (-2 * t) ≤ Real.exp (-t / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    norm_num [Nat.cast_add, Nat.cast_one]
    calc
      (n + 1 : ℝ) / (Real.exp t / 2) ^ 2 =
          4 * (n + 1 : ℝ) * Real.exp (-2 * t) := by
        rw [show -2 * t = -(2 * t) by ring, Real.exp_neg]
        have hexp_sq : Real.exp (2 * t) = (Real.exp t) ^ 2 := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        rw [hexp_sq]
        field_simp
        ring
      _ ≤ 4 * (n + 1 : ℝ) * Real.exp (-t / 2) := by
        gcongr

end UpperTail

section LogTail

variable {μ : Measure ℂ} {L : ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Combined two-sided tail for the normalized affine logarithm. -/
theorem measure_abs_log_affineValue_div_le (hμ : IsBoundedDensityAtom μ L)
    {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E) (hv : ‖v‖ ≠ 0)
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin (n + 1) => μ)
        {x | t < |Real.log (‖affineValue v₀ v x‖ / affineLambda v₀ v)|} ≤
      ENNReal.ofReal
        (16 * (1 + L) * (n + 1 : ℝ) * Real.exp (-t / 2)) := by
  let lambda := affineLambda v₀ v
  have hlambda_pos : 0 < lambda := affineLambda_pos v₀ v hv
  let U : Set (Fin (n + 1) → ℂ) :=
    {x | Real.exp t * lambda < ‖affineValue v₀ v x‖}
  let D : Set (Fin (n + 1) → ℂ) :=
    {x | ‖affineValue v₀ v x‖ ≤ Real.exp (-t) * lambda}
  have hsubset :
      {x : Fin (n + 1) → ℂ |
          t < |Real.log (‖affineValue v₀ v x‖ / lambda)|} ⊆ U ∪ D := by
    intro x hx
    let a := Real.log (‖affineValue v₀ v x‖ / lambda)
    change t < |a| at hx
    by_cases hup : t < a
    · left
      change Real.exp t * lambda < ‖affineValue v₀ v x‖
      have hnorm : 0 < ‖affineValue v₀ v x‖ := by
        by_contra hzero
        have : ‖affineValue v₀ v x‖ = 0 := le_antisymm (le_of_not_gt hzero) (norm_nonneg _)
        simp [a, this] at hup
        linarith
      have hratio : 0 < ‖affineValue v₀ v x‖ / lambda := div_pos hnorm hlambda_pos
      have := (Real.lt_log_iff_exp_lt hratio).1 hup
      exact (lt_div_iff₀ hlambda_pos).1 this
    · right
      change ‖affineValue v₀ v x‖ ≤ Real.exp (-t) * lambda
      have ha_neg : a < -t := by
        by_cases ha : 0 ≤ a
        · rw [abs_of_nonneg ha] at hx
          exact False.elim (hup hx)
        · rw [abs_of_neg (lt_of_not_ge ha)] at hx
          linarith
      by_cases hzero : ‖affineValue v₀ v x‖ = 0
      · rw [hzero]
        exact mul_nonneg (Real.exp_pos _).le hlambda_pos.le
      · have hnorm : 0 < ‖affineValue v₀ v x‖ :=
          lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
        have hratio : 0 < ‖affineValue v₀ v x‖ / lambda := div_pos hnorm hlambda_pos
        have := (Real.log_lt_iff_lt_exp hratio).1 ha_neg
        exact (div_lt_iff₀ hlambda_pos).1 this |>.le
  calc
    (Measure.pi fun _ : Fin (n + 1) => μ)
        {x | t < |Real.log (‖affineValue v₀ v x‖ / lambda)|} ≤
        (Measure.pi fun _ : Fin (n + 1) => μ) (U ∪ D) := measure_mono hsubset
    _ ≤ (Measure.pi fun _ : Fin (n + 1) => μ) U +
        (Measure.pi fun _ : Fin (n + 1) => μ) D := measure_union_le U D
    _ ≤ ENNReal.ofReal (4 * (n + 1 : ℝ) * Real.exp (-t / 2)) +
        ENNReal.ofReal (8 * (1 + L) * (n + 1 : ℝ) * Real.exp (-t / 2)) := by
      apply add_le_add
      · simpa [U, lambda] using measure_affineValue_upper_le hμ v₀ v hv t ht
      · simpa [D, lambda] using measure_affineValue_lower_le hμ v₀ v hv t ht
    _ = ENNReal.ofReal
        (4 * (n + 1 : ℝ) * Real.exp (-t / 2) +
          8 * (1 + L) * (n + 1 : ℝ) * Real.exp (-t / 2)) := by
      rw [ENNReal.ofReal_add]
      · positivity
      · have : 0 ≤ 1 + L := by linarith [hμ.nonneg]
        positivity
    _ ≤ ENNReal.ofReal
        (16 * (1 + L) * (n + 1 : ℝ) * Real.exp (-t / 2)) := by
      apply ENNReal.ofReal_le_ofReal
      have hp : 0 ≤ (n + 1 : ℝ) := by positivity
      have he : 0 ≤ Real.exp (-t / 2) := (Real.exp_pos _).le
      have hcoef : 12 + 8 * L ≤ 16 * (1 + L) := by linarith [hμ.nonneg]
      calc
        4 * (n + 1 : ℝ) * Real.exp (-t / 2) +
            8 * (1 + L) * (n + 1 : ℝ) * Real.exp (-t / 2) =
            (12 + 8 * L) * (n + 1 : ℝ) * Real.exp (-t / 2) := by ring
        _ ≤ 16 * (1 + L) * (n + 1 : ℝ) * Real.exp (-t / 2) := by
          gcongr

end LogTail

/-! The remaining lemmas are stated using Lebesgue integrals in `ℝ≥0∞`.
This avoids building integrability into an interface: finiteness is a theorem
consequence of the explicit bound below. -/

open BernoulliSection10 (lintegral_sq_le_of_exponential_tail
  lintegral_sq_add_const_le lintegral_lintegral_sq_sub_le)

section AffineMoment

variable {μ : Measure ℂ} {L : ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The normalized log-ratio version of the centered estimate in the proof
of Lemma 10.2. -/
theorem affine_log_ratio_lambda_lintegral_le (hμ : IsBoundedDensityAtom μ L)
    {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E) (hv : ‖v‖ ≠ 0) :
    ∫⁻ x, ENNReal.ofReal
        (|Real.log (‖affineValue v₀ v x‖ / affineLambda v₀ v)| ^ 2)
        ∂(Measure.pi fun _ : Fin (n + 1) => μ) ≤
      ENNReal.ofReal
        (affineLogConstant L *
          Real.log (Real.exp 1 * (n + 1 : ℝ)) ^ 2) := by
  letI := hμ.toIsProbabilityMeasure
  let Z : (Fin (n + 1) → ℂ) → ℝ := fun x =>
    |Real.log (‖affineValue v₀ v x‖ / affineLambda v₀ v)|
  let B : ℝ := 16 * (1 + L) * (n + 1 : ℝ)
  have hB : 1 ≤ B := by
    dsimp [B]
    have hp : (1 : ℝ) ≤ n + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    nlinarith [hμ.nonneg]
  have hZ : Measurable Z := by
    dsimp [Z]
    exact continuous_abs.measurable.comp (Real.measurable_log.comp
      ((measurable_affineValue v₀ v).div_const _))
  have hraw := lintegral_sq_le_of_exponential_tail
    (Measure.pi fun _ : Fin (n + 1) => μ) Z hZ (fun _ => abs_nonneg _) B hB
    (fun t ht => by
      simpa [Z, B] using measure_abs_log_affineValue_div_le hμ v₀ v hv t ht)
  refine hraw.trans ?_
  apply ENNReal.ofReal_le_ofReal
  let A : ℝ := 16 * (1 + L)
  let q : ℝ := n + 1
  let ℓ : ℝ := Real.log (Real.exp 1 * q)
  have hA : 1 ≤ A := by
    dsimp [A]
    nlinarith [hμ.nonneg]
  have hq : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hℓ : ℓ = 1 + Real.log q := by
    dsimp [ℓ]
    rw [Real.log_mul (Real.exp_ne_zero 1) hqpos.ne', Real.log_exp]
  have hlogB : Real.log B = Real.log A + Real.log q := by
    dsimp [B, A, q]
    rw [Real.log_mul hApos.ne' hqpos.ne']
  have hlogBnonneg : 0 ≤ Real.log B := Real.log_nonneg hB
  have hℓone : 1 ≤ ℓ := by rw [hℓ]; linarith
  have hlogle : Real.log B ≤ (1 + Real.log A) * ℓ := by
    rw [hlogB, hℓ]
    nlinarith [mul_nonneg hlogA hlogq]
  have hsq : Real.log B ^ 2 ≤ (1 + Real.log A) ^ 2 * ℓ ^ 2 := by
    have hright : 0 ≤ (1 + Real.log A) * ℓ := by positivity
    nlinarith
  dsimp [affineLogConstant]
  change 16 * Real.log B ^ 2 + 32 ≤
    1024 * (1 + Real.log (16 * (1 + L))) ^ 2 *
      Real.log (Real.exp 1 * (n + 1 : ℝ)) ^ 2
  change 16 * Real.log B ^ 2 + 32 ≤
    1024 * (1 + Real.log A) ^ 2 * ℓ ^ 2
  have honeA : 1 ≤ (1 + Real.log A) ^ 2 := by nlinarith [sq_nonneg (Real.log A)]
  have honeℓ : 1 ≤ ℓ ^ 2 := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg (1 + Real.log A)) (sq_nonneg ℓ)]

/-- A nonconstant affine map vanishes on a null set under the product law. -/
theorem measure_affineValue_eq_zero (hμ : IsBoundedDensityAtom μ L)
    {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E) (hv : ‖v‖ ≠ 0) :
    (Measure.pi fun _ : Fin (n + 1) => μ) {x | affineValue v₀ v x = 0} = 0 := by
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm v).1
  have hvi : v i ≠ 0 := by
    intro hz
    apply hv
    simpa [hz] using hi.symm
  apply nonpos_iff_eq_zero.mp
  calc
    (Measure.pi fun _ : Fin (n + 1) => μ) {x | affineValue v₀ v x = 0} ≤
        (Measure.pi fun _ : Fin (n + 1) => μ) {x | ‖affineValue v₀ v x‖ ≤ 0} := by
      apply measure_mono
      intro x hx
      simp [hx]
    _ ≤ ENNReal.ofReal (2 * L * 0 / ‖v i‖) :=
      measure_pi_norm_affineValue_le hμ v₀ v i hvi 0 le_rfl
    _ = 0 := by simp

/-- Centered-at-`λ` form with the paper's difference of logarithms. -/
theorem affine_log_lambda_lintegral_le (hμ : IsBoundedDensityAtom μ L)
    {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E) (hv : ‖v‖ ≠ 0) :
    ∫⁻ x, ENNReal.ofReal
        (|Real.log ‖affineValue v₀ v x‖ - Real.log (affineLambda v₀ v)| ^ 2)
        ∂(Measure.pi fun _ : Fin (n + 1) => μ) ≤
      ENNReal.ofReal
        (affineLogConstant L *
          Real.log (Real.exp 1 * (n + 1 : ℝ)) ^ 2) := by
  have hlambda_ne : affineLambda v₀ v ≠ 0 := (affineLambda_pos v₀ v hv).ne'
  have hzero := measure_affineValue_eq_zero hμ v₀ v hv
  have hae_nonzero : ∀ᵐ x ∂(Measure.pi fun _ : Fin (n + 1) => μ),
      affineValue v₀ v x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_ne_iff] using hzero
  have hae : ∀ᵐ x ∂(Measure.pi fun _ : Fin (n + 1) => μ),
      ENNReal.ofReal
          (|Real.log ‖affineValue v₀ v x‖ - Real.log (affineLambda v₀ v)| ^ 2) =
        ENNReal.ofReal
          (|Real.log (‖affineValue v₀ v x‖ / affineLambda v₀ v)| ^ 2) := by
    filter_upwards [hae_nonzero] with x hx
    rw [Real.log_div (norm_ne_zero_iff.mpr hx) hlambda_ne]
  rw [lintegral_congr_ae hae]
  exact affine_log_ratio_lambda_lintegral_le hμ v₀ v hv

/-- The second, `ρ`-centered conclusion of Lemma 10.2 in the nonconstant
coefficient case.  The deterministic comparison with `λ` is discharged here. -/
theorem affine_log_rho_lintegral_le_of_piNorm_ne_zero
    (hμ : IsBoundedDensityAtom μ L)
    {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E) (hv : ‖v‖ ≠ 0) :
    ∫⁻ x, ENNReal.ofReal
        (|Real.log ‖affineValue v₀ v x‖ - Real.log (affineRho v₀ v)| ^ 2)
        ∂(Measure.pi fun _ : Fin (n + 1) => μ) ≤
      ENNReal.ofReal
        (2 * (affineLogConstant L + 1) *
          Real.log (Real.exp 1 * (n + 1 : ℝ)) ^ 2) := by
  letI := hμ.toIsProbabilityMeasure
  let ν : Measure (Fin (n + 1) → ℂ) := Measure.pi fun _ : Fin (n + 1) => μ
  let ell : ℝ := Real.log (Real.exp 1 * (n + 1 : ℝ))
  let f : (Fin (n + 1) → ℂ) → ℝ := fun x ↦
    Real.log ‖affineValue v₀ v x‖ - Real.log (affineLambda v₀ v)
  let c : ℝ := Real.log (affineLambda v₀ v) - Real.log (affineRho v₀ v)
  have hf : Measurable f := by
    dsimp [f]
    exact (Real.measurable_log.comp (measurable_affineValue v₀ v)).sub_const _
  have hC : 0 ≤ affineLogConstant L := by
    unfold affineLogConstant
    positivity
  have hK : 0 ≤ affineLogConstant L * ell ^ 2 :=
    mul_nonneg hC (sq_nonneg ell)
  have hbase :
      ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂ν ≤
        ENNReal.ofReal (affineLogConstant L * ell ^ 2) := by
    simpa [f, ell, ν] using affine_log_lambda_lintegral_le hμ v₀ v hv
  have hshift := lintegral_sq_add_const_le ν f hf c
    (affineLogConstant L * ell ^ 2) hK hbase
  have hell_nonneg : 0 ≤ ell := by
    have hq : (1 : ℝ) ≤ n + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hqpos : (0 : ℝ) < n + 1 := zero_lt_one.trans_le hq
    dsimp [ell]
    rw [Real.log_mul (Real.exp_ne_zero 1) hqpos.ne', Real.log_exp]
    linarith [Real.log_nonneg hq]
  have hcabs : |c| ≤ ell := by
    simpa [c, ell] using abs_log_affineLambda_sub_log_affineRho_le v₀ v hv
  have hc_sq : c ^ 2 ≤ ell ^ 2 := by
    apply (sq_le_sq).2
    simpa [abs_of_nonneg hell_nonneg] using hcabs
  calc
    (∫⁻ x, ENNReal.ofReal
        (|Real.log ‖affineValue v₀ v x‖ - Real.log (affineRho v₀ v)| ^ 2) ∂ν) =
        ∫⁻ x, ENNReal.ofReal ((f x + c) ^ 2) ∂ν := by
      apply lintegral_congr
      intro x
      rw [sq_abs]
      congr 2
      dsimp [f, c]
      ring
    _ ≤ ENNReal.ofReal
        (2 * (affineLogConstant L * ell ^ 2) + 2 * c ^ 2) := hshift
    _ ≤ ENNReal.ofReal (2 * (affineLogConstant L + 1) * ell ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        2 * (affineLogConstant L * ell ^ 2) + 2 * c ^ 2 ≤
            2 * (affineLogConstant L * ell ^ 2) + 2 * ell ^ 2 := by
          gcongr
        _ = 2 * (affineLogConstant L + 1) * ell ^ 2 := by ring

/-- Caller-facing `ρ`-centered assertion of Lemma 10.2.  The only extra
hypothesis says exactly that the affine map is not identically zero. -/
theorem lemma_10_2_rho_lintegral_le (hμ : IsBoundedDensityAtom μ L)
    {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E) (hG : v₀ ≠ 0 ∨ v ≠ 0) :
    ∫⁻ x, ENNReal.ofReal
        (|Real.log ‖affineValue v₀ v x‖ - Real.log (affineRho v₀ v)| ^ 2)
        ∂(Measure.pi fun _ : Fin (n + 1) => μ) ≤
      ENNReal.ofReal
        (lemma10_2Constant L * Real.log (Real.exp 1 * (n + 1 : ℝ)) ^ 2) := by
  by_cases hv : ‖v‖ = 0
  · have hvzero : v = 0 := norm_eq_zero.mp hv
    subst v
    simp [affineValue, affineRho, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  · refine (affine_log_rho_lintegral_le_of_piNorm_ne_zero hμ v₀ v hv).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hC : 0 ≤ affineLogConstant L + 1 := by
      unfold affineLogConstant
      positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num) hC)
      (sq_nonneg (Real.log (Real.exp 1 * (n + 1 : ℝ))))

/-- The independent-resampling assertion of Lemma 10.2.  The two nested
Lebesgue integrals are expectation with respect to two independent copies of
the canonical product vector. -/
theorem lemma_10_2_resampling_lintegral_le (hμ : IsBoundedDensityAtom μ L)
    {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E) (hG : v₀ ≠ 0 ∨ v ≠ 0) :
    ∫⁻ x, ∫⁻ x', ENNReal.ofReal
        (|Real.log ‖affineValue v₀ v x‖ - Real.log ‖affineValue v₀ v x'‖| ^ 2)
        ∂(Measure.pi fun _ : Fin (n + 1) => μ)
        ∂(Measure.pi fun _ : Fin (n + 1) => μ) ≤
      ENNReal.ofReal
        (lemma10_2Constant L * Real.log (Real.exp 1 * (n + 1 : ℝ)) ^ 2) := by
  by_cases hv : ‖v‖ = 0
  · have hvzero : v = 0 := norm_eq_zero.mp hv
    subst v
    simp [affineValue]
  · letI := hμ.toIsProbabilityMeasure
    let ν : Measure (Fin (n + 1) → ℂ) := Measure.pi fun _ : Fin (n + 1) => μ
    let ell : ℝ := Real.log (Real.exp 1 * (n + 1 : ℝ))
    let f : (Fin (n + 1) → ℂ) → ℝ := fun x ↦
      Real.log ‖affineValue v₀ v x‖ - Real.log (affineRho v₀ v)
    let K : ℝ := 2 * (affineLogConstant L + 1) * ell ^ 2
    have hf : Measurable f := by
      dsimp [f]
      exact (Real.measurable_log.comp (measurable_affineValue v₀ v)).sub_const _
    have hK : 0 ≤ K := by
      dsimp [K]
      have hC : 0 ≤ affineLogConstant L + 1 := by
        unfold affineLogConstant
        positivity
      positivity
    have hbase : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂ν ≤ ENNReal.ofReal K := by
      simpa [f, K, ell, ν] using
        affine_log_rho_lintegral_le_of_piNorm_ne_zero hμ v₀ v hv
    have hres := lintegral_lintegral_sq_sub_le ν f hf K hK hbase
    calc
      (∫⁻ x, ∫⁻ x', ENNReal.ofReal
          (|Real.log ‖affineValue v₀ v x‖ - Real.log ‖affineValue v₀ v x'‖| ^ 2)
          ∂ν ∂ν) =
          ∫⁻ x, ∫⁻ x', ENNReal.ofReal ((f x - f x') ^ 2) ∂ν ∂ν := by
        apply lintegral_congr
        intro x
        apply lintegral_congr
        intro x'
        rw [sq_abs]
        congr 2
        dsimp [f]
        ring
      _ ≤ ENNReal.ofReal (4 * K) := hres
      _ = ENNReal.ofReal (lemma10_2Constant L * ell ^ 2) := by
        apply congrArg ENNReal.ofReal
        dsimp [K, lemma10_2Constant]
        ring

/-- The resampling estimate with an arbitrary positive number `p` of
coordinates.  This is the form consumed by block-row applications, whose
natural coordinate type is `Fin p` rather than a syntactic successor. -/
theorem lemma_10_2_resampling_lintegral_le_of_pos
    (hμ : IsBoundedDensityAtom μ L) {p : ℕ} (hp : 0 < p)
    (v₀ : E) (v : Fin p → E) (hG : v₀ ≠ 0 ∨ v ≠ 0) :
    ∫⁻ x, ∫⁻ x', ENNReal.ofReal
        (|Real.log ‖affineValue v₀ v x‖ - Real.log ‖affineValue v₀ v x'‖| ^ 2)
        ∂(Measure.pi fun _ : Fin p => μ)
        ∂(Measure.pi fun _ : Fin p => μ) ≤
      ENNReal.ofReal
        (lemma10_2Constant L * Real.log (Real.exp 1 * (p : ℝ)) ^ 2) := by
  cases p with
  | zero => simp at hp
  | succ n =>
      simpa [Nat.succ_eq_add_one] using
        lemma_10_2_resampling_lintegral_le hμ v₀ v hG

/-- The same estimate without a nonzero side condition.  This is logically
stronger only because Lean's total logarithm satisfies `log 0 = 0`; the zero
affine map is discharged explicitly, while the nonzero branch is precisely
Lemma 10.2. -/
theorem lemma_10_2_resampling_lintegral_le_of_pos_unconditional
    (hμ : IsBoundedDensityAtom μ L) {p : ℕ} (hp : 0 < p)
    (v₀ : E) (v : Fin p → E) :
    ∫⁻ x, ∫⁻ x', ENNReal.ofReal
        (|Real.log ‖affineValue v₀ v x‖ - Real.log ‖affineValue v₀ v x'‖| ^ 2)
        ∂(Measure.pi fun _ : Fin p => μ)
        ∂(Measure.pi fun _ : Fin p => μ) ≤
      ENNReal.ofReal
        (lemma10_2Constant L * Real.log (Real.exp 1 * (p : ℝ)) ^ 2) := by
  by_cases hG : v₀ ≠ 0 ∨ v ≠ 0
  · exact lemma_10_2_resampling_lintegral_le_of_pos hμ hp v₀ v hG
  · have hv₀ : v₀ = 0 := not_ne_iff.mp (fun hv₀ ↦ hG (Or.inl hv₀))
    have hv : v = 0 := not_ne_iff.mp (fun hv ↦ hG (Or.inr hv))
    subst v₀
    subst v
    simp [affineValue]

/-- Measurability of the squared logarithmic difference on two copies of
the coefficient space. -/
theorem measurable_affineLogSqDifference {p : ℕ}
    (v₀ : E) (v : Fin p → E) :
    Measurable fun z : (Fin p → ℂ) × (Fin p → ℂ) ↦
      |Real.log ‖affineValue v₀ v z.1‖ - Real.log ‖affineValue v₀ v z.2‖| ^ 2 := by
  have hlog : Measurable fun x : Fin p → ℂ ↦ Real.log ‖affineValue v₀ v x‖ :=
    Real.measurable_log.comp (measurable_affineValue v₀ v)
  simpa [Real.norm_eq_abs] using
    ((hlog.comp measurable_fst).sub (hlog.comp measurable_snd)).norm.pow_const (2 : ℕ)

/-- Product-space integrability of the squared logarithmic difference.  No
certificate is exposed: bounded density and positive coordinate count are
the only assumptions. -/
theorem lemma_10_2_resampling_integrable_of_pos
    (hμ : IsBoundedDensityAtom μ L) {p : ℕ} (hp : 0 < p)
    (v₀ : E) (v : Fin p → E) :
    Integrable
      (fun z : (Fin p → ℂ) × (Fin p → ℂ) ↦
        |Real.log ‖affineValue v₀ v z.1‖ - Real.log ‖affineValue v₀ v z.2‖| ^ 2)
      ((Measure.pi fun _ : Fin p => μ).prod (Measure.pi fun _ : Fin p => μ)) := by
  letI := hμ.toIsProbabilityMeasure
  let ν : Measure (Fin p → ℂ) := Measure.pi fun _ : Fin p => μ
  let F : (Fin p → ℂ) × (Fin p → ℂ) → ℝ := fun z ↦
    |Real.log ‖affineValue v₀ v z.1‖ - Real.log ‖affineValue v₀ v z.2‖| ^ 2
  have hF : Measurable F := by
    simpa [F] using measurable_affineLogSqDifference v₀ v
  have hlin :
      ∫⁻ z, ENNReal.ofReal (F z) ∂ν.prod ν ≤
        ENNReal.ofReal
          (lemma10_2Constant L * Real.log (Real.exp 1 * (p : ℝ)) ^ 2) := by
    rw [MeasureTheory.lintegral_prod _ hF.ennreal_ofReal.aemeasurable]
    simpa [F, ν] using
      lemma_10_2_resampling_lintegral_le_of_pos_unconditional hμ hp v₀ v
  have hfinite : ∫⁻ z, ENNReal.ofReal (F z) ∂ν.prod ν < ∞ :=
    lt_of_le_of_lt hlin (by simp)
  have hnonneg : 0 ≤ᵐ[ν.prod ν] F :=
    ae_of_all _ fun z ↦ sq_nonneg _
  have hfi : HasFiniteIntegral F (ν.prod ν) :=
    (hasFiniteIntegral_iff_ofReal hnonneg).2 hfinite
  have : Integrable F (ν.prod ν) := ⟨hF.aestronglyMeasurable, hfi⟩
  simpa [F, ν] using this

/-- Ordinary (Bochner) iterated-integral form of the independent-resampling
bound, suitable for direct use in later variance estimates. -/
theorem lemma_10_2_resampling_integral_le_of_pos
    (hμ : IsBoundedDensityAtom μ L) {p : ℕ} (hp : 0 < p)
    (v₀ : E) (v : Fin p → E) :
    ∫ x, ∫ x',
        |Real.log ‖affineValue v₀ v x‖ - Real.log ‖affineValue v₀ v x'‖| ^ 2
        ∂(Measure.pi fun _ : Fin p => μ)
        ∂(Measure.pi fun _ : Fin p => μ) ≤
      lemma10_2Constant L * Real.log (Real.exp 1 * (p : ℝ)) ^ 2 := by
  letI := hμ.toIsProbabilityMeasure
  let ν : Measure (Fin p → ℂ) := Measure.pi fun _ : Fin p => μ
  let F : (Fin p → ℂ) × (Fin p → ℂ) → ℝ := fun z ↦
    |Real.log ‖affineValue v₀ v z.1‖ - Real.log ‖affineValue v₀ v z.2‖| ^ 2
  have hFmeas : Measurable F := by
    simpa [F] using measurable_affineLogSqDifference v₀ v
  have hFint : Integrable F (ν.prod ν) := by
    simpa [F, ν] using lemma_10_2_resampling_integrable_of_pos hμ hp v₀ v
  rw [← MeasureTheory.integral_prod F hFint]
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun z ↦ sq_nonneg _) hFmeas.aestronglyMeasurable]
  apply ENNReal.toReal_le_of_le_ofReal
  · have hC : 0 ≤ affineLogConstant L + 1 := by
      unfold affineLogConstant
      positivity
    exact mul_nonneg (by simp [lemma10_2Constant, hC]) (sq_nonneg _)
  · rw [MeasureTheory.lintegral_prod _ hFmeas.ennreal_ofReal.aemeasurable]
    simpa [F, ν] using
      lemma_10_2_resampling_lintegral_le_of_pos_unconditional hμ hp v₀ v

/-- A nonzero affine map is nonzero almost surely; this includes the constant
case and exposes no conditional-density certificate. -/
theorem lemma_10_2_measure_affineValue_eq_zero (hμ : IsBoundedDensityAtom μ L)
    {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E) (hG : v₀ ≠ 0 ∨ v ≠ 0) :
    (Measure.pi fun _ : Fin (n + 1) => μ) {x | affineValue v₀ v x = 0} = 0 := by
  by_cases hv : ‖v‖ = 0
  · have hvzero : v = 0 := norm_eq_zero.mp hv
    have hv₀ : v₀ ≠ 0 := hG.resolve_right (by simpa [hvzero])
    subst v
    simp [affineValue, hv₀]
  · exact measure_affineValue_eq_zero hμ v₀ v hv

theorem lemma_10_2_affineValue_ne_zero_ae (hμ : IsBoundedDensityAtom μ L)
    {n : ℕ} (v₀ : E) (v : Fin (n + 1) → E) (hG : v₀ ≠ 0 ∨ v ≠ 0) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin (n + 1) => μ), affineValue v₀ v x ≠ 0 := by
  rw [ae_iff]
  simpa only [not_ne_iff] using lemma_10_2_measure_affineValue_eq_zero hμ v₀ v hG

end AffineMoment

end BernoulliSection10Complex
