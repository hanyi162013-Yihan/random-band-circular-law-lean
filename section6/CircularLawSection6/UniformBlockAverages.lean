import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Uniform block-length limits and normalized block averages

Convergence for every admissible choice of block length forces uniform
convergence over each finite length window. Therefore the dimension-weighted
block expectation has the same limit, regardless of how many blocks there
are. No union bound over blocks, and no uniform comparison theorem, is
assumed in this deterministic passage.
-/

open Filter Topology
open scoped BigOperators

namespace CircularLawSection6

theorem uniform_block_window_of_all_selections (F : ℕ → ℕ → ℝ)
    (lo hi : ℕ → ℕ) (hwindow : ∀ n, lo n ≤ hi n) (target : ℝ)
    (hchoice : ∀ m : ℕ → ℕ, (∀ n, lo n ≤ m n ∧ m n ≤ hi n) →
      Tendsto (fun n => F n (m n)) atTop (𝓝 target)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ m, lo n ≤ m → m ≤ hi n → |F n m - target| < ε := by
  classical
  intro ε hε
  let bad (n : ℕ) := ∃ m, lo n ≤ m ∧ m ≤ hi n ∧ ε ≤ |F n m - target|
  let choice (n : ℕ) := if h : bad n then Classical.choose h else lo n
  have hmem (n : ℕ) : lo n ≤ choice n ∧ choice n ≤ hi n := by
    by_cases h : bad n
    · simpa only [choice, dif_pos h] using
        And.intro (Classical.choose_spec h).1 (Classical.choose_spec h).2.1
    · simpa only [choice, dif_neg h] using And.intro (le_refl (lo n)) (hwindow n)
  have hlim := hchoice choice hmem
  filter_upwards [hlim.eventually (Metric.ball_mem_nhds target hε)] with n hn
  intro m hlo hhi
  by_contra hnot
  have hbad : bad n := ⟨m, hlo, hhi, not_lt.mp hnot⟩
  have hlarge := (Classical.choose_spec hbad).2.2
  have hsmall : |F n (choice n) - target| < ε := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hn
  rw [show choice n = Classical.choose hbad from dif_pos hbad] at hsmall
  exact (not_lt_of_ge hlarge) hsmall

theorem weighted_block_error_le {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (target ε : ℝ) (herror : ∀ i, |x i - target| ≤ ε) :
    |(∑ i, w i * x i) - target| ≤ ε := by
  have heq : (∑ i, w i * x i) - target = ∑ i, w i * (x i - target) := by
    symm
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [heq]
  calc
    _ ≤ ∑ i, |w i * (x i - target)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w i * |x i - target| := by
      simp_rw [abs_mul, abs_of_nonneg (hw _)]
    _ ≤ ∑ i, w i * ε := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (herror i) (hw i))
    _ = ε := by rw [← Finset.sum_mul, hsum, one_mul]

theorem tendsto_weighted_blocks_of_uniform (q : ℕ → ℕ)
    (w x : ∀ n, Fin (q n) → ℝ) (hw : ∀ n i, 0 ≤ w n i)
    (hsum : ∀ n, ∑ i, w n i = 1) (target : ℝ)
    (huniform : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i, |x n i - target| < ε) :
    Tendsto (fun n => ∑ i, w n i * x n i) atTop (𝓝 target) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [huniform (ε / 2) (half_pos hε)] with n hn
  rw [Real.dist_eq]
  exact (weighted_block_error_le (w n) (x n) (hw n) (hsum n) target (ε / 2)
    (fun i => (hn i).le)).trans_lt (half_lt_self hε)

theorem dimension_weights_sum_one {q N : ℕ} (len : Fin q → ℕ)
    (hN : 0 < N) (hsum : ∑ b, len b = N) :
    (∑ b, (len b : ℝ) / (N : ℝ)) = 1 := by
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, hsum, ← div_eq_mul_inv,
    div_self (Nat.cast_ne_zero.mpr hN.ne')]

theorem block_average_tendsto_of_all_lengths
    (F : ℕ → ℕ → ℝ) (lo hi : ℕ → ℕ) (hwindow : ∀ n, lo n ≤ hi n)
    (N q : ℕ → ℕ) (hN : ∀ n, 0 < N n) (len : ∀ n, Fin (q n) → ℕ)
    (hsum : ∀ n, ∑ b, len n b = N n)
    (hsize : ∀ n b, lo n ≤ len n b ∧ len n b ≤ hi n) (target : ℝ)
    (hchoice : ∀ m : ℕ → ℕ, (∀ n, lo n ≤ m n ∧ m n ≤ hi n) →
      Tendsto (fun n => F n (m n)) atTop (𝓝 target)) :
    Tendsto (fun n => ∑ b, ((len n b : ℝ) / (N n : ℝ)) * F n (len n b))
      atTop (𝓝 target) := by
  apply tendsto_weighted_blocks_of_uniform q
    (fun n b => (len n b : ℝ) / (N n : ℝ)) (fun n b => F n (len n b))
    (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun n => dimension_weights_sum_one (len n) (hN n) (hsum n)) target
  intro ε hε
  filter_upwards [uniform_block_window_of_all_selections F lo hi hwindow target hchoice ε hε]
    with n hn
  exact fun b => hn (len n b) (hsize n b).1 (hsize n b).2

end CircularLawSection6
