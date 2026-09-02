import TaoVuReplacement.EmpiricalSpectrum
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Smooth compactly supported approximation of vague test functions

Tao--Vu, Theorem 2.1 concludes vague convergence, hence tests against all
continuous compactly supported functions.  The Green identity is first
proved for smooth compactly supported functions.  This file supplies the
machine-checked passage between those two classes.
-/

open Function Metric Set
open scoped CompactlySupported ContDiff

noncomputable section

namespace TaoVuReplacement

/-- A continuous compactly supported function on the complex plane admits a
global uniform approximation by an infinitely differentiable compactly
supported function.

The construction first uses smooth convolution to approximate globally, and
then multiplies by a smooth bump which is one on the original support. -/
theorem exists_contDiff_hasCompactSupport_dist_lt
    (f : ℂ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      ∀ x, dist (g x) (f x) < ε := by
  let F : C_c(ℂ, ℝ) :=
    { toFun := f
      continuous_toFun := hf
      hasCompactSupport' := hfc }
  obtain ⟨h, hh_smooth, hh_close⟩ :=
    (CompactlySupportedContinuousMapClass.uniformContinuous F).exists_contDiff_dist_le hε
  have hF (x : ℂ) : F x = f x := by rfl
  have hh_close_f : ∀ x, dist (h x) (f x) < ε := by
    intro x
    simpa only [hF x] using hh_close x

  obtain ⟨r, hr⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hfc.isCompact.isBounded
  let R : ℝ := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right r 1)
  have hsuppR : tsupport f ⊆ closedBall (0 : ℂ) R := by
    exact hr.trans (closedBall_subset_closedBall (le_max_left r 1))
  let χ : ContDiffBump (0 : ℂ) :=
    { rIn := R
      rOut := R + 1
      rIn_pos := hR
      rIn_lt_rOut := lt_add_one R }
  let g : ℂ → ℝ := fun x ↦ χ x * h x
  have hg_smooth : ContDiff ℝ ∞ g := by
    exact χ.contDiff.mul hh_smooth
  have hg_compact : HasCompactSupport g := by
    exact χ.hasCompactSupport.mul_right
  refine ⟨g, hg_smooth, hg_compact, ?_⟩
  intro x
  by_cases hx : x ∈ tsupport f
  · have hχx : χ x = 1 := χ.one_of_mem_closedBall (hsuppR hx)
    simpa only [g, hχx, one_mul] using hh_close_f x
  · have hfx : f x = 0 := by
      have hx' : x ∉ support f := fun h ↦ hx (subset_tsupport f h)
      simpa only [mem_support, not_not] using hx'
    have hhx : |h x| < ε := by
      simpa only [hfx, Real.dist_eq, sub_zero] using hh_close_f x
    have hχabs : |χ x| ≤ 1 := by
      rw [abs_of_nonneg χ.nonneg]
      exact χ.le_one
    change dist (χ x * h x) (f x) < ε
    rw [hfx, Real.dist_eq, sub_zero, abs_mul]
    calc
      |χ x| * |h x| ≤ 1 * |h x| :=
        mul_le_mul_of_nonneg_right hχabs (abs_nonneg _)
      _ < 1 * ε := by simpa only [one_mul] using hhx
      _ = ε := one_mul ε

/-- A finite empirical spectral probability measure is `1`-Lipschitz with
respect to the uniform norm of a real test function. -/
theorem abs_realEsdTest_sub_le_of_forall
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) (f g : ℂ → ℝ) {ε : ℝ} (_hε : 0 ≤ ε)
    (hfg : ∀ z, |f z - g z| ≤ ε) :
    |realEsdTest A f - realEsdTest A g| ≤ ε := by
  let s := eigenvalueMultiset A
  have hsum :
      |((s.map f).sum - (s.map g).sum)| ≤ (s.card : ℝ) * ε := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
          Nat.cast_add, Nat.cast_one]
        calc
          |f a + (s.map f).sum - (g a + (s.map g).sum)| =
              |(f a - g a) + ((s.map f).sum - (s.map g).sum)| := by ring_nf
          _ ≤ |f a - g a| + |(s.map f).sum - (s.map g).sum| := abs_add_le _ _
          _ ≤ ε + (s.card : ℝ) * ε := add_le_add (hfg a) ih
          _ = ((s.card : ℝ) + 1) * ε := by ring
  have hcard_pos : 0 < (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [realEsdTest, realEsdTest]
  change
    |((eigenvalueMultiset A).map f).sum / (Fintype.card n : ℝ) -
      ((eigenvalueMultiset A).map g).sum / (Fintype.card n : ℝ)| ≤ ε
  rw [← sub_div, abs_div, abs_of_pos hcard_pos]
  calc
    |((eigenvalueMultiset A).map f).sum -
        ((eigenvalueMultiset A).map g).sum| / (Fintype.card n : ℝ) ≤
        ((eigenvalueMultiset A).card : ℝ) * ε /
          (Fintype.card n : ℝ) := div_le_div_of_nonneg_right hsum hcard_pos.le
    _ = ε := by
      rw [card_eigenvalueMultiset]
      field_simp

/-- The difference of two empirical spectral measures is `2`-Lipschitz in
the uniform norm.  This is the approximation estimate in Tao--Vu §3.6. -/
theorem abs_esdDifference_sub_le_of_forall
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A B : Matrix n n ℂ) (f g : ℂ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hfg : ∀ z, |f z - g z| ≤ ε) :
    |(realEsdTest A f - realEsdTest B f) -
      (realEsdTest A g - realEsdTest B g)| ≤ 2 * ε := by
  calc
    |(realEsdTest A f - realEsdTest B f) -
        (realEsdTest A g - realEsdTest B g)| =
        |(realEsdTest A f - realEsdTest A g) -
          (realEsdTest B f - realEsdTest B g)| := by ring_nf
    _ ≤ |realEsdTest A f - realEsdTest A g| +
        |realEsdTest B f - realEsdTest B g| := abs_sub _ _
    _ ≤ ε + ε := add_le_add
      (abs_realEsdTest_sub_le_of_forall A f g hε hfg)
      (abs_realEsdTest_sub_le_of_forall B f g hε hfg)
    _ = 2 * ε := by ring

end TaoVuReplacement

