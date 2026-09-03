/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/PoissonCounting.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.BigOperators
-- Local import-only adaptation: avoid unrelated tactic modules.
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Poisson-kernel proof omitted after v3 Corollary 3.5

This file contains no probability or random-matrix hypothesis.  It proves the complete
finite-spectrum counting argument behind Corollary 3.5, including the exact imaginary-part
identity for the empirical Stieltjes transform.
-/

namespace Arxiv2410V3

open Complex
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Poisson kernel used in the standard proof cited after v3 Corollary 3.5. -/
noncomputable def poissonKernel (v x : ℝ) : ℝ := v / (x ^ 2 + v ^ 2)

/-- A spectral parameter `E + i v`. -/
def spectralParameter (E v : ℝ) : ℂ := (E : ℂ) + (v : ℂ) * Complex.I

/-- The normalized Stieltjes transform of a finite real spectrum, with the paper's convention
`(lambda - eta)⁻¹`. -/
noncomputable def empiricalStieltjes (eigenvalue : ι → ℝ) (eta : ℂ) : ℂ :=
  (∑ i, (((eigenvalue i : ℂ) - eta)⁻¹)) / (Fintype.card ι : ℂ)

/-- Indices whose eigenvalues lie in the closed interval `[a,b]`, counted with multiplicity. -/
noncomputable def eigenvaluesInInterval
    (eigenvalue : ι → ℝ) (a b : ℝ) : Finset ι :=
  Finset.univ.filter fun i => a ≤ eigenvalue i ∧ eigenvalue i ≤ b

/-- The pointwise Poisson-kernel inequality used in v3 Corollary 3.5. -/
theorem one_le_two_v_poissonKernel {x v : ℝ} (hv : 0 < v) (hx : |x| ≤ v) :
    1 ≤ 2 * v * poissonKernel v x := by
  have hden : 0 < x ^ 2 + v ^ 2 := by positivity
  rw [poissonKernel]
  rw [show 2 * v * (v / (x ^ 2 + v ^ 2)) =
      (2 * v ^ 2) / (x ^ 2 + v ^ 2) by ring]
  apply (le_div_iff₀ hden).2
  rcases abs_le.mp hx with ⟨hxlow, hxhigh⟩
  nlinarith

omit [DecidableEq ι] in
/-- Exact spectral representation of the imaginary part:
`Im m(E+iv) = (1/N) ∑ P_v(lambda_i-E)`.
-/
theorem empiricalStieltjes_im (eigenvalue : ι → ℝ) (E v : ℝ) :
    (empiricalStieltjes eigenvalue (spectralParameter E v)).im =
      (∑ i, poissonKernel v (eigenvalue i - E)) / (Fintype.card ι : ℝ) := by
  rw [empiricalStieltjes, Complex.div_natCast_im, Complex.im_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.inv_im, Complex.normSq_apply]
  simp [spectralParameter, poissonKernel]
  ring

omit [DecidableEq ι] in
/-- Deterministic interval count from the Poisson sum.  The point `E` may be any point for
which the interval is covered by `[E-v,E+v]`. -/
theorem interval_count_le_two_v_poissonSum
    (eigenvalue : ι → ℝ) {a b E v : ℝ}
    (hv : 0 < v)
    (hcover : ∀ i, a ≤ eigenvalue i → eigenvalue i ≤ b →
      |eigenvalue i - E| ≤ v) :
    ((eigenvaluesInInterval eigenvalue a b).card : ℝ) ≤
      2 * v * ∑ i, poissonKernel v (eigenvalue i - E) := by
  rw [eigenvaluesInInterval, Finset.natCast_card_filter]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : a ≤ eigenvalue i ∧ eigenvalue i ≤ b
  · simp only [hi]
    exact one_le_two_v_poissonKernel hv (hcover i hi.1 hi.2)
  · simp only [hi, if_false]
    have hk : 0 ≤ poissonKernel v (eigenvalue i - E) := by
      exact div_nonneg hv.le (add_nonneg (sq_nonneg _) (sq_nonneg _))
    positivity

omit [DecidableEq ι] in
/-- The central deterministic implication behind v3 Corollary 3.5:
a Stieltjes bound at a covering spectral parameter gives a local eigenvalue count.
-/
theorem interval_count_le_of_stieltjes_bound_at [Nonempty ι]
    (eigenvalue : ι → ℝ) {a b E v C : ℝ}
    (hv : 0 < v)
    (hcover : ∀ i, a ≤ eigenvalue i → eigenvalue i ≤ b →
      |eigenvalue i - E| ≤ v)
    (htrace : ‖empiricalStieltjes eigenvalue (spectralParameter E v)‖ ≤ C) :
    ((eigenvaluesInInterval eigenvalue a b).card : ℝ) ≤
      2 * (Fintype.card ι : ℝ) * C * v := by
  have hcount := interval_count_le_two_v_poissonSum eigenvalue hv hcover
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have him := empiricalStieltjes_im eigenvalue E v
  have hsum :
      (∑ i, poissonKernel v (eigenvalue i - E)) =
        (Fintype.card ι : ℝ) *
          (empiricalStieltjes eigenvalue (spectralParameter E v)).im := by
    have := (div_eq_iff hcard).mp him.symm
    nlinarith
  rw [hsum] at hcount
  have him_le :
      (empiricalStieltjes eigenvalue (spectralParameter E v)).im ≤ C :=
    (Complex.im_le_norm _).trans htrace
  have hfactor : 0 ≤ 2 * v * (Fintype.card ι : ℝ) := by positivity
  calc
    ((eigenvaluesInInterval eigenvalue a b).card : ℝ)
        ≤ 2 * v * ((Fintype.card ι : ℝ) *
          (empiricalStieltjes eigenvalue (spectralParameter E v)).im) := hcount
    _ ≤ 2 * v * ((Fintype.card ι : ℝ) * C) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left him_le (by positivity)) (by positivity)
    _ = 2 * (Fintype.card ι : ℝ) * C * v := by ring

omit [DecidableEq ι] in
/-- Midpoint specialization: every `lambda ∈ [a,b]` lies within distance `b-a` of
`E=(a+b)/2`. -/
theorem interval_count_le_of_midpoint_stieltjes_bound [Nonempty ι]
    (eigenvalue : ι → ℝ) {a b C : ℝ}
    (hab : a < b)
    (htrace : ‖empiricalStieltjes eigenvalue
      (spectralParameter ((a + b) / 2) (b - a))‖ ≤ C) :
    ((eigenvaluesInInterval eigenvalue a b).card : ℝ) ≤
      2 * (Fintype.card ι : ℝ) * C * (b - a) := by
  apply interval_count_le_of_stieltjes_bound_at eigenvalue (sub_pos.mpr hab) _ htrace
  intro i hai hib
  rw [abs_le]
  constructor <;> linarith

/-- If `[a,b] ⊆ [-5,5]` and its length is at most four, the midpoint parameter used above
lies in the disk `|eta| ≤ 5` required by v3 formula (3.10). -/
theorem norm_midpoint_parameter_le_five
    {a b : ℝ} (ha : -5 ≤ a) (hb : b ≤ 5) (hab : a ≤ b)
    (hlen : b - a ≤ 4) :
    ‖spectralParameter ((a + b) / 2) (b - a)‖ ≤ 5 := by
  let E := (a + b) / 2
  let v := b - a
  have hv0 : 0 ≤ v := sub_nonneg.mpr hab
  have hv4 : v ≤ 4 := hlen
  have hElow : -5 + v / 2 ≤ E := by dsimp [E, v]; linarith
  have hEhigh : E ≤ 5 - v / 2 := by dsimp [E, v]; linarith
  have hbound0 : 0 ≤ 5 - v / 2 := by linarith
  have hEabs : |E| ≤ 5 - v / 2 := (abs_le).2 ⟨by linarith, hEhigh⟩
  have hEsq : E ^ 2 ≤ (5 - v / 2) ^ 2 := by nlinarith [sq_nonneg (|E| + (5 - v / 2))]
  have htotal : E ^ 2 + v ^ 2 ≤ 25 := by
    calc
      E ^ 2 + v ^ 2 ≤ (5 - v / 2) ^ 2 + v ^ 2 := by linarith
      _ ≤ 25 := by nlinarith
  have hnormsq : ‖spectralParameter E v‖ ^ 2 = E ^ 2 + v ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [spectralParameter]
    ring
  have hnorm0 := norm_nonneg (spectralParameter E v)
  dsimp [E, v] at hnormsq ⊢
  nlinarith

end Arxiv2410V3
