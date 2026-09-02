import CircularLawSections56.Section5.TaperedWeights
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The actual polynomial taper sampled on the band grid

The finite-variation assumption is retained from the manuscript.  The discrete
bounds below only need its pointwise hypotheses, and are valid even at `W = 0`.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace CircularLawSections56.Section5

structure PolynomialTaperProfile where
  f : ℝ → ℝ
  lower : ℝ
  upper : ℝ
  exponent : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  exponent_nonneg : 0 ≤ exponent
  nonneg : ∀ x, 0 ≤ f x
  boundedVariation : BoundedVariationOn f Set.univ
  vanishes : ∀ x, 1 ≤ |x| → f x = 0
  interior : ∀ x, |x| < 1 → lower * (1 - |x|) ^ exponent ≤ f x ∧ f x ≤ upper

def taperGrid (W : ℕ) (i : Fin (2 * W + 1)) : ℝ :=
  ((i : ℝ) - (W : ℝ)) / (W + 1 : ℝ)

def taperInnerIndex (W : ℕ) (j : Fin (W + 1)) : Fin (2 * W + 1) :=
  ⟨W / 2 + j.val, by have := j.isLt; omega⟩

theorem taperInnerIndex_injective (W : ℕ) : Function.Injective (taperInnerIndex W) := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  dsimp only [taperInnerIndex] at hval
  omega

theorem taperGrid_abs_le (W : ℕ) (i : Fin (2 * W + 1)) :
    |taperGrid W i| ≤ (W : ℝ) / (W + 1 : ℝ) := by
  have hi : (i : ℝ) ≤ 2 * (W : ℝ) := by exact_mod_cast (show i.val ≤ 2 * W by omega)
  have hi0 : 0 ≤ (i : ℝ) := by positivity
  rw [taperGrid, abs_div, abs_of_pos (by positivity : 0 < (W + 1 : ℝ))]
  exact div_le_div_of_nonneg_right (abs_le.2 ⟨by linarith, by linarith⟩) (by positivity)

theorem taperGrid_abs_lt_one (W : ℕ) (i : Fin (2 * W + 1)) : |taperGrid W i| < 1 :=
  (taperGrid_abs_le W i).trans_lt ((div_lt_one (by positivity)).2 (by linarith))

theorem taperGrid_endpoint_gap (W : ℕ) (i : Fin (2 * W + 1)) :
    1 / (W + 1 : ℝ) ≤ 1 - |taperGrid W i| := by
  have h := taperGrid_abs_le W i
  have heq : 1 - (W : ℝ) / (W + 1 : ℝ) = 1 / (W + 1 : ℝ) := by
    field_simp
    ring
  linarith

theorem taperGrid_inner_abs_le_half (W : ℕ) (j : Fin (W + 1)) :
    |taperGrid W (taperInnerIndex W j)| ≤ 1 / 2 := by
  have hlow : W ≤ 2 * (W / 2) + 1 := by omega
  have hupp : 2 * (W / 2) ≤ W := by omega
  have hj : j.val ≤ W := by omega
  have hlow' : (W : ℝ) ≤ 2 * (W / 2 : ℕ) + 1 := by exact_mod_cast hlow
  have hupp' : 2 * (W / 2 : ℕ) ≤ (W : ℝ) := by exact_mod_cast hupp
  have hj' : (j : ℝ) ≤ W := by exact_mod_cast hj
  have hj0 : 0 ≤ (j : ℝ) := by positivity
  rw [taperGrid, abs_div, abs_of_pos (by positivity : 0 < (W + 1 : ℝ))]
  apply (div_le_iff₀ (by positivity)).2
  change |((W / 2 + j.val : ℕ) : ℝ) - (W : ℝ)| ≤ 1 / 2 * (W + 1 : ℝ)
  rw [Nat.cast_add]
  exact abs_le.2 ⟨by linarith, by linarith⟩

namespace PolynomialTaperProfile

def raw (p : PolynomialTaperProfile) (W : ℕ) (i : Fin (2 * W + 1)) : ℝ :=
  p.f (taperGrid W i)

def mass (p : PolynomialTaperProfile) (W : ℕ) : ℝ := ∑ i, p.raw W i

def weight (p : PolynomialTaperProfile) (W : ℕ) (i : Fin (2 * W + 1)) : ℝ :=
  p.raw W i / p.mass W

theorem raw_bounds (p : PolynomialTaperProfile) (W : ℕ) (i : Fin (2 * W + 1)) :
    p.lower * (1 / (W + 1 : ℝ)) ^ p.exponent ≤ p.raw W i ∧ p.raw W i ≤ p.upper := by
  have h := p.interior (taperGrid W i) (taperGrid_abs_lt_one W i)
  exact ⟨(mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
    (taperGrid_endpoint_gap W i) p.exponent_nonneg) p.lower_pos.le).trans h.1, h.2⟩

theorem raw_inner_lower (p : PolynomialTaperProfile) (W : ℕ) (j : Fin (W + 1)) :
    p.lower * (1 / 2 : ℝ) ^ p.exponent ≤ p.raw W (taperInnerIndex W j) := by
  have h := p.interior _ (taperGrid_abs_lt_one W (taperInnerIndex W j))
  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by norm_num)
    (by linarith [taperGrid_inner_abs_le_half W j]) p.exponent_nonneg) p.lower_pos.le).trans h.1

theorem mass_bounds (p : PolynomialTaperProfile) (W : ℕ) :
    (W + 1 : ℝ) * (p.lower * (1 / 2 : ℝ) ^ p.exponent) ≤ p.mass W ∧
      p.mass W ≤ (2 * W + 1 : ℝ) * p.upper := by
  classical
  constructor
  · calc
      _ = ∑ _j : Fin (W + 1), p.lower * (1 / 2 : ℝ) ^ p.exponent := by simp
      _ ≤ ∑ j : Fin (W + 1), p.raw W (taperInnerIndex W j) :=
        Finset.sum_le_sum fun j _ => p.raw_inner_lower W j
      _ = ∑ i ∈ Finset.univ.image (taperInnerIndex W), p.raw W i :=
        (Finset.sum_image (fun i _ j _ h => taperInnerIndex_injective W h)).symm
      _ ≤ p.mass W := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => p.nonneg _)
  · calc
      _ ≤ ∑ _i : Fin (2 * W + 1), p.upper := Finset.sum_le_sum fun i _ => (p.raw_bounds W i).2
      _ = _ := by simp [Nat.cast_add, Nat.cast_mul]

theorem mass_pos (p : PolynomialTaperProfile) (W : ℕ) : 0 < p.mass W :=
  (mul_pos (by positivity) (mul_pos p.lower_pos (Real.rpow_pos_of_pos (by norm_num) _))).trans_le
    (p.mass_bounds W).1

theorem weight_pos (p : PolynomialTaperProfile) (W : ℕ) (i : Fin (2 * W + 1)) :
    0 < p.weight W i :=
  div_pos ((mul_pos p.lower_pos (Real.rpow_pos_of_pos (by positivity) _)).trans_le
    (p.raw_bounds W i).1) (p.mass_pos W)

theorem sum_weight (p : PolynomialTaperProfile) (W : ℕ) : ∑ i, p.weight W i = 1 := by
  simp only [weight, ← Finset.sum_div]
  change p.mass W / p.mass W = 1
  exact div_self (p.mass_pos W).ne'

theorem weight_bounds (p : PolynomialTaperProfile) (W : ℕ) (i : Fin (2 * W + 1)) :
    (p.lower * (1 / (W + 1 : ℝ)) ^ p.exponent) / ((2 * W + 1 : ℝ) * p.upper) ≤
        p.weight W i ∧
      p.weight W i ≤ p.upper / ((W + 1 : ℝ) * (p.lower * (1 / 2 : ℝ) ^ p.exponent)) := by
  have hl := p.lower_pos
  have h := taperedNormalizedWeight_bounds Finset.univ (p.raw W)
    _ _ _ _ (by positivity) p.upper_pos.le
    (by positivity) (p.mass_bounds W).1 (p.mass_bounds W).2
    (fun j _ => p.raw_bounds W j) i (Finset.mem_univ _)
  simpa only [taperedNormalizedWeight, taperedNormalizer, weight, mass] using h

end PolynomialTaperProfile

end CircularLawSections56.Section5
