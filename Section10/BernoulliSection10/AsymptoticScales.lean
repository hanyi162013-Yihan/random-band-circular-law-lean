import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Literal cell scales for Section 10.4--10.6

The ceiling and integer division below are those of (10.30) and (10.51).
In particular, the scale estimates are proved for the actual cell sizes,
not supplied as asymptotic assumptions. All limits allow arbitrary
bandwidth sequences tending to infinity.
-/

open Filter
open scoped Topology

noncomputable section

namespace BernoulliSection10

/-- The number `s_W` of sites in one core, equation (10.30). -/
def densityCoreSites (W : ℕ) : ℕ := ⌈(W : ℝ) ^ (1 / 200 : ℝ)⌉₊

/-- One complete cell consists of a core and a three-site reset. -/
def densityCellSites (W : ℕ) : ℕ := densityCoreSites W + 3

/-- The scalar dimension `ℓ_W` of the short anchor ring. -/
def densityAnchorSize (W : ℕ) : ℕ := densityCellSites W * W

/-- Complete cells after reserving the three-site terminal seam. -/
def densityCellCount (m W : ℕ) : ℕ := (m - 3) / densityCellSites W

/-- The remaining sites after the complete cells, equation (10.51). -/
def densityRemainderSites (m W : ℕ) : ℕ := (m - 3) % densityCellSites W

/-- The factor `log(eW)` occurring in the local and global error bounds. -/
def densityLogScale (W : ℕ) : ℝ := Real.log (Real.exp 1 * (W : ℝ))

theorem densityCellSites_pos (W : ℕ) : 0 < densityCellSites W := by
  simp [densityCellSites]

theorem densityCoreSites_pos {W : ℕ} (hW : 0 < W) : 0 < densityCoreSites W := by
  apply Nat.one_le_ceil_iff.mpr
  exact Real.rpow_pos_of_pos (by exact_mod_cast hW) _

theorem densityAnchorSize_pos {W : ℕ} (hW : 0 < W) : 0 < densityAnchorSize W :=
  Nat.mul_pos (densityCellSites_pos W) hW

theorem rpow_le_densityCellSites (W : ℕ) :
    (W : ℝ) ^ (1 / 200 : ℝ) ≤ densityCellSites W := by
  have h := Nat.le_ceil ((W : ℝ) ^ (1 / 200 : ℝ))
  simp only [densityCellSites, densityCoreSites, Nat.cast_add, Nat.cast_ofNat]
  linarith

theorem densityCellSites_le_five_mul_rpow {W : ℕ} (hW : 0 < W) :
    (densityCellSites W : ℝ) ≤ 5 * (W : ℝ) ^ (1 / 200 : ℝ) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hr := Real.one_le_rpow hW1 (by norm_num : (0 : ℝ) ≤ 1 / 200)
  have hc := Nat.ceil_lt_add_one
    (Real.rpow_nonneg (Nat.cast_nonneg W) (1 / 200 : ℝ))
  simp only [densityCellSites, densityCoreSites, Nat.cast_add, Nat.cast_ofNat]
  linarith

theorem rpow_anchor_exponent {W : ℕ} (hW : 0 < W) :
    (W : ℝ) ^ (201 / 200 : ℝ) = (W : ℝ) ^ (1 / 200 : ℝ) * W := by
  rw [show (201 / 200 : ℝ) = 1 / 200 + 1 by norm_num,
    Real.rpow_add_one (by exact_mod_cast Nat.ne_of_gt hW)]

theorem rpow_le_densityAnchorSize {W : ℕ} (hW : 0 < W) :
    (W : ℝ) ^ (201 / 200 : ℝ) ≤ densityAnchorSize W := by
  rw [rpow_anchor_exponent hW, densityAnchorSize, Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right (rpow_le_densityCellSites W) (by positivity)

theorem densityAnchorSize_le_five_mul_rpow {W : ℕ} (hW : 0 < W) :
    (densityAnchorSize W : ℝ) ≤ 5 * (W : ℝ) ^ (201 / 200 : ℝ) := by
  rw [densityAnchorSize, Nat.cast_mul, rpow_anchor_exponent hW, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (densityCellSites_le_five_mul_rpow hW)
    (by positivity)

theorem densityRemainderSites_lt (m W : ℕ) :
    densityRemainderSites m W < densityCellSites W :=
  Nat.mod_lt _ (densityCellSites_pos W)

/-- The subtraction definition of the remainder in the paper agrees with
the modulus definition, including before any size assumption is imposed. -/
theorem densityRemainderSites_eq_sub (m W : ℕ) :
    densityRemainderSites m W = m - 3 - densityCellCount m W * densityCellSites W := by
  exact Nat.mod_eq_sub_div_mul

/-- Exact, rather than asymptotic, accounting for the terminal seam. -/
theorem densityCell_partition {m : ℕ} (hm : 3 ≤ m) (W : ℕ) :
    densityCellCount m W * densityCellSites W + densityRemainderSites m W + 3 = m := by
  have h := Nat.div_add_mod' (m - 3) (densityCellSites W)
  simp only [densityCellCount, densityRemainderSites]
  omega

/-- The two exact equalities preceding the limit in (10.52). -/
theorem densityCell_dimension_ratio {m W : ℕ} (hm : 3 ≤ m) (hW : 0 < W) :
    (densityCellCount m W : ℝ) * densityAnchorSize W / ((m : ℝ) * W) =
      1 - (3 + (densityRemainderSites m W : ℝ)) / m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hW0 : (W : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hW
  have hp : (densityCellCount m W : ℝ) * densityCellSites W +
      densityRemainderSites m W + 3 = m := by
    exact_mod_cast densityCell_partition hm W
  rw [densityAnchorSize, Nat.cast_mul]
  field_simp
  nlinarith

theorem densityLogScale_eq {W : ℕ} (hW : 0 < W) :
    densityLogScale W = 1 + Real.log W := by
  rw [densityLogScale, Real.log_mul (Real.exp_ne_zero _)
    (by exact_mod_cast Nat.ne_of_gt hW), Real.log_exp]

theorem densityLogScale_nonneg {W : ℕ} (hW : 0 < W) : 0 ≤ densityLogScale W := by
  rw [densityLogScale_eq hW]
  have h : (1 : ℝ) ≤ W := by exact_mod_cast hW
  linarith [Real.log_nonneg h]

/-- Every positive power beats the literal logarithm used in the paper. -/
theorem tendsto_densityLogScale_div_rpow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun W : ℕ => densityLogScale W / (W : ℝ) ^ a) atTop (𝓝 0) := by
  have hpow : Tendsto (fun W : ℕ => (W : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun W : ℕ => 1 / (W : ℝ) ^ a) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hpow
  have hlog : Tendsto (fun W : ℕ => Real.log W / (W : ℝ) ^ a) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  apply (show Tendsto (fun W : ℕ => 1 / (W : ℝ) ^ a +
      Real.log W / (W : ℝ) ^ a) atTop (𝓝 0) by simpa using hone.add hlog).congr'
  filter_upwards [eventually_ge_atTop 1] with W hW
  rw [densityLogScale_eq (by omega), add_div]

/-- The direct branch satisfies the actual high-band inequality with the
paper's fixed choice `ω_* = 1/20`, without an asymptotic certificate. -/
theorem density_direct_highBand {N W : ℕ} (hW : 0 < W)
    (hshort : (N : ℝ) ≤ (W : ℝ) ^ (101 / 100 : ℝ)) :
    (N : ℝ) ^ (8 / 9 + 1 / 20 : ℝ) ≤ W := by
  calc
    (N : ℝ) ^ (8 / 9 + 1 / 20 : ℝ) ≤
        ((W : ℝ) ^ (101 / 100 : ℝ)) ^ (8 / 9 + 1 / 20 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hshort (by norm_num)
    _ = (W : ℝ) ^ ((101 / 100 : ℝ) * (8 / 9 + 1 / 20)) :=
      (Real.rpow_mul (by positivity) _ _).symm
    _ ≤ (W : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hW) (by norm_num)
    _ = W := Real.rpow_one _

/-- The ceiling-defined short ring eventually satisfies Proposition 10.1's
bandwidth inequality with `ω_* = 1/20`, as required by (10.32). -/
theorem eventually_density_anchor_highBand :
    ∀ᶠ W : ℕ in atTop,
      (densityAnchorSize W : ℝ) ^ (8 / 9 + 1 / 20 : ℝ) ≤ W := by
  have hδ : (0 : ℝ) < 1 - (201 / 200) * (8 / 9 + 1 / 20) := by norm_num
  have ht : Tendsto (fun W : ℕ =>
      (W : ℝ) ^ (1 - (201 / 200) * (8 / 9 + 1 / 20) : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    ht.eventually (eventually_ge_atTop ((5 : ℝ) ^ (8 / 9 + 1 / 20 : ℝ)))] with W hW h5
  calc
    (densityAnchorSize W : ℝ) ^ (8 / 9 + 1 / 20 : ℝ) ≤
        (5 * (W : ℝ) ^ (201 / 200 : ℝ)) ^ (8 / 9 + 1 / 20 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (densityAnchorSize_le_five_mul_rpow hW)
        (by norm_num)
    _ = (5 : ℝ) ^ (8 / 9 + 1 / 20 : ℝ) *
        (W : ℝ) ^ ((201 / 200) * (8 / 9 + 1 / 20) : ℝ) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by positivity)]
    _ ≤ (W : ℝ) ^ (1 - (201 / 200) * (8 / 9 + 1 / 20) : ℝ) *
        (W : ℝ) ^ ((201 / 200) * (8 / 9 + 1 / 20) : ℝ) :=
      mul_le_mul_of_nonneg_right h5 (by positivity)
    _ = W := by
      rw [← Real.rpow_add (by exact_mod_cast hW)]
      norm_num

end BernoulliSection10
