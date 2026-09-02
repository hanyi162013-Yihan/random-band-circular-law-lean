import Mathlib.Data.Real.Basic

/-!
# Balanced mesoscopic cell division

This file formalizes the exact Euclidean-division bookkeeping in
`eq:balanced-cell-division`.  The hypotheses are deliberately finite and quantitative;
the asymptotic facts used in the paper are needed only to establish them eventually.
-/

namespace CircularLawSections56.Section5

/-- Number of complete mesoscopic cells cut from `n` rows. -/
def balancedCellCount (n m₀ : ℕ) : ℕ := n / m₀

/-- Common cell length after balancing the `q` cells. -/
def balancedCellLength (n m₀ : ℕ) : ℕ := n / balancedCellCount n m₀

/-- Terminal remainder after the balanced cells. -/
def balancedCellRemainder (n m₀ : ℕ) : ℕ :=
  n - balancedCellCount n m₀ * balancedCellLength n m₀

/-- Exact finite form of the balanced-division assertions used in Section 5.

If at least two base cells fit, then `q > 0`, the balanced cell length lies in
`[m₀,2m₀)`, and the terminal remainder contains fewer than `q` rows. -/
theorem balanced_cell_division_spec (n m₀ : ℕ)
    (hm₀ : 0 < m₀) (hn : 2 * m₀ ≤ n) :
    0 < balancedCellCount n m₀ ∧
      m₀ ≤ balancedCellLength n m₀ ∧
      balancedCellLength n m₀ < 2 * m₀ ∧
      balancedCellRemainder n m₀ < balancedCellCount n m₀ := by
  unfold balancedCellCount balancedCellLength balancedCellRemainder
  have hq : 0 < n / m₀ := Nat.div_pos (by omega) hm₀
  have hqTwo : 2 ≤ n / m₀ :=
    (Nat.le_div_iff_mul_le hm₀).2 hn
  have hlower : m₀ ≤ n / (n / m₀) :=
    (Nat.le_div_iff_mul_le hq).2 (Nat.mul_div_le n m₀)
  have hnext : n < m₀ * (n / m₀ + 1) :=
    Nat.lt_mul_div_succ n hm₀
  have hsucc : n / m₀ + 1 ≤ 2 * (n / m₀) := by omega
  have hscaled : m₀ * (n / m₀ + 1) ≤ (2 * m₀) * (n / m₀) := by
    calc
      m₀ * (n / m₀ + 1) ≤ m₀ * (2 * (n / m₀)) :=
        Nat.mul_le_mul_left m₀ hsucc
      _ = (2 * m₀) * (n / m₀) := by ac_rfl
  have hupper : n / (n / m₀) < 2 * m₀ :=
    (Nat.div_lt_iff_lt_mul hq).2 (hnext.trans_le hscaled)
  have hrem : n - n / m₀ * (n / (n / m₀)) < n / m₀ := by
    rw [← Nat.mod_eq_sub_mul_div]
    exact Nat.mod_lt n hq
  constructor
  · exact hq
  constructor
  · exact hlower
  exact ⟨hupper, hrem⟩

/-- The remainder identity in the form used to compare lengths: the balanced cells and
the terminal segment partition all `n` rows exactly. -/
theorem balanced_cells_add_remainder (n m₀ : ℕ) :
    balancedCellCount n m₀ * balancedCellLength n m₀ +
        balancedCellRemainder n m₀ = n := by
  unfold balancedCellRemainder
  exact Nat.add_sub_of_le (Nat.mul_div_le n (balancedCellCount n m₀))

/-- A pointwise row-cost bound immediately controls the balanced terminal segment. -/
theorem balanced_remainder_cost_le
    (n m₀ : ℕ) (costPerRow : ℝ) (hcost : 0 ≤ costPerRow)
    (hm₀ : 0 < m₀) (hn : 2 * m₀ ≤ n) :
    (balancedCellRemainder n m₀ : ℝ) * costPerRow ≤
      (balancedCellCount n m₀ : ℝ) * costPerRow := by
  have hNat : balancedCellRemainder n m₀ ≤ balancedCellCount n m₀ :=
    (balanced_cell_division_spec n m₀ hm₀ hn).2.2.2.le
  have hReal : (balancedCellRemainder n m₀ : ℝ) ≤ balancedCellCount n m₀ :=
    Nat.cast_le.mpr hNat
  exact mul_le_mul_of_nonneg_right hReal hcost

end CircularLawSections56.Section5
