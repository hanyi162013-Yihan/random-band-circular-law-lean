import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-!
# Inverse costs and terminal remainders

This file isolates the scalar argument behind `eq:pathwise-remainder` in Section 5.
For positive quantities `base` and `extended`, the two submultiplicative estimates

* `extended ≤ forward * base`, and
* `base ≤ inverse * extended`

give a two-sided logarithmic comparison.  In the matrix application these quantities
are `‖P‖`, `‖R P‖`, `‖R‖`, and `‖R⁻¹‖`, respectively.

The specialized exterior-power identity used by the manuscript to rewrite the inverse
cost is deliberately an ordinary theorem argument below.  Section 4 proves invertibility
of the relevant companion compounds, but does not currently export the singular-value
identity identifying the inverse norm with a complementary exterior norm divided by the
determinant.  No unproved declaration is introduced here.
-/

open scoped BigOperators

namespace CircularLawSections56.Section5

/-- The positive logarithm `log⁺ x = max 0 (log x)`, kept local so this module only
needs the already-cached basic logarithm API. -/
noncomputable def positiveLog (x : ℝ) : ℝ := max 0 (Real.log x)

@[simp]
theorem positiveLog_nonneg (x : ℝ) : 0 ≤ positiveLog x := by
  exact le_max_left _ _

/-- The forward multiplicative comparison gives the upper logarithmic increment bound. -/
theorem log_sub_log_le_posLog_of_le_mul
    {base extended forward : ℝ}
    (hbase : 0 < base) (hextended : 0 < extended) (hforward : 0 < forward)
    (hle : extended ≤ forward * base) :
    Real.log extended - Real.log base ≤ positiveLog forward := by
  have hratio : extended / base ≤ forward := by
    exact (div_le_iff₀ hbase).2 hle
  have hlog : Real.log (extended / base) ≤ Real.log forward :=
    (Real.log_le_log_iff (div_pos hextended hbase) hforward).2 hratio
  calc
    Real.log extended - Real.log base = Real.log (extended / base) := by
      rw [Real.log_div hextended.ne' hbase.ne']
    _ ≤ Real.log forward := hlog
    _ ≤ positiveLog forward := by
      unfold positiveLog
      exact le_max_right _ _

/-- Scalar form of the manuscript's pathwise remainder estimate
`|log ‖R P‖ - log ‖P‖| ≤ log⁺ ‖R‖ + log⁺ ‖R⁻¹‖`.

Only the two norm-submultiplicativity consequences are needed, so this theorem can be
used without committing the Sections 5--6 project to a particular matrix norm API. -/
theorem pathwise_remainder_log_inequality
    {base extended forward inverse : ℝ}
    (hbase : 0 < base) (hextended : 0 < extended)
    (hforward : 0 < forward) (hinverse : 0 < inverse)
    (happend : extended ≤ forward * base)
    (hremove : base ≤ inverse * extended) :
    |Real.log extended - Real.log base| ≤
      positiveLog forward + positiveLog inverse := by
  have hupp :
      Real.log extended - Real.log base ≤ positiveLog forward :=
    log_sub_log_le_posLog_of_le_mul hbase hextended hforward happend
  have hrev :
      Real.log base - Real.log extended ≤ positiveLog inverse :=
    log_sub_log_le_posLog_of_le_mul hextended hbase hinverse hremove
  have hforwardNonneg : 0 ≤ positiveLog forward := positiveLog_nonneg forward
  have hinverseNonneg : 0 ≤ positiveLog inverse := positiveLog_nonneg inverse
  rw [abs_le]
  constructor <;> linarith

/-- Interface for the exterior inverse formula used in `lem:inverse-row`.

The hypothesis `hinverseIdentity` is where a future matrix-level theorem may be plugged
in.  For the manuscript it has the shape
`‖(ᶜ⁽ʳ⁾)⁻¹‖ = ‖ᶜ⁽ᵈ⁻ʳ⁾‖ / |α β|`.
This wrapper proves the full pathwise conclusion from that fact; it is a theorem with an
explicit premise, not an axiom. -/
theorem pathwise_remainder_log_of_inverse_identity
    {base extended forward inverse complementary determinantScale : ℝ}
    (hbase : 0 < base) (hextended : 0 < extended)
    (hforward : 0 < forward) (hinverse : 0 < inverse)
    (happend : extended ≤ forward * base)
    (hremove : base ≤ inverse * extended)
    (hinverseIdentity : inverse = complementary / determinantScale) :
    |Real.log extended - Real.log base| ≤
      positiveLog forward +
        positiveLog (complementary / determinantScale) := by
  simpa only [← hinverseIdentity] using
    pathwise_remainder_log_inequality hbase hextended hforward hinverse
      happend hremove

/-- Absolute increments telescope with the sum of their individual costs. -/
theorem abs_telescope_le_sum_cost
    (value cost : ℕ → ℝ) (steps : ℕ)
    (hstep : ∀ j < steps, |value (j + 1) - value j| ≤ cost j) :
    |value steps - value 0| ≤ ∑ j ∈ Finset.range steps, cost j := by
  rw [← Finset.sum_range_sub value]
  calc
    |∑ j ∈ Finset.range steps, (value (j + 1) - value j)| ≤
        ∑ j ∈ Finset.range steps, |value (j + 1) - value j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range steps, cost j := by
      apply Finset.sum_le_sum
      intro j hj
      exact hstep j (Finset.mem_range.mp hj)

/-- Repeated multiplication/removal costs telescope along a finite row segment.

In the matrix application `value j` is the norm of the product after appending `j` rows.
The conclusion is the pathwise `s`-row remainder estimate before taking expectations. -/
theorem pathwise_remainder_log_telescope
    (value forward inverse : ℕ → ℝ) (steps : ℕ)
    (hvalue : ∀ j ≤ steps, 0 < value j)
    (hforward : ∀ j < steps, 0 < forward j)
    (hinverse : ∀ j < steps, 0 < inverse j)
    (happend : ∀ j < steps,
      value (j + 1) ≤ forward j * value j)
    (hremove : ∀ j < steps,
      value j ≤ inverse j * value (j + 1)) :
    |Real.log (value steps) - Real.log (value 0)| ≤
      ∑ j ∈ Finset.range steps,
        (positiveLog (forward j) + positiveLog (inverse j)) := by
  apply abs_telescope_le_sum_cost
    (fun j => Real.log (value j))
    (fun j => positiveLog (forward j) + positiveLog (inverse j))
    steps
  intro j hj
  exact pathwise_remainder_log_inequality
    (hvalue j (Nat.le_of_lt hj))
    (hvalue (j + 1) (Nat.succ_le_iff.2 hj))
    (hforward j hj) (hinverse j hj)
    (happend j hj) (hremove j hj)

/-- If every appended row has cost at most `rowCost`, the total terminal remainder is at
most `steps * rowCost`.  This is the scalar expectation-level telescope used after the
one-row forward/inverse estimate has been integrated. -/
theorem uniform_step_cost_telescope
    (value : ℕ → ℝ) (steps : ℕ) (rowCost : ℝ)
    (hstep : ∀ j < steps, |value (j + 1) - value j| ≤ rowCost) :
    |value steps - value 0| ≤ (steps : ℝ) * rowCost := by
  have h := abs_telescope_le_sum_cost value (fun _ => rowCost) steps hstep
  simpa using h

/-- A direct high-level form for mean pressures: once a pathwise/integrated one-row cost
has supplied `|F(j+1)-F(j)| ≤ rowCost`, appending or deleting `steps` rows changes the
pressure by at most `steps * rowCost`. -/
theorem mean_pressure_remainder_of_one_row_cost
    (pressure : ℕ → ℝ) (steps : ℕ) (rowCost : ℝ)
    (hone : ∀ j < steps,
      |pressure (j + 1) - pressure j| ≤ rowCost) :
    |pressure steps - pressure 0| ≤ (steps : ℝ) * rowCost :=
  uniform_step_cost_telescope pressure steps rowCost hone

end CircularLawSections56.Section5
