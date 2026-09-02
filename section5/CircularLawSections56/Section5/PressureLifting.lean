import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend

/-!
# Finite-degree pressure lifting

This file isolates the quantitative algebra in the pressure-lifting step of Section 5.
All pressures are real numbers and may have either sign.  The probabilistic cell estimates
enter only through bounds on the successive expected log-norm increments.

The main conclusions are:

* finite maxima are stable under a uniform signed perturbation;
* lower and upper bounds for each exterior degree pass to the finite maximum;
* cell increments telescope without a loss depending on the number of cells; and
* after division by the total length, the degreewise cell bounds give exactly the
  `eq:pressure-lift-max` error `cellError / m`.
-/

open scoped BigOperators

namespace CircularLawSections56.Section5

section FiniteSignedMax

variable {ι : Type*}

/-- The maximum of a real-valued family over a nonempty finite set of degrees.

The adjective `Signed` records that no nonnegativity assumption is made on the values.
This matters for logarithmic pressures, which can be negative. -/
def finiteSignedMax (degrees : Finset ι) (hdegrees : degrees.Nonempty)
    (pressure : ι → ℝ) : ℝ :=
  degrees.sup' hdegrees pressure

/-- Every degree is bounded by the finite signed maximum. -/
theorem le_finiteSignedMax {degrees : Finset ι} (hdegrees : degrees.Nonempty)
    (pressure : ι → ℝ) {r : ι} (hr : r ∈ degrees) :
    pressure r ≤ finiteSignedMax degrees hdegrees pressure := by
  exact Finset.le_sup' pressure hr

/-- The finite signed maximum is bounded by every common upper bound. -/
theorem finiteSignedMax_le {degrees : Finset ι} (hdegrees : degrees.Nonempty)
    (pressure : ι → ℝ) {bound : ℝ}
    (hbound : ∀ r ∈ degrees, pressure r ≤ bound) :
    finiteSignedMax degrees hdegrees pressure ≤ bound := by
  exact Finset.sup'_le hdegrees pressure hbound

/-- A maximum over finitely many degrees is attained. -/
theorem exists_eq_finiteSignedMax {degrees : Finset ι} (hdegrees : degrees.Nonempty)
    (pressure : ι → ℝ) :
    ∃ r ∈ degrees, finiteSignedMax degrees hdegrees pressure = pressure r := by
  simpa [finiteSignedMax] using Finset.exists_mem_eq_sup' hdegrees pressure

/-- Pointwise comparison passes to finite signed maxima. -/
theorem finiteSignedMax_mono {degrees : Finset ι} (hdegrees : degrees.Nonempty)
    {pressure₁ pressure₂ : ι → ℝ}
    (hpressure : ∀ r ∈ degrees, pressure₁ r ≤ pressure₂ r) :
    finiteSignedMax degrees hdegrees pressure₁ ≤
      finiteSignedMax degrees hdegrees pressure₂ := by
  apply finiteSignedMax_le hdegrees pressure₁
  intro r hr
  exact (hpressure r hr).trans (le_finiteSignedMax hdegrees pressure₂ hr)

/-- Adding the same (possibly negative) constant commutes with a finite signed maximum. -/
theorem finiteSignedMax_add_const {degrees : Finset ι} (hdegrees : degrees.Nonempty)
    (pressure : ι → ℝ) (c : ℝ) :
    finiteSignedMax degrees hdegrees (fun r => pressure r + c) =
      finiteSignedMax degrees hdegrees pressure + c := by
  apply le_antisymm
  · apply finiteSignedMax_le hdegrees
    intro r hr
    linarith [le_finiteSignedMax hdegrees pressure hr]
  · obtain ⟨r, hr, hmax⟩ := exists_eq_finiteSignedMax hdegrees pressure
    rw [hmax]
    exact le_finiteSignedMax hdegrees (fun i => pressure i + c) hr

/-- Multiplication by a nonnegative scalar commutes with a finite signed maximum. -/
theorem finiteSignedMax_mul_nonneg {degrees : Finset ι} (hdegrees : degrees.Nonempty)
    (pressure : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    finiteSignedMax degrees hdegrees (fun r => c * pressure r) =
      c * finiteSignedMax degrees hdegrees pressure := by
  apply le_antisymm
  · apply finiteSignedMax_le hdegrees
    intro r hr
    exact mul_le_mul_of_nonneg_left (le_finiteSignedMax hdegrees pressure hr) hc
  · obtain ⟨r, hr, hmax⟩ := exists_eq_finiteSignedMax hdegrees pressure
    rw [hmax]
    exact le_finiteSignedMax hdegrees (fun i => c * pressure i) hr

/-- A uniform two-sided perturbation bound controls the difference of finite maxima.
The values and the error hypotheses are genuinely signed; nonnegativity of `error` need
not be supplied separately. -/
theorem abs_finiteSignedMax_sub_le {degrees : Finset ι}
    (hdegrees : degrees.Nonempty) (pressure₁ pressure₂ : ι → ℝ) (error : ℝ)
    (herror : ∀ r ∈ degrees, |pressure₁ r - pressure₂ r| ≤ error) :
    |finiteSignedMax degrees hdegrees pressure₁ -
        finiteSignedMax degrees hdegrees pressure₂| ≤ error := by
  have h₁₂ :
      finiteSignedMax degrees hdegrees pressure₁ ≤
        finiteSignedMax degrees hdegrees pressure₂ + error := by
    apply finiteSignedMax_le hdegrees pressure₁
    intro r hr
    have hdiff := (abs_le.mp (herror r hr)).2
    have hmax := le_finiteSignedMax hdegrees pressure₂ hr
    linarith
  have h₂₁ :
      finiteSignedMax degrees hdegrees pressure₂ ≤
        finiteSignedMax degrees hdegrees pressure₁ + error := by
    apply finiteSignedMax_le hdegrees pressure₂
    intro r hr
    have hdiff := (abs_le.mp (herror r hr)).1
    have hmax := le_finiteSignedMax hdegrees pressure₁ hr
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- The sharp finite-family form: the change of the maximum is bounded by the maximum
of the pointwise absolute changes. -/
theorem abs_finiteSignedMax_sub_le_finiteSignedMax_abs_sub
    {degrees : Finset ι} (hdegrees : degrees.Nonempty)
    (pressure₁ pressure₂ : ι → ℝ) :
    |finiteSignedMax degrees hdegrees pressure₁ -
        finiteSignedMax degrees hdegrees pressure₂| ≤
      finiteSignedMax degrees hdegrees (fun r => |pressure₁ r - pressure₂ r|) := by
  apply abs_finiteSignedMax_sub_le hdegrees pressure₁ pressure₂
  intro r hr
  exact le_finiteSignedMax hdegrees (fun i => |pressure₁ i - pressure₂ i|) hr

/-- Degreewise cell bounds pass to the finite maximum.  This is the algebraic step
immediately before `eq:pressure-lift-max`. -/
theorem finiteSignedMax_cell_bounds {degrees : Finset ι}
    (hdegrees : degrees.Nonempty) (base lifted : ι → ℝ)
    (q cellError : ℝ) (hq : 0 ≤ q)
    (hdegree : ∀ r ∈ degrees,
      q * (base r - cellError) ≤ lifted r ∧
        lifted r ≤ q * (base r + cellError)) :
    q * (finiteSignedMax degrees hdegrees base - cellError) ≤
        finiteSignedMax degrees hdegrees lifted ∧
      finiteSignedMax degrees hdegrees lifted ≤
        q * (finiteSignedMax degrees hdegrees base + cellError) := by
  constructor
  · obtain ⟨r, hr, hmax⟩ := exists_eq_finiteSignedMax hdegrees base
    calc
      q * (finiteSignedMax degrees hdegrees base - cellError) =
          q * (base r - cellError) := by rw [hmax]
      _ ≤ lifted r := (hdegree r hr).1
      _ ≤ finiteSignedMax degrees hdegrees lifted :=
        le_finiteSignedMax hdegrees lifted hr
  · apply finiteSignedMax_le hdegrees lifted
    intro r hr
    calc
      lifted r ≤ q * (base r + cellError) := (hdegree r hr).2
      _ ≤ q * (finiteSignedMax degrees hdegrees base + cellError) := by
        apply mul_le_mul_of_nonneg_left _ hq
        linarith [le_finiteSignedMax hdegrees base hr]

end FiniteSignedMax

section CellTelescoping

/-- Abstract quantitative telescope with cell-dependent lower and upper increments.

In the probabilistic application, `potential j` is the expected logarithmic norm after
`j` independent cells.  Conditional independence and the adapted unit vector establish
`hstep`; this lemma performs the exact telescope and introduces no union-bound loss. -/
theorem cell_telescope_sum_bounds (potential lower upper : ℕ → ℝ) (q : ℕ)
    (hstep : ∀ j < q,
      lower j ≤ potential (j + 1) - potential j ∧
        potential (j + 1) - potential j ≤ upper j) :
    (∑ j ∈ Finset.range q, lower j) ≤ potential q - potential 0 ∧
      potential q - potential 0 ≤ ∑ j ∈ Finset.range q, upper j := by
  have hlower :
      (∑ j ∈ Finset.range q, lower j) ≤
        ∑ j ∈ Finset.range q, (potential (j + 1) - potential j) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hstep j (Finset.mem_range.mp hj)).1
  have hupper :
      (∑ j ∈ Finset.range q, (potential (j + 1) - potential j)) ≤
        ∑ j ∈ Finset.range q, upper j := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hstep j (Finset.mem_range.mp hj)).2
  simpa only [Finset.sum_range_sub] using And.intro hlower hupper

/-- Constant per-cell bounds accumulate linearly in the number of cells. -/
theorem repeated_cell_telescope_bounds (potential : ℕ → ℝ)
    (lower upper : ℝ) (q : ℕ)
    (hstep : ∀ j < q,
      lower ≤ potential (j + 1) - potential j ∧
        potential (j + 1) - potential j ≤ upper) :
    (q : ℝ) * lower ≤ potential q - potential 0 ∧
      potential q - potential 0 ≤ (q : ℝ) * upper := by
  simpa using cell_telescope_sum_bounds potential (fun _ => lower) (fun _ => upper) q hstep

/-- Symmetric cell errors also telescope quantitatively, with total error exactly
`q * cellError`. -/
theorem repeated_cell_telescope_abs_error (potential : ℕ → ℝ)
    (center cellError : ℝ) (q : ℕ)
    (hstep : ∀ j < q,
      |(potential (j + 1) - potential j) - center| ≤ cellError) :
    |(potential q - potential 0) - (q : ℝ) * center| ≤
      (q : ℝ) * cellError := by
  have hbounds := repeated_cell_telescope_bounds potential
    (center - cellError) (center + cellError) q (fun j hj => by
      have h := abs_le.mp (hstep j hj)
      constructor <;> linarith)
  have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  rw [abs_le]
  constructor <;> nlinarith [hq]

/-- The abstract degreewise form of `eq:pressure-lift-r`.

The initial zero corresponds to the log norm of the empty cell product.  The statement
also covers `q = 0`; the paper later assumes `q ≥ 1` only because it normalizes by `q`. -/
theorem pressure_lift_degree (cellPressure : ℕ → ℝ)
    (basePressure cellError : ℝ) (q : ℕ)
    (hzero : cellPressure 0 = 0)
    (hcell : ∀ j < q,
      basePressure - cellError ≤ cellPressure (j + 1) - cellPressure j ∧
        cellPressure (j + 1) - cellPressure j ≤ basePressure + cellError) :
    (q : ℝ) * (basePressure - cellError) ≤ cellPressure q ∧
      cellPressure q ≤ (q : ℝ) * (basePressure + cellError) := by
  simpa [hzero] using repeated_cell_telescope_bounds cellPressure
    (basePressure - cellError) (basePressure + cellError) q hcell

end CellTelescoping

section PressureLiftMax

variable {ι : Type*}

/-- Paper equation `eq:pressure-lift-max`.

If every exterior degree satisfies the `q`-cell estimate
`q * (Fᵣ(ell) - E) ≤ Fᵣ(qm) ≤ q * (Fᵣ(ell) + E)`, then maximizing over the
finite degree set and normalizing by the total length gives error at most `E / m`.
No sign assumption on the pressures is used. -/
theorem max_pressure_lift {degrees : Finset ι} (hdegrees : degrees.Nonempty)
    (base lifted : ι → ℝ) (q m : ℕ) (cellError : ℝ)
    (hq : 0 < q) (hm : 0 < m)
    (hdegree : ∀ r ∈ degrees,
      (q : ℝ) * (base r - cellError) ≤ lifted r ∧
        lifted r ≤ (q : ℝ) * (base r + cellError)) :
    |finiteSignedMax degrees hdegrees lifted / ((q : ℝ) * (m : ℝ)) -
        finiteSignedMax degrees hdegrees base / (m : ℝ)| ≤
      cellError / (m : ℝ) := by
  let baseMax := finiteSignedMax degrees hdegrees base
  let liftedMax := finiteSignedMax degrees hdegrees lifted
  have hqReal : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hmReal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmax :
      (q : ℝ) * (baseMax - cellError) ≤ liftedMax ∧
        liftedMax ≤ (q : ℝ) * (baseMax + cellError) := by
    simpa [baseMax, liftedMax] using
      finiteSignedMax_cell_bounds hdegrees base lifted (q : ℝ) cellError hqReal.le hdegree
  have hscaled : |liftedMax / (q : ℝ) - baseMax| ≤ cellError := by
    rw [abs_le]
    constructor
    · have hlower : baseMax - cellError ≤ liftedMax / (q : ℝ) := by
        rw [le_div_iff₀ hqReal, mul_comm]
        exact hmax.1
      linarith
    · have hupper : liftedMax / (q : ℝ) ≤ baseMax + cellError := by
        rw [div_le_iff₀ hqReal, mul_comm]
        exact hmax.2
      linarith
  have hrearrange :
      liftedMax / ((q : ℝ) * (m : ℝ)) - baseMax / (m : ℝ) =
        (liftedMax / (q : ℝ) - baseMax) / (m : ℝ) := by
    rw [div_mul_eq_div_div, sub_div]
  rw [show finiteSignedMax degrees hdegrees lifted = liftedMax by rfl,
    show finiteSignedMax degrees hdegrees base = baseMax by rfl,
    hrearrange, abs_div, abs_of_pos hmReal]
  exact div_le_div_of_nonneg_right hscaled hmReal.le

/-- Combined telescope-to-maximum form.  This is the reusable abstract version of the
cell argument: establish the same one-cell increment bounds at every degree, telescope
each degree, then invoke `eq:pressure-lift-max`. -/
theorem max_pressure_lift_of_cell_telescopes
    {degrees : Finset ι} (hdegrees : degrees.Nonempty)
    (base : ι → ℝ) (cellPressure : ι → ℕ → ℝ)
    (q m : ℕ) (cellError : ℝ) (hq : 0 < q) (hm : 0 < m)
    (hzero : ∀ r ∈ degrees, cellPressure r 0 = 0)
    (hcell : ∀ r ∈ degrees, ∀ j < q,
      base r - cellError ≤ cellPressure r (j + 1) - cellPressure r j ∧
        cellPressure r (j + 1) - cellPressure r j ≤ base r + cellError) :
    |finiteSignedMax degrees hdegrees (fun r => cellPressure r q) /
          ((q : ℝ) * (m : ℝ)) -
        finiteSignedMax degrees hdegrees base / (m : ℝ)| ≤
      cellError / (m : ℝ) := by
  apply max_pressure_lift hdegrees base (fun r => cellPressure r q)
    q m cellError hq hm
  intro r hr
  exact pressure_lift_degree (cellPressure r) (base r) cellError q
    (hzero r hr) (hcell r hr)

end PressureLiftMax

end CircularLawSections56.Section5
