import CircularLawSections56.Section6.Potentials
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FunProp

/-! # Continuity of the actual variance-scaled circular potential

This discharges the target-continuity step in the compact-core exhaustion;
continuity is proved from the explicit circular potential, not assumed.
-/

open Filter Topology Set

namespace CircularLawSection6

open CircularLawSections56.Section6

theorem continuous_circularRadialPotential : Continuous circularRadialPotential := by
  unfold circularRadialPotential
  apply continuous_if_le continuous_id continuous_const
  · fun_prop
  · intro x hx
    exact (Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le zero_lt_one hx))).continuousWithinAt
  · intro x hx
    change x = 1 at hx
    rw [hx]
    norm_num

theorem continuousAt_varianceScaledRadialPotential
    {v radius : ℝ} (hv : 0 < v) :
    ContinuousAt (fun w => varianceScaledRadialPotential w radius) v := by
  unfold varianceScaledRadialPotential
  exact ((Real.continuousAt_log hv.ne').const_mul _).add
    (continuous_circularRadialPotential.continuousAt.comp
      (continuousAt_const.div Real.continuous_sqrt.continuousAt
        (Real.sqrt_pos.2 hv).ne'))

/-- The limiting compact-core potential approaches the circular potential as
the core mass tends to one, including at spectral parameter zero. -/
theorem varianceScaledRadialPotential_tendsto_one
    {v : ℕ → ℝ} (hv : Tendsto v atTop (𝓝 1)) (radius : ℝ) :
    Tendsto (fun R => varianceScaledRadialPotential (v R) radius)
      atTop (𝓝 (circularRadialPotential radius)) := by
  simpa only [Function.comp_def, varianceScaledRadialPotential_one] using
    (continuousAt_varianceScaledRadialPotential
    (radius := radius) zero_lt_one).tendsto.comp hv

end CircularLawSection6
