import BernoulliSection8.RademacherEnergy
import Mathlib.Data.Fintype.Pi

/-!
# Finite support and measurable events for physical Rademacher coordinates

Each fixed interval has only finitely many sign configurations. Restricting
any event to these configurations therefore gives a measurable event with
the same probability. This is a concrete restriction to the interval's own
coordinates and makes no choice of a global measurable hull.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BernoulliSection8

open BernoulliSection10

def rademacherIntervalSupport (W s : ℕ) : Set (IntervalRows W s) :=
  {x | ∀ i a, x i a = 1 ∨ x i a = -1}

theorem rademacherIntervalSupport_finite (W s : ℕ) :
    (rademacherIntervalSupport W s).Finite := by
  have hsign : ({x : ℝ | x = 1 ∨ x = -1} : Set ℝ).Finite := by
    have hset : ({x : ℝ | x = 1 ∨ x = -1} : Set ℝ) = {1, -1} := by
      ext x
      simp
    rw [hset]
    exact (Set.finite_singleton (-1 : ℝ)).insert 1
  have hrow : ({x : PhysicalRowAtoms W | ∀ a, x a = 1 ∨ x a = -1} :
      Set (PhysicalRowAtoms W)).Finite := Set.Finite.pi' (fun _ => hsign)
  exact Set.Finite.pi' (fun _ => hrow)

theorem measurableSet_rademacherIntervalSupport (W s : ℕ) :
    MeasurableSet (rademacherIntervalSupport W s) :=
  (rademacherIntervalSupport_finite W s).measurableSet

theorem rademacherIntervalSupport_ae (W s : ℕ) :
    ∀ᵐ x ∂intervalRowsLaw W s rademacherLaw,
      x ∈ rademacherIntervalSupport W s :=
  rademacherRows_ae_sign W s

/-- Every predicate on a finite Rademacher interval has a concrete
measurable realization, with no measurability premise on the predicate. -/
def rademacherRestrictedEvent (W s : ℕ) (E : Set (IntervalRows W s)) :
    Set (IntervalRows W s) :=
  E ∩ rademacherIntervalSupport W s

theorem rademacherRestrictedEvent_finite (W s : ℕ) (E : Set (IntervalRows W s)) :
    (rademacherRestrictedEvent W s E).Finite :=
  (rademacherIntervalSupport_finite W s).subset inter_subset_right

theorem measurableSet_rademacherRestrictedEvent
    (W s : ℕ) (E : Set (IntervalRows W s)) :
    MeasurableSet (rademacherRestrictedEvent W s E) :=
  (rademacherRestrictedEvent_finite W s E).measurableSet

theorem rademacherRestrictedEvent_ae_eq (W s : ℕ) (E : Set (IntervalRows W s)) :
    rademacherRestrictedEvent W s E =ᵐ[intervalRowsLaw W s rademacherLaw] E := by
  filter_upwards [rademacherIntervalSupport_ae W s] with x hx
  apply propext
  change (x ∈ E ∧ x ∈ rademacherIntervalSupport W s) ↔ x ∈ E
  exact and_iff_left hx

theorem measure_rademacherRestrictedEvent (W s : ℕ) (E : Set (IntervalRows W s)) :
    intervalRowsLaw W s rademacherLaw (rademacherRestrictedEvent W s E) =
      intervalRowsLaw W s rademacherLaw E :=
  measure_congr (rademacherRestrictedEvent_ae_eq W s E)

theorem measureReal_rademacherRestrictedEvent (W s : ℕ) (E : Set (IntervalRows W s)) :
    (intervalRowsLaw W s rademacherLaw).real (rademacherRestrictedEvent W s E) =
      (intervalRowsLaw W s rademacherLaw).real E :=
  measureReal_congr (rademacherRestrictedEvent_ae_eq W s E)

/-- The corresponding good event is finite and measurable, and its
complement has exactly the original bad-event probability. -/
def rademacherGoodEvent (W s : ℕ) (E : Set (IntervalRows W s)) :
    Set (IntervalRows W s) :=
  rademacherIntervalSupport W s \ E

theorem measurableSet_rademacherGoodEvent (W s : ℕ) (E : Set (IntervalRows W s)) :
    MeasurableSet (rademacherGoodEvent W s E) :=
  ((rademacherIntervalSupport_finite W s).subset sdiff_subset).measurableSet

theorem rademacherGoodEvent_compl_ae_eq (W s : ℕ) (E : Set (IntervalRows W s)) :
    (rademacherGoodEvent W s E)ᶜ =ᵐ[intervalRowsLaw W s rademacherLaw] E := by
  filter_upwards [rademacherIntervalSupport_ae W s] with x hx
  apply propext
  change ¬(x ∈ rademacherIntervalSupport W s ∧ x ∉ E) ↔ x ∈ E
  simp only [hx, true_and, not_not]

theorem measureReal_rademacherGoodEvent_compl (W s : ℕ) (E : Set (IntervalRows W s)) :
    (intervalRowsLaw W s rademacherLaw).real (rademacherGoodEvent W s E)ᶜ =
      (intervalRowsLaw W s rademacherLaw).real E :=
  measureReal_congr (rademacherGoodEvent_compl_ae_eq W s E)

end BernoulliSection8
