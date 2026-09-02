import CircularLawSection4.PaperIndicatorFreshSample
import CircularLawSection4.PaperOperatorAffineL2
import CircularLawSection4.FreshAtomProductSplit
import CircularLawSection4.PiRestrictMarginal

/-!
# The actual flat sample marginal on a fresh block

When `d + 1 ≤ N`, the `d + 1` cyclic fresh rows do not wrap onto one
another.  Consequently their reset-labelled atoms are distinct coordinates
of the flat IID sample, and restriction to them preserves the full finite
product law.
-/

open scoped ENNReal MeasureTheory
open MeasureTheory

noncomputable section

namespace CircularLawSection4

/-- The band-coefficient slot corresponding to a reset/star label. -/
def paperFreshLabelSlot (d : ℕ) : ResetLabel (d + 1) → Fin (d + 2) :=
  (paperOperatorAffineLabelEquiv d).symm

/-- The flat sample coordinate carrying one reset-labelled fresh atom. -/
def paperIndicatorFreshCoordinateIndex
    (N d : ℕ) [NeZero N] (start : ZMod N) :
    FreshAtomIndex (d + 1) → Fin (N * (d + 2)) :=
  fun u => paperIndicatorFlatIndex N d
    (paperIndicatorFreshRowSite N d start u.1) (paperFreshLabelSlot d u.2)

theorem paperIndicatorFreshRowSite_injective
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N) :
    Function.Injective (paperIndicatorFreshRowSite N d start) := by
  intro t u h
  have hcast : (t.val : ZMod N) = (u.val : ZMod N) := by
    exact add_left_cancel h
  apply Fin.ext
  exact CharP.natCast_injOn_Iio (ZMod N) N
    (lt_of_lt_of_le t.isLt hsize) (lt_of_lt_of_le u.isLt hsize) hcast

theorem paperIndicatorFreshCoordinateIndex_injective
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N) :
    Function.Injective (paperIndicatorFreshCoordinateIndex N d start) := by
  intro u v h
  have hp := congrArg (paperIndicatorIndexEquiv N d) h
  simp only [paperIndicatorFreshCoordinateIndex,
    paperIndicatorIndexEquiv_flatIndex] at hp
  apply Prod.ext
  · exact paperIndicatorFreshRowSite_injective N d start hsize
      (congrArg Prod.fst hp)
  · exact (paperOperatorAffineLabelEquiv d).symm.injective
      (congrArg Prod.snd hp)

/-- The fresh-coordinate restriction of a flat IID sample has exactly the
full reset-labelled IID product law. -/
theorem paperIndicatorFreshCoordinates_measurePreserving
    {K : Type*} [MeasurableSpace K]
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N)
    (nu : Measure K) [SigmaFinite nu] [IsProbabilityMeasure nu] :
    MeasurePreserving
      (fun omega : Fin (N * (d + 2)) → K =>
        fun u => omega (paperIndicatorFreshCoordinateIndex N d start u))
      (iidMeasure nu (N * (d + 2)))
      (Measure.pi (fun _ : FreshAtomIndex (d + 1) => nu)) := by
  simpa only [iidMeasure_eq_pi] using
    measurePreserving_pi_restrict_injective
      (paperIndicatorFreshCoordinateIndex N d start)
      (paperIndicatorFreshCoordinateIndex_injective N d start hsize) nu

/-- Pointwise identification of the abstract coordinate restriction with the
actual complex fresh atoms read by the paper model. -/
theorem paperIndicatorFreshAtoms_eq_coordinateRestriction
    (N d : ℕ) [NeZero N] (start : ZMod N)
    (omega : Fin (N * (d + 2)) → ℂ) :
    paperIndicatorFreshAtoms N d start omega =
      fun t ell => omega (paperIndicatorFreshCoordinateIndex N d start (t, ell)) := by
  funext t ell
  cases ell with
  | none =>
      rfl
  | some j =>
      simp [paperIndicatorFreshAtoms, paperIndicatorFreshCoordinateIndex,
        paperFreshLabelSlot, paperOperatorAffineLabelEquiv]

end CircularLawSection4
