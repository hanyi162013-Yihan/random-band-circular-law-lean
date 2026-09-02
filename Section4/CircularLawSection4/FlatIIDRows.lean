import CircularLawSection4.IIDOperatorAffineSmallBall
import Mathlib.Probability.ProductMeasure

/-!
# Flattened and row-wise finite IID samples

A sample indexed by `Fin (N * d)` is measurably equivalent to a row-wise
sample indexed by `Fin N -> Fin d -> K`.  The equivalence first reindexes
along `finProdFinEquiv` and then curries the resulting function on
`Fin N × Fin d`.

Under an IID atom law `ν`, this equivalence carries the flat recursive IID
law to the recursive IID law whose atoms are IID rows.  This is the generic
measure-theoretic bridge needed to pass between the scalar sample space and
the row-wise sample space used by random-matrix arguments.
-/

open MeasureTheory

namespace CircularLawSection4

universe u

section Equivalence

variable {K : Type u} [MeasurableSpace K]

/-- The measurable equivalence from a flat `N * d` sample to `N` rows of
length `d`.  The column coordinate varies fastest. -/
def flatIIDRowsMeasurableEquiv (N d : ℕ) :
    (Fin (N * d) → K) ≃ᵐ (Fin N → Fin d → K) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (N * d) ↦ K) finProdFinEquiv).symm.trans
    (MeasurableEquiv.curry (Fin N) (Fin d) K)

@[simp]
theorem flatIIDRowsMeasurableEquiv_apply (N d : ℕ)
    (ω : Fin (N * d) → K) (i : Fin N) (j : Fin d) :
    flatIIDRowsMeasurableEquiv N d ω i j =
      ω (finProdFinEquiv (i, j)) := by
  rfl

@[simp]
theorem flatIIDRowsMeasurableEquiv_symm_apply (N d : ℕ)
    (ω : Fin N → Fin d → K) (k : Fin (N * d)) :
    (flatIIDRowsMeasurableEquiv N d).symm ω k =
      ω (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
  simp [flatIIDRowsMeasurableEquiv, MeasurableEquiv.trans_symm,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]

end Equivalence

section Measure

variable {K : Type u} [MeasurableSpace K]
variable (N d : ℕ) (ν : Measure K)
  [SigmaFinite ν] [IsProbabilityMeasure ν]

local instance iidMeasureProbability :
    IsProbabilityMeasure (iidMeasure ν d) :=
  iidMeasure_isProbability ν d

/-- Currying a finite product of identical atom laws is measure preserving.
This finite statement is obtained from mathlib's corresponding infinite
product formula. -/
theorem measurePreserving_curry_fin_iid :
    MeasurePreserving (MeasurableEquiv.curry (Fin N) (Fin d) K)
      (Measure.pi (fun _ : Fin N × Fin d ↦ ν))
      (Measure.pi (fun _ : Fin N ↦
        Measure.pi (fun _ : Fin d ↦ ν))) := by
  refine ⟨(MeasurableEquiv.curry (Fin N) (Fin d) K).measurable, ?_⟩
  simpa only [Measure.infinitePi_eq_pi] using
    (Measure.infinitePi_map_curry
      (fun _ : Fin N ↦ fun _ : Fin d ↦ ν))

/-- The flat-to-row equivalence sends the recursive IID law on all scalar
coordinates to the recursive IID law on IID rows. -/
theorem flatIIDRows_measurePreserving :
    MeasurePreserving (flatIIDRowsMeasurableEquiv N d)
      (iidMeasure ν (N * d)) (iidMeasure (iidMeasure ν d) N) := by
  have hreindex :
      MeasurePreserving
        (MeasurableEquiv.piCongrLeft
          (fun _ : Fin (N * d) ↦ K) finProdFinEquiv).symm
        (Measure.pi (fun _ : Fin (N * d) ↦ ν))
        (Measure.pi (fun _ : Fin N × Fin d ↦ ν)) := by
    exact (measurePreserving_piCongrLeft
      (fun _ : Fin (N * d) ↦ ν) finProdFinEquiv).symm
  have hcurry := measurePreserving_curry_fin_iid N d ν
  rw [iidMeasure_eq_pi, iidMeasure_eq_pi]
  simp_rw [iidMeasure_eq_pi ν d]
  simpa only [flatIIDRowsMeasurableEquiv, MeasurableEquiv.coe_trans,
    Function.comp_def] using hcurry.comp hreindex

/-- Push-forward form of `flatIIDRows_measurePreserving`. -/
theorem iidMeasure_map_flatIIDRows :
    Measure.map (flatIIDRowsMeasurableEquiv N d)
        (iidMeasure ν (N * d)) =
      iidMeasure (iidMeasure ν d) N :=
  (flatIIDRows_measurePreserving N d ν).map_eq

end Measure

end CircularLawSection4
