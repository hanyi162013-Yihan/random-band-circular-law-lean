import CircularLawSections56.Section6.PhysicalReplacementBridge
import Mathlib.Probability.ProductMeasure

/-!
# Canonical common-space realization of the triangular model

The finite matrix-size spaces need not come with a coupling. Their countable
product is constructed here, each coordinate projection is measure preserving,
and the triangular Section 5 limits are transported into the proved replacement
theorem. No coupling or replacement assertion is an additional hypothesis.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 800000

namespace CircularLawSections56.Section6

open CircularLawSections56.Section5 TaoVuReplacement

universe u
variable {Ω : ℕ → Type u} [∀ k, MeasurableSpace (Ω k)]

theorem tri_probability_canonical_lift
    (μ : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (μ k)]
    (X : ∀ k, Ω k → ℝ) (a : ℝ) (hMeas : ∀ k, Measurable (X k))
    (hX : TendstoInProbabilityTri μ X a) :
    TendstoInProbabilityTri (fun _ => Measure.infinitePi μ)
      (fun k ω => X k (ω k)) a := by
  intro ε hε
  have heq : ∀ k, (Measure.infinitePi μ).real {ω | ε ≤ |X k (ω k) - a|} =
      (μ k).real {x | ε ≤ |X k x - a|} := by
    intro k
    have hs : MeasurableSet {x | ε ≤ |X k x - a|} := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using
        measurableSet_le measurable_const (((hMeas k).sub measurable_const).norm)
    exact congrArg ENNReal.toReal
      ((measurePreserving_eval_infinitePi μ k).measure_preimage hs.nullMeasurableSet)
  simpa only [heq] using hX ε hε

theorem canonical_integral_eq
    (μ : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (μ k)]
    (k : ℕ) (g : Ω k → ℝ) (hg : Integrable g (μ k)) :
    (∫ ω, g (ω k) ∂Measure.infinitePi μ) = ∫ x, g x ∂μ k := by
  have hp := measurePreserving_eval_infinitePi μ k
  have hgmap : AEStronglyMeasurable g (Measure.map (Function.eval k) (Measure.infinitePi μ)) := by
    rw [hp.map_eq]
    exact hg.aestronglyMeasurable
  calc
    _ = ∫ x, g x ∂Measure.map (Function.eval k) (Measure.infinitePi μ) :=
      (integral_map hp.measurable.aemeasurable hgmap).symm
    _ = _ := by rw [hp.map_eq]

theorem measurable_physicalLogPotential
    {SigmaSpace : Type*} [MeasurableSpace SigmaSpace] {k : ℕ}
    (X : SigmaSpace → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j)) (z : ℂ) :
    Measurable (fun ω => physicalLogPotential (X ω) z) := by
  have hA : ∀ i j, Measurable (fun ω => undoPhysicalNormalization (X ω) i j) :=
    fun i j => measurable_const.mul (hX i j)
  simpa only [normalizedLogDet_undoPhysicalNormalization] using
    measurable_normalizedLogDet_fixed_of_entrywise (fun ω => undoPhysicalNormalization (X ω)) hA z

/-- Actual ESD comparison on the canonical realization of the triangular array. -/
theorem triangular_physical_replacement
    (μ : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (μ k)]
    (X Y : ∀ k, Ω k → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hX : ∀ k i j, Measurable fun ω => X k ω i j)
    (hY : ∀ k i j, Measurable fun ω => Y k ω i j)
    (energyBound : ℝ) (hEnergyBound : 0 ≤ energyBound)
    (hEnergyInt : ∀ k, Integrable
      (fun ω => physicalEnergy (X k ω) + physicalEnergy (Y k ω)) (μ k))
    (hEnergy : ∀ k, ∫ ω, physicalEnergy (X k ω) + physicalEnergy (Y k ω) ∂μ k ≤ energyBound)
    (target : ℂ → ℝ)
    (hLogX : ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri μ
      (fun k ω => physicalLogPotential (X k ω) z) (target z))
    (hLogY : ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri μ
      (fun k ω => physicalLogPotential (Y k ω) z) (target z)) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi μ)
        (fun k ω => esdDifference (X k (ω k)) (Y k (ω k)) f) atTop 0 := by
  apply physical_replacement_of_logPotential_limits (Measure.infinitePi μ)
    (fun k ω => X k (ω k)) (fun k ω => Y k (ω k))
    (fun k i j => (hX k i j).comp (measurable_pi_apply k))
    (fun k i j => (hY k i j).comp (measurable_pi_apply k))
    energyBound hEnergyBound ?_ ?_ target ?_ ?_
  · intro k
    exact (measurePreserving_eval_infinitePi μ k).integrable_comp_of_integrable (hEnergyInt k)
  · intro k
    rw [canonical_integral_eq μ k _ (hEnergyInt k)]
    exact hEnergy k
  · filter_upwards [hLogX] with z hz
    have h := tri_probability_canonical_lift μ
      (fun k ω => physicalLogPotential (X k ω) z) (target z)
      (fun k => measurable_physicalLogPotential (X k) (hX k) z) hz
    convert h using 1
  · filter_upwards [hLogY] with z hz
    have h := tri_probability_canonical_lift μ
      (fun k ω => physicalLogPotential (Y k ω) z) (target z)
      (fun k => measurable_physicalLogPotential (Y k) (hY k) z) hz
    convert h using 1

/-- A comparison ensemble's known spectral limit transfers to the physical model.
The remaining comparison theorem is a concrete test-function limit, not an abstract
implication whose conclusion is the desired circular law. -/
theorem esd_limit_of_replacement
    {SigmaSpace : Type*} [MeasurableSpace SigmaSpace] (P : Measure SigmaSpace) [IsProbabilityMeasure P]
    (X Y : ∀ k, SigmaSpace → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (limitTest : (ℂ → ℝ) → ℝ)
    (hReplacement : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure P (fun k ω => esdDifference (X k ω) (Y k ω) f) atTop 0)
    (hComparison : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure P (fun k ω => realEsdTest (Y k ω) f) atTop (fun _ => limitTest f)) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure P (fun k ω => realEsdTest (X k ω) f) atTop (fun _ => limitTest f) := by
  intro f hf hc
  have hdiff := (tendstoInMeasure_iff_tri P _ 0).1 (hReplacement f hf hc)
  have hY := (tendstoInMeasure_iff_tri P _ (limitTest f)).1 (hComparison f hf hc)
  apply (tendstoInMeasure_iff_tri P _ (limitTest f)).2
  simpa only [esdDifference, sub_add_cancel, zero_add] using hdiff.add (fun _ => P) hY

end CircularLawSections56.Section6
