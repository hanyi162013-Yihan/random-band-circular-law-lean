import ShortRingAnchor.AtomAssumption21

/-! Inspect density-record field quantifiers independently of its adapters.

The construction below guards against accidentally generalizing `top` in
the finiteness field. Its only bound hypothesis is `K < ∞`.
-/

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

example {E : Type*} [MeasurableSpace E] (μ ν : Measure E)
    (ρ : E → ℝ≥0∞) (hρ : AEMeasurable ρ ν) (K : ℝ≥0∞)
    (hK : K < ∞) (hbound : ∀ᵐ x ∂ν, ρ x ≤ K)
    (hlaw : μ = ν.withDensity ρ) :
    ShortRingAnchor.HasBoundedDensityWithRespectTo μ ν :=
  ⟨ρ, hρ, K, hK, hbound, hlaw⟩

set_option pp.fullNames true
set_option pp.explicit true

#print ShortRingAnchor.HasBoundedDensityWithRespectTo
#check @ShortRingAnchor.HasBoundedDensityWithRespectTo.bound_lt_top
#print ShortRingAnchor.AtomDensityAlternative21
