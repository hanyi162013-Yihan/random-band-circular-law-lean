import BernoulliSection10.ProductMarginal
import Mathlib.Probability.ProductMeasure

/-!
# Exact finite i.i.d. coordinate transports

Flattening rows, separating coordinate blocks, and selecting distinct
coordinates preserve the specified atom law. These transports are used
to identify the padded packet law with a literal three-site physical
interval and to justify independent cell integration.
-/

open MeasureTheory

noncomputable section

namespace BernoulliSection10

variable {ι κ X : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace X]

theorem measurePreserving_iid_uncurry (μ : Measure X) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun x : ι → κ → X => fun p : ι × κ => x p.1 p.2)
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ)
      (Measure.pi fun _ : ι × κ => μ) := by
  refine ⟨by fun_prop, ?_⟩
  have h := Measure.infinitePi_map_curry_symm (fun _ : ι => fun _ : κ => μ)
  change Measure.map (fun x : ι → κ → X => fun p : ι × κ => x p.1 p.2)
    (Measure.infinitePi fun _ : ι => Measure.infinitePi fun _ : κ => μ) =
      (Measure.infinitePi fun _ : ι × κ => μ) at h
  simpa only [Measure.infinitePi_eq_pi] using h

theorem measurePreserving_iid_curry (μ : Measure X) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun x : ι × κ → X => fun i j => x (i, j))
      (Measure.pi fun _ : ι × κ => μ)
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ) := by
  refine ⟨by fun_prop, ?_⟩
  have h := Measure.infinitePi_map_curry (fun _ : ι => fun _ : κ => μ)
  change Measure.map (fun x : ι × κ → X => fun i j => x (i, j))
    (Measure.infinitePi fun _ : ι × κ => μ) =
      (Measure.infinitePi fun _ : ι => Measure.infinitePi fun _ : κ => μ) at h
  simpa only [Measure.infinitePi_eq_pi] using h

theorem measurePreserving_iid_sum_elim (μ : Measure X) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun p : (ι → X) × (κ → X) => Sum.elim p.1 p.2)
      ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : κ => μ))
      (Measure.pi fun _ : ι ⊕ κ => μ) :=
  measurePreserving_sumPiEquivProdPi_symm (fun _ : ι ⊕ κ => μ)

theorem measurePreserving_iid_sum_split (μ : Measure X) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun x : ι ⊕ κ → X =>
      ((fun i => x (Sum.inl i)), fun j => x (Sum.inr j)))
      (Measure.pi fun _ : ι ⊕ κ => μ)
      ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : κ => μ)) :=
  measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ κ => μ)

/-- A permutation of all coordinates is a special case of the proved
injective-selection theorem and needs no additional distribution input. -/
theorem measurePreserving_iid_reindex (μ : Measure X) [IsProbabilityMeasure μ]
    (e : κ ≃ ι) :
    MeasurePreserving (fun x : ι → X => fun j => x (e j))
      (Measure.pi fun _ : ι => μ) (Measure.pi fun _ : κ => μ) :=
  measurePreserving_pi_restrict_embedding μ e.toEmbedding

end BernoulliSection10
