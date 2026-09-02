import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.Real

/-!
# The weak law on literal finite i.i.d. sample spaces

Only an integrable atom observable is required. In particular, applying
this to its square uses the paper's second moment, not a hidden fourth
moment. The infinite sequence is an internal coupling whose finite
marginals are proved to have exactly the specified finite product laws.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal

noncomputable section

namespace BernoulliSection10

variable {X : Type*} [MeasurableSpace X]

theorem measurePreserving_initialIIDCoordinates
    (μ : Measure X) [IsProbabilityMeasure μ] (d : ℕ) :
    MeasurePreserving (fun ω : ℕ → X => fun i : Fin d => ω i)
      (Measure.infinitePi fun _ : ℕ => μ) (Measure.pi fun _ : Fin d => μ) := by
  refine ⟨by fun_prop, ?_⟩
  simpa only [Measure.infinitePi_eq_pi] using
    (Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => μ) (f := fun i : Fin d => (i : ℕ)) Fin.val_injective)

theorem iid_average_tendsto_ae
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ)
    (hf : Measurable f) (hfi : Integrable f μ) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => μ),
      Tendsto (fun d : ℕ => (∑ i : Fin d, f (ω i)) / (d : ℝ))
        atTop (𝓝 (∫ x, f x ∂μ)) := by
  let P := Measure.infinitePi (fun _ : ℕ => μ)
  have heval (i : ℕ) : MeasurePreserving (Function.eval i) P μ :=
    measurePreserving_eval_infinitePi (fun _ : ℕ => μ) i
  have hind : iIndepFun (fun i : ℕ => fun ω : ℕ → X => f (ω i)) P :=
    iIndepFun_infinitePi (fun _ => hf)
  have hident (i : ℕ) : IdentDistrib (fun ω : ℕ → X => f (ω i))
      (fun ω => f (ω 0)) P P := by
    refine ⟨(hf.comp (measurable_pi_apply i)).aemeasurable,
      (hf.comp (measurable_pi_apply 0)).aemeasurable, ?_⟩
    change Measure.map (f ∘ Function.eval i) P = Measure.map (f ∘ Function.eval 0) P
    rw [← Measure.map_map hf (measurable_pi_apply i),
      ← Measure.map_map hf (measurable_pi_apply 0), (heval i).map_eq, (heval 0).map_eq]
  have h := strong_law_ae_real (fun i : ℕ => fun ω : ℕ → X => f (ω i))
    ((heval 0).integrable_comp_of_integrable hfi)
    (fun _ _ hij => hind.indepFun hij) hident
  have hmean : (∫ ω, f (ω 0) ∂P) = ∫ x, f x ∂μ := by
    have hp := heval 0
    rw [← hp.map_eq]
    exact (integral_map hp.measurable.aemeasurable
      (by rw [hp.map_eq]; exact hfi.aestronglyMeasurable)).symm
  simpa only [← Fin.sum_univ_eq_sum_range, hmean] using h

theorem finiteIID_average_tendsto_in_probability
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ)
    (hf : Measurable f) (hfi : Integrable f μ)
    (d : ℕ → ℕ) (hd : Tendsto d atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (Measure.pi (fun _ : Fin (d n) => μ)).real
      {x | ε ≤ |(∑ i, f (x i)) / (d n : ℝ) - ∫ y, f y ∂μ|}) atTop (𝓝 0) := by
  let P := Measure.infinitePi (fun _ : ℕ => μ)
  let M := ∫ y, f y ∂μ
  have hmeas (n : ℕ) : Measurable (fun ω : ℕ → X =>
      (∑ i : Fin (d n), f (ω i)) / (d n : ℝ)) :=
    (Finset.measurable_sum Finset.univ (fun i _ => hf.comp (measurable_pi_apply i.val))).div_const _
  have hconv : TendstoInMeasure P
      (fun n ω => (∑ i : Fin (d n), f (ω i)) / (d n : ℝ)) atTop (fun _ => M) := by
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hmeas n).aestronglyMeasurable)
    filter_upwards [iid_average_tendsto_ae μ f hf hfi] with ω hω
    exact hω.comp hd
  have hprob := (tendstoInMeasure_iff_norm.mp hconv) ε hε
  have heq (n : ℕ) : (Measure.pi (fun _ : Fin (d n) => μ)).real
      {x | ε ≤ |(∑ i, f (x i)) / (d n : ℝ) - M|} =
      P.real {ω | ε ≤ ‖(∑ i : Fin (d n), f (ω i)) / (d n : ℝ) - M‖} := by
    have hp := measurePreserving_initialIIDCoordinates μ (d n)
    have hm : Measurable (fun x : Fin (d n) → X =>
        (∑ i, f (x i)) / (d n : ℝ)) :=
      (Finset.measurable_sum Finset.univ (fun i _ => hf.comp (measurable_pi_apply i))).div_const _
    have hs : MeasurableSet {x : Fin (d n) → X |
        ε ≤ |(∑ i, f (x i)) / (d n : ℝ) - M|} := by
      simpa only [Real.norm_eq_abs] using measurableSet_le measurable_const (hm.sub_const M).norm
    simp only [measureReal_def]
    rw [← hp.map_eq, Measure.map_apply hp.measurable hs]
    rfl
  change Tendsto (fun n => (Measure.pi (fun _ : Fin (d n) => μ)).real
    {x | ε ≤ |(∑ i, f (x i)) / (d n : ℝ) - M|}) atTop (𝓝 0)
  simp_rw [heq]
  exact (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hprob

end BernoulliSection10
