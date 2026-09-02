import CircularLawSection4.UnboundedRawContinuousEfronStein
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Automatic global `L²` from finite IID replacement energy

Symmetric clips of a measurable finite real observable are bounded.  If
their variances are uniformly bounded, the independent-copy identity and
Fatou's lemma put the pair difference `f x - f y` in `L²`.  Fubini then
provides one finite anchor `y`; adding back the constant `f y` proves that
`f` itself lies in `L²`.

For a finite IID product, integrable raw coordinate-replacement squares give
the required uniform clipped-variance bound by bounded Efron--Stein.  Thus no
global first- or second-moment assumption on the observable is needed.
-/

open scoped ENNReal MeasureTheory Topology
open MeasureTheory ProbabilityTheory Filter

namespace CircularLawSection4

universe u

section Fatou

variable {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)

/-- A nonnegative pointwise limit of integrable measurable functions is
integrable when their integrals have a common finite real upper bound. -/
theorem integrable_of_tendsto_of_nonneg_of_integral_le
    (G : ℕ → Ω → ℝ) (f : Ω → ℝ)
    (hG : ∀ n, Measurable (G n)) (hf : Measurable f)
    (hGint : ∀ n, Integrable (G n) μ)
    (hGnonneg : ∀ n x, 0 ≤ G n x) (hfnonneg : ∀ x, 0 ≤ f x)
    (htendsto : ∀ x, Tendsto (fun n => G n x) atTop (𝓝 (f x)))
    {C : ℝ} (hbound : ∀ n, ∫ x, G n x ∂μ ≤ C) :
    Integrable f μ := by
  have hfatou : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      (∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
          ∫⁻ x, liminf (fun n => ENNReal.ofReal (G n x)) atTop ∂μ := by
        apply lintegral_congr
        intro x
        exact ((ENNReal.continuous_ofReal.tendsto (f x)).comp
          (htendsto x)).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (G n x) ∂μ) atTop :=
        lintegral_liminf_le (fun n => ENNReal.measurable_ofReal.comp (hG n))
      _ ≤ ENNReal.ofReal C := by
        apply Filter.liminf_le_of_frequently_le'
        apply Frequently.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hGint n)
          (ae_of_all μ (hGnonneg n))]
        exact ENNReal.ofReal_le_ofReal (hbound n)
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all μ hfnonneg)]
  exact hfatou.trans_lt ENNReal.ofReal_lt_top

end Fatou

section Pair

variable {Ω : Type u} [MeasurableSpace Ω]
  (μ : Measure Ω) [SFinite μ] [IsProbabilityMeasure μ]

/-- Uniform variance control of every symmetric clip forces the original
finite real observable to belong to `L²`. -/
theorem memLp_two_of_variance_symmetricClip_le
    (f : Ω → ℝ) (hf : Measurable f) {C : ℝ}
    (hvariance : ∀ N : ℕ,
      variance (fun x => symmetricClip (N : ℝ) (f x)) μ ≤ C) :
    MemLp f 2 μ := by
  let g : ℕ → Ω → ℝ := fun N x => symmetricClip (N : ℝ) (f x)
  let G : ℕ → Ω × Ω → ℝ := fun N p => (g N p.1 - g N p.2) ^ 2
  let F : Ω × Ω → ℝ := fun p => (f p.1 - f p.2) ^ 2
  have hg (N : ℕ) : Measurable (g N) :=
    (measurable_symmetricClip (N : ℝ)).comp hf
  have hgBound (N : ℕ) (x : Ω) : ‖g N x‖ ≤ (N : ℝ) := by
    rw [Real.norm_eq_abs]
    exact abs_symmetricClip_le_radius (N : ℝ) (f x) (by positivity)
  have hG (N : ℕ) : Measurable (G N) := by
    exact ((hg N).comp measurable_fst).sub ((hg N).comp measurable_snd) |>.pow_const 2
  have hGint (N : ℕ) : Integrable (G N) (μ.prod μ) := by
    apply Integrable.of_bound (hG N).aestronglyMeasurable ((2 * (N : ℝ)) ^ 2)
    apply ae_of_all
    intro p
    dsimp only [G]
    convert norm_sub_sq_le_bound (hgBound N) p.1 p.2 using 1
    rw [abs_of_nonneg]
    positivity
  have hF : Measurable F := by
    exact ((hf.comp measurable_fst).sub (hf.comp measurable_snd)).pow_const 2
  have hGnonneg (N : ℕ) (p : Ω × Ω) : 0 ≤ G N p := sq_nonneg _
  have hFnonneg (p : Ω × Ω) : 0 ≤ F p := sq_nonneg _
  have htendsto (p : Ω × Ω) :
      Tendsto (fun N => G N p) atTop (𝓝 (F p)) := by
    exact ((tendsto_symmetricClip_nat (f p.1)).sub
      (tendsto_symmetricClip_nat (f p.2))).pow 2
  have hGbound (N : ℕ) : ∫ p, G N p ∂μ.prod μ ≤ 2 * C := by
    have hpair := variance_eq_half_pairDifference_bounded (μ := μ)
      (g N) (hg N) (N : ℝ) (hgBound N)
    have hprod : (∫ p, G N p ∂μ.prod μ) =
        ∫ x, ∫ y, (g N x - g N y) ^ 2 ∂μ ∂μ := by
      exact integral_prod (G N) (hGint N)
    dsimp only [G] at hprod
    rw [← hprod] at hpair
    linarith [hvariance N]
  have hFint : Integrable F (μ.prod μ) :=
    integrable_of_tendsto_of_nonneg_of_integral_le (μ.prod μ)
      G F hG hF hGint hGnonneg hFnonneg htendsto hGbound
  have hsection : ∀ᵐ y ∂μ, Integrable (fun x => F (x, y)) μ := by
    exact hFint.prod_left_ae
  obtain ⟨y₀, hy₀⟩ := hsection.exists
  have hdiffSq : Integrable (fun x => (f x - f y₀) ^ 2) μ := by
    simpa only [F] using hy₀
  have hdiff : MemLp (fun x => f x - f y₀) 2 μ :=
    (memLp_two_iff_integrable_sq
      ((hf.sub_const (f y₀)).aestronglyMeasurable)).2 hdiffSq
  have hconst : MemLp (fun _x : Ω => f y₀) 2 μ := memLp_const _
  convert hdiff.add hconst using 1
  funext x
  simp

end Pair

section IIDRaw

variable {K : Type u} [MeasurableSpace K]
  (ν : Measure K) [SFinite ν] [IsProbabilityMeasure ν]

/-- Finite raw coordinate-replacement square integrals force a measurable
real observable on a finite IID product to belong to `L²`.  No prior first-
or second-moment assumption on the observable is required. -/
theorem memLp_two_of_iid_raw_replacement_integrable {n : ℕ}
    (f : (Fin n → K) → ℝ) (hf : Measurable f)
    (hinner : ∀ i x, Integrable (fun a' =>
      (f x - f (Function.update x i a')) ^ 2) ν)
    (houter : ∀ i, Integrable (fun x => ∫ a',
      (f x - f (Function.update x i a')) ^ 2 ∂ν)
      (iidMeasure ν n)) :
    MemLp f 2 (iidMeasure ν n) := by
  let _ := iidMeasure_isProbability ν n
  refine memLp_two_of_variance_symmetricClip_le (iidMeasure ν n) f hf
    (C := (1 / 2 : ℝ) * ∑ i : Fin n, iidRawResamplingEnergy ν f i) ?_
  intro N
  let g : (Fin n → K) → ℝ := fun x => symmetricClip (N : ℝ) (f x)
  have hg : Measurable g := (measurable_symmetricClip (N : ℝ)).comp hf
  have hgBound : ∀ x, ‖g x‖ ≤ (N : ℝ) := by
    intro x
    rw [Real.norm_eq_abs]
    exact abs_symmetricClip_le_radius (N : ℝ) (f x) (by positivity)
  change variance g (iidMeasure ν n) ≤
    (1 / 2 : ℝ) * ∑ i : Fin n, iidRawResamplingEnergy ν f i
  refine (variance_iidMeasure_le_half_sum_raw ν g hg (N : ℝ) hgBound).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i _hi
  exact iidRawResamplingEnergy_symmetricClip_le ν f hf i
    (hinner i) (houter i) (N : ℝ) (by positivity)

end IIDRaw

end CircularLawSection4
