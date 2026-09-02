import CircularLawSection4.RawContinuousEfronStein
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Raw-coordinate Efron--Stein for `L²` observables

The bounded continuous-IID result is extended to a measurable `L²`
observable by symmetric 1-Lipschitz clipping.  The clipping does not increase
any coordinate-replacement energy, while its variance converges to the
variance of the original observable by dominated convergence.
-/

open scoped ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace CircularLawSection4

universe u

/-- Symmetric clipping to the interval `[-A,A]`. -/
def symmetricClip (A x : ℝ) : ℝ := max (-A) (min x A)

theorem symmetricClip_lipschitz (A : ℝ) :
    LipschitzWith 1 (symmetricClip A) := by
  exact (LipschitzWith.id.min_const A).const_max (-A)

theorem measurable_symmetricClip (A : ℝ) : Measurable (symmetricClip A) :=
  (symmetricClip_lipschitz A).continuous.measurable

@[simp] theorem symmetricClip_eq_self_of_abs_le {A x : ℝ}
    (_hA : 0 ≤ A) (hx : |x| ≤ A) : symmetricClip A x = x := by
  rw [symmetricClip, min_eq_left (le_trans (le_abs_self x) hx)]
  exact max_eq_right ((neg_le_iff_add_nonneg).2 (by
    linarith [neg_abs_le x]))

theorem abs_symmetricClip_le (A x : ℝ) (hA : 0 ≤ A) :
    |symmetricClip A x| ≤ |x| := by
  by_cases hx : |x| ≤ A
  · rw [symmetricClip_eq_self_of_abs_le hA hx]
  · have hAx : A < |x| := lt_of_not_ge hx
    rcases le_total x A with hle | hge
    · rw [symmetricClip, min_eq_left hle]
      by_cases hlow : -A ≤ x
      · rw [max_eq_right hlow]
      · rw [max_eq_left (le_of_not_ge hlow)]
        simpa [abs_of_nonneg hA] using hAx.le
    · rw [symmetricClip, min_eq_right hge, max_eq_right (by linarith)]
      simpa [abs_of_nonneg hA] using hAx.le

theorem abs_symmetricClip_le_radius (A x : ℝ) (hA : 0 ≤ A) :
    |symmetricClip A x| ≤ A := by
  rw [symmetricClip]
  have hlo : -A ≤ max (-A) (min x A) := le_max_left _ _
  have hhi : max (-A) (min x A) ≤ A :=
    max_le (by linarith) (min_le_right _ _)
  exact abs_le.2 ⟨hlo, hhi⟩

theorem symmetricClip_sub_sq_le (A x y : ℝ) :
    (symmetricClip A x - symmetricClip A y) ^ 2 ≤ (x - y) ^ 2 := by
  have hdist := (symmetricClip_lipschitz A).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hdist
  exact sq_le_sq.mpr hdist

theorem tendsto_symmetricClip_nat (x : ℝ) :
    Tendsto (fun n : ℕ => symmetricClip (n : ℝ) x) atTop (𝓝 x) := by
  apply tendsto_const_nhds.congr'
  have hevent : ∀ᶠ n : ℕ in atTop, |x| < (n : ℝ) :=
    (tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop |x|))
  filter_upwards [hevent] with n hn
  exact (symmetricClip_eq_self_of_abs_le (by positivity) hn.le).symm

section L2Limit

variable {Ω : Type u} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The variance of symmetric clips converges to the variance of a measurable
`L²` observable. -/
theorem tendsto_variance_symmetricClip_nat
    (f : Ω → ℝ) (hf : Measurable f) (hf2 : MemLp f 2 μ) :
    Tendsto (fun n : ℕ => variance (fun x => symmetricClip (n : ℝ) (f x)) μ)
      atTop (𝓝 (variance f μ)) := by
  have hf1 : Integrable f μ := hf2.integrable one_le_two
  have hfsq : Integrable (fun x => f x ^ 2) μ := hf2.integrable_sq
  have hmean : Tendsto
      (fun n : ℕ => ∫ x, symmetricClip (n : ℝ) (f x) ∂μ)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => |f x|)
    · intro n
      exact ((measurable_symmetricClip (n : ℝ)).comp hf).aestronglyMeasurable
    · exact hf1.abs
    · intro n
      exact ae_of_all μ fun x => by
        rw [Real.norm_eq_abs]
        exact abs_symmetricClip_le (n : ℝ) (f x) (by positivity)
    · exact ae_of_all μ fun x => tendsto_symmetricClip_nat (f x)
  have hsquare : Tendsto
      (fun n : ℕ => ∫ x, (symmetricClip (n : ℝ) (f x)) ^ 2 ∂μ)
      atTop (𝓝 (∫ x, f x ^ 2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => f x ^ 2)
    · intro n
      exact (((measurable_symmetricClip (n : ℝ)).comp hf).pow_const 2).aestronglyMeasurable
    · exact hfsq
    · intro n
      exact ae_of_all μ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq.mpr
          (abs_symmetricClip_le (n : ℝ) (f x) (by positivity))
    · exact ae_of_all μ fun x =>
        (tendsto_symmetricClip_nat (f x)).pow 2
  have hformula (n : ℕ) :
      variance (fun x => symmetricClip (n : ℝ) (f x)) μ =
        (∫ x, (symmetricClip (n : ℝ) (f x)) ^ 2 ∂μ) -
          (∫ x, symmetricClip (n : ℝ) (f x) ∂μ) ^ 2 := by
    apply variance_eq_sub
    exact memLp_of_measurable_of_bound
      ((measurable_symmetricClip (n : ℝ)).comp hf) (n : ℝ)
      (fun x => by
        rw [Real.norm_eq_abs]
        exact abs_symmetricClip_le_radius (n : ℝ) (f x) (by positivity)) 2
  have htarget : variance f μ =
      (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 :=
    variance_eq_sub hf2
  rw [htarget]
  convert hsquare.sub (hmean.pow 2) using 1
  ext n
  exact hformula n

end L2Limit

section RawL2

variable {K : Type u} [MeasurableSpace K]
  (ν : Measure K) [SFinite ν] [IsProbabilityMeasure ν]

theorem iidRawResamplingEnergy_symmetricClip_le {n : ℕ}
    (f : (Fin n → K) → ℝ) (hf : Measurable f) (i : Fin n)
    (hinner : ∀ x, Integrable (fun a' =>
      (f x - f (Function.update x i a')) ^ 2) ν)
    (houter : Integrable (fun x => ∫ a',
      (f x - f (Function.update x i a')) ^ 2 ∂ν) (iidMeasure ν n))
    (A : ℝ) (hA : 0 ≤ A) :
    iidRawResamplingEnergy ν (fun x => symmetricClip A (f x)) i ≤
      iidRawResamplingEnergy ν f i := by
  let g : (Fin n → K) → ℝ := fun x => symmetricClip A (f x)
  have hg : Measurable g := (measurable_symmetricClip A).comp hf
  have hgC : ∀ x, ‖g x‖ ≤ A := by
    intro x
    rw [Real.norm_eq_abs]
    exact abs_symmetricClip_le_radius A (f x) hA
  have hinner_le (x : Fin n → K) :
      (∫ a', (g x - g (Function.update x i a')) ^ 2 ∂ν) ≤
        ∫ a', (f x - f (Function.update x i a')) ^ 2 ∂ν := by
    apply integral_mono
      (by
        have hmeas : Measurable (fun a' =>
            (g x - g (Function.update x i a')) ^ 2) := by fun_prop
        exact Integrable.of_bound hmeas.aestronglyMeasurable
          ((2 * |A|) ^ 2) (ae_of_all ν fun a' =>
            norm_sub_sq_le_bound hgC x (Function.update x i a')))
      (hinner x)
    intro a'
    exact symmetricClip_sub_sq_le A (f x) (f (Function.update x i a'))
  unfold iidRawResamplingEnergy
  exact integral_mono (integrable_rawInner ν hg hgC i) houter hinner_le

/-- Standard continuous IID Efron--Stein for measurable `L²` observables.
The explicit integrability hypotheses are precisely those needed to interpret
the iterated raw-coordinate energies as Bochner integrals. -/
theorem variance_iidMeasure_le_half_sum_raw_memLp {n : ℕ}
    (f : (Fin n → K) → ℝ) (hf : Measurable f)
    (hf2 : MemLp f 2 (iidMeasure ν n))
    (hinner : ∀ i x, Integrable (fun a' =>
      (f x - f (Function.update x i a')) ^ 2) ν)
    (houter : ∀ i, Integrable (fun x => ∫ a',
      (f x - f (Function.update x i a')) ^ 2 ∂ν) (iidMeasure ν n)) :
    variance f (iidMeasure ν n) ≤
      (1 / 2 : ℝ) * ∑ i, iidRawResamplingEnergy ν f i := by
  let _ := iidMeasure_isProbability ν n
  have hclip (N : ℕ) :
      variance (fun x => symmetricClip (N : ℝ) (f x)) (iidMeasure ν n) ≤
        (1 / 2 : ℝ) * ∑ i, iidRawResamplingEnergy ν f i := by
    have hmeas : Measurable (fun x => symmetricClip (N : ℝ) (f x)) :=
      (measurable_symmetricClip (N : ℝ)).comp hf
    have hbound : ∀ x, ‖symmetricClip (N : ℝ) (f x)‖ ≤ (N : ℝ) := by
      intro x
      rw [Real.norm_eq_abs]
      exact abs_symmetricClip_le_radius (N : ℝ) (f x) (by positivity)
    refine (variance_iidMeasure_le_half_sum_raw ν _ hmeas (N : ℝ) hbound).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum fun i _ =>
      iidRawResamplingEnergy_symmetricClip_le ν f hf i
        (hinner i) (houter i) (N : ℝ) (by positivity)
  exact le_of_tendsto
    (tendsto_variance_symmetricClip_nat (iidMeasure ν n) f hf hf2)
    (Eventually.of_forall hclip)

/-- Raw-coordinate Efron--Stein for `L²` observables followed by the Section 4
pressure maximal-deviation closure. -/
theorem pressure_maximal_concentration_iid_raw_memLp
    (n W : ℕ) (Y : Fin (2 * W).succ → (Fin n → K) → ℝ)
    (hY : ∀ r, Measurable (Y r))
    (hY2 : ∀ r, MemLp (Y r) 2 (iidMeasure ν n))
    (hinner : ∀ r i x, Integrable (fun a' =>
      (Y r x - Y r (Function.update x i a')) ^ 2) ν)
    (houter : ∀ r i, Integrable (fun x => ∫ a',
      (Y r x - Y r (Function.update x i a')) ^ 2 ∂ν) (iidMeasure ν n))
    {D : ℝ} (hD : ∀ r i, iidRawResamplingEnergy ν (Y r) i ≤ D) :
    (∫ ω, maxCenteredAbs (iidMeasure ν n) Y ω ∂iidMeasure ν n) ≤
      Real.sqrt (((2 * W + 1 : ℕ) : ℝ) *
        ((1 / 2 : ℝ) * (n : ℝ) * D)) := by
  let _ := iidMeasure_isProbability ν n
  apply pressure_maximal_concentration_of_variance W
  · exact hY2
  · intro r
    refine (variance_iidMeasure_le_half_sum_raw_memLp ν (Y r) (hY r)
      (hY2 r) (hinner r) (houter r)).trans ?_
    calc
      (1 / 2 : ℝ) * ∑ i, iidRawResamplingEnergy ν (Y r) i ≤
          (1 / 2 : ℝ) * ∑ _i : Fin n, D := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum fun i _ => hD r i
      _ = (1 / 2 : ℝ) * (n : ℝ) * D := by simp; ring

end RawL2

end CircularLawSection4
