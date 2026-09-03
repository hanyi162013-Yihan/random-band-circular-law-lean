import ShortRingAnchor.Proposition38.AtomMoments
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Proposition 3.8: the atom is spread in Cook's sense

Cook 1.12 uses a fixed finite spread parameter. This is not assumed here:
truncating a centered variance-one atom on `|x| ≤ n` gives variances tending
to one. The argument only needs the first two integrable moments; the
subgaussian hypothesis supplies these internally.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace ShortRingAnchor.Proposition38

def CookSpread (A : Atom) (κ : ℝ) : Prop :=
  1 ≤ κ ∧ κ⁻¹ ≤
    (∫ x : ℝ in {x | |x| ≤ κ}, x ^ 2 ∂A.law) -
      (∫ x : ℝ in {x | |x| ≤ κ}, x ∂A.law) ^ 2

/-- Cook Definition 1.1, used in Proposition 3.8: the displayed truncated
second moment minus squared mean is exactly the truncated variance. -/
theorem truncated_variance_eq (A : Atom) (κ : ℝ) :
    variance (({x : ℝ | |x| ≤ κ}).indicator (fun x => x)) A.law =
      (∫ x : ℝ in {x | |x| ≤ κ}, x ^ 2 ∂A.law) -
        (∫ x : ℝ in {x | |x| ≤ κ}, x ∂A.law) ^ 2 := by
  have hs : MeasurableSet {x : ℝ | |x| ≤ κ} :=
    measurableSet_le measurable_id.abs measurable_const
  rw [variance_eq_sub ((A.subgaussian.memLp 2).indicator hs), integral_indicator hs]
  congr 1
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : |x| ≤ κ <;> simp [Set.indicator_apply, hx]

/-- Proposition 3.8, Cook atom hypothesis: expanding bounded truncations
exhaust the real line and preserve each integrable moment in the limit. -/
theorem integral_bounded_truncation_tendsto (A : Atom) (f : ℝ → ℝ)
    (hf : Integrable f A.law) :
    Tendsto (fun n : ℕ => ∫ x : ℝ in {x | |x| ≤ (n : ℝ)}, f x ∂A.law)
      atTop (𝓝 (∫ x : ℝ, f x ∂A.law)) := by
  have hs : ∀ n : ℕ, MeasurableSet {x : ℝ | |x| ≤ (n : ℝ)} := by
    intro n
    exact measurableSet_le measurable_id.abs measurable_const
  have hm : Monotone (fun n : ℕ => {x : ℝ | |x| ≤ (n : ℝ)}) := by
    intro n m hnm x hx
    change |x| ≤ (n : ℝ) at hx
    change |x| ≤ (m : ℝ)
    exact hx.trans (by exact_mod_cast hnm)
  have hu : (⋃ n : ℕ, {x : ℝ | |x| ≤ (n : ℝ)}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact Set.mem_iUnion.mpr ⟨n, hn.le⟩
  simpa only [hu, Measure.restrict_univ] using
    tendsto_setIntegral_of_monotone hs hm hf.integrableOn

/-- Proposition 3.8, Cook atom hypothesis: no spread interface is needed.
Every allowed atom has some fixed finite Cook spread parameter. -/
theorem Atom.exists_cookSpread (A : Atom) : ∃ κ : ℝ, CookSpread A κ := by
  have hfirst : Integrable (fun x : ℝ => x) A.law := A.subgaussian.integrable
  have hsecond : Integrable (fun x : ℝ => x ^ 2) A.law := by
    simpa only [Real.norm_eq_abs, sq_abs] using A.integrable_norm_pow 2
  have hm := integral_bounded_truncation_tendsto A (fun x => x) hfirst
  have hs := integral_bounded_truncation_tendsto A (fun x => x ^ 2) hsecond
  rw [A.centered] at hm
  rw [A.second_moment] at hs
  have hv : Tendsto (fun n : ℕ =>
      (∫ x : ℝ in {x | |x| ≤ (n : ℝ)}, x ^ 2 ∂A.law) -
        (∫ x : ℝ in {x | |x| ≤ (n : ℝ)}, x ∂A.law) ^ 2) atTop (𝓝 1) := by
    simpa using hs.sub (hm.pow 2)
  obtain ⟨n, hn, hvn⟩ := ((eventually_ge_atTop (2 : ℕ)).and
    (hv.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))).exists
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨n, by linarith, ?_⟩
  have hi : (n : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hnR
  exact hi.trans (by norm_num at hvn ⊢; exact hvn.le)

end ShortRingAnchor.Proposition38
