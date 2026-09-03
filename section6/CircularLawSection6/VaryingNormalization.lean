import CircularLawSection6.IteratedSqueeze
import Mathlib.Topology.Order.IsLUB
import Mathlib.MeasureTheory.OuterMeasure.AE

/-! # Varying normalization from a countable dense family

The compact-core radius depends on matrix size. Pointwise fixed-radius
convergence alone does not permit substituting this varying radius. Radial
monotonicity gives the missing squeeze. Only a dense family of fixed radii
is needed, allowing a single full-measure set of spectral parameters.
-/

open Filter Topology Set MeasureTheory

namespace CircularLawSection6

theorem tendsto_varying_radius_of_monotone_dense
    {s : Set ℝ} (hs : Dense s)
    (F : ℕ → ℝ → ℝ) (U : ℝ → ℝ) (radius : ℕ → ℝ) {r : ℝ}
    (hr : 0 < r) (hRadius : Tendsto radius atTop (𝓝 r))
    (hMono : ∀ n, MonotoneOn (F n) (Ioi 0))
    (hFixed : ∀ x ∈ s, 0 < x → Tendsto (fun n => F n x) atTop (𝓝 (U x)))
    (hContinuous : ContinuousAt U r) :
    Tendsto (fun n => F n (radius n)) atTop (𝓝 (U r)) := by
  obtain ⟨lo, _, hlo, hLoLimit⟩ := hs.exists_seq_strictMono_tendsto_of_lt hr
  obtain ⟨hi, _, hhi, hHiLimit⟩ := hs.exists_seq_strictAnti_tendsto_of_lt
    (lt_add_one r)
  apply tendsto_of_iterated_squeeze
    (fun n => F n (radius n)) (fun R n => F n (lo R)) (fun R n => F n (hi R))
    (fun R => U (lo R)) (fun R => U (hi R)) (U r)
  · intro R
    filter_upwards [hRadius.eventually (Ioi_mem_nhds (hlo R).1.2)] with n hn
    exact hMono n (hlo R).1.1 ((hlo R).1.1.trans hn) hn.le
  · intro R
    filter_upwards [hRadius.eventually (Ioi_mem_nhds hr),
      hRadius.eventually (Iio_mem_nhds (hhi R).1.1)] with n hnpos hn
    exact hMono n hnpos (hr.trans (hhi R).1.1) hn.le
  · intro R
    exact hFixed _ (hlo R).2 (hlo R).1.1
  · intro R
    exact hFixed _ (hhi R).2 (hr.trans (hhi R).1.1)
  · exact hContinuous.tendsto.comp hLoLimit
  · exact hContinuous.tendsto.comp hHiLimit

/-- A common full-measure set suffices for all fixed radii in a countable dense
set. The varying radius conclusion therefore preserves the a.e. quantifier;
no uncountable intersection of full-measure sets is taken. -/
theorem ae_tendsto_varying_radius_of_countable_dense
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    {s : Set ℝ} (hs : Dense s) (hCountable : s.Countable)
    (F : Z → ℕ → ℝ → ℝ) (U : Z → ℝ → ℝ) (radius : ℕ → ℝ) {r : ℝ}
    (hr : 0 < r) (hRadius : Tendsto radius atTop (𝓝 r))
    (hMono : ∀ᵐ z ∂μ, ∀ n, MonotoneOn (F z n) (Ioi 0))
    (hFixed : ∀ x ∈ s, ∀ᵐ z ∂μ,
      0 < x → Tendsto (fun n => F z n x) atTop (𝓝 (U z x)))
    (hContinuous : ∀ᵐ z ∂μ, ContinuousAt (U z) r) :
    ∀ᵐ z ∂μ, Tendsto (fun n => F z n (radius n)) atTop (𝓝 (U z r)) := by
  have hTogether : ∀ᵐ z ∂μ, ∀ x ∈ s,
      0 < x → Tendsto (fun n => F z n x) atTop (𝓝 (U z x)) :=
    (ae_ball_iff hCountable).2 hFixed
  filter_upwards [hMono, hTogether, hContinuous] with z hzMono hzFixed hzContinuous
  exact tendsto_varying_radius_of_monotone_dense hs (F z) (U z) radius hr hRadius
    hzMono hzFixed hzContinuous

end CircularLawSection6
