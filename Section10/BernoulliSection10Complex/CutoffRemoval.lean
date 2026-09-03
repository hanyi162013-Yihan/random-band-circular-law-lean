import BernoulliSection10Complex.ProfileMoments
import ShortRingAnchor.SourceScales

/-!
# Removing the Hilbert--Schmidt cutoff using its actual first moment

The auxiliary cutoff may depend on the desired probability error. This
proves the qualitative removal with only a uniform first moment of the
normalized square energy; no rate or extra moment is inferred.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

theorem measure_tendsto_zero_of_energy_cutoffs
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (bad : ℕ → Set Ω) (E : ℕ → Ω → ℝ)
    (hE : ∀ n ω, 0 ≤ E n ω) (hEi : ∀ n, Integrable (E n) P)
    (hEm : ∀ n, ∫ ω, E n ω ∂P ≤ 1)
    (hrestricted : ∀ R : ℝ, 0 < R →
      Tendsto (fun n => P (bad n ∩ {ω | E n ω ≤ R})) atTop (𝓝 0)) :
    Tendsto (fun n => P (bad n)) atTop (𝓝 0) := by
  rw [← ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let R : ℝ := 4 / ε
  have hR : 0 < R := div_pos (by norm_num) hε
  have hres : Tendsto (fun n => P.real (bad n ∩ {ω | E n ω ≤ R})) atTop (𝓝 0) := by
    exact (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mpr (hrestricted R hR)
  have hsmall := hres.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 2))
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp hsmall
  refine ⟨n0, fun n hn => ?_⟩
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (hE n)) (hEi n) R
  have htail : P.real {ω | R < E n ω} ≤ ε / 4 := by
    have hsub : P.real {ω | R < E n ω} ≤ P.real {ω | R ≤ E n ω} :=
      measureReal_mono (μ := P) (fun ω (h : R < E n ω) => h.le)
    have hm := mul_le_mul_of_nonneg_left hsub hR.le
    have hidentity : R * (ε / 4) = 1 := by dsimp [R]; field_simp
    nlinarith [hEm n]
  have hcover : bad n ⊆ (bad n ∩ {ω | E n ω ≤ R}) ∪ {ω | R < E n ω} := by
    intro ω hω
    by_cases he : E n ω ≤ R
    · exact Or.inl ⟨hω, he⟩
    · exact Or.inr (lt_of_not_ge he)
  have hb := (measureReal_mono (μ := P) hcover).trans
    (measureReal_union_le (μ := P) _ _)
  change dist (P.real (bad n)) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  linarith [hn0 n hn]

theorem exp_neg_sourceHardEdgeScale
    (N W : ℕ → ℕ) (κ : ℝ) (n : ℕ) (hN : 0 < N n) :
    Real.exp (-(ShortRingAnchor.sourceHardEdgeScale N W κ n)) =
      (N n : ℝ) ^ (-2 : ℝ) *
        Real.exp (-((N n : ℝ) ^ (3 * κ) * N n / W n)) := by
  have hNp : (0 : ℝ) < N n := Nat.cast_pos.mpr hN
  have hr : (N n : ℝ) ^ (1 + 3 * κ) = (N n : ℝ) ^ (3 * κ) * N n := by
    rw [add_comm 1, Real.rpow_add_one hNp.ne']
  rw [ShortRingAnchor.sourceHardEdgeScale, hr, Real.rpow_def_of_pos hNp (-2),
    ← Real.exp_add]
  congr 1
  ring

end BernoulliSection10Complex
