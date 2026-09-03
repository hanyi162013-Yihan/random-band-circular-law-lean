import BernoulliSection10Source.IIDModels
import BernoulliSection10Source.DensityRepresentative
import BernoulliSection10.ProfileMoments
import ShortRingAnchor.CyclicRealHighBandModel
import ShortRingAnchor.HighBandRealLSVProbability

/-!
# The published real Theorem 3.1 applied to the actual full-block matrix

Geometric Brascamp--Lieb is the explicitly accepted literature premise.
The density representative and all matrix-law certificates are constructed.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
noncomputable section
namespace BernoulliSection10Source
open BernoulliSection10 BernoulliSection10.SourceInputs
open ShortRingAnchor Arxiv2410V3 HighBandLSV LivshytsProjectionFormalization

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem realAtomMoments {μ : Measure ℝ} {L : ℝ}
    (hμ : BernoulliSection10.IsBoundedDensityAtom μ L)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ) :
    AtomMomentAssumption21 μ Complex.ofReal := by
  refine ⟨Complex.measurable_ofReal.stronglyMeasurable, ?_, ?_, ?_⟩
  · simpa only [integral_complex_ofReal, hμ.centered, Complex.ofReal_zero]
  · simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hμ.variance_one
  · simpa only [Complex.norm_real, Real.norm_eq_abs] using h3

def physicalRealBandModel
    {ρ : ℝ} (f : ℝ → ℝ≥0∞) (hf : Measurable f) (hint : ∫⁻ x, f x = 1)
    (hbound : ∀ x, f x ≤ ENNReal.ofReal ρ)
    (W s : ℕ) (hW : 0 < W) :
    RealBandModel ((s + 3) * W) W (1 / 3) 1 ρ where
  sigma := physicalProfile W s
  sigma_nonneg := physicalProfile_nonnegative W s
  local_floor := by
    intro i j h
    apply physicalProfile_lsv_lower W s hW i j
    simpa only [scalarCyclicDistance, Section5Formalization.cyclicDist, Nat.dist] using h
  variance_upper := fun i j => (entryVariance_le_maxEntryVariance _ i j).trans
    (physicalProfile_lsv_upper W s hW)
  row_normalization := physicalProfile_row W s hW
  density := fun _ => ⟨fun _ => f, fun _ => hf, fun _ => hint, fun _ => hbound⟩

theorem physicalRealBandModel_identDistrib
    {μ : Measure ℝ} {L ρ : ℝ}
    (hμ : BernoulliSection10.IsBoundedDensityAtom μ L)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) (hint : ∫⁻ x, f x = 1)
    (hbound : ∀ x, f x ≤ ENNReal.ofReal ρ) (hlaw : volume.withDensity f = μ)
    (W s : ℕ) (hW : 0 < W) :
    IdentDistrib (profileMatrix (physicalProfile W s))
      (physicalRealBandModel f hf hint hbound W s hW).matrix
      (inputLaw μ) (physicalRealBandModel f hf hint hbound W s hW).law := by
  letI := hμ.toIsProbabilityMeasure
  let v := profileV3Model μ Complex.ofReal (realAtomMoments hμ h3)
    (physicalProfile W s) (physicalProfile_doublyStochastic W s hW)
  let m := physicalRealBandModel f hf hint hbound W s hW
  have hraw : IdentDistrib v.matrix m.matrix (sampleLaw μ) m.law := by
    apply identDistrib_matrix_of_independent_entries _ _ v.entry_measurable
      (fun i j => by unfold RealBandModel.matrix; fun_prop)
      v.entries_independent (realBandModel_entries_independent m)
    intro i j
    exact (v.entry_law i j).trans
      (realBandModel_entry_law m Complex.ofReal Complex.measurable_ofReal
        (ae_of_all _ fun _ => rfl)
        (fun _ _ => by simpa [m, physicalRealBandModel, RealBandModel.atomLaw] using hlaw)
        i j).symm
  change IdentDistrib (actualProfileMatrix Complex.ofReal (physicalProfile W s))
    m.matrix (sampleLaw μ) m.law at hraw
  simpa only [actualProfileMatrix, profileMatrix, Complex.ofReal_mul, sampleLaw, inputLaw] using hraw

/-- The real source LSV conclusion. Its only non-model mathematical input
is the explicitly named geometric Brascamp--Lieb theorem. -/
theorem physical_real_minimum_input
    {μ : Measure ℝ} {L : ℝ}
    (hμ : BernoulliSection10.IsBoundedDensityAtom μ L)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hGBL : RealFiniteGeometricBrascampLieb)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n)
    (hN : Tendsto (fun n => (s n + 3) * W n) atTop atTop)
    {χ κ : ℝ} (hχ : 0 < χ) (hχ1 : χ ≤ 1 / 2) (hκ : 0 < κ)
    (hband : ∀ᶠ n in atTop,
      (((s n + 3) * W n : ℕ) : ℝ) ^ (1 / 2 + χ) ≤ W n)
    (z : ℂ) :
    ∃ good, Theorem31MinimumSingularValueInput
      (fun n => Nat.mul_pos (by omega) (hW n)) (inputLaw μ)
      (fun n => profileMatrix (physicalProfile (W n) (s n)))
      z (sourceHardEdgeScale (fun n => (s n + 3) * W n) W κ) good := by
  letI := hμ.toIsProbabilityMeasure
  obtain ⟨ρ, hρ, f, hf, hint, hbound, hlaw⟩ := exists_real_density_representative hμ.density_le
  let N := fun n => (s n + 3) * W n
  let m := fun n => physicalRealBandModel f hf hint hbound (W n) (s n) (hW n)
  have hpos (n) : 0 < N n := Nat.mul_pos (by omega) (hW n)
  have hu : ∀ᶠ n in atTop, (W n : ℝ) ≤ N n := by
    apply Eventually.of_forall
    intro n
    exact_mod_cast Nat.le_mul_of_pos_left (W n) (by omega : 0 < s n + 3)
  apply theorem31MinimumInput_of_truncated_estimate hpos hN _ z hκ
    (D := 2 * Real.sqrt 2 * Real.exp 1 * ρ / Real.sqrt (1 / 3))
    (profileMatrix_row_moments hμ (fun n => physicalProfile (W n) (s n))
      (fun n => physicalProfile_doublyStochastic (W n) (s n) (hW n)))
  intro R hR
  filter_upwards [eventually_real_lsv_along_dimensions m hGBL hN
    (by norm_num : (0 : ℝ) < 1 / 3) hρ hχ hχ1 hκ hR (norm_nonneg z)
    (Eventually.of_forall hW) hband hu] with n hn
  exact (highBand_strict_bad_le_of_identDistrib (hpos n)
    (physicalRealBandModel_identDistrib hμ h3 f hf hint hbound hlaw (W n) (s n) (hW n))
    z _ R).trans (hn z le_rfl _ (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end BernoulliSection10Source
