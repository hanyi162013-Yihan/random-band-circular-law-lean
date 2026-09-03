import BernoulliSection10Source.IIDModels
import BernoulliSection10Complex.ProfileMoments
import ShortRingAnchor.HighBandLSVProbability

/-! # The published planar Theorem 3.1 applied to the actual full-block matrix -/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
noncomputable section
namespace BernoulliSection10Source
open BernoulliSection10 BernoulliSection10.SourceInputs
open ShortRingAnchor Arxiv2410V3 HighBandLSV

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem planarAtomMoments {μ : Measure ℂ} {L : ℝ}
    (hμ : BernoulliSection10Complex.IsPlanarDensityAtom μ L)
    (h3 : Integrable (fun x : ℂ => ‖x‖ ^ 3) μ) :
    AtomMomentAssumption21 μ id :=
  ⟨measurable_id.stronglyMeasurable, hμ.centered, hμ.variance_one, h3⟩

def physicalPlanarBandModel {μ : Measure ℂ} {L : ℝ}
    (hμ : BernoulliSection10Complex.IsPlanarDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) :
    PlanarBandModel ((s + 3) * W) W (1 / 3) 1 L where
  sigma := physicalProfile W s
  sigma_nonneg := physicalProfile_nonnegative W s
  local_floor := by
    intro i j h
    apply physicalProfile_lsv_lower W s hW i j
    simpa only [scalarCyclicDistance, Section5Formalization.cyclicDist, Nat.dist] using h
  upper := fun i j => (entryVariance_le_maxEntryVariance _ i j).trans
    (physicalProfile_lsv_upper W s hW)
  row_normalization := physicalProfile_row W s hW
  atomLaw := fun _ _ => μ
  atom_probability := fun _ _ => hμ.toIsProbabilityMeasure
  atom_density := fun _ _ => hμ.density_le

theorem physicalPlanarBandModel_identDistrib
    {μ : Measure ℂ} {L : ℝ}
    (hμ : BernoulliSection10Complex.IsPlanarDensityAtom μ L)
    (h3 : Integrable (fun x : ℂ => ‖x‖ ^ 3) μ)
    (W s : ℕ) (hW : 0 < W) :
    IdentDistrib
      (BernoulliSection10Complex.SourceInputs.profileMatrix (physicalProfile W s))
      (physicalPlanarBandModel hμ W s hW).matrix
      (BernoulliSection10Complex.SourceInputs.inputLaw μ)
      (physicalPlanarBandModel hμ W s hW).law := by
  letI := hμ.toIsProbabilityMeasure
  let v := profileV3Model μ id (planarAtomMoments hμ h3)
    (physicalProfile W s) (physicalProfile_doublyStochastic W s hW)
  let m := physicalPlanarBandModel hμ W s hW
  apply identDistrib_matrix_of_independent_entries _ _ v.entry_measurable
    (fun i j => by unfold PlanarBandModel.matrix; fun_prop)
    v.entries_independent (planarBandModel_entries_independent m)
  intro i j
  exact (v.entry_law i j).trans
    (planarBandModel_entry_law m id measurable_id (fun _ _ => by simp [m,
      physicalPlanarBandModel]) i j).symm

/-- No LSV, numerical, law-transport or HS-cutoff certificate is an input.
This invokes the proved Section 3 planar theorem on the concrete IID law. -/
theorem physical_planar_minimum_input
    {μ : Measure ℂ} {L : ℝ}
    (hμ : BernoulliSection10Complex.IsPlanarDensityAtom μ L)
    (h3 : Integrable (fun x : ℂ => ‖x‖ ^ 3) μ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n)
    (hN : Tendsto (fun n => (s n + 3) * W n) atTop atTop)
    {χ κ : ℝ} (hχ : 0 < χ) (hχ1 : χ ≤ 1 / 2) (hκ : 0 < κ)
    (hband : ∀ᶠ n in atTop,
      (((s n + 3) * W n : ℕ) : ℝ) ^ (1 / 2 + χ) ≤ W n)
    (z : ℂ) :
    ∃ good, Theorem31MinimumSingularValueInput
      (fun n => Nat.mul_pos (by omega) (hW n))
      (BernoulliSection10Complex.SourceInputs.inputLaw μ)
      (fun n => BernoulliSection10Complex.SourceInputs.profileMatrix (physicalProfile (W n) (s n)))
      z (sourceHardEdgeScale (fun n => (s n + 3) * W n) W κ) good := by
  letI := hμ.toIsProbabilityMeasure
  let N := fun n => (s n + 3) * W n
  let m := fun n => physicalPlanarBandModel hμ (W n) (s n) (hW n)
  have hpos (n) : 0 < N n := Nat.mul_pos (by omega) (hW n)
  have hu : ∀ᶠ n in atTop, (W n : ℝ) ≤ N n := by
    apply Eventually.of_forall
    intro n
    exact_mod_cast Nat.le_mul_of_pos_left (W n) (by omega : 0 < s n + 3)
  apply theorem31MinimumInput_of_truncated_estimate hpos hN _ z hκ
    (D := Real.sqrt (Real.pi * L / (1 / 3)))
    (BernoulliSection10Complex.SourceInputs.profileMatrix_row_moments hμ.normalized
      (fun n => physicalProfile (W n) (s n))
      (fun n => physicalProfile_doublyStochastic (W n) (s n) (hW n)))
  intro R hR
  filter_upwards [eventually_planar_lsv_along_dimensions m hN
    (by norm_num : (0 : ℝ) < 1 / 3) hμ.nonneg hχ hχ1 hκ hR (norm_nonneg z)
    (Eventually.of_forall hW) hband hu] with n hn
  exact (highBand_strict_bad_le_of_identDistrib (hpos n)
    (physicalPlanarBandModel_identDistrib hμ h3 (W n) (s n) (hW n)) z _ R).trans
      (hn z le_rfl _ (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end BernoulliSection10Source
