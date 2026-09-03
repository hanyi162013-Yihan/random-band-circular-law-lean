import CircularLawSection6.FlexibleCompactSourceAssembly
import CircularLawSection6.ProfileCompactSourceBridge

/-! # Automatic short-or-long partition for the actual unit-core model

The input model has the prescribed dimension N, not an independently
specified sum of block lengths. A valid partition is constructed and its
dimension equality is eliminated. Local source inputs are only requested
on the window from the band width to twice the chosen mesoscopic size.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

theorem unitCore_cutoff_limit_of_local_inputs_ae (p : NoncompactProfile)
    (N H m₀ d : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hwidth : ∀ n, d n + 2 = 2 * H n + 1)
    (hglobal : ∀ n, d n + 2 ≤ N n)
    (hfitm : ∀ n, 2 * H n + 1 ≤ m₀ n)
    (center : ∀ n, Fin (d n + 1)) (hcenter : ∀ n, (center n).val = H n)
    (W : ℕ → ℝ) (hratio : Tendsto (fun n => (H n : ℝ) / m₀ n) atTop (𝓝 0))
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ σ : Measure ℝ, IsProbabilityMeasure σ →
      (∀ᵐ s ∂σ, 0 ≤ s) → Integrable (fun s : ℝ => s ^ 2) σ →
      (∀ M : ℕ → ℕ+, (∀ n, 2 * H n + 1 ≤ (M n : ℕ) ∧ (M n : ℕ) ≤ 2 * m₀ n) →
        CyclicGinibreCdfInput M H
          (fun n => p.coreRoutedAmplitude (N n) (d n) (H n) (hwidth n) (center n) (W n)) z ∧
        GinibreSquaredTestInput M z σ) →
      Tendsto (fun n => ∫ ω, matrixCutoffPotential
        (p.unitCoreMatrix (N n) (H n) (W n) ω - z • 1) a ∂gaussianProfileLaw (N n))
        atTop (𝓝 (∫ s, Real.log (max s a) ∂σ)) := by
  have hfitN (n : ℕ) : 2 * H n + 1 ≤ N n := (hwidth n).symm.trans_le (hglobal n)
  choose q len hq hsum hsize hmin using
    (fun n => exists_one_or_periodic_block_lengths (hfitN n) (hfitm n))
  letI : ∀ n j, NeZero (len n j) := fun n j => ⟨by have := (hsize n j).1; omega⟩
  have hN : (fun n => ∑ j, len n j) = N := funext hsum
  subst N
  let b (n : ℕ) := p.coreRoutedAmplitude (∑ j, len n j) (d n) (H n) (hwidth n) (center n) (W n)
  have hb (n : ℕ) : ∑ s, ‖b n s‖ ^ 2 = 1 :=
    p.coreRoutedAmplitude_normalized (∑ j, len n j) (d n) (H n) (hwidth n) (hglobal n)
      (center n) (hcenter n) (W n)
  have htransport := ae_all_iff.2 (fun n => p.unitCore_expected_cutoff_eq_fullBlock_ae
    (len n) (d n) (H n) (hwidth n) (hglobal n) (center n) (hcenter n) (W n) circularComplexGaussian)
  filter_upwards [one_or_fullBlock_cutoff_limit_of_section3_inputs_ae q H m₀
    (fun n => 2 * H n + 1) (fun n => 2 * m₀ n) len
    (fun n => by have := hfitm n; omega) hmin (fun n => by omega) (fun n => le_rfl)
    (fun n => by have := hfitm n; omega) hsize b hb hratio ha, htransport] with z hz heq
  intro σ hσ hσpos hσ2 hsource
  apply (hz σ hσ hσpos hσ2 hsource).congr'
  exact Eventually.of_forall fun n => (heq n a ha).symm

end CircularLawSection6.NoncompactProfile
