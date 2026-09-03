import CircularLawSection6.UnequalGinibreCutoff
import CircularLawSection6.AutomaticCorePartition
import CircularLawSection6.QuadraticBlockScale

/-! # Local finite CDF comparison with a moving Ginibre reference

Subtract the ambient Ginibre expectation before taking block averages.
The reference therefore need not have a separately supplied singular-law
limit. All exceptional sets are chosen before arbitrary block selections.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5
open CircularLawSections56.Section5.PublishedSection3Concrete (BBVComparisonInput)
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

attribute [local instance 2000] CircularLawSection6.complexMatrixMeasurableSpace
  CircularLawSection6.complexMatrixBorelSpace

theorem cyclicBlock_moving_ginibre_of_cdf_ae
    (hBBV : BBVComparisonInput) (N : ℕ → ℕ+) (hN : Tendsto (fun n => (N n : ℕ)) atTop atTop)
    (H lo hi : ℕ → ℕ) (hlo : ∀ n, 0 < lo n) (hloLim : Tendsto lo atTop atTop)
    (hfit : ∀ n, 2 * H n + 1 ≤ lo n)
    (b : ∀ n, Fin (2 * H n + 1) → ℂ) (hb : ∀ n, ∑ s, ‖b n s‖ ^ 2 = 1) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      (∀ M : ℕ → ℕ+, (∀ n, lo n ≤ (M n : ℕ) ∧ (M n : ℕ) ≤ hi n) →
        CyclicGinibreCdfInput M H b z) →
      ∀ a : ℝ, 0 < a → ∀ m : ℕ → ℕ,
        (∀ n, lo n ≤ m n ∧ m n ≤ hi n) →
        Tendsto (fun n => cyclicBlockExpectedCutoff (m n) (H n) (b n) circularComplexGaussian z a -
          ∫ ω, matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) a
            ∂cyclicAtomLaw (N n) circularComplexGaussian) atTop (𝓝 0) := by
  have hdA : ∀ᵐ z ∂(volume : Measure ℂ), ∀ n (m : ℕ+),
      ∀ᵐ ω ∂Measure.pi (fun _ : Fin (m : ℕ) × Fin (2 * H n + 1) => circularComplexGaussian),
        (routedBandMatrix (cyclicFinSlot (N := (m : ℕ)) (H n)) (b n) ω - z • 1).det ≠ 0 :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (fun m => ae_shifted_matrix_det_ne_zero _
      (routedBandMatrix (cyclicFinSlot (N := (m : ℕ)) (H n)) (b n)) (routedBandMatrix_measurable _ _)))
  have hdB : ∀ᵐ z ∂(volume : Measure ℂ), ∀ m : ℕ+,
      ∀ᵐ ω ∂cyclicAtomLaw (m : ℕ) circularComplexGaussian, (ginibreMatrix (m : ℕ) ω - z • 1).det ≠ 0 :=
    ae_all_iff.2 (fun m => ae_shifted_matrix_det_ne_zero _ (ginibreMatrix (m : ℕ)) (ginibreMatrix_measurable _))
  filter_upwards [hdA, hdB, unequal_ginibre_cutoff_of_bbv_ae hBBV] with z hzA hzB hzG
  intro hsource a ha m hm
  let M (n : ℕ) : ℕ+ := ⟨m n, (hlo n).trans_le (hm n).1⟩
  let μ (n : ℕ) := Measure.pi (fun _ : Fin (M n : ℕ) × Fin (2 * H n + 1) => circularComplexGaussian)
  let ν (n : ℕ) := cyclicAtomLaw (M n) circularComplexGaussian
  let A (n : ℕ) := routedBandMatrix (cyclicFinSlot (N := (M n : ℕ)) (H n)) (b n)
  have hA (n : ℕ) := routedBandMatrix_measurable (cyclicFinSlot (N := (M n : ℕ)) (H n)) (b n)
  have henergy (n : ℕ) := routedBand_expected_energy (cyclicFinSlot (N := (M n : ℕ)) (H n))
    (cyclicFinSlot_injective ((hfit n).trans (hm n).1)) (b n) (hb n)
    circularComplexGaussian circularComplexGaussian_sq_integrable circularComplexGaussian_secondMoment
  have heA (n : ℕ) := expected_shifted_scaled_energy_le (μ n) (A n) (hA n)
    (henergy n).1 (henergy n).2 (1 : ℂ) z
  simp only [one_smul, norm_one, one_pow, mul_one] at heA
  have hcmp := matrixCutoff_expectation_difference_of_coupled_cdf μ ν (fun n => (μ n).prod (ν n))
    (fun _ => Prod.fst) (fun _ => Prod.snd) (fun _ => measurePreserving_fst) (fun _ => measurePreserving_snd)
    (fun n ω => A n ω - z • 1) (fun n ω => ginibreMatrix (M n) ω - z • 1)
    (fun n => (hA n).sub measurable_const) (fun n => (ginibreMatrix_measurable (M n)).sub measurable_const)
    (fun n => hzA n (M n)) (fun n => hzB (M n))
    (fun n => (heA n).1) (fun n => (ginibre_shifted_expected_energy (M n) z).1)
    (2 + 2 * ‖z‖ ^ 2) (2 + 2 * ‖z‖ ^ 2) (fun n => (heA n).2)
    (fun n => by simpa only [ZMod.card] using (ginibre_shifted_expected_energy (M n) z).2)
    (hsource M hm) ha
  have hM : Tendsto (fun n => (M n : ℕ)) atTop atTop :=
    tendsto_atTop_mono (fun n => (hm n).1) hloLim
  have hlim := hcmp.add (hzG M N hM hN a ha)
  dsimp only [ν] at hlim
  simp only [sub_add_sub_cancel, add_zero] at hlim
  apply hlim.congr'
  apply Eventually.of_forall
  intro n
  let : NeZero (m n) := ⟨((hlo n).trans_le (hm n).1).ne'⟩
  exact congrArg (fun x => x - ∫ ω, matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) a
    ∂cyclicAtomLaw (N n) circularComplexGaussian)
    (cyclicBlockExpectedCutoff_eq (m n) (H n) (b n) circularComplexGaussian z a).symm

/-- A moving scalar is subtracted inside each block before applying the
existing all-selections theorem with the fixed target zero. -/
theorem periodicBlock_moving_cutoff_of_all_lengths
    (q H lo hi : ℕ → ℕ) (len : ∀ n, Fin (q n) → ℕ)
    [∀ n j, NeZero (len n j)] [∀ n, NeZero (∑ j, len n j)]
    (hwindow : ∀ n, lo n ≤ hi n)
    (hsize : ∀ n j, lo n ≤ len n j ∧ len n j ≤ hi n)
    (hfit : ∀ n j, 2 * H n + 1 ≤ len n j)
    (b : ∀ n, Fin (2 * H n + 1) → ℂ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ g : ℕ → ℝ,
      (∀ m : ℕ → ℕ, (∀ n, lo n ≤ m n ∧ m n ≤ hi n) →
        Tendsto (fun n => cyclicBlockExpectedCutoff (m n) (H n) (b n) ν z a - g n) atTop (𝓝 0)) →
      Tendsto (fun n => (∫ ω, matrixCutoffPotential
        (routedBandMatrix (periodicBlockRoute (len n) (H n)) (b n) ω - z • 1) a
          ∂Measure.pi (fun _ : ((j : Fin (q n)) × Fin (len n j)) × Fin (2 * H n + 1) => ν)) - g n)
        atTop (𝓝 0) := by
  have hall := ae_all_iff.2 (fun n =>
    periodicBlockMatrix_expected_cutoff_average_ae (len n) (hfit n) (b n) ν hInt)
  filter_upwards [hall] with z hz
  intro g hchoice
  have havg := block_average_tendsto_of_all_lengths
    (fun n m => cyclicBlockExpectedCutoff m (H n) (b n) ν z a - g n)
    lo hi hwindow (fun n => ∑ j, len n j) q (fun n => NeZero.pos _) len (fun _ => rfl)
    hsize 0 hchoice
  apply havg.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul,
    dimension_weights_sum_one (len n) (NeZero.pos _) rfl, one_mul, (hz n a ha).2]
  congr 1
  simp_rw [cyclicBlockExpectedCutoff_eq]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem one_or_fullBlock_moving_cutoff_of_all_lengths
    (q H m₀ lo hi : ℕ → ℕ) (len : ∀ n, Fin (q n) → ℕ)
    [∀ n j, NeZero (len n j)] [∀ n, NeZero (∑ j, len n j)]
    (hm₀ : ∀ n, 0 < m₀ n)
    (hmin : ∀ n, q n = 1 ∨ ∀ j, m₀ n ≤ len n j)
    (hwindow : ∀ n, lo n ≤ hi n)
    (hsize : ∀ n j, lo n ≤ len n j ∧ len n j ≤ hi n)
    (hfit : ∀ n j, 2 * H n + 1 ≤ len n j)
    (b : ∀ n, Fin (2 * H n + 1) → ℂ) (hb : ∀ n, ∑ s, ‖b n s‖ ^ 2 = 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hMoment : (∫ u : ℂ, ‖u‖ ^ 2 ∂ν) = 1)
    (hratio : Tendsto (fun n => (H n : ℝ) / m₀ n) atTop (𝓝 0))
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ g : ℕ → ℝ,
      (∀ m : ℕ → ℕ, (∀ n, lo n ≤ m n ∧ m n ≤ hi n) →
        Tendsto (fun n => cyclicBlockExpectedCutoff (m n) (H n) (b n) ν z a - g n) atTop (𝓝 0)) →
      Tendsto (fun n => (∫ ω, matrixCutoffPotential
        (routedBandMatrix (fullBlockRoute (len n) (H n)) (b n) ω - z • 1) a
          ∂Measure.pi (fun _ : ((j : Fin (q n)) × Fin (len n j)) × Fin (2 * H n + 1) => ν)) - g n)
        atTop (𝓝 0) := by
  let : ∀ n, Nonempty ((j : Fin (q n)) × Fin (len n j)) := fun n =>
    Fintype.card_pos_iff.mp (by
      simpa only [Fintype.card_sigma, Fintype.card_fin] using NeZero.pos (∑ j, len n j))
  let μ (n : ℕ) := Measure.pi
    (fun _ : ((j : Fin (q n)) × Fin (len n j)) × Fin (2 * H n + 1) => ν)
  let A (n : ℕ) := routedBandMatrix (fullBlockRoute (len n) (H n)) (b n)
  let B (n : ℕ) := routedBandMatrix (periodicBlockRoute (len n) (H n)) (b n)
  have hA (n : ℕ) : Measurable (A n) := routedBandMatrix_measurable _ _
  have hdet := ae_all_iff.2 (fun n => ae_shifted_matrix_det_ne_zero (μ n) (A n) (hA n))
  have hper := periodicBlock_moving_cutoff_of_all_lengths q H lo hi len hwindow hsize hfit b ν hInt ha
  have hmean := ae_all_iff.2 (fun n =>
    periodicBlockMatrix_expected_cutoff_average_ae (len n) (hfit n) (b n) ν hInt)
  have herr := ae_all_iff.2 (fun n => one_or_periodicization_expected_cutoff_ae (len n) (hm₀ n)
    (hmin n) (hfit n) (b n) (hb n) ν hInt hMoment)
  have hrate : Tendsto (fun n => Real.sqrt (8 * (H n : ℝ) / m₀ n) / a) atTop (𝓝 0) := by
    simpa only [← mul_div_assoc, mul_zero, Real.sqrt_zero, zero_div] using
      (hratio.const_mul 8).sqrt.div_const a
  filter_upwards [hdet, hper, hmean, herr] with z hz hp hm he
  intro g hchoice
  have hbound (n : ℕ) :
      |(∫ ω, matrixCutoffPotential (A n ω - z • 1) a ∂μ n) -
        ∫ ω, matrixCutoffPotential (B n ω - z • 1) a ∂μ n| ≤
          Real.sqrt (8 * (H n : ℝ) / m₀ n) / a := by
    have hBi : Integrable (fun ω => matrixCutoffPotential (B n ω - z • 1) a) (μ n) := (hm n a ha).1
    have hAm := aestronglyMeasurable_matrixCutoffPotential (μ n) (fun ω => A n ω - z • 1)
      ((hA n).sub measurable_const) (hz n) ha
    have hd : Integrable (fun ω => matrixCutoffPotential (A n ω - z • 1) a -
        matrixCutoffPotential (B n ω - z • 1) a) (μ n) := by
      apply (integrable_norm_iff (hAm.sub hBi.aestronglyMeasurable)).mp
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using (he n a ha).1
    have hAi : Integrable (fun ω => matrixCutoffPotential (A n ω - z • 1) a) (μ n) := by
      apply (hd.add hBi).congr
      filter_upwards with ω
      exact sub_add_cancel _ _
    rw [← integral_sub hAi hBi]
    exact abs_integral_le_integral_abs.trans (he n a ha).2
  have hdiff : Tendsto (fun n => (∫ ω, matrixCutoffPotential (A n ω - z • 1) a ∂μ n) -
      ∫ ω, matrixCutoffPotential (B n ω - z • 1) a ∂μ n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by simpa only [Real.norm_eq_abs] using hbound n) hrate
  have hlim := hdiff.add (hp g hchoice)
  dsimp only [A, B, μ] at hlim
  simpa only [sub_add_sub_cancel, add_zero] using hlim

namespace NoncompactProfile

/-- The actual unit core is compared directly with ambient Ginibre.
Only finite local CDF comparisons remain as the local Section 3 input. -/
theorem unitCore_cutoff_comparison_of_local_cdf_ae (p : NoncompactProfile)
    (hBBV : BBVComparisonInput)
    (N H m₀ d : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (hH : Tendsto H atTop atTop)
    (hwidth : ∀ n, d n + 2 = 2 * H n + 1)
    (hglobal : ∀ n, d n + 2 ≤ N n)
    (hfitm : ∀ n, 2 * H n + 1 ≤ m₀ n)
    (center : ∀ n, Fin (d n + 1)) (hcenter : ∀ n, (center n).val = H n)
    (W : ℕ → ℝ) (hratio : Tendsto (fun n => (H n : ℝ) / m₀ n) atTop (𝓝 0))
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      (∀ M : ℕ → ℕ+, (∀ n, 2 * H n + 1 ≤ (M n : ℕ) ∧ (M n : ℕ) ≤ 2 * m₀ n) →
        CyclicGinibreCdfInput M H
          (fun n => p.coreRoutedAmplitude (N n) (d n) (H n) (hwidth n) (center n) (W n)) z) →
      Tendsto (fun n =>
        (∫ ω, matrixCutoffPotential (p.unitCoreMatrix (N n) (H n) (W n) ω - z • 1) a
          ∂gaussianProfileLaw (N n)) -
        ∫ ω, matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) a
          ∂cyclicAtomLaw (N n) circularComplexGaussian) atTop (𝓝 0) := by
  have hfitN (n : ℕ) : 2 * H n + 1 ≤ N n := (hwidth n).symm.trans_le (hglobal n)
  choose q len hq hsum hsize hmin using
    (fun n => exists_one_or_periodic_block_lengths (hfitN n) (hfitm n))
  let : ∀ n j, NeZero (len n j) := fun n j => ⟨by have := (hsize n j).1; omega⟩
  have hNeq : (fun n => ∑ j, len n j) = N := funext hsum
  subst N
  let b (n : ℕ) := p.coreRoutedAmplitude (∑ j, len n j) (d n) (H n) (hwidth n) (center n) (W n)
  have hb (n : ℕ) : ∑ s, ‖b n s‖ ^ 2 = 1 :=
    p.coreRoutedAmplitude_normalized (∑ j, len n j) (d n) (H n) (hwidth n) (hglobal n)
      (center n) (hcenter n) (W n)
  have hloLim : Tendsto (fun n => 2 * H n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by omega) hH
  have hlocal := cyclicBlock_moving_ginibre_of_cdf_ae hBBV
    (fun n => ⟨∑ j, len n j, NeZero.pos _⟩) hN H
    (fun n => 2 * H n + 1) (fun n => 2 * m₀ n) (fun n => by omega) hloLim
    (fun _ => le_rfl) b hb
  have hfull := one_or_fullBlock_moving_cutoff_of_all_lengths q H m₀
    (fun n => 2 * H n + 1) (fun n => 2 * m₀ n) len
    (fun n => by have := hfitm n; omega) hmin
    (fun n => by have := hfitm n; omega) hsize
    (fun n j => (hsize n j).1) b hb circularComplexGaussian
    circularComplexGaussian_sq_integrable circularComplexGaussian_secondMoment hratio ha
  have htransport := ae_all_iff.2 (fun n => p.unitCore_expected_cutoff_eq_fullBlock_ae
    (len n) (d n) (H n) (hwidth n) (hglobal n) (center n) (hcenter n) (W n) circularComplexGaussian)
  filter_upwards [hlocal, hfull, htransport] with z hl hf heq
  intro hsource
  let g (n : ℕ) : ℝ := ∫ ω, matrixCutoffPotential
    (ginibreMatrix (∑ j, len n j) ω - z • 1) a
      ∂cyclicAtomLaw (∑ j, len n j) circularComplexGaussian
  have hlim := hf g (hl hsource a ha)
  apply hlim.congr'
  exact Eventually.of_forall fun n => congrArg (fun x : ℝ => x - g n) (heq n a ha).symm

/-- Restore the initial non-fitting prefix after applying the moving
reference comparison to the canonical quadratic block partition. -/
theorem canonical_core_cutoff_comparison_of_local_cdf (p : NoncompactProfile)
    (hBBV : BBVComparisonInput)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (N n : ℝ)) atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R)
    (hlocal : ∀ K : ℕ, ∀ hH : ∀ n, 0 < ⌊R * W (n + K)⌋₊,
      (∀ n, 2 * ⌊R * W (n + K)⌋₊ + 1 ≤ N (n + K)) →
      ∀ᵐ z ∂(volume : Measure ℂ), ∀ M : ℕ → ℕ+,
        (∀ n, 2 * ⌊R * W (n + K)⌋₊ + 1 ≤ (M n : ℕ) ∧
          (M n : ℕ) ≤ 2 * quadraticBlockScale ⌊R * W (n + K)⌋₊) →
        CyclicGinibreCdfInput M (fun n => ⌊R * W (n + K)⌋₊)
          (fun n => p.coreRoutedAmplitude (N (n + K))
            (canonicalCoreBand ⌊R * W (n + K)⌋₊) ⌊R * W (n + K)⌋₊
            (canonicalCoreBand_width (hH n)) (canonicalCoreCenter _ (hH n)) (W (n + K))) z)
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n =>
        (∫ ω, matrixCutoffPotential (p.unitCoreMatrix (N n) ⌊R * W n⌋₊ (W n) ω - z • 1) a
          ∂gaussianProfileLaw (N n)) -
        ∫ ω, matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) a
          ∂cyclicAtomLaw (N n) circularComplexGaussian) atTop (𝓝 0) := by
  have hgeom := canonical_floor_core_eventually_fits N hN W hW hWlim hsparse hR
  obtain ⟨K, hK⟩ := eventually_atTop.1 hgeom
  have hH (n : ℕ) : 0 < ⌊R * W (n + K)⌋₊ := (hK (n + K) (by omega)).1
  have hfit (n : ℕ) : 2 * ⌊R * W (n + K)⌋₊ + 1 ≤ N (n + K) := by
    have h := (hK (n + K) (by omega)).2
    rwa [canonicalCoreBand_width (hH n)] at h
  have hHlim := floor_radius_atTop _ (hWlim.comp (tendsto_add_atTop_nat K)) hR
  have hcore := p.unitCore_cutoff_comparison_of_local_cdf_ae hBBV
    (fun n => N (n + K)) (fun n => ⌊R * W (n + K)⌋₊)
    (fun n => quadraticBlockScale ⌊R * W (n + K)⌋₊)
    (fun n => canonicalCoreBand ⌊R * W (n + K)⌋₊)
    (hN.comp (tendsto_add_atTop_nat K)) hHlim
    (fun n => canonicalCoreBand_width (hH n))
    (fun n => (canonicalCoreBand_width (hH n)).trans_le (hfit n))
    (fun n => quadraticBlockScale_fits _)
    (fun n => canonicalCoreCenter _ (hH n)) (fun n => rfl)
    (fun n => W (n + K)) (quadraticBlockScale_ratio_tendsto _ hHlim) ha
  filter_upwards [hcore, hlocal K hH hfit] with z hc hl
  exact (tendsto_add_atTop_iff_nat K).mp (hc hl)

end NoncompactProfile
end CircularLawSection6
