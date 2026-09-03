import CircularLawSection6.FlexiblePeriodicization
import CircularLawSection6.PeriodicCutoffLimit

/-! # Cutoff averaging for arbitrary admissible windows and a direct branch

The one-block branch has zero coupling cost. In the multi-block branch
the original mesoscopic lower bound controls the boundary error. The
admissible source window can therefore include dimensions below that scale.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem periodicBlock_expected_cutoff_limit_of_interval_lengths
    (q H lo hi : ℕ → ℕ) (len : ∀ n, Fin (q n) → ℕ)
    [∀ n b, NeZero (len n b)] [∀ n, NeZero (∑ b, len n b)]
    (hwindow : ∀ n, lo n ≤ hi n)
    (hsize : ∀ n b, lo n ≤ len n b ∧ len n b ≤ hi n)
    (hfit : ∀ n b, 2 * H n + 1 ≤ len n b)
    (b : ∀ n, Fin (2 * H n + 1) → ℂ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ target : ℝ,
      (∀ m : ℕ → ℕ, (∀ n, lo n ≤ m n ∧ m n ≤ hi n) →
        Tendsto (fun n => cyclicBlockExpectedCutoff (m n) (H n) (b n) ν z a)
          atTop (𝓝 target)) →
      Tendsto (fun n => ∫ ω, matrixCutoffPotential
        (routedBandMatrix (periodicBlockRoute (len n) (H n)) (b n) ω - z • 1) a
          ∂Measure.pi (fun _ : ((j : Fin (q n)) × Fin (len n j)) × Fin (2 * H n + 1) => ν))
        atTop (𝓝 target) := by
  have hall := ae_all_iff.2 (fun n =>
    periodicBlockMatrix_expected_cutoff_average_ae (len n) (hfit n) (b n) ν hInt)
  filter_upwards [hall] with z hz
  intro target hchoice
  have havg := block_average_tendsto_of_all_lengths
    (fun n m => cyclicBlockExpectedCutoff m (H n) (b n) ν z a)
    lo hi hwindow
    (fun n => ∑ j, len n j) q (fun n => NeZero.pos _) len (fun _ => rfl)
    hsize target hchoice
  apply havg.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [(hz n a ha).2]
  simp_rw [cyclicBlockExpectedCutoff_eq]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem one_or_fullBlock_expected_cutoff_limit_of_interval_lengths
    (q H m₀ lo hi : ℕ → ℕ) (len : ∀ n, Fin (q n) → ℕ)
    [∀ n b, NeZero (len n b)] [∀ n, NeZero (∑ b, len n b)]
    (hm₀ : ∀ n, 0 < m₀ n)
    (hmin : ∀ n, q n = 1 ∨ ∀ j, m₀ n ≤ len n j)
    (hwindow : ∀ n, lo n ≤ hi n)
    (hsize : ∀ n b, lo n ≤ len n b ∧ len n b ≤ hi n)
    (hfit : ∀ n b, 2 * H n + 1 ≤ len n b)
    (b : ∀ n, Fin (2 * H n + 1) → ℂ) (hb : ∀ n, ∑ s, ‖b n s‖ ^ 2 = 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hMoment : (∫ u : ℂ, ‖u‖ ^ 2 ∂ν) = 1)
    (hratio : Tendsto (fun n => (H n : ℝ) / m₀ n) atTop (𝓝 0))
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ target : ℝ,
      (∀ m : ℕ → ℕ, (∀ n, lo n ≤ m n ∧ m n ≤ hi n) →
        Tendsto (fun n => cyclicBlockExpectedCutoff (m n) (H n) (b n) ν z a)
          atTop (𝓝 target)) →
      Tendsto (fun n => ∫ ω, matrixCutoffPotential
        (routedBandMatrix (fullBlockRoute (len n) (H n)) (b n) ω - z • 1) a
          ∂Measure.pi (fun _ : ((j : Fin (q n)) × Fin (len n j)) × Fin (2 * H n + 1) => ν))
        atTop (𝓝 target) := by
  let : ∀ n, Nonempty ((j : Fin (q n)) × Fin (len n j)) := fun n =>
    Fintype.card_pos_iff.mp (by
      simpa only [Fintype.card_sigma, Fintype.card_fin] using NeZero.pos (∑ j, len n j))
  let μ (n : ℕ) := Measure.pi
    (fun _ : ((j : Fin (q n)) × Fin (len n j)) × Fin (2 * H n + 1) => ν)
  let A (n : ℕ) := routedBandMatrix (fullBlockRoute (len n) (H n)) (b n)
  let B (n : ℕ) := routedBandMatrix (periodicBlockRoute (len n) (H n)) (b n)
  have hA (n : ℕ) : Measurable (A n) := routedBandMatrix_measurable _ _
  have hdet := ae_all_iff.2 (fun n => ae_shifted_matrix_det_ne_zero (μ n) (A n) (hA n))
  have hper := periodicBlock_expected_cutoff_limit_of_interval_lengths q H lo hi len hwindow hsize hfit b ν hInt ha
  have hmean := ae_all_iff.2 (fun n =>
    periodicBlockMatrix_expected_cutoff_average_ae (len n) (hfit n) (b n) ν hInt)
  have herr := ae_all_iff.2 (fun n => one_or_periodicization_expected_cutoff_ae (len n) (hm₀ n)
    (hmin n) (hfit n) (b n) (hb n) ν hInt hMoment)
  have hrate : Tendsto (fun n => Real.sqrt (8 * (H n : ℝ) / m₀ n) / a) atTop (𝓝 0) := by
    simpa only [← mul_div_assoc, mul_zero, Real.sqrt_zero, zero_div] using
      (hratio.const_mul 8).sqrt.div_const a
  filter_upwards [hdet, hper, hmean, herr] with z hz hp hm he
  intro target hchoice
  have hplim := hp target hchoice
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
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [hrate.eventually (gt_mem_nhds (half_pos hε)),
    hplim.eventually (Metric.ball_mem_nhds target (half_pos hε))] with n hn hp
  have hclose : |(∫ ω, matrixCutoffPotential (B n ω - z • 1) a ∂μ n) - target| < ε / 2 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hp
  have htriangle := abs_sub_le
    (∫ ω, matrixCutoffPotential (A n ω - z • 1) a ∂μ n)
    (∫ ω, matrixCutoffPotential (B n ω - z • 1) a ∂μ n) target
  rw [Real.dist_eq]
  have hbnd := hbound n
  change |(∫ ω, matrixCutoffPotential (A n ω - z • 1) a ∂μ n) - target| < ε
  linarith

end CircularLawSection6
