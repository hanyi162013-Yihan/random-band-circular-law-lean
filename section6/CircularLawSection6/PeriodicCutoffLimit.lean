import CircularLawSection6.PeriodicBlockCutoff
import CircularLawSection6.UniformBlockAverages

/-! # Actual periodic block expectations and the full routed cutoff limit

Convergence along every admissible choice of block lengths gives uniform
block convergence. The exact IID expectation identity then yields the
periodicized mean limit, and the proved HS boundary coupling transfers
that limit to the original routed band. The actual block expectation
limit remains an explicit premise, supplied by the compact comparison
step; no uniform convergence or full-matrix error is assumed.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

def cyclicBlockExpectedCutoff (N H : ℕ) (b : Fin (2 * H + 1) → ℂ)
    (ν : Measure ℂ) (z : ℂ) (a : ℝ) : ℝ :=
  if hN : 0 < N then
    let : NeZero N := ⟨hN.ne'⟩
    ∫ ω, matrixCutoffPotential
      (routedBandMatrix (cyclicFinSlot (N := N) H) b ω - z • 1) a
        ∂Measure.pi (fun _ : Fin N × Fin (2 * H + 1) => ν)
  else 0

theorem cyclicBlockExpectedCutoff_eq (N H : ℕ) [NeZero N]
    (b : Fin (2 * H + 1) → ℂ) (ν : Measure ℂ) (z : ℂ) (a : ℝ) :
    cyclicBlockExpectedCutoff N H b ν z a =
      ∫ ω, matrixCutoffPotential
        (routedBandMatrix (cyclicFinSlot (N := N) H) b ω - z • 1) a
          ∂Measure.pi (fun _ : Fin N × Fin (2 * H + 1) => ν) := by
  simp only [cyclicBlockExpectedCutoff, dif_pos (NeZero.pos N)]

theorem periodicBlock_expected_cutoff_limit_of_all_lengths
    (q H m₀ : ℕ → ℕ) (len : ∀ n, Fin (q n) → ℕ)
    [∀ n b, NeZero (len n b)] [∀ n, NeZero (∑ b, len n b)]
    (hsize : ∀ n b, m₀ n ≤ len n b ∧ len n b ≤ 2 * m₀ n)
    (hfit : ∀ n b, 2 * H n + 1 ≤ len n b)
    (b : ∀ n, Fin (2 * H n + 1) → ℂ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ target : ℝ,
      (∀ m : ℕ → ℕ, (∀ n, m₀ n ≤ m n ∧ m n ≤ 2 * m₀ n) →
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
    m₀ (fun n => 2 * m₀ n) (fun n => by omega)
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

theorem fullBlock_expected_cutoff_limit_of_all_lengths
    (q H m₀ : ℕ → ℕ) (len : ∀ n, Fin (q n) → ℕ)
    [∀ n b, NeZero (len n b)] [∀ n, NeZero (∑ b, len n b)]
    (hm₀ : ∀ n, 0 < m₀ n)
    (hsize : ∀ n b, m₀ n ≤ len n b ∧ len n b ≤ 2 * m₀ n)
    (hfit : ∀ n b, 2 * H n + 1 ≤ len n b)
    (b : ∀ n, Fin (2 * H n + 1) → ℂ) (hb : ∀ n, ∑ s, ‖b n s‖ ^ 2 = 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hMoment : (∫ u : ℂ, ‖u‖ ^ 2 ∂ν) = 1)
    (hratio : Tendsto (fun n => (H n : ℝ) / m₀ n) atTop (𝓝 0))
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ target : ℝ,
      (∀ m : ℕ → ℕ, (∀ n, m₀ n ≤ m n ∧ m n ≤ 2 * m₀ n) →
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
  have hper := periodicBlock_expected_cutoff_limit_of_all_lengths q H m₀ len hsize hfit b ν hInt ha
  have hmean := ae_all_iff.2 (fun n =>
    periodicBlockMatrix_expected_cutoff_average_ae (len n) (hfit n) (b n) ν hInt)
  have herr := ae_all_iff.2 (fun n => periodicization_expected_cutoff_ae (len n) (hm₀ n)
    (fun j => (hsize n j).1) (hfit n) (b n) (hb n) ν hInt hMoment)
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
