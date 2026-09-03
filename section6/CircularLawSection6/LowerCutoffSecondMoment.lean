import CircularLawSection6.MatrixClippedCutoff
import CircularLawSection6.RawPotentialScaling
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.MetricSpace.Bounded

/-! # Uniform second moments for the actual lower-cutoff correction

The positive logarithmic part has squared normalized average bounded by
normalized matrix energy. Consequently every lower-cutoff correction with
threshold at most one has a second moment controlled independently of the
threshold by energy and the raw-potential second moment. Together with
the Gaussian variance and mean limits, this supplies the uniform
integrability missing from a mere negative-moment tightness argument.
-/

open MeasureTheory ProbabilityTheory Filter Topology TaoVuReplacement
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem log_max_one_nonneg_le {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ Real.log (max s 1) ∧ Real.log (max s 1) ≤ s := by
  refine ⟨Real.log_nonneg (le_max_right _ _), ?_⟩
  by_cases h : s ≤ 1
  · simpa only [max_eq_right h, Real.log_one] using hs
  · rw [max_eq_left (le_of_not_ge h)]
    have hl := Real.log_le_sub_one_of_pos (zero_lt_one.trans (lt_of_not_ge h))
    linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixCutoffPotential_one_nonneg (A : Matrix ι ι ℂ) :
    0 ≤ matrixCutoffPotential A 1 := by
  unfold matrixCutoffPotential operatorCutoffPotential
  exact div_nonneg (Finset.sum_nonneg fun i _ =>
    (log_max_one_nonneg_le (A.toEuclideanLin.singularValues_nonneg i)).1) (Nat.cast_nonneg _)

theorem matrixCutoffPotential_mono (A : Matrix ι ι ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    matrixCutoffPotential A a ≤ matrixCutoffPotential A b := by
  unfold matrixCutoffPotential operatorCutoffPotential
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  exact Real.log_le_log (ha.trans_le (le_max_right _ _)) (max_le_max_left _ hab)

theorem matrixCutoffPotential_one_sq_le_energy [Nonempty ι]
    (A : Matrix ι ι ℂ) (hA : A.det ≠ 0) :
    matrixCutoffPotential A 1 ^ 2 ≤ hilbertSchmidtSq A / (Fintype.card ι : ℝ) := by
  let s : Fin (Module.finrank ℂ (EuclideanSpace ℂ ι)) → ℝ := fun i => A.toEuclideanLin.singularValues i
  have hn : (0 : ℝ) < Module.finrank ℂ (EuclideanSpace ℂ ι) := by
    simpa only [finrank_euclideanSpace] using Nat.cast_pos.mpr (Fintype.card_pos (α := ι))
  have hlog : 0 ≤ ∑ i, Real.log (max (s i) 1) :=
    Finset.sum_nonneg fun i _ => (log_max_one_nonneg_le (A.toEuclideanLin.singularValues_nonneg i)).1
  have hs : 0 ≤ ∑ i, s i := Finset.sum_nonneg fun i _ => A.toEuclideanLin.singularValues_nonneg i
  have hle : (∑ i, Real.log (max (s i) 1)) ≤ ∑ i, s i :=
    Finset.sum_le_sum fun i _ => (log_max_one_nonneg_le (A.toEuclideanLin.singularValues_nonneg i)).2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) s
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hcs
  have henergy : (∑ i, s i ^ 2) = hilbertSchmidtSq A := by
    change (∑ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ ι)),
      A.toEuclideanLin.singularValues i ^ 2) = hilbertSchmidtSq A
    rw [singularValues_sq_sum_eq_energy A.toEuclideanLin (toEuclideanLin_injective_of_det_ne_zero A hA),
      operatorHilbertSchmidtSq_toEuclideanLin]
  rw [henergy] at hcs
  have hsq := ((sq_le_sq₀ hlog hs).mpr hle).trans hcs
  unfold matrixCutoffPotential operatorCutoffPotential
  rw [div_pow]
  calc
    _ ≤ ((Module.finrank ℂ (EuclideanSpace ℂ ι) : ℝ) * hilbertSchmidtSq A) /
        (Module.finrank ℂ (EuclideanSpace ℂ ι) : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hsq (sq_nonneg _)
    _ = hilbertSchmidtSq A / (Module.finrank ℂ (EuclideanSpace ℂ ι) : ℝ) := by
      field_simp [hn.ne']
    _ = _ := by rw [finrank_euclideanSpace]

theorem matrixLowerCutoff_correction_sq_le [Nonempty ι]
    (A : Matrix ι ι ℂ) (hA : A.det ≠ 0) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (matrixCutoffPotential A a - matrixRawPotential A) ^ 2 ≤
      2 * (hilbertSchmidtSq A / (Fintype.card ι : ℝ)) + 2 * matrixRawPotential A ^ 2 := by
  have hlo := matrixRawPotential_le_cutoff A hA a
  have hhi := matrixCutoffPotential_mono A ha ha1
  have henergy := matrixCutoffPotential_one_sq_le_energy A hA
  have hsq : (matrixCutoffPotential A a - matrixRawPotential A) ^ 2 ≤
      (matrixCutoffPotential A 1 - matrixRawPotential A) ^ 2 :=
    (sq_le_sq₀ (sub_nonneg.mpr hlo) (sub_nonneg.mpr (hlo.trans hhi))).mpr
      (sub_le_sub hhi le_rfl)
  nlinarith [sq_nonneg (matrixCutoffPotential A 1 + matrixRawPotential A)]

theorem expected_matrixLowerCutoff_secondMoment [Nonempty ι]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix ι ι ℂ) (hA : Measurable A) (hdet : ∀ᵐ ω ∂μ, (A ω).det ≠ 0)
    (hE : Integrable (fun ω => hilbertSchmidtSq (A ω)) μ)
    (hraw : MemLp (fun ω => matrixRawPotential (A ω)) 2 μ)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    MemLp (fun ω => matrixCutoffPotential (A ω) a - matrixRawPotential (A ω)) 2 μ ∧
      (∫ ω, (matrixCutoffPotential (A ω) a - matrixRawPotential (A ω)) ^ 2 ∂μ) ≤
        2 * ((∫ ω, hilbertSchmidtSq (A ω) ∂μ) / (Fintype.card ι : ℝ)) +
          2 * ∫ ω, matrixRawPotential (A ω) ^ 2 ∂μ := by
  have hm := (aestronglyMeasurable_matrixCutoffPotential μ A hA hdet ha).sub hraw.aestronglyMeasurable
  have hraw2 := (memLp_two_iff_integrable_sq hraw.aestronglyMeasurable).mp hraw
  have hmajor := ((hE.div_const (Fintype.card ι : ℝ)).const_mul 2).add (hraw2.const_mul 2)
  have hpoint : ∀ᵐ ω ∂μ,
      (matrixCutoffPotential (A ω) a - matrixRawPotential (A ω)) ^ 2 ≤
        2 * (hilbertSchmidtSq (A ω) / (Fintype.card ι : ℝ)) + 2 * matrixRawPotential (A ω) ^ 2 := by
    filter_upwards [hdet] with ω hω
    exact matrixLowerCutoff_correction_sq_le (A ω) hω ha ha1
  have hint : Integrable (fun ω => (matrixCutoffPotential (A ω) a - matrixRawPotential (A ω)) ^ 2) μ := by
    apply hmajor.mono' (hm.pow 2)
    filter_upwards [hpoint] with ω hω
    change ‖(matrixCutoffPotential (A ω) a - matrixRawPotential (A ω)) ^ 2‖ ≤
      2 * (hilbertSchmidtSq (A ω) / (Fintype.card ι : ℝ)) + 2 * matrixRawPotential (A ω) ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (matrixCutoffPotential (A ω) a - matrixRawPotential (A ω)))]
    exact hω
  refine ⟨(memLp_two_iff_integrable_sq hm).mpr hint, ?_⟩
  calc
    _ ≤ ∫ ω, 2 * (hilbertSchmidtSq (A ω) / (Fintype.card ι : ℝ)) + 2 * matrixRawPotential (A ω) ^ 2 ∂μ :=
      integral_mono_ae hint hmajor hpoint
    _ = _ := by
      rw [integral_add ((hE.div_const _).const_mul 2) (hraw2.const_mul 2),
        integral_const_mul, integral_const_mul, integral_div]

theorem secondMoment_tendsto_of_mean_variance
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (hX : ∀ n, MemLp (X n) 2 (μ n)) {target v : ℝ}
    (hmean : Tendsto (fun n => ∫ ω, X n ω ∂μ n) atTop (𝓝 target))
    (hvar : Tendsto (fun n => variance (X n) (μ n)) atTop (𝓝 v)) :
    Tendsto (fun n => ∫ ω, X n ω ^ 2 ∂μ n) atTop (𝓝 (v + target ^ 2)) := by
  have h := hvar.add (hmean.pow 2)
  apply h.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [variance_eq_sub (hX n)]
  exact sub_add_cancel _ _

theorem exists_uniform_secondMoment_of_mean_variance
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (hX : ∀ n, MemLp (X n) 2 (μ n)) {target v : ℝ}
    (hmean : Tendsto (fun n => ∫ ω, X n ω ∂μ n) atTop (𝓝 target))
    (hvar : Tendsto (fun n => variance (X n) (μ n)) atTop (𝓝 v)) :
    ∃ C : ℝ, ∀ n, (∫ ω, X n ω ^ 2 ∂μ n) ≤ C := by
  have hlim := secondMoment_tendsto_of_mean_variance μ X hX hmean hvar
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hlim).bddAbove
  exact ⟨C, fun n => hC ⟨n, rfl⟩⟩

end CircularLawSection6
