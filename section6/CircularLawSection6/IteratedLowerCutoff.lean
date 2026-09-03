import CircularLawSection6.NegativeMomentCutoff

/-! # Lower-cutoff expectation control in the correct order of limits

The cutoff index tends to infinity only after the matrix-size limit.
The conclusion is an eventual-in-cutoff, eventual-in-size bound; it does
not assume convergence uniformly in the cutoff or exchange the limits.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem integral_abs_le_secondMoment_threshold_probability_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX2 : MemLp X 2 μ) {ε M : ℝ} (hε : 0 ≤ ε) (hM : 0 < M) :
    (∫ ω, |X ω| ∂μ) ≤ ε + (∫ ω, X ω ^ 2 ∂μ) / M + M * μ.real {ω | ε ≤ |X ω|} := by
  let Y := hX2.aestronglyMeasurable.mk X
  have hXY : X =ᵐ[μ] Y := hX2.aestronglyMeasurable.ae_eq_mk
  have h := integral_abs_le_secondMoment_threshold_probability μ Y
    hX2.aestronglyMeasurable.measurable_mk (hX2.ae_eq hXY) hε hM
  have h₁ : (∫ ω, |X ω| ∂μ) = ∫ ω, |Y ω| ∂μ := by
    apply integral_congr_ae
    filter_upwards [hXY] with ω hω
    rw [hω]
  have h₂ : (∫ ω, X ω ^ 2 ∂μ) = ∫ ω, Y ω ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hXY] with ω hω
    rw [hω]
  have h₃ : μ.real {ω | ε ≤ |X ω|} = μ.real {ω | ε ≤ |Y ω|} := by
    apply measureReal_congr
    filter_upwards [hXY] with ω hω
    change (ε ≤ |X ω|) = (ε ≤ |Y ω|)
    rw [hω]
  rwa [h₁, h₂, h₃]

theorem iterated_L1_of_secondMoment_tight_domination
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ℕ → ∀ n, Ω n → ℝ) (Y : ∀ n, Ω n → ℝ)
    (hX : ∀ R n, MemLp (X R n) 2 (μ n)) (C : ℝ)
    (hC : ∀ R n, (∫ ω, X R n ω ^ 2 ∂μ n) ≤ C)
    (b : ℕ → ℝ) (hb : Tendsto b atTop (𝓝 0)) (hY : BoundedInProbabilityTri μ Y)
    (hbound : ∀ R n, ∀ᵐ ω ∂μ n, |X R n ω| ≤ |b R| * |Y n ω|) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ R in atTop, ∀ᶠ n in atTop, (∫ ω, |X R n ω| ∂μ n) < ε := by
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  have hlarge : ∀ᶠ M : ℝ in atTop, 0 < M ∧ C / M < ε / 3 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (tendsto_id.const_div_atTop C).eventually (gt_mem_nhds hthird)] with M hM hMC
    exact ⟨hM, hMC⟩
  obtain ⟨M, hM, hMC⟩ := hlarge.exists
  obtain ⟨K, hK, htail⟩ := hY (ε / (3 * M)) (by positivity)
  have hsmall : ∀ᶠ R in atTop, |b R| * K < ε / 3 := by
    have hlim : Tendsto (fun R => |b R| * K) atTop (𝓝 0) := by
      simpa only [abs_zero, zero_mul] using hb.abs.mul_const K
    exact hlim.eventually (gt_mem_nhds hthird)
  filter_upwards [hsmall] with R hR
  filter_upwards [htail] with n hn
  have hprob : (μ n).real {ω | ε / 3 ≤ |X R n ω|} ≤ (μ n).real {ω | K < |Y n ω|} := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hbound R n] with ω hω
    intro hx
    change ε / 3 ≤ |X R n ω| at hx
    change K < |Y n ω|
    by_contra hy
    exact (not_le_of_gt hR) (hx.trans (hω.trans
      (mul_le_mul_of_nonneg_left (le_of_not_gt hy) (abs_nonneg _))))
  have hprobsmall : M * (μ n).real {ω | ε / 3 ≤ |X R n ω|} < ε / 3 := by
    have h := mul_lt_mul_of_pos_left (hprob.trans_lt hn) hM
    have heq : M * (ε / (3 * M)) = ε / 3 := by field_simp [hM.ne']
    rwa [heq] at h
  have h := integral_abs_le_secondMoment_threshold_probability_ae (μ n) (X R n) (hX R n) hthird.le hM
  have hboundC := div_le_div_of_nonneg_right (hC R n) hM.le
  linarith

theorem matrixLowerCutoff_iterated_L1_of_negativeMoment
    {Ω ι : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Nonempty (ι n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, Ω n → Matrix (ι n) (ι n) ℂ) (hA : ∀ n, Measurable (A n))
    (hdet : ∀ n, ∀ᵐ ω ∂μ n, (A n ω).det ≠ 0)
    (hE : ∀ n, Integrable (fun ω => hilbertSchmidtSq (A n ω)) (μ n))
    (hraw : ∀ n, MemLp (fun ω => matrixRawPotential (A n ω)) 2 (μ n))
    (CE CL : ℝ)
    (hEb : ∀ n, (∫ ω, hilbertSchmidtSq (A n ω) ∂μ n) / (Fintype.card (ι n) : ℝ) ≤ CE)
    (hLb : ∀ n, (∫ ω, matrixRawPotential (A n ω) ^ 2 ∂μ n) ≤ CL)
    {p : ℝ} (hp : 0 < p)
    (hBC12 : BoundedInProbabilityTri μ (fun n ω => matrixNegativeMoment (A n ω) p))
    (a : ℕ → ℝ) (ha : ∀ R, 0 < a R) (ha1 : ∀ R, a R ≤ 1)
    (ha0 : Tendsto a atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ R in atTop, ∀ᶠ n in atTop,
      (∫ ω, |matrixCutoffPotential (A n ω) (a R) - matrixRawPotential (A n ω)| ∂μ n) < ε := by
  have hm (R n : ℕ) := expected_matrixLowerCutoff_secondMoment (μ n) (A n)
    (hA n) (hdet n) (hE n) (hraw n) (ha R) (ha1 R)
  apply iterated_L1_of_secondMoment_tight_domination μ _ _ (fun R n => (hm R n).1) (2 * CE + 2 * CL)
    (fun R n => (hm R n).2.trans (add_le_add (mul_le_mul_of_nonneg_left (hEb n) (by norm_num))
      (mul_le_mul_of_nonneg_left (hLb n) (by norm_num))))
    (fun R => a R ^ p / p) (ShortRingAnchor.rpow_div_tendsto_zero ha0 hp) hBC12
  intro R n
  filter_upwards [hdet n] with ω hω
  have hs : 0 ≤ a R ^ p / p := div_nonneg (Real.rpow_nonneg (ha R).le p) hp.le
  rw [abs_of_nonneg hs]
  exact (matrixLowerCutoff_le_negativeMoment (A n ω) hω (ha R) hp).trans
    (mul_le_mul_of_nonneg_left (le_abs_self _) hs)

end CircularLawSection6
