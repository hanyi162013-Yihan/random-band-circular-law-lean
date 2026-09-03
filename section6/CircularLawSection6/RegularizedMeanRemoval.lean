import CircularLawSection6.RegularizedCutoffComparison

/-! # Removing regularization after taking the matrix-size limit

The error is first made small by the cutoff parameter, then eventually
small in the matrix size. No interchange of these two limits is assumed.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem tendsto_of_iterated_approximations
    (Y : ℕ → ℝ) (X : ℕ → ℕ → ℝ) (c : ℕ → ℝ) (target : ℝ)
    (hc : Tendsto c atTop (𝓝 target))
    (hX : ∀ k, Tendsto (X k) atTop (𝓝 (c k)))
    (herror : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ᶠ n in atTop,
      |Y n - X k n| < ε) :
    Tendsto Y atTop (𝓝 target) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  have hsmall := hc.eventually (Metric.ball_mem_nhds target hthird)
  obtain ⟨k, hk, hcsmall⟩ := ((herror (ε / 3) hthird).and hsmall).exists
  have hpoint := (hX k).eventually (Metric.ball_mem_nhds (c k) hthird)
  filter_upwards [hk, hpoint] with n hn hx
  rw [Real.dist_eq] at hcsmall hx
  rw [Real.dist_eq]
  have htri := abs_sub_le (Y n) (X k n) target
  have htri2 := abs_sub_le (X k n) (c k) target
  linarith

theorem expected_regularized_raw_error_le_cutoff
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → Matrix ι ι ℂ)
    (hA : Measurable A) (hdet : ∀ᵐ ω ∂μ, (A ω).det ≠ 0)
    (hE : Integrable (fun ω => hilbertSchmidtSq (A ω)) μ)
    (hraw : Integrable (fun ω => matrixRawPotential (A ω)) μ)
    {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    |(∫ ω, matrixRawPotential (A ω) ∂μ) -
      ∫ ω, matrixRegularizedPotential (A ω) t ∂μ| ≤
      (∫ ω, |matrixCutoffPotential (A ω) a - matrixRawPotential (A ω)| ∂μ) +
        t ^ 2 / (2 * a ^ 2) := by
  have hreg := integrable_matrixRegularizedPotential hA hE ht
  have hcut := integrable_matrixCutoffPotential μ A hA hdet hE ha
  have hcuterr : Integrable
      (fun ω => |matrixCutoffPotential (A ω) a - matrixRawPotential (A ω)|) μ := by
    simpa only [Pi.sub_apply] using (hcut.sub hraw).abs
  rw [← integral_sub hraw hreg]
  calc
    _ ≤ ∫ ω, |matrixRawPotential (A ω) - matrixRegularizedPotential (A ω) t| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ ω, |matrixCutoffPotential (A ω) a - matrixRawPotential (A ω)| +
        t ^ 2 / (2 * a ^ 2) ∂μ := by
      apply integral_mono_ae (hraw.sub hreg).abs
        (hcuterr.add (integrable_const _))
      filter_upwards [hdet] with ω hω
      change |matrixRawPotential (A ω) - matrixRegularizedPotential (A ω) t| ≤
        |matrixCutoffPotential (A ω) a - matrixRawPotential (A ω)| + t ^ 2 / (2 * a ^ 2)
      rw [abs_sub_comm, abs_of_nonneg
        (sub_nonneg.2 (matrixRawPotential_le_regularized (A ω) hω t))]
      have hup := matrixRegularizedPotential_le_cutoff (A ω) ha ht
      have habs := le_abs_self (matrixCutoffPotential (A ω) a - matrixRawPotential (A ω))
      linarith
    _ = _ := by
      rw [integral_add hcuterr (integrable_const _)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

theorem matrixRaw_mean_of_regularized_mean_limits
    {Ω ι : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Nonempty (ι n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, Ω n → Matrix (ι n) (ι n) ℂ) (hA : ∀ n, Measurable (A n))
    (hdet : ∀ n, ∀ᵐ ω ∂μ n, (A n ω).det ≠ 0)
    (hE : ∀ n, Integrable (fun ω => hilbertSchmidtSq (A n ω)) (μ n))
    (hraw : ∀ n, Integrable (fun ω => matrixRawPotential (A n ω)) (μ n))
    (a c : ℕ → ℝ) (target : ℝ) (ha : ∀ k, 0 < a k)
    (ha0 : Tendsto a atTop (𝓝 0)) (hc : Tendsto c atTop (𝓝 target))
    (hreg : ∀ k, Tendsto
      (fun n => ∫ ω, matrixRegularizedPotential (A n ω) (a k ^ 2) ∂μ n)
      atTop (𝓝 (c k)))
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ᶠ n in atTop,
      (∫ ω, |matrixCutoffPotential (A n ω) (a k) - matrixRawPotential (A n ω)| ∂μ n) < ε) :
    Tendsto (fun n => ∫ ω, matrixRawPotential (A n ω) ∂μ n) atTop (𝓝 target) := by
  apply tendsto_of_iterated_approximations
    (fun n => ∫ ω, matrixRawPotential (A n ω) ∂μ n)
    (fun k n => ∫ ω, matrixRegularizedPotential (A n ω) (a k ^ 2) ∂μ n)
    c target hc hreg
  intro ε hε
  have hrate : Tendsto (fun k => a k ^ 2 / 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div] using (ha0.pow 2).div_const 2
  filter_upwards [hlower (ε / 2) (half_pos hε),
    hrate.eventually (gt_mem_nhds (half_pos hε))] with k hk hs
  filter_upwards [hk] with n hn
  have hbound := expected_regularized_raw_error_le_cutoff
    (μ n) (A n) (hA n) (hdet n) (hE n) (hraw n) (ha k) (sq_pos_of_pos (ha k))
  have hid : (a k ^ 2) ^ 2 / (2 * a k ^ 2) = a k ^ 2 / 2 := by
    field_simp [(ha k).ne']
  rw [hid] at hbound
  linarith

end CircularLawSection6
