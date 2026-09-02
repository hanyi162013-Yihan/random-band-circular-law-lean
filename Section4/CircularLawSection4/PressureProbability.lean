import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.Data.Finset.Max

/-!
# The finite-family closing step in Section 4

The pressure-concentration proof first establishes an `L²`/variance estimate
for every exterior degree. Its last step is deterministic: the expectation
of the maximum over the finitely many degrees is controlled by the square
root of the sum of those variances. This file formalizes that step over an
arbitrary probability space and arbitrary nonempty finite index type.
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Real

namespace CircularLawSection4

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- Maximum absolute coordinate of a nonempty finite real family. -/
noncomputable def finiteMaxAbs [Fintype ι] [Nonempty ι] (x : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => |x i|

theorem finiteMaxAbs_nonneg [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    0 ≤ finiteMaxAbs x := by
  classical
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i : ι => |x i|)
  rw [finiteMaxAbs, hi]
  exact abs_nonneg _

theorem finiteMaxAbs_sq_le_sum_sq [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    (finiteMaxAbs x) ^ 2 ≤ ∑ i, (x i) ^ 2 := by
  classical
  obtain ⟨i, hi, hmax⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i : ι => |x i|)
  rw [finiteMaxAbs, hmax, sq_abs]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) hi

/-- A finite supremum of real `Lᵖ` functions is again in `Lᵖ`. -/
theorem memLp_finsetSup'
    {μ : Measure Ω} {p : ℝ≥0∞} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → Ω → ℝ} (hf : ∀ i ∈ s, MemLp (f i) p μ) :
    MemLp (fun ω => s.sup' hs fun i => f i ω) p μ := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
      simpa using hf i (Finset.mem_singleton_self i)
  | @cons i s his hs ih =>
      have hmem := (hf i (Finset.mem_cons_self i s)).sup
        (ih fun j hj => hf j (Finset.mem_cons_of_mem hj))
      exact hmem.ae_eq (ae_of_all _ fun ω => by
        rw [Pi.sup_apply]
        change max (f i ω) (s.sup' hs fun j => f j ω) =
          (Finset.cons i s his).sup' _ (fun j => f j ω)
        exact (Finset.sup'_cons hs (fun j => f j ω)).symm)

/-- Center a real random variable at its expectation. -/
noncomputable def centered (μ : Measure Ω) (Y : ι → Ω → ℝ) (i : ι) (ω : Ω) : ℝ :=
  Y i ω - ∫ x, Y i x ∂μ

/-- The pointwise maximum of the centered absolute deviations. -/
noncomputable def maxCenteredAbs [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) (Y : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  finiteMaxAbs fun i => centered μ Y i ω

theorem memLp_centered {μ : Measure Ω} [IsFiniteMeasure μ] {Y : ι → Ω → ℝ}
    (hY : ∀ i, MemLp (Y i) 2 μ) (i : ι) :
    MemLp (centered μ Y i) 2 μ := by
  unfold centered
  have hmem := (hY i).sub (memLp_const (∫ x, Y i x ∂μ) :
    MemLp (fun _ : Ω => ∫ x, Y i x ∂μ) 2 μ)
  exact hmem.ae_eq (ae_of_all _ fun ω => Pi.sub_apply _ _ ω)

theorem memLp_maxCenteredAbs [Fintype ι] [Nonempty ι]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {Y : ι → Ω → ℝ} (hY : ∀ i, MemLp (Y i) 2 μ) :
    MemLp (maxCenteredAbs μ Y) 2 μ := by
  classical
  unfold maxCenteredAbs finiteMaxAbs
  exact memLp_finsetSup' (μ := μ) Finset.univ_nonempty
    (fun i _ => (memLp_centered hY i).abs)

/-- Cauchy--Schwarz on a probability space, specialized to the finite maximum. -/
theorem integral_maxCenteredAbs_le_sqrt_secondMoment
    [Fintype ι] [Nonempty ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : ι → Ω → ℝ} (hY : ∀ i, MemLp (Y i) 2 μ) :
    (∫ ω, maxCenteredAbs μ Y ω ∂μ) ≤
      √(∫ ω, (maxCenteredAbs μ Y ω) ^ 2 ∂μ) := by
  have hmax_nonneg : 0 ≤ᵐ[μ] maxCenteredAbs μ Y :=
    ae_of_all _ fun ω => by
      exact finiteMaxAbs_nonneg (fun i => centered μ Y i ω)
  have hone_nonneg : 0 ≤ᵐ[μ] (fun _ : Ω => (1 : ℝ)) :=
    ae_of_all _ fun _ => zero_le_one
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) Real.HolderConjugate.two_two hmax_nonneg hone_nonneg
    (by simpa using memLp_maxCenteredAbs hY)
    (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ))
  simpa [Real.rpow_two, Real.sqrt_eq_rpow] using hcs

/-- The squared finite maximum is bounded by the sum of coordinate variances. -/
theorem integral_maxCenteredAbs_sq_le_sum_variance
    [Fintype ι] [Nonempty ι] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Y : ι → Ω → ℝ} (hY : ∀ i, MemLp (Y i) 2 μ) :
    (∫ ω, (maxCenteredAbs μ Y ω) ^ 2 ∂μ) ≤
      ∑ i, variance (Y i) μ := by
  have hmax_sq : Integrable (fun ω => (maxCenteredAbs μ Y ω) ^ 2) μ :=
    (memLp_maxCenteredAbs hY).integrable_sq
  have hcentered_sq : ∀ i, Integrable (fun ω => (centered μ Y i ω) ^ 2) μ :=
    fun i => (memLp_centered hY i).integrable_sq
  have hsum_sq : Integrable (fun ω => ∑ i, (centered μ Y i ω) ^ 2) μ :=
    integrable_finsetSum Finset.univ fun i _ => hcentered_sq i
  calc
    (∫ ω, (maxCenteredAbs μ Y ω) ^ 2 ∂μ) ≤
        ∫ ω, ∑ i, (centered μ Y i ω) ^ 2 ∂μ := by
      apply integral_mono hmax_sq hsum_sq
      intro ω
      simpa [maxCenteredAbs] using
        finiteMaxAbs_sq_le_sum_sq (fun i => centered μ Y i ω)
    _ = ∑ i, ∫ ω, (centered μ Y i ω) ^ 2 ∂μ := by
      exact integral_finsetSum Finset.univ fun i _ => hcentered_sq i
    _ = ∑ i, variance (Y i) μ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (variance_eq_integral (hY i).aemeasurable).symm

/-- Final maximal-concentration deduction used in Proposition 4. -/
theorem integral_maxCenteredAbs_le_sqrt_sum_variance
    [Fintype ι] [Nonempty ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : ι → Ω → ℝ} (hY : ∀ i, MemLp (Y i) 2 μ) :
    (∫ ω, maxCenteredAbs μ Y ω ∂μ) ≤
      √(∑ i, variance (Y i) μ) :=
  (integral_maxCenteredAbs_le_sqrt_secondMoment hY).trans
    (Real.sqrt_le_sqrt (integral_maxCenteredAbs_sq_le_sum_variance hY))

/-- Uniform coordinate variance bounds give the usual square-root-cardinality loss. -/
theorem integral_maxCenteredAbs_le_sqrt_card_mul
    [Fintype ι] [Nonempty ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : ι → Ω → ℝ} (hY : ∀ i, MemLp (Y i) 2 μ)
    {V : ℝ} (hV : ∀ i, variance (Y i) μ ≤ V) :
    (∫ ω, maxCenteredAbs μ Y ω ∂μ) ≤
      √((Fintype.card ι : ℝ) * V) := by
  refine (integral_maxCenteredAbs_le_sqrt_sum_variance hY).trans
    (Real.sqrt_le_sqrt ?_)
  calc
    (∑ i, variance (Y i) μ) ≤ ∑ _i : ι, V :=
      Finset.sum_le_sum fun i _ => hV i
    _ = (Fintype.card ι : ℝ) * V := by simp

/-- Paper-shaped specialization: the exterior degrees are `0, ..., 2W`. -/
theorem pressure_maximal_concentration_of_variance
    (W : ℕ) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Fin (2 * W).succ → Ω → ℝ}
    (hY : ∀ r, MemLp (Y r) 2 μ) {V : ℝ}
    (hV : ∀ r, variance (Y r) μ ≤ V) :
    (∫ ω, maxCenteredAbs μ Y ω ∂μ) ≤ √(((2 * W + 1 : ℕ) : ℝ) * V) := by
  simpa [Nat.succ_eq_add_one] using
    integral_maxCenteredAbs_le_sqrt_card_mul hY hV

end CircularLawSection4
