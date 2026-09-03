import CircularLawSection6.LowerCutoffSecondMoment
import CircularLawSection6.SquareBoundedProbability
import ShortRingAnchor.GinibreLowerEdge

/-! # Actual lower-cutoff control from triangular negative-moment tightness

The source BC12 negative-moment input is expressed on the literal finite
sample spaces. The deterministic lower correction is identified with the
actual matrix cutoff minus log determinant. Tightness then gives small
correction in probability; a separate uniform second moment gives L1.
-/

open MeasureTheory Filter Topology ShortRingAnchor TaoVuReplacement
open CircularLawSections56.Section5
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

def BoundedInProbabilityTri {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n in atTop, (μ n).real {ω | C < |X n ω|} < δ

theorem tendstoInProbabilityTri_of_tight_domination
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X Y : ∀ n, Ω n → ℝ) (b : ℕ → ℝ)
    (hY : BoundedInProbabilityTri μ Y) (hb : Tendsto b atTop (𝓝 0))
    (hbound : ∀ n, ∀ᵐ ω ∂μ n, |X n ω| ≤ |b n| * |Y n ω|) :
    TendstoInProbabilityTri μ X 0 := by
  intro ε hε
  apply Metric.tendsto_nhds.2
  intro δ hδ
  obtain ⟨C, hC, htail⟩ := hY δ hδ
  have hsmall : ∀ᶠ n in atTop, |b n| * C < ε := by
    have hlim : Tendsto (fun n => |b n| * C) atTop (𝓝 0) := by
      simpa only [abs_zero, zero_mul] using hb.abs.mul_const C
    exact hlim.eventually (gt_mem_nhds hε)
  filter_upwards [htail, hsmall] with n hn hnsmall
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  refine lt_of_le_of_lt ?_ hn
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hbound n] with ω hω
  intro hx
  change ε ≤ |X n ω - 0| at hx
  rw [sub_zero] at hx
  change C < |Y n ω|
  by_contra hy
  have hle := mul_le_mul_of_nonneg_left (le_of_not_gt hy) (abs_nonneg (b n))
  exact (not_le_of_gt hnsmall) (hx.trans (hω.trans hle))

def matrixNegativeMoment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (p : ℝ) : ℝ :=
  normalizedNegativeMoment p (fun i : Fin (Fintype.card ι) => A.toEuclideanLin.singularValues i)

theorem matrixLowerCutoff_eq_empirical {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.det ≠ 0) (a : ℝ) :
    matrixCutoffPotential A a - matrixRawPotential A =
      empiricalLowerLogCorrection a (fun i : Fin (Fintype.card ι) => A.toEuclideanLin.singularValues i) := by
  have hindex : (∑ i : Fin (Module.finrank ℂ (EuclideanSpace ℂ ι)),
      Real.log (max (A.toEuclideanLin.singularValues i) a)) =
      ∑ i : Fin (Fintype.card ι), Real.log (max (A.toEuclideanLin.singularValues i) a) :=
    Fintype.sum_equiv (finCongr (finrank_euclideanSpace (𝕜 := ℂ) (ι := ι))) _ _ (fun _ => rfl)
  unfold matrixCutoffPotential operatorCutoffPotential matrixRawPotential
  rw [hindex, finrank_euclideanSpace, matrix_log_norm_det_eq_sum_log_singularValues A hA]
  unfold empiricalLowerLogCorrection empiricalAverage
  rw [← sub_div, ← Finset.sum_sub_distrib, Fintype.card_fin]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : A.toEuclideanLin.singularValues i < a
  · simp only [lowerLogCorrection, if_pos h, max_eq_right h.le]
  · simp only [lowerLogCorrection, if_neg h, max_eq_left (le_of_not_gt h), sub_self]

theorem matrixLowerCutoff_le_negativeMoment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.det ≠ 0) {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    |matrixCutoffPotential A a - matrixRawPotential A| ≤ (a ^ p / p) * matrixNegativeMoment A p := by
  rw [abs_of_nonneg (sub_nonneg.mpr (matrixRawPotential_le_cutoff A hA a)),
    matrixLowerCutoff_eq_empirical A hA a]
  exact empiricalLowerLogCorrection_le_scaled_negativeMoment
    (fun i => A.toEuclideanLin.injective_iff_forall_lt_finrank_singularValues_pos.mp
      (toEuclideanLin_injective_of_det_ne_zero A hA) i
      (by simpa only [finrank_euclideanSpace] using i.isLt)) ha hp

theorem matrixLowerCutoff_probability_of_negativeMoment
    {Ω ι : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, Ω n → Matrix (ι n) (ι n) ℂ)
    (hdet : ∀ n, ∀ᵐ ω ∂μ n, (A n ω).det ≠ 0) {p : ℝ} (hp : 0 < p)
    (hBC12 : BoundedInProbabilityTri μ (fun n ω => matrixNegativeMoment (A n ω) p))
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha0 : Tendsto a atTop (𝓝 0)) :
    TendstoInProbabilityTri μ (fun n ω => matrixCutoffPotential (A n ω) (a n) - matrixRawPotential (A n ω)) 0 := by
  apply tendstoInProbabilityTri_of_tight_domination μ _ _ (fun n => a n ^ p / p) hBC12
    (rpow_div_tendsto_zero ha0 hp)
  intro n
  filter_upwards [hdet n] with ω hω
  have hscale : 0 ≤ a n ^ p / p := div_nonneg (Real.rpow_nonneg (ha n).le p) hp.le
  rw [abs_of_nonneg hscale]
  exact (matrixLowerCutoff_le_negativeMoment (A n ω) hω (ha n) hp).trans
    (mul_le_mul_of_nonneg_left (le_abs_self _) hscale)

theorem matrixLowerCutoff_L1_of_negativeMoment
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
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n ≤ 1)
    (ha0 : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |matrixCutoffPotential (A n ω) (a n) - matrixRawPotential (A n ω)| ∂μ n)
      atTop (𝓝 0) := by
  have hm (n : ℕ) := expected_matrixLowerCutoff_secondMoment (μ n) (A n)
    (hA n) (hdet n) (hE n) (hraw n) (ha n) (ha1 n)
  apply tendsto_L1_of_ae_uniform_secondMoment_probability μ _ (fun n => (hm n).1) (2 * CE + 2 * CL)
  · intro n
    exact (hm n).2.trans (add_le_add (mul_le_mul_of_nonneg_left (hEb n) (by norm_num))
      (mul_le_mul_of_nonneg_left (hLb n) (by norm_num)))
  · exact matrixLowerCutoff_probability_of_negativeMoment μ A hdet hp hBC12 a ha ha0

end CircularLawSection6
