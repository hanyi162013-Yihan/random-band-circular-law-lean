import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Probability.Moments.Variance

/-!
# Bounded-density atoms

This file packages the real-atom branch of the hypotheses used in Section 10:
it is a probability law on `ℝ`, has mean zero and second moment one, and is
dominated by `L` times Lebesgue measure.  It also records the elementary
one-dimensional interval and affine small-ball estimates used later.
-/

open scoped ENNReal NNReal Topology
open Set MeasureTheory

namespace BernoulliSection10

/-- A real probability law satisfying the bounded-density, centering, and
variance-one hypotheses of Section 10.  Domination by `L • volume` is the
measure-theoretic formulation of having a Lebesgue density bounded by `L`.
-/
structure IsBoundedDensityAtom (μ : Measure ℝ) (L : ℝ) : Prop where
  nonneg : 0 ≤ L
  probability : μ univ = 1
  density_le : μ ≤ ENNReal.ofReal L • volume
  integrable_id : Integrable (fun x : ℝ => x) μ
  centered : ∫ x : ℝ, x ∂μ = 0
  integrable_sq : Integrable (fun x : ℝ => x ^ 2) μ
  variance_one : ∫ x : ℝ, x ^ 2 ∂μ = 1

namespace IsBoundedDensityAtom

variable {μ : Measure ℝ} {L : ℝ}

/-- The probability-measure instance carried by a bounded-density atom.  It is
kept as a definition rather than a global instance because the density bound
`L` is an explicit parameter. -/
def toIsProbabilityMeasure (h : IsBoundedDensityAtom μ L) : IsProbabilityMeasure μ :=
  ⟨h.probability⟩

/-- A bounded density controls the mass of every measurable set by its
Lebesgue volume. -/
theorem measure_le_volume (h : IsBoundedDensityAtom μ L) {s : Set ℝ}
    (hs : MeasurableSet s) :
    μ s ≤ ENNReal.ofReal L * volume s := by
  simpa [Measure.smul_apply, hs] using h.density_le s

/-- Interval small-ball estimate in `ℝ≥0∞` form. -/
theorem measure_Icc_le (h : IsBoundedDensityAtom μ L) (a b : ℝ) :
    μ (Icc a b) ≤ ENNReal.ofReal (L * (b - a)) := by
  by_cases hab : a ≤ b
  · calc
      μ (Icc a b) ≤ ENNReal.ofReal L * volume (Icc a b) :=
        h.measure_le_volume measurableSet_Icc
      _ = ENNReal.ofReal (L * (b - a)) := by
        rw [Real.volume_Icc]
        rw [ENNReal.ofReal_mul h.nonneg]
  · simp [not_le.mp hab]

/-- Symmetric interval small-ball estimate. -/
theorem measure_abs_sub_le (h : IsBoundedDensityAtom μ L) (c r : ℝ) (hr : 0 ≤ r) :
    μ {x : ℝ | |x - c| ≤ r} ≤ ENNReal.ofReal (2 * L * r) := by
  have hset : {x : ℝ | |x - c| ≤ r} = Icc (c - r) (c + r) := by
    ext x
    simp only [mem_setOf_eq, mem_Icc, abs_le]
    constructor
    · rintro ⟨hx₁, hx₂⟩
      constructor <;> linarith
    · rintro ⟨hx₁, hx₂⟩
      constructor <;> linarith
  rw [hset]
  convert h.measure_Icc_le (c - r) (c + r) using 1 <;> ring_nf

/-- Affine one-coordinate small-ball estimate.  The coefficient is allowed to
have either sign; only its absolute value enters the interval length. -/
theorem measure_abs_add_mul_le (h : IsBoundedDensityAtom μ L)
    (a c r : ℝ) (hc : c ≠ 0) (hr : 0 ≤ r) :
    μ {x : ℝ | |a + x * c| ≤ r} ≤ ENNReal.ofReal (2 * L * r / |c|) := by
  have hcabs : 0 < |c| := abs_pos.mpr hc
  have hset :
      {x : ℝ | |a + x * c| ≤ r} =
        {x : ℝ | |x - (-a / c)| ≤ r / |c|} := by
    ext x
    simp only [mem_setOf_eq]
    have halg : a + x * c = c * (x - (-a / c)) := by
      field_simp
      ring
    rw [halg, abs_mul]
    constructor
    · intro hx
      exact (le_div_iff₀ hcabs).2 (by simpa [mul_comm] using hx)
    · intro hx
      simpa [mul_comm] using (le_div_iff₀ hcabs).1 hx
  rw [hset]
  convert h.measure_abs_sub_le (-a / c) (r / |c|) (div_nonneg hr hcabs.le) using 1 <;>
    congr 1 <;> field_simp <;> ring

/-- A bounded-density atom has no point masses. -/
theorem measure_singleton (h : IsBoundedDensityAtom μ L) (a : ℝ) : μ {a} = 0 := by
  apply le_zero_iff.mp
  calc
    μ {a} ≤ ENNReal.ofReal L * volume ({a} : Set ℝ) :=
      h.measure_le_volume (MeasurableSet.singleton a)
    _ = 0 := by simp

/-- A nonconstant scalar affine function of a bounded-density atom vanishes
only on a null set. -/
theorem measure_affine_eq_zero (h : IsBoundedDensityAtom μ L)
    (a c : ℝ) (hc : c ≠ 0) : μ {x : ℝ | a + x * c = 0} = 0 := by
  have hset : {x : ℝ | a + x * c = 0} = {-a / c} := by
    ext x
    simp only [mem_setOf_eq, mem_singleton_iff]
    constructor
    · intro hx
      apply (eq_div_iff hc).2
      linarith
    · intro hx
      have hx' := (eq_div_iff hc).1 hx
      linarith
  rw [hset, h.measure_singleton]

/-- The variance-one hypothesis gives the scalar Chebyshev estimate used in
the large deterministic-center case of the affine logarithm lemma. -/
theorem measure_abs_ge_le (h : IsBoundedDensityAtom μ L) (t : ℝ) (ht : 0 < t) :
    μ {x : ℝ | t ≤ |x|} ≤ ENNReal.ofReal (1 / t ^ 2) := by
  letI := h.toIsProbabilityMeasure
  have hmem : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 h.integrable_sq
  have hvar : ProbabilityTheory.variance (fun x : ℝ => x) μ = 1 := by
    calc
      ProbabilityTheory.variance (fun x : ℝ => x) μ = ∫ x : ℝ, x ^ 2 ∂μ :=
        ProbabilityTheory.variance_of_integral_eq_zero
          (X := fun x : ℝ => x) measurable_id.aemeasurable h.centered
      _ = 1 := h.variance_one
  simpa [h.centered, hvar] using
    (ProbabilityTheory.meas_ge_le_variance_div_sq hmem ht)

/-- Coordinate Chebyshev estimate on the canonical finite product law. -/
theorem measure_pi_abs_apply_ge_le (h : IsBoundedDensityAtom μ L)
    {p : ℕ} (i : Fin p) (t : ℝ) (ht : 0 < t) :
    (Measure.pi fun _ : Fin p => μ) {x : Fin p → ℝ | t ≤ |x i|} ≤
      ENNReal.ofReal (1 / t ^ 2) := by
  letI := h.toIsProbabilityMeasure
  let ν : Measure (Fin p → ℝ) := Measure.pi fun _ : Fin p => μ
  let s : Set ℝ := {x : ℝ | t ≤ |x|}
  have hs : MeasurableSet s := by
    exact measurableSet_le measurable_const continuous_abs.measurable
  have hmap := congrArg (fun m : Measure ℝ => m s)
    (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin p => μ) i).map_eq
  rw [Measure.map_apply (measurable_pi_apply i) hs] at hmap
  change ν ((Function.eval i) ⁻¹' s) ≤ ENNReal.ofReal (1 / t ^ 2)
  rw [hmap]
  exact h.measure_abs_ge_le t ht

/-- A union-bound version of Chebyshev for the sup norm of a nonempty finite
sample.  The right side is `p / t²`, with `p = n+1`. -/
theorem measure_pi_norm_ge_le (h : IsBoundedDensityAtom μ L)
    {n : ℕ} (t : ℝ) (ht : 0 < t) :
    (Measure.pi fun _ : Fin (n + 1) => μ)
        {x : Fin (n + 1) → ℝ | t ≤ ‖x‖} ≤
      ENNReal.ofReal (((n + 1 : ℕ) : ℝ) / t ^ 2) := by
  letI := h.toIsProbabilityMeasure
  let ν : Measure (Fin (n + 1) → ℝ) := Measure.pi fun _ : Fin (n + 1) => μ
  have hsubset :
      {x : Fin (n + 1) → ℝ | t ≤ ‖x‖} ⊆
        ⋃ i : Fin (n + 1), {x : Fin (n + 1) → ℝ | t ≤ |x i|} := by
    intro x hx
    obtain ⟨i, hi⟩ := (IsGreatest.pi_norm x).1
    refine mem_iUnion.2 ⟨i, ?_⟩
    calc
      t ≤ ‖x‖ := hx
      _ = ‖x i‖ := hi.symm
      _ = |x i| := Real.norm_eq_abs _
  calc
    ν {x : Fin (n + 1) → ℝ | t ≤ ‖x‖} ≤
        ν (⋃ i : Fin (n + 1), {x : Fin (n + 1) → ℝ | t ≤ |x i|}) :=
      measure_mono hsubset
    _ ≤ ∑ i : Fin (n + 1),
        ν {x : Fin (n + 1) → ℝ | t ≤ |x i|} :=
      measure_iUnion_fintype_le ν _
    _ ≤ ∑ _i : Fin (n + 1), ENNReal.ofReal (1 / t ^ 2) := by
      exact Finset.sum_le_sum fun i _ => h.measure_pi_abs_apply_ge_le i t ht
    _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) / t ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [nsmul_eq_mul]
      have hcast :
          ENNReal.ofReal (((n + 1 : ℕ) : ℝ)) = ((n + 1 : ℕ) : ℝ≥0∞) := by
        exact ENNReal.ofReal_natCast (n + 1)
      calc
        ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / t ^ 2) =
            ENNReal.ofReal ((n + 1 : ℕ) : ℝ) * ENNReal.ofReal (1 / t ^ 2) := by
          rw [hcast]
        _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * (1 / t ^ 2)) :=
          (ENNReal.ofReal_mul (Nat.cast_nonneg (n + 1))).symm
        _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) / t ^ 2) := by
          congr 1
          ring

/-- Dimension-free vector small-ball estimate.  A norming real functional
supplied by Hahn--Banach reduces the assertion to the scalar interval bound.
No Hilbert structure and no finite-dimensionality are needed. -/
theorem measure_norm_add_smul_le (h : IsBoundedDensityAtom μ L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a w : E) (hw : w ≠ 0) (r : ℝ) (hr : 0 ≤ r) :
    μ {x : ℝ | ‖a + x • w‖ ≤ r} ≤
      ENNReal.ofReal (2 * L * r / ‖w‖) := by
  obtain ⟨φ, hφ, hφw⟩ := exists_dual_vector'' ℝ w
  have hsubset :
      {x : ℝ | ‖a + x • w‖ ≤ r} ⊆
        {x : ℝ | |φ a + x * ‖w‖| ≤ r} := by
    intro x hx
    have hnorm : |φ (a + x • w)| ≤ ‖a + x • w‖ := by
      calc
        |φ (a + x • w)| = ‖φ (a + x • w)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖φ‖ * ‖a + x • w‖ := φ.le_opNorm _
        _ ≤ 1 * ‖a + x • w‖ :=
          mul_le_mul_of_nonneg_right hφ (norm_nonneg _)
        _ = ‖a + x • w‖ := one_mul _
    have happly : φ (a + x • w) = φ a + x * ‖w‖ := by
      simp [hφw]
    rw [happly] at hnorm
    exact hnorm.trans hx
  exact (measure_mono hsubset).trans (by
    simpa [abs_of_nonneg (norm_nonneg w)] using
      h.measure_abs_add_mul_le (φ a) ‖w‖ r (norm_ne_zero_iff.mpr hw) hr)

end IsBoundedDensityAtom

end BernoulliSection10
