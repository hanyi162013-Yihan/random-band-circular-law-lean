import BernoulliSection10.BoundedDensity
import CircularLawSection4.ProductSmallBall
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Planar bounded-density atoms

The public hypotheses concern the joint law on `ℂ`. No independence of
real and imaginary parts, isotropy, or vanishing complex second moment is
assumed. The numerical bound is enlarged internally to `max 1 L` only.
The disk estimate is imported from the verified Section 4 library.
-/

open scoped ENNReal NNReal Topology
open Set MeasureTheory

namespace BernoulliSection10Complex

/-- The original planar atom hypotheses, with second moment `E ‖ξ‖² = 1`. -/
structure IsPlanarDensityAtom (μ : Measure ℂ) (L : ℝ) : Prop where
  nonneg : 0 ≤ L
  probability : μ univ = 1
  density_le : μ ≤ ENNReal.ofReal L • volume
  integrable_id : Integrable (fun x : ℂ => x) μ
  centered : ∫ x : ℂ, x ∂μ = 0
  integrable_sq : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ
  variance_one : ∫ x : ℂ, ‖x‖ ^ 2 ∂μ = 1

/-- Internal numerical normalization, discharged by `normalized` below. -/
structure IsBoundedDensityAtom (μ : Measure ℂ) (L : ℝ) : Prop
    extends IsPlanarDensityAtom μ L where
  one_le : 1 ≤ L

namespace IsPlanarDensityAtom

variable {μ : Measure ℂ} {L : ℝ}

def toIsProbabilityMeasure (h : IsPlanarDensityAtom μ L) : IsProbabilityMeasure μ :=
  ⟨h.probability⟩

theorem mono (h : IsPlanarDensityAtom μ L) {K : ℝ} (hLK : L ≤ K) :
    IsPlanarDensityAtom μ K := by
  refine { h with nonneg := h.nonneg.trans hLK, density_le := ?_ }
  exact h.density_le.trans (by
    intro s
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hLK) _)

/-- Every public planar model yields the internal normalized model. -/
theorem normalized (h : IsPlanarDensityAtom μ L) :
    IsBoundedDensityAtom μ (max 1 L) :=
  { h.mono (le_max_right _ _) with one_le := le_max_left _ _ }

theorem complexBallBound (h : IsPlanarDensityAtom μ L) :
    CircularLawSection4.ComplexBallBound μ (ENNReal.ofReal L) :=
  CircularLawSection4.complexBallBound_of_le_smul_volume h.density_le

end IsPlanarDensityAtom

namespace IsBoundedDensityAtom

variable {μ : Measure ℂ} {L : ℝ}

def toIsProbabilityMeasure (h : IsBoundedDensityAtom μ L) : IsProbabilityMeasure μ :=
  h.toIsPlanarDensityAtom.toIsProbabilityMeasure

theorem measure_le_volume (h : IsBoundedDensityAtom μ L) {s : Set ℂ}
    (hs : MeasurableSet s) : μ s ≤ ENNReal.ofReal L * volume s := by
  simpa [Measure.smul_apply, hs] using h.density_le s

/-- The sharp quadratic disk bound, available without the normalization. -/
theorem measure_closedBall_le (h : IsBoundedDensityAtom μ L) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) :
    μ (Metric.closedBall c r) ≤
      ENNReal.ofReal Real.pi * ENNReal.ofReal L * ENNReal.ofReal r ^ 2 :=
  h.toIsPlanarDensityAtom.complexBallBound c r hr

/-- Probability and planar area imply the linear envelope used in the
dimension-free affine logarithm argument. The normalization `L ≥ 1` is
internal; arbitrary original bounds are handled by `normalized`. -/
theorem measure_norm_sub_le (h : IsBoundedDensityAtom μ L) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) : μ {x : ℂ | ‖x - c‖ ≤ r} ≤ ENNReal.ofReal (2 * L * r) := by
  letI := h.toIsProbabilityMeasure
  by_cases hlarge : 1 ≤ 2 * L * r
  · exact prob_le_one.trans (ENNReal.one_le_ofReal.mpr hlarge)
  have hsmall : 2 * L * r < 1 := lt_of_not_ge hlarge
  have hrhalf : r ≤ 1 / 2 := by nlinarith [h.one_le]
  have hquad : Real.pi * L * r ^ 2 ≤ 2 * L * r := by
    have harea : Real.pi * r ≤ 2 := by
      nlinarith [Real.pi_lt_four, Real.pi_pos]
    nlinarith [mul_nonneg h.nonneg hr,
      mul_nonneg (show 0 ≤ 2 - Real.pi * r by linarith) (mul_nonneg h.nonneg hr)]
  calc
    μ {x : ℂ | ‖x - c‖ ≤ r} = μ (Metric.closedBall c r) := by
      congr 1
      ext x
      simp [Metric.mem_closedBall, dist_eq_norm]
    _ ≤ ENNReal.ofReal Real.pi * ENNReal.ofReal L * ENNReal.ofReal r ^ 2 :=
      h.measure_closedBall_le c r hr
    _ = ENNReal.ofReal (Real.pi * L * r ^ 2) := by
      rw [← ENNReal.ofReal_mul Real.pi_pos.le, ← ENNReal.ofReal_pow hr,
        ← ENNReal.ofReal_mul (mul_nonneg Real.pi_pos.le h.nonneg)]
    _ ≤ ENNReal.ofReal (2 * L * r) := ENNReal.ofReal_le_ofReal hquad

theorem measure_norm_add_mul_le (h : IsBoundedDensityAtom μ L)
    (a c : ℂ) (r : ℝ) (hc : c ≠ 0) (hr : 0 ≤ r) :
    μ {x : ℂ | ‖a + x * c‖ ≤ r} ≤ ENNReal.ofReal (2 * L * r / ‖c‖) := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hset : {x : ℂ | ‖a + x * c‖ ≤ r} =
      {x : ℂ | ‖x - (-a / c)‖ ≤ r / ‖c‖} := by
    ext x
    have halg : a + x * c = c * (x - (-a / c)) := by field_simp; ring
    simp only [mem_setOf_eq, halg, norm_mul]
    rw [le_div_iff₀ hcpos, mul_comm]
  rw [hset]
  convert h.measure_norm_sub_le (-a / c) (r / ‖c‖) (div_nonneg hr hcpos.le) using 1 <;>
    congr 1 <;> ring

theorem measure_singleton (h : IsBoundedDensityAtom μ L) (a : ℂ) : μ {a} = 0 := by
  apply le_zero_iff.mp
  exact (h.measure_le_volume (MeasurableSet.singleton a)).trans (by simp)

theorem measure_affine_eq_zero (h : IsBoundedDensityAtom μ L)
    (a c : ℂ) (hc : c ≠ 0) : μ {x : ℂ | a + x * c = 0} = 0 := by
  have hset : {x : ℂ | a + x * c = 0} = {-a / c} := by
    ext x
    simp only [mem_setOf_eq, mem_singleton_iff, eq_div_iff hc]
    constructor <;> intro hx <;> linear_combination hx
  rw [hset, h.measure_singleton]

/-- Norm-square Markov inequality; no condition on `E ξ²` is used. -/
theorem measure_norm_ge_le (h : IsBoundedDensityAtom μ L) (t : ℝ) (ht : 0 < t) :
    μ {x : ℂ | t ≤ ‖x‖} ≤ ENNReal.ofReal (1 / t ^ 2) := by
  letI := h.toIsProbabilityMeasure
  have hset : {x : ℂ | t ^ 2 ≤ ‖x‖ ^ 2} = {x : ℂ | t ≤ ‖x‖} := by
    ext x
    simp only [mem_setOf_eq]
    constructor <;> intro hx <;> nlinarith [norm_nonneg x]
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun x : ℂ => sq_nonneg ‖x‖) h.integrable_sq (t ^ 2)
  rw [h.variance_one, hset] at hm
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  simpa [mul_comm, measureReal_def] using hm

/-- Complex Hahn--Banach reduces vector small balls to planar scalar disks. -/
theorem measure_norm_add_smul_le (h : IsBoundedDensityAtom μ L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a w : E) (hw : w ≠ 0) (r : ℝ) (hr : 0 ≤ r) :
    μ {x : ℂ | ‖a + x • w‖ ≤ r} ≤ ENNReal.ofReal (2 * L * r / ‖w‖) := by
  obtain ⟨φ, hφ, hφw⟩ := exists_dual_vector'' ℂ w
  have hsubset : {x : ℂ | ‖a + x • w‖ ≤ r} ⊆
      {x : ℂ | ‖φ a + x * (‖w‖ : ℂ)‖ ≤ r} := by
    intro x hx
    have hnorm : ‖φ (a + x • w)‖ ≤ ‖a + x • w‖ := by
      calc
        ‖φ (a + x • w)‖ ≤ ‖φ‖ * ‖a + x • w‖ := φ.le_opNorm _
        _ ≤ 1 * ‖a + x • w‖ := mul_le_mul_of_nonneg_right hφ (norm_nonneg _)
        _ = ‖a + x • w‖ := one_mul _
    simpa [hφw] using hnorm.trans hx
  exact (measure_mono hsubset).trans (by
    simpa using h.measure_norm_add_mul_le (φ a) (‖w‖ : ℂ) r
      (by exact_mod_cast norm_ne_zero_iff.mpr hw) hr)

theorem measure_pi_norm_apply_ge_le (h : IsBoundedDensityAtom μ L)
    {p : ℕ} (i : Fin p) (t : ℝ) (ht : 0 < t) :
    (Measure.pi fun _ : Fin p => μ) {x : Fin p → ℂ | t ≤ ‖x i‖} ≤
      ENNReal.ofReal (1 / t ^ 2) := by
  letI := h.toIsProbabilityMeasure
  let ν : Measure (Fin p → ℂ) := Measure.pi fun _ : Fin p => μ
  let s : Set ℂ := {x : ℂ | t ≤ ‖x‖}
  have hs : MeasurableSet s := by
    exact measurableSet_le measurable_const continuous_norm.measurable
  have hmap := congrArg (fun m : Measure ℂ => m s)
    (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin p => μ) i).map_eq
  rw [Measure.map_apply (measurable_pi_apply i) hs] at hmap
  change ν ((Function.eval i) ⁻¹' s) ≤ ENNReal.ofReal (1 / t ^ 2)
  rw [hmap]
  exact h.measure_norm_ge_le t ht

/-- A union-bound version of Chebyshev for the sup norm of a nonempty finite
sample.  The right side is `p / t²`, with `p = n+1`. -/
theorem measure_pi_norm_ge_le (h : IsBoundedDensityAtom μ L)
    {n : ℕ} (t : ℝ) (ht : 0 < t) :
    (Measure.pi fun _ : Fin (n + 1) => μ)
        {x : Fin (n + 1) → ℂ | t ≤ ‖x‖} ≤
      ENNReal.ofReal (((n + 1 : ℕ) : ℝ) / t ^ 2) := by
  letI := h.toIsProbabilityMeasure
  let ν : Measure (Fin (n + 1) → ℂ) := Measure.pi fun _ : Fin (n + 1) => μ
  have hsubset :
      {x : Fin (n + 1) → ℂ | t ≤ ‖x‖} ⊆
        ⋃ i : Fin (n + 1), {x : Fin (n + 1) → ℂ | t ≤ ‖x i‖} := by
    intro x hx
    obtain ⟨i, hi⟩ := (IsGreatest.pi_norm x).1
    refine mem_iUnion.2 ⟨i, ?_⟩
    calc
      t ≤ ‖x‖ := hx
      _ = ‖x i‖ := hi.symm
  calc
    ν {x : Fin (n + 1) → ℂ | t ≤ ‖x‖} ≤
        ν (⋃ i : Fin (n + 1), {x : Fin (n + 1) → ℂ | t ≤ ‖x i‖}) :=
      measure_mono hsubset
    _ ≤ ∑ i : Fin (n + 1),
        ν {x : Fin (n + 1) → ℂ | t ≤ ‖x i‖} :=
      measure_iUnion_fintype_le ν _
    _ ≤ ∑ _i : Fin (n + 1), ENNReal.ofReal (1 / t ^ 2) := by
      exact Finset.sum_le_sum fun i _ => h.measure_pi_norm_apply_ge_le i t ht
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

end IsBoundedDensityAtom

end BernoulliSection10Complex
