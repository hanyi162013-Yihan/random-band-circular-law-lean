import CircularLawSection6.RowLogUniformBound
import CircularLawSection6.CyclicMatrix
import CircularLawSection4.FlatIIDRows
import CircularLawSection4.PiRestrictMarginal

/-! # Transporting the actual cyclic atoms to IID matrix rows

For each row, the map from a column to its cyclic displacement is a
permutation. Combining these permutations with the existing finite-product
currying theorem identifies the row law exactly. Determinants are unchanged
by the simultaneous finite-index reindexing.
-/

open MeasureTheory ProbabilityTheory CircularLawSection4

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

attribute [local instance] iidMeasure_isProbability

def cyclicColumnCoordinate (N : ℕ) [NeZero N] (k : Fin N × Fin N) : ZMod N × ZMod N :=
  (ZMod.finEquiv N k.1, ZMod.finEquiv N k.2 - ZMod.finEquiv N k.1)

theorem cyclicColumnCoordinate_injective (N : ℕ) [NeZero N] :
    Function.Injective (cyclicColumnCoordinate N) := by
  intro a b h
  have hi : ZMod.finEquiv N a.1 = ZMod.finEquiv N b.1 := congrArg Prod.fst h
  have hj : ZMod.finEquiv N a.2 - ZMod.finEquiv N a.1 =
      ZMod.finEquiv N b.2 - ZMod.finEquiv N b.1 := congrArg Prod.snd h
  rw [hi] at hj
  exact Prod.ext ((ZMod.finEquiv N).injective hi)
    ((ZMod.finEquiv N).injective (sub_left_inj.1 hj))

def cyclicColumnSample (N : ℕ) [NeZero N]
    (ω : ZMod N × ZMod N → ℂ) : Fin N → Fin N → ℂ :=
  fun i j => ω (cyclicColumnCoordinate N (i, j))

theorem cyclicColumnSample_measurePreserving (N : ℕ) [NeZero N]
    (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    MeasurePreserving (cyclicColumnSample N) (cyclicAtomLaw N ν)
      (iidMeasure (iidMeasure ν N) N) := by
  have hr := measurePreserving_pi_restrict_injective (cyclicColumnCoordinate N)
    (cyclicColumnCoordinate_injective N) ν
  have hc := measurePreserving_curry_fin_iid N N ν
  unfold cyclicColumnSample cyclicAtomLaw
  rw [iidMeasure_eq_pi]
  simp_rw [iidMeasure_eq_pi ν N]
  simpa only [MeasurableEquiv.coe_curry, Function.curry, Function.comp_def] using hc.comp hr

def cyclicRowAmplitude (N : ℕ) [NeZero N] (q : ZMod N → ℝ) (r : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (r : ℂ) * (Real.sqrt (q (ZMod.finEquiv N j - ZMod.finEquiv N i)) : ℂ)

def cyclicRawLogDet (N : ℕ) [NeZero N] (q : ZMod N → ℝ) (r : ℝ) (z : ℂ)
    (ω : ZMod N × ZMod N → ℂ) : ℝ :=
  Real.log ‖((r : ℂ) • weightedCyclicMatrix N q ω - z • 1).det‖

theorem weightedRowsLogDet_cyclicColumnSample (N : ℕ) [NeZero N]
    (q : ZMod N → ℝ) (r : ℝ) (z : ℂ) (ω : ZMod N × ZMod N → ℂ) :
    weightedRowsLogDet (cyclicRowAmplitude N q r) z (cyclicColumnSample N ω) =
      cyclicRawLogDet N q r z ω := by
  have he : weightedRowsMatrix (cyclicRowAmplitude N q r) (cyclicColumnSample N ω) - z • 1 =
      ((r : ℂ) • weightedCyclicMatrix N q ω - z • 1).submatrix
        (ZMod.finEquiv N) (ZMod.finEquiv N) := by
    ext i j
    simp [weightedRowsMatrix, cyclicRowAmplitude, cyclicColumnSample, cyclicColumnCoordinate,
      weightedCyclicMatrix, Matrix.submatrix, Matrix.one_apply, mul_assoc]
  unfold weightedRowsLogDet cyclicRawLogDet
  rw [he, Matrix.det_submatrix_equiv_self (ZMod.finEquiv N).toEquiv]

theorem cyclicRowAmplitude_diagonal (N : ℕ) [NeZero N]
    (q : ZMod N → ℝ) {r : ℝ} (hr : 0 ≤ r) (i : Fin N) :
    ‖cyclicRowAmplitude N q r i i‖ = r * Real.sqrt (q 0) := by
  simp only [cyclicRowAmplitude, sub_self, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Actual cyclic determinant concentration, on its original atom sample
space. No equality-in-law or determinant-integrability premise is required. -/
theorem cyclicRawLogDet_memLp_and_variance (n : ℕ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] {L δ : ℝ}
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (q : ZMod (n + 1) → ℝ) {r : ℝ} (hr : 0 ≤ r) (z : ℂ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : δ ≤ r * Real.sqrt (q 0))
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    MemLp (cyclicRawLogDet (n + 1) q r z) 2 (cyclicAtomLaw (n + 1) ν) ∧
      variance (cyclicRawLogDet (n + 1) q r z) (cyclicAtomLaw (n + 1) ν) ≤
        2 * (n + 1 : ℝ) * affineRowLogBound n δ L z := by
  have hrows := weightedRowsLogDet_memLp_and_variance ν hν hL
    (cyclicRowAmplitude (n + 1) q r) z hδ hδ1
    (fun i => by rw [cyclicRowAmplitude_diagonal _ _ hr]; exact hb) hInt hSecond
  have hmp := cyclicColumnSample_measurePreserving (n + 1) ν
  constructor
  · simpa only [Function.comp_def, weightedRowsLogDet_cyclicColumnSample] using
      hrows.1.comp_measurePreserving hmp
  · have he := hmp.variance_fun_comp
      (weightedRowsLogDet_measurable (cyclicRowAmplitude (n + 1) q r) z).aemeasurable
    simp only [weightedRowsLogDet_cyclicColumnSample] at he
    exact he.trans_le hrows.2

end CircularLawSection6
