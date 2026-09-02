import BernoulliSection9.ExternalInputs
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.OpenPos

open scoped Matrix.Norms.L2Operator ProbabilityTheory BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

open Metric Set

namespace BernoulliSection9

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 1000000 in
theorem sphere_quarter_packing_bound (n : ℕ) (hn : 0 < n) :
    Metric.packingNumber (1 / 4 : ℝ≥0)
        (Metric.sphere (0 : E n) 1) ≤ (9 ^ n : ℕ) := by
  let A : Set (E n) := Metric.sphere 0 1
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have htb : TotallyBounded A := (isCompact_sphere (0 : E n) 1).totallyBounded
  obtain ⟨t, htA, htfin, htcov⟩ :=
    Metric.finite_approx_of_totallyBounded htb (1 / 8 : ℝ) (by norm_num)
  have htcover : Metric.IsCover (1 / 8 : ℝ≥0) A t := by
    intro x hx
    obtain ⟨y, hyt, hxy⟩ := by simpa only [Set.mem_iUnion] using htcov hx
    refine ⟨y, hyt, ?_⟩
    have hd : dist x y < (1 / 8 : ℝ) := by
      simpa [Metric.mem_ball, dist_comm] using hxy
    change edist x y ≤ ((↑(1 / 8 : ℝ≥0)) : ℝ≥0∞)
    rw [edist_dist, ENNReal.coe_nnreal_eq]
    norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    exact ENNReal.ofReal_le_ofReal hd.le
  have hpackFinite :
      Metric.packingNumber (1 / 4 : ℝ≥0) A < ⊤ := by
    calc
      Metric.packingNumber (1 / 4 : ℝ≥0) A
          ≤ Metric.externalCoveringNumber (1 / 8 : ℝ≥0) A := by
            convert Metric.packingNumber_two_mul_le_externalCoveringNumber
              (1 / 8 : ℝ≥0) A using 1 <;> norm_num
      _ ≤ t.encard := htcover.externalCoveringNumber_le_encard
      _ < ⊤ := Set.encard_lt_top_iff.mpr htfin
  have hpackNe : Metric.packingNumber (1 / 4 : ℝ≥0) A ≠ ⊤ := ne_of_lt hpackFinite
  let C : Set (E n) := Metric.maximalSeparatedSet (1 / 4 : ℝ≥0) A
  have hCsub : C ⊆ A := Metric.maximalSeparatedSet_subset
  have hCsep := Metric.isSeparated_maximalSeparatedSet
    (A := A) (ε := (1 / 4 : ℝ≥0))
  have hCfin : C.Finite := by
    dsimp [C, Metric.maximalSeparatedSet]
    rw [dif_pos hpackNe]
    exact (Metric.exists_set_encard_eq_packingNumber hpackNe).choose_spec.2.1
  let F : Finset (E n) := hCfin.toFinset
  have hFmem {x : E n} : x ∈ F ↔ x ∈ C := by
    simp [F]
  have hdisj : (↑F : Set (E n)).PairwiseDisjoint
      (fun x ↦ Metric.ball x (1 / 8 : ℝ)) := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    have hdx : dist z x < (1 / 8 : ℝ) := Metric.mem_ball.mp hzx
    have hdy : dist z y < (1 / 8 : ℝ) := Metric.mem_ball.mp hzy
    have hsep : (1 / 4 : ℝ) < dist x y := by
      have := hCsep (hFmem.mp hx) (hFmem.mp hy) hxy
      change ((↑(1 / 4 : ℝ≥0)) : ℝ≥0∞) < edist x y at this
      rw [edist_dist, ENNReal.coe_nnreal_eq] at this
      norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at this
      exact (ENNReal.ofReal_lt_ofReal_iff').mp this |>.1
    have htri : dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
    rw [dist_comm x z] at htri
    linarith
  have hunionSub :
      (⋃ x ∈ F, Metric.ball x (1 / 8 : ℝ)) ⊆
        Metric.ball (0 : E n) (9 / 8 : ℝ) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hxF, hzx⟩ := hz
    have hxC : x ∈ C := hFmem.mp hxF
    have hxA : x ∈ A := hCsub hxC
    have hnormx : ‖x‖ = 1 := by
      simpa [A, Metric.mem_sphere, dist_eq_norm] using hxA
    have hdist : dist z x < (1 / 8 : ℝ) := Metric.mem_ball.mp hzx
    have hnormz : ‖z‖ < 9 / 8 := calc
      ‖z‖ = dist z 0 := by simp
      _ ≤ dist z x + dist x 0 := dist_triangle _ _ _
      _ < (1 / 8 : ℝ) + 1 := by
        simpa [dist_eq_norm, hnormx] using (add_lt_add_right hdist 1)
      _ = 9 / 8 := by norm_num
    simpa only [Metric.mem_ball, dist_zero_right] using hnormz
  have hvol :
      (F.card : ℝ≥0∞) * volume (Metric.ball (0 : E n) (1 / 8 : ℝ)) ≤
        volume (Metric.ball (0 : E n) (9 / 8 : ℝ)) := by
    calc
      (F.card : ℝ≥0∞) * volume (Metric.ball (0 : E n) (1 / 8 : ℝ)) =
          ∑ x ∈ F, volume (Metric.ball x (1 / 8 : ℝ)) := by
            simp [EuclideanSpace.volume_ball]
      _ = volume (⋃ x ∈ F, Metric.ball x (1 / 8 : ℝ)) := by
        rw [measure_biUnion_finset hdisj (fun _ _ ↦ measurableSet_ball)]
      _ ≤ volume (Metric.ball (0 : E n) (9 / 8 : ℝ)) := measure_mono hunionSub
  have hscale :
      volume (Metric.ball (0 : E n) (9 / 8 : ℝ)) =
        (9 ^ n : ℕ) * volume (Metric.ball (0 : E n) (1 / 8 : ℝ)) := by
    rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
    rw [show ENNReal.ofReal (9 / 8 : ℝ) =
        9 * ENNReal.ofReal (1 / 8 : ℝ) by
          calc
            ENNReal.ofReal (9 / 8 : ℝ) = ENNReal.ofReal ((9 : ℝ) * (1 / 8)) := by
              norm_num
            _ = ENNReal.ofReal 9 * ENNReal.ofReal (1 / 8 : ℝ) :=
              ENNReal.ofReal_mul (by norm_num)
            _ = 9 * ENNReal.ofReal (1 / 8 : ℝ) := by norm_num,
      mul_pow]
    simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [hscale] at hvol
  have hsmall0 : volume (Metric.ball (0 : E n) (1 / 8 : ℝ)) ≠ 0 :=
    ne_of_gt (measure_ball_pos volume (0 : E n) (by norm_num))
  have hsmallTop : volume (Metric.ball (0 : E n) (1 / 8 : ℝ)) ≠ ⊤ :=
    ne_of_lt measure_ball_lt_top
  have hcard : F.card ≤ 9 ^ n := by
    exact_mod_cast ((ENNReal.mul_le_mul_iff_left hsmall0 hsmallTop).mp hvol)
  rw [← Metric.encard_maximalSeparatedSet hpackNe]
  change C.encard ≤ (9 ^ n : ℕ)
  letI := hCfin.fintype
  rw [Set.encard_eq_coe_toFinset_card C]
  exact_mod_cast (by simpa [F] using hcard)

/-- A concrete finite quarter-net of the real Euclidean unit sphere, with
the standard volume-packing cardinality bound. -/
theorem exists_sphere_quarter_net (n : ℕ) (hn : 0 < n) :
    ∃ N : Finset (E n),
      N.card ≤ 9 ^ n ∧
      (∀ x ∈ N, ‖x‖ = 1) ∧
      ∀ x : E n, ‖x‖ = 1 → ∃ y ∈ N, ‖x - y‖ ≤ (1 / 4 : ℝ) := by
  let A : Set (E n) := Metric.sphere 0 1
  have hpack := sphere_quarter_packing_bound n hn
  have hpackNe : Metric.packingNumber (1 / 4 : ℝ≥0) A ≠ ⊤ := by
    apply ne_of_lt
    exact hpack.trans_lt (ENat.coe_lt_top (9 ^ n))
  let C : Set (E n) := Metric.maximalSeparatedSet (1 / 4 : ℝ≥0) A
  have hCfin : C.Finite := by
    dsimp [C, Metric.maximalSeparatedSet]
    rw [dif_pos hpackNe]
    exact (Metric.exists_set_encard_eq_packingNumber hpackNe).choose_spec.2.1
  let N : Finset (E n) := hCfin.toFinset
  refine ⟨N, ?_, ?_, ?_⟩
  · have henc := Metric.encard_maximalSeparatedSet hpackNe
    have hNC : (N : Set (E n)) = C := by ext x; simp [N]
    have hNenc : (N.card : ℕ∞) = C.encard := by
      rw [← hNC]
      simp
    have hNatCast : (N.card : ℕ∞) ≤ ((9 ^ n : ℕ) : ℕ∞) := by
      rw [hNenc, henc]
      exact hpack
    exact_mod_cast hNatCast
  · intro x hx
    have hxC : x ∈ C := by simpa [N] using hx
    have hxA : x ∈ A := Metric.maximalSeparatedSet_subset hxC
    simpa [A, Metric.mem_sphere, dist_eq_norm] using hxA
  · intro x hx
    have hxA : x ∈ A := by simpa [A, Metric.mem_sphere, dist_eq_norm] using hx
    obtain ⟨y, hyC, hxy⟩ := Metric.isCover_maximalSeparatedSet hpackNe hxA
    refine ⟨y, by simpa [N, C] using hyC, ?_⟩
    change edist x y ≤ ((↑(1 / 4 : ℝ≥0)) : ℝ≥0∞) at hxy
    rw [edist_dist, ENNReal.coe_nnreal_eq] at hxy
    norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at hxy
    have hd : dist x y ≤ (1 / 4 : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hxy
    simpa [dist_eq_norm] using hd

def rawRealMatrix
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n) (ω : Ω) :
    Matrix (Fin n) (Fin n) ℝ := fun i j ↦ S.atom (i, j) ω

def realBilinear
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n)
    (x y : E n) (ω : Ω) : ℝ :=
  ∑ p : Fin n × Fin n, y p.1 * x p.2 * S.atom p ω

def subgaussianEnvelope
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n) : ℝ≥0 :=
  S.subgaussianParameter + 1

lemma subgaussianEnvelope_pos
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n) :
    0 < subgaussianEnvelope S := by
  exact lt_of_lt_of_le zero_lt_one (by simp [subgaussianEnvelope])

lemma _root_.ProbabilityTheory.HasSubgaussianMGF.mono_parameter
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {c d : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (hcd : c ≤ d) :
    HasSubgaussianMGF X d μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := h.mgf_le t |>.trans <| Real.exp_le_exp.mpr <| by
    have ht : 0 ≤ t ^ 2 := sq_nonneg t
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hcd) ht) (by norm_num)

lemma sum_coordinate_sq_eq_norm_sq {n : ℕ} (x : E n) :
    (∑ i : Fin n, (x i) ^ 2) = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Real.norm_eq_abs, sq_abs]

lemma sum_bilinear_coeff_sq {n : ℕ} (x y : E n)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (∑ p : Fin n × Fin n, (y p.1 * x p.2) ^ 2) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [mul_pow]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_coordinate_sq_eq_norm_sq,
    sum_coordinate_sq_eq_norm_sq, hx, hy]
  norm_num

set_option maxHeartbeats 1000000 in
theorem hasSubgaussianMGF_realBilinear
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n)
    (x y : E n) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    HasSubgaussianMGF (realBilinear S x y) (subgaussianEnvelope S) μ := by
  let c : Fin n × Fin n → ℝ≥0 := fun p ↦
    Real.toNNReal ((y p.1 * x p.2) ^ 2) * S.subgaussianParameter
  let X : Fin n × Fin n → Ω → ℝ := fun p ω ↦
    (y p.1 * x p.2) * S.atom p ω
  have hXindep : iIndepFun X μ := by
    dsimp [X]
    exact S.independent.comp
      (fun p r ↦ (y p.1 * x p.2) * r)
      (fun _ ↦ measurable_const.mul measurable_id)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hXindep
    (s := Finset.univ) (c := c) (fun p _ ↦ by
      convert (S.subgaussian p).const_mul (y p.1 * x p.2) using 1
      change Real.toNNReal ((y p.1 * x p.2) ^ 2) * S.subgaussianParameter = _
      rw [Real.toNNReal_of_nonneg (sq_nonneg _)]
      rfl)
  have hc : (∑ p : Fin n × Fin n, c p) = S.subgaussianParameter := by
    simp only [c]
    rw [← Finset.sum_mul]
    have ha :
        (∑ p : Fin n × Fin n,
          Real.toNNReal ((y p.1 * x p.2) ^ 2)) = 1 := by
      apply NNReal.eq
      simp only [NNReal.coe_sum, Real.coe_toNNReal _ (sq_nonneg _), NNReal.coe_one]
      exact sum_bilinear_coeff_sq x y hx hy
    rw [ha, one_mul]
  have hraw : HasSubgaussianMGF (realBilinear S x y)
      S.subgaussianParameter μ := by
    rw [hc] at hsum
    exact hsum.congr (ae_of_all _ fun ω ↦ by simp [realBilinear, X])
  exact hraw.mono_parameter (by simp [subgaussianEnvelope])

theorem realBilinear_abs_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n)
    (x y : E n) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |realBilinear S x y ω|} ≤
      2 * Real.exp (-t ^ 2 / (2 * (subgaussianEnvelope S : ℝ))) := by
  letI : IsProbabilityMeasure μ := S.independent.isProbabilityMeasure
  let Z := realBilinear S x y
  have hZ : HasSubgaussianMGF Z (subgaussianEnvelope S) μ :=
    hasSubgaussianMGF_realBilinear S x y hx hy
  have hright : μ.real {ω | t ≤ Z ω} ≤
      Real.exp (-t ^ 2 / (2 * (subgaussianEnvelope S : ℝ))) :=
    hZ.measure_ge_le ht
  have hleft : μ.real {ω | t ≤ -Z ω} ≤
      Real.exp (-t ^ 2 / (2 * (subgaussianEnvelope S : ℝ))) := by
    simpa only [Pi.neg_apply] using hZ.neg.measure_ge_le ht
  have hsub : {ω | t ≤ |Z ω|} ⊆ {ω | t ≤ Z ω} ∪ {ω | t ≤ -Z ω} := by
    intro ω hω
    by_cases hz : 0 ≤ Z ω
    · exact Or.inl (by simpa [abs_of_nonneg hz] using hω)
    · exact Or.inr (by simpa [abs_of_nonpos (le_of_not_ge hz)] using hω)
  calc
    μ.real {ω | t ≤ |realBilinear S x y ω|}
        ≤ μ.real ({ω | t ≤ Z ω} ∪ {ω | t ≤ -Z ω}) := by
          simpa [Z] using measureReal_mono hsub
    _ ≤ μ.real {ω | t ≤ Z ω} + μ.real {ω | t ≤ -Z ω} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-t ^ 2 / (2 * (subgaussianEnvelope S : ℝ))) +
          Real.exp (-t ^ 2 / (2 * (subgaussianEnvelope S : ℝ))) :=
      add_le_add hright hleft
    _ = 2 * Real.exp (-t ^ 2 / (2 * (subgaussianEnvelope S : ℝ))) := by ring

set_option maxHeartbeats 1000000 in
theorem opNorm_le_two_mul_of_quarter_net {n : ℕ}
    (T : E n →L[ℝ] E n) (N : Finset (E n))
    (hNunit : ∀ x ∈ N, ‖x‖ = 1)
    (hNcover : ∀ x : E n, ‖x‖ = 1 →
      ∃ y ∈ N, ‖x - y‖ ≤ (1 / 4 : ℝ))
    (t : ℝ) (ht : 0 ≤ t)
    (hgrid : ∀ x ∈ N, ∀ y ∈ N, |inner ℝ (T x) y| ≤ t) :
    ‖T‖ ≤ 2 * t := by
  have hpre : ‖T‖ ≤ t + ‖T‖ / 2 := by
    apply T.opNorm_le_of_re_inner_le (by positivity)
    intro x y hx hy
    obtain ⟨x0, hx0N, hxx0⟩ := hNcover x hx
    obtain ⟨y0, hy0N, hyy0⟩ := hNcover y hy
    have hx0 : ‖x0‖ = 1 := hNunit x0 hx0N
    have hy0 : ‖y0‖ = 1 := hNunit y0 hy0N
    have hfirst : |inner ℝ (T (x - x0)) y| ≤ ‖T‖ / 4 := by
      calc
        |inner ℝ (T (x - x0)) y| = ‖inner ℝ (T (x - x0)) y‖ := by
          rw [Real.norm_eq_abs]
        _ ≤ ‖T (x - x0)‖ * ‖y‖ := norm_inner_le_norm _ _
        _ ≤ (‖T‖ * ‖x - x0‖) * ‖y‖ := by
          gcongr
          exact T.le_opNorm (x - x0)
        _ ≤ (‖T‖ * (1 / 4 : ℝ)) * 1 := by
          gcongr
          simpa [hy]
        _ = ‖T‖ / 4 := by ring
    have hsecond : |inner ℝ (T x0) (y - y0)| ≤ ‖T‖ / 4 := by
      calc
        |inner ℝ (T x0) (y - y0)| = ‖inner ℝ (T x0) (y - y0)‖ := by
          rw [Real.norm_eq_abs]
        _ ≤ ‖T x0‖ * ‖y - y0‖ := norm_inner_le_norm _ _
        _ ≤ (‖T‖ * ‖x0‖) * ‖y - y0‖ := by
          gcongr
          exact T.le_opNorm x0
        _ ≤ (‖T‖ * 1) * (1 / 4 : ℝ) := by
          gcongr
          simpa [hx0]
        _ = ‖T‖ / 4 := by ring
    have heq : inner ℝ (T x) y =
        inner ℝ (T x0) y0 + inner ℝ (T (x - x0)) y +
          inner ℝ (T x0) (y - y0) := by
      simp only [map_sub, inner_sub_left, inner_sub_right]
      ring
    rw [RCLike.re_to_real, heq]
    calc
      inner ℝ (T x0) y0 + inner ℝ (T (x - x0)) y +
            inner ℝ (T x0) (y - y0)
          ≤ |inner ℝ (T x0) y0| + |inner ℝ (T (x - x0)) y| +
              |inner ℝ (T x0) (y - y0)| := by
            gcongr <;> exact le_abs_self _
      _ ≤ t + ‖T‖ / 4 + ‖T‖ / 4 := by
        gcongr
        exact hgrid x0 hx0N y0 hy0N
      _ = t + ‖T‖ / 2 := by ring
  linarith

lemma inner_rawRealMatrix_eq_realBilinear
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n)
    (x y : E n) (ω : Ω) :
    inner ℝ (((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ))
      (rawRealMatrix S ω)) x) y =
      realBilinear S x y ω := by
  change inner ℝ ((rawRealMatrix S ω).toEuclideanLin x) y = _
  simp only [Matrix.toEuclideanLin_apply,
    Matrix.mulVec, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    realBilinear, rawRealMatrix]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma two_mul_eightyOne_pow_mul_exp_le (n : ℕ) (hn : 0 < n) :
    2 * (81 : ℝ) ^ n * Real.exp (-200 * (n : ℝ)) ≤
      Real.exp (-(n : ℝ)) := by
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have htwo : (2 : ℝ) ≤ Real.exp (n : ℝ) := by
    calc
      (2 : ℝ) ≤ 1 + (n : ℝ) := by linarith
      _ ≤ Real.exp (n : ℝ) := by
        simpa [add_comm] using Real.add_one_le_exp (n : ℝ)
  have h81 : (81 : ℝ) ≤ Real.exp 81 := by
    calc
      (81 : ℝ) ≤ 1 + 81 := by norm_num
      _ ≤ Real.exp 81 := by
        simpa [add_comm] using Real.add_one_le_exp 81
  have h81pow : (81 : ℝ) ^ n ≤ Real.exp (81 * (n : ℝ)) := by
    calc
      (81 : ℝ) ^ n ≤ (Real.exp 81) ^ n := pow_le_pow_left₀ (by norm_num) h81 n
      _ = Real.exp (81 * (n : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  calc
    2 * (81 : ℝ) ^ n * Real.exp (-200 * (n : ℝ))
        ≤ Real.exp (n : ℝ) * Real.exp (81 * (n : ℝ)) *
            Real.exp (-200 * (n : ℝ)) := by
          gcongr
    _ = Real.exp (-118 * (n : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(n : ℝ)) := Real.exp_le_exp.mpr (by nlinarith)

set_option maxHeartbeats 1000000 in
theorem rawRealMatrix_opNorm_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n) (hn : 0 < n) :
    μ.real {ω | 40 * Real.sqrt (subgaussianEnvelope S : ℝ) *
          Real.sqrt n < ‖rawRealMatrix S ω‖} ≤
      Real.exp (-(n : ℝ)) := by
  letI : IsProbabilityMeasure μ := S.independent.isProbabilityMeasure
  obtain ⟨N, hNcard, hNunit, hNcover⟩ := exists_sphere_quarter_net n hn
  let κ : ℝ := (subgaussianEnvelope S : ℝ)
  let t : ℝ := 20 * Real.sqrt κ * Real.sqrt n
  have hκ : 0 < κ := by
    exact_mod_cast subgaussianEnvelope_pos S
  have hnR : 0 ≤ (n : ℝ) := by positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  let B : Set Ω := ⋃ p ∈ N.product N,
    {ω | t ≤ |realBilinear S p.1 p.2 ω|}
  have hbadSub :
      {ω | 40 * Real.sqrt κ * Real.sqrt n < ‖rawRealMatrix S ω‖} ⊆ B := by
    intro ω hω
    by_contra hωB
    have hgrid : ∀ x ∈ N, ∀ y ∈ N,
        |inner ℝ (((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ))
          (rawRealMatrix S ω)) x) y| ≤ t := by
      intro x hx y hy
      have hnot : ω ∉ {ω | t ≤ |realBilinear S x y ω|} := by
        intro hmem
        apply hωB
        exact Set.mem_iUnion_of_mem (x, y) <|
          Set.mem_iUnion_of_mem (Finset.mem_product.mpr ⟨hx, hy⟩) hmem
      rw [inner_rawRealMatrix_eq_realBilinear]
      exact le_of_not_ge hnot
    have hop := opNorm_le_two_mul_of_quarter_net
      ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ))
        (rawRealMatrix S ω)) N hNunit hNcover t ht hgrid
    rw [← Matrix.cstar_norm_def] at hop
    dsimp [t] at hop
    change 40 * Real.sqrt κ * Real.sqrt n < ‖rawRealMatrix S ω‖ at hω
    linarith
  have hexponent :
      -t ^ 2 / (2 * κ) = -200 * (n : ℝ) := by
    have hsκ : (Real.sqrt κ) ^ 2 = κ := Real.sq_sqrt hκ.le
    have hsn : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR
    dsimp [t]
    rw [show (20 * Real.sqrt κ * Real.sqrt n) ^ 2 =
        400 * (Real.sqrt κ) ^ 2 * (Real.sqrt n) ^ 2 by ring,
      hsκ, hsn]
    field_simp [ne_of_gt hκ]
    ring
  have hB : μ.real B ≤
      2 * (81 : ℝ) ^ n * Real.exp (-200 * (n : ℝ)) := by
    calc
      μ.real B ≤ ∑ p ∈ N.product N,
          μ.real {ω | t ≤ |realBilinear S p.1 p.2 ω|} := by
        exact measureReal_biUnion_finset_le (N.product N)
          (fun p ↦ {ω | t ≤ |realBilinear S p.1 p.2 ω|})
      _ ≤ ∑ _p ∈ N.product N,
          2 * Real.exp (-200 * (n : ℝ)) := by
        gcongr with p hp
        have hp' := Finset.mem_product.mp hp
        simpa [κ, hexponent] using realBilinear_abs_tail S p.1 p.2
          (hNunit p.1 hp'.1) (hNunit p.2 hp'.2) t ht
      _ = ((N.card : ℝ) * (N.card : ℝ)) *
          (2 * Real.exp (-200 * (n : ℝ))) := by simp
      _ ≤ (((9 ^ n : ℕ) : ℝ) * ((9 ^ n : ℕ) : ℝ)) *
          (2 * Real.exp (-200 * (n : ℝ))) := by
        gcongr <;> exact_mod_cast hNcard
      _ = 2 * (81 : ℝ) ^ n * Real.exp (-200 * (n : ℝ)) := by
        push_cast
        rw [show (81 : ℝ) ^ n = (9 : ℝ) ^ n * (9 : ℝ) ^ n by
          rw [← mul_pow]
          norm_num]
        ring
  calc
    μ.real {ω | 40 * Real.sqrt (subgaussianEnvelope S : ℝ) *
          Real.sqrt n < ‖rawRealMatrix S ω‖}
        = μ.real {ω | 40 * Real.sqrt κ * Real.sqrt n <
            ‖rawRealMatrix S ω‖} := by rfl
    _ ≤ μ.real B := measureReal_mono hbadSub (measure_ne_top μ B)
    _ ≤ 2 * (81 : ℝ) ^ n * Real.exp (-200 * (n : ℝ)) := hB
    _ ≤ Real.exp (-(n : ℝ)) := two_mul_eightyOne_pow_mul_exp_le n hn

def complexReVec {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) : E n :=
  WithLp.toLp 2 (fun i ↦ (z i).re)

def complexImVec {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) : E n :=
  WithLp.toLp 2 (fun i ↦ (z i).im)

lemma complex_norm_sq_decompose {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) :
    ‖z‖ ^ 2 = ‖complexReVec z‖ ^ 2 + ‖complexImVec z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.sq_norm]
  simp [Complex.normSq, complexReVec, complexImVec, Real.norm_eq_abs, sq_abs]
  ring

lemma complexReVec_raw_action
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n)
    (z : EuclideanSpace ℂ (Fin n)) (ω : Ω) :
    complexReVec (((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
      (S.rawMatrix ω)) z) =
      ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ))
        (rawRealMatrix S ω)) (complexReVec z) := by
  ext i
  change (∑ j : Fin n, (S.atom (i, j) ω : ℂ) * z.ofLp j).re =
    ∑ j : Fin n, S.atom (i, j) ω * (complexReVec z).ofLp j
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [complexReVec, PiLp.toLp_apply, Complex.mul_re]

lemma complexImVec_raw_action
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n)
    (z : EuclideanSpace ℂ (Fin n)) (ω : Ω) :
    complexImVec (((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
      (S.rawMatrix ω)) z) =
      ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ))
        (rawRealMatrix S ω)) (complexImVec z) := by
  ext i
  change (∑ j : Fin n, (S.atom (i, j) ω : ℂ) * z.ofLp j).im =
    ∑ j : Fin n, S.atom (i, j) ω * (complexImVec z).ofLp j
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [complexImVec, PiLp.toLp_apply, Complex.mul_im]

set_option maxHeartbeats 1000000 in
theorem rawComplexMatrix_norm_le_rawRealMatrix
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n) (ω : Ω) :
    ‖S.rawMatrix ω‖ ≤ ‖rawRealMatrix S ω‖ := by
  let Ac := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) (S.rawMatrix ω)
  let Ar := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) (rawRealMatrix S ω)
  rw [Matrix.cstar_norm_def, Matrix.cstar_norm_def]
  change ‖Ac‖ ≤ ‖Ar‖
  apply Ac.opNorm_le_bound (norm_nonneg Ar)
  intro z
  have hre := Ar.le_opNorm (complexReVec z)
  have him := Ar.le_opNorm (complexImVec z)
  have hreSq : ‖Ar (complexReVec z)‖ ^ 2 ≤
      (‖Ar‖ * ‖complexReVec z‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hre
  have himSq : ‖Ar (complexImVec z)‖ ^ 2 ≤
      (‖Ar‖ * ‖complexImVec z‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr him
  have hAc : ‖Ac z‖ ^ 2 =
      ‖Ar (complexReVec z)‖ ^ 2 + ‖Ar (complexImVec z)‖ ^ 2 := by
    rw [complex_norm_sq_decompose]
    congr 1
    · exact congrArg (fun u ↦ ‖u‖ ^ 2) (complexReVec_raw_action S z ω)
    · exact congrArg (fun u ↦ ‖u‖ ^ 2) (complexImVec_raw_action S z ω)
  have hz := complex_norm_sq_decompose z
  have hsquare : ‖Ac z‖ ^ 2 ≤ (‖Ar‖ * ‖z‖) ^ 2 := by
    rw [hAc]
    calc
      ‖Ar (complexReVec z)‖ ^ 2 + ‖Ar (complexImVec z)‖ ^ 2
          ≤ (‖Ar‖ * ‖complexReVec z‖) ^ 2 +
              (‖Ar‖ * ‖complexImVec z‖) ^ 2 := add_le_add hreSq himSq
      _ = ‖Ar‖ ^ 2 *
          (‖complexReVec z‖ ^ 2 + ‖complexImVec z‖ ^ 2) := by ring
      _ = ‖Ar‖ ^ 2 * ‖z‖ ^ 2 := by rw [← hz]
      _ = (‖Ar‖ * ‖z‖) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hsquare

theorem rawComplexMatrix_opNorm_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n) (hn : 0 < n) :
    μ.real {ω | 40 * Real.sqrt (subgaussianEnvelope S : ℝ) *
          Real.sqrt n < ‖S.rawMatrix ω‖} ≤
      Real.exp (-(n : ℝ)) := by
  letI : IsProbabilityMeasure μ := S.independent.isProbabilityMeasure
  calc
    μ.real {ω | 40 * Real.sqrt (subgaussianEnvelope S : ℝ) *
          Real.sqrt n < ‖S.rawMatrix ω‖}
        ≤ μ.real {ω | 40 * Real.sqrt (subgaussianEnvelope S : ℝ) *
          Real.sqrt n < ‖rawRealMatrix S ω‖} := by
            apply measureReal_mono _ (measure_ne_top μ _)
            intro ω hω
            exact hω.trans_le (rawComplexMatrix_norm_le_rawRealMatrix S ω)
    _ ≤ Real.exp (-(n : ℝ)) := rawRealMatrix_opNorm_tail S hn

def subgaussianOpNormConstant
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n) : ℝ :=
  40 * Real.sqrt (subgaussianEnvelope S : ℝ)

def subgaussianOpNormBadEvent
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n) : Set Ω :=
  {ω | subgaussianOpNormConstant S <
    ‖((((Real.sqrt n)⁻¹ : ℝ) : ℂ) • S.rawMatrix ω)‖}

lemma measurableSet_subgaussianOpNormBadEvent
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n) :
    MeasurableSet (subgaussianOpNormBadEvent S) := by
  letI : MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) :=
    borel (Matrix (Fin n) (Fin n) ℂ)
  letI : BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩
  have hraw : Measurable S.rawMatrix := by
    have hsum : Measurable (fun ω ↦
        ∑ i : Fin n, ∑ j : Fin n,
          (S.atom (i, j) ω : ℂ) •
            Matrix.single i j (1 : ℂ)) := by
      apply Finset.measurable_sum
      intro i hi
      apply Finset.measurable_sum
      intro j hj
      exact (Complex.measurable_ofReal.comp
        (S.measurable_atom (i, j))).smul_const _
    convert hsum using 1
    funext ω
    simpa [IidSubgaussianSquare.rawMatrix] using
      (Matrix.matrix_eq_sum_single (S.rawMatrix ω))
  exact measurableSet_lt measurable_const
    (hraw.const_smul ((((Real.sqrt n)⁻¹ : ℝ) : ℂ))).norm

lemma subgaussianOpNormConstant_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n) :
    0 ≤ subgaussianOpNormConstant S := by
  dsimp [subgaussianOpNormConstant]
  positivity

theorem normalizedRawComplexMatrix_opNorm_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n) (hn : 0 < n) :
    μ.real (subgaussianOpNormBadEvent S) ≤ Real.exp (-(n : ℝ)) := by
  letI : IsProbabilityMeasure μ := S.independent.isProbabilityMeasure
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  calc
    μ.real (subgaussianOpNormBadEvent S) ≤
        μ.real {ω | 40 * Real.sqrt (subgaussianEnvelope S : ℝ) * Real.sqrt n <
          ‖S.rawMatrix ω‖} := by
      apply measureReal_mono _ (measure_ne_top μ _)
      intro ω hω
      change subgaussianOpNormConstant S <
        ‖((((Real.sqrt n)⁻¹ : ℝ) : ℂ) • S.rawMatrix ω)‖ at hω
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_inv, abs_of_pos hsqrt] at hω
      dsimp [subgaussianOpNormConstant] at hω
      change 40 * Real.sqrt (subgaussianEnvelope S : ℝ) <
        (Real.sqrt n)⁻¹ * ‖S.rawMatrix ω‖ at hω
      rw [inv_mul_eq_div] at hω
      exact (lt_div_iff₀ hsqrt).mp hω
    _ ≤ Real.exp (-(n : ℝ)) := rawComplexMatrix_opNorm_tail S hn

lemma norm_invSqrtThreeN_raw_le_of_opNormGood
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n)
    (ω : Ω) (hn : 0 < n) (hgood : ω ∉ subgaussianOpNormBadEvent S) :
    ‖((((Real.sqrt (3 * (n : ℝ)))⁻¹ : ℝ) : ℂ) • S.rawMatrix ω)‖ ≤
      subgaussianOpNormConstant S := by
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsqrt3n : 0 < Real.sqrt (3 * (n : ℝ)) := by positivity
  have hnorm :
      ‖((((Real.sqrt n)⁻¹ : ℝ) : ℂ) • S.rawMatrix ω)‖ ≤
        subgaussianOpNormConstant S := le_of_not_gt hgood
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_inv, abs_of_pos hsqrtn] at hnorm
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_inv, abs_of_pos hsqrt3n]
  have hsqrt_le : Real.sqrt n ≤ Real.sqrt (3 * (n : ℝ)) := by
    apply Real.sqrt_le_sqrt
    have hnR : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hinv : (Real.sqrt (3 * (n : ℝ)))⁻¹ ≤ (Real.sqrt n)⁻¹ :=
    inv_anti₀ hsqrtn hsqrt_le
  exact (mul_le_mul_of_nonneg_right hinv (norm_nonneg _)).trans hnorm

/-- Caller-facing operator-norm interface: the bad event is measurable, has
an `exp (-n)` tail, and outside it the paper's `(3n)⁻¹ᐟ²` normalization is
bounded by an explicit constant derived only from the MGF parameter. -/
theorem normalizedRawComplexMatrix_opNorm_interface
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : BernoulliSection9.IidSubgaussianSquare Ω μ n) (hn : 0 < n) :
    MeasurableSet (subgaussianOpNormBadEvent S) ∧
      μ.real (subgaussianOpNormBadEvent S) ≤ Real.exp (-(n : ℝ)) ∧
      ∀ ω ∉ subgaussianOpNormBadEvent S,
        ‖((((Real.sqrt (3 * (n : ℝ)))⁻¹ : ℝ) : ℂ) •
          S.rawMatrix ω)‖ ≤ subgaussianOpNormConstant S := by
  exact ⟨measurableSet_subgaussianOpNormBadEvent S,
    normalizedRawComplexMatrix_opNorm_tail S hn,
    fun ω hω ↦ norm_invSqrtThreeN_raw_le_of_opNormGood S ω hn hω⟩

end BernoulliSection9
