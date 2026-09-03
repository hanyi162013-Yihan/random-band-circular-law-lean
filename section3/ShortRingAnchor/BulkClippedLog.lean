import ShortRingAnchor.ClippedLog

/-!
# Bulk clipped logarithms and CDF comparison

This file completes the finite-family integration-by-parts step used in the
proof of Proposition 3.6.  It upgrades the one-point formula in
`ClippedLog.lean` to an exact layer-cake formula for an empirical measure and
then proves the deterministic `(3.12)`-type estimate from the uniform distance
between two empirical CDFs.

No probabilistic or random-matrix input is used here.
-/

open Set MeasureTheory
open scoped BigOperators Interval

noncomputable section

namespace ShortRingAnchor

/-- The strict empirical upper tail.  With the manuscript convention
`F(t) = # {i | x_i <= t} / #I`, this is exactly `1 - F(t)` for a nonempty
family. -/
noncomputable def empiricalTail {I : Type*} [Fintype I]
    (x : I -> Real) (t : Real) : Real :=
  (((Finset.univ.filter fun i => t < x i).card : Nat) : Real) /
    (Fintype.card I : Real)

/-- Finite-family complement identity behind the layer-cake formula. -/
theorem empiricalTail_eq_one_sub_cdf
    {I : Type*} [Fintype I] [Nonempty I]
    (x : I -> Real) (t : Real) :
    empiricalTail x t = 1 - empiricalCdf x t := by
  classical
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset I)) (p := fun i => x i <= t)
  simp only [not_le] at hcard
  have hn : (Fintype.card I : Real) ≠ 0 := by positivity
  have hcardR :
      ((Finset.univ.filter fun i : I => x i <= t).card : Real) +
          ((Finset.univ.filter fun i : I => t < x i).card : Real) =
        (Fintype.card I : Real) := by
    exact_mod_cast hcard
  unfold empiricalTail empiricalCdf
  rw [div_eq_iff hn, sub_mul, one_mul, div_mul_cancel₀ _ hn]
  linarith

/-- The sum of the pointwise threshold indicators is the strict-tail count. -/
theorem sum_indicator_one_div_eq_tail_count
    {I : Type*} [Fintype I] (x : I -> Real) (t : Real) :
    (∑ i, (Iio (x i)).indicator (fun _ : Real => 1 / t) t) =
      (((Finset.univ.filter fun i => t < x i).card : Nat) : Real) * (1 / t) := by
  classical
  change Finset.univ.sum (fun i => if t < x i then 1 / t else 0) = _
  rw [← Finset.sum_filter]
  simp

/-- Averaging the threshold indicators gives the CDF kernel
`(1-F(t))/t`. -/
theorem average_indicator_one_div_eq_cdfKernel
    {I : Type*} [Fintype I] [Nonempty I]
    (x : I -> Real) (t : Real) :
    (∑ i, (Iio (x i)).indicator (fun u : Real => 1 / u) t) /
        (Fintype.card I : Real) =
      (1 - empiricalCdf x t) * (1 / t) := by
  change (∑ i, (Iio (x i)).indicator (fun _ : Real => 1 / t) t) /
      (Fintype.card I : Real) = _
  rw [sum_indicator_one_div_eq_tail_count]
  calc
    (((Finset.univ.filter fun i : I => t < x i).card : Real) * (1 / t)) /
          (Fintype.card I : Real) =
        empiricalTail x t * (1 / t) := by
          simp only [empiricalTail]
          ring
    _ = (1 - empiricalCdf x t) * (1 / t) := by
      rw [empiricalTail_eq_one_sub_cdf]

/-- The reciprocal kernel is integrable on an interval bounded away from
zero. -/
theorem integrableOn_one_div_Ico {u v : Real} (hu : 0 < u) :
    IntegrableOn (fun t : Real => 1 / t) (Ico u v) := by
  exact ((continuousOn_one_div_Icc hu).integrableOn_Icc).mono_set
    Ico_subset_Icc_self

/-- Each one-point indicator kernel is integrable on a common positive
clipping interval. -/
theorem integrableOn_indicator_one_div_Ico {u v x : Real} (hu : 0 < u) :
    IntegrableOn ((Iio x).indicator (fun t : Real => 1 / t)) (Ico u v) :=
  (integrableOn_one_div_Ico hu).indicator measurableSet_Iio

/-- The empirical CDF kernel in the bulk layer-cake formula is integrable. -/
theorem integrableOn_cdfKernel
    {I : Type*} [Fintype I] [Nonempty I]
    {u v : Real} (hu : 0 < u) (x : I -> Real) :
    IntegrableOn (fun t => (1 - empiricalCdf x t) * (1 / t)) (Ico u v) := by
  classical
  have hsum : IntegrableOn
      (fun t => ∑ i, (Iio (x i)).indicator (fun s : Real => 1 / s) t)
      (Ico u v) := by
    apply integrable_finsetSum Finset.univ
    intro i _hi
    exact integrableOn_indicator_one_div_Ico hu
  refine (hsum.mul_const ((Fintype.card I : Real)⁻¹)).congr ?_
  exact Filter.Eventually.of_forall fun t => by
    simpa only [div_eq_mul_inv] using
      average_indicator_one_div_eq_cdfKernel x t

/-- Finite summation commutes with the set integral of the indicator
kernels. -/
theorem integral_sum_indicator_one_div
    {I : Type*} [Fintype I]
    {u v : Real} (hu : 0 < u) (x : I -> Real) :
    (∫ t : Real in Ico u v,
        ∑ i, (Iio (x i)).indicator (fun s : Real => 1 / s) t) =
      ∑ i, ∫ t : Real in Ico u v,
        (Iio (x i)).indicator (fun s : Real => 1 / s) t := by
  classical
  apply integral_finsetSum Finset.univ
  intro i _hi
  exact integrableOn_indicator_one_div_Ico hu

/-- Exact finite-empirical layer-cake / integration-by-parts identity:

`average_i log(clamp(a²,R²,x_i))/2
  = log a + (1/2) ∫_[a²,R²) (1-F_x(t)) dt/t`.

This is the bulk version of the one-point identity used in the proof step
leading to manuscript formula `(3.12)`. -/
theorem empiricalClippedLog_layerCake
    {I : Type*} [Fintype I] [Nonempty I]
    {a R : Real} (ha : 0 < a) (haR : a <= R) (x : I -> Real) :
    empiricalClippedLog a R x = Real.log a +
      (1 / 2 : Real) *
        ∫ t : Real in Ico (a ^ 2) (R ^ 2),
          (1 - empiricalCdf x t) * (1 / t) := by
  classical
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hn : (Fintype.card I : Real) ≠ 0 := by positivity
  have hsumIntegral := integral_sum_indicator_one_div (v := R ^ 2) ha2 x
  have hkernelIntegral :
      (∫ t : Real in Ico (a ^ 2) (R ^ 2),
          (1 - empiricalCdf x t) * (1 / t)) =
        (∑ i, ∫ t : Real in Ico (a ^ 2) (R ^ 2),
          (Iio (x i)).indicator (fun s : Real => 1 / s) t) /
            (Fintype.card I : Real) := by
    calc
      (∫ t : Real in Ico (a ^ 2) (R ^ 2),
          (1 - empiricalCdf x t) * (1 / t)) =
          ∫ t : Real in Ico (a ^ 2) (R ^ 2),
            (∑ i, (Iio (x i)).indicator (fun s : Real => 1 / s) t) /
              (Fintype.card I : Real) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun t =>
              (average_indicator_one_div_eq_cdfKernel x t).symm
      _ = (∫ t : Real in Ico (a ^ 2) (R ^ 2),
            ∑ i, (Iio (x i)).indicator (fun s : Real => 1 / s) t) /
              (Fintype.card I : Real) := by
            rw [integral_div]
      _ = (∑ i, ∫ t : Real in Ico (a ^ 2) (R ^ 2),
            (Iio (x i)).indicator (fun s : Real => 1 / s) t) /
              (Fintype.card I : Real) := by rw [hsumIntegral]
  unfold empiricalClippedLog empiricalAverage
  simp_rw [clippedLog_eq_log_add_integral ha haR]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum]
  rw [hkernelIntegral]
  field_simp

/-- The set integral of `1/t` over a positive half-open interval. -/
theorem integral_Ico_one_div_eq_log_sub
    {u v : Real} (hu : 0 < u) (huv : u <= v) :
    (∫ t : Real in Ico u v, 1 / t) = Real.log v - Real.log u := by
  rw [integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le huv,
    intervalIntegral_one_div_eq_log_sub hu huv]

/-- Difference form of the empirical layer-cake identity.  The logarithmic
boundary term cancels exactly. -/
theorem empiricalClippedLog_sub_eq_integral_cdf_sub
    {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    {a R : Real} (ha : 0 < a) (haR : a <= R)
    (x : I -> Real) (y : J -> Real) :
    empiricalClippedLog a R x - empiricalClippedLog a R y =
      (1 / 2 : Real) *
        ∫ t : Real in Ico (a ^ 2) (R ^ 2),
          (empiricalCdf y t - empiricalCdf x t) * (1 / t) := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  rw [empiricalClippedLog_layerCake ha haR x,
    empiricalClippedLog_layerCake ha haR y]
  have hx := integrableOn_cdfKernel (v := R ^ 2) ha2 x
  have hy := integrableOn_cdfKernel (v := R ^ 2) ha2 y
  calc
    (Real.log a + (1 / 2 : Real) *
          ∫ t : Real in Ico (a ^ 2) (R ^ 2),
            (1 - empiricalCdf x t) * (1 / t)) -
        (Real.log a + (1 / 2 : Real) *
          ∫ t : Real in Ico (a ^ 2) (R ^ 2),
            (1 - empiricalCdf y t) * (1 / t)) =
      (1 / 2 : Real) *
        ((∫ t : Real in Ico (a ^ 2) (R ^ 2),
            (1 - empiricalCdf x t) * (1 / t)) -
          ∫ t : Real in Ico (a ^ 2) (R ^ 2),
            (1 - empiricalCdf y t) * (1 / t)) := by ring
    _ = (1 / 2 : Real) *
        ∫ t : Real in Ico (a ^ 2) (R ^ 2),
          ((1 - empiricalCdf x t) * (1 / t) -
            (1 - empiricalCdf y t) * (1 / t)) := by
          rw [integral_sub hx hy]
    _ = (1 / 2 : Real) *
        ∫ t : Real in Ico (a ^ 2) (R ^ 2),
          (empiricalCdf y t - empiricalCdf x t) * (1 / t) := by
          congr 2
          funext t
          ring

/-- A CDF takes values in `[0,1]`. -/
theorem empiricalCdf_nonneg
    {I : Type*} [Fintype I] [Nonempty I]
    (x : I -> Real) (t : Real) : 0 <= empiricalCdf x t := by
  unfold empiricalCdf
  positivity

/-- Upper half of the range bound for an empirical CDF. -/
theorem empiricalCdf_le_one
    {I : Type*} [Fintype I] [Nonempty I]
    (x : I -> Real) (t : Real) : empiricalCdf x t <= 1 := by
  have hcard :
      (Finset.univ.filter fun i : I => x i <= t).card <= Fintype.card I := by
    change (Finset.univ.filter fun i : I => x i <= t).card <=
      (Finset.univ : Finset I).card
    exact Finset.card_le_card (Finset.filter_subset _ _)
  unfold empiricalCdf
  apply (div_le_one (by positivity : (0 : Real) < Fintype.card I)).2
  exact_mod_cast hcard

/-- The pointwise distance of two empirical CDFs is at most one. -/
theorem abs_empiricalCdf_sub_le_one
    {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (x : I -> Real) (y : J -> Real) (t : Real) :
    |empiricalCdf x t - empiricalCdf y t| <= 1 := by
  rw [abs_le]
  constructor <;>
    linarith [empiricalCdf_nonneg x t, empiricalCdf_le_one x t,
      empiricalCdf_nonneg y t, empiricalCdf_le_one y t]

/-- The Kolmogorov (uniform CDF) distance between two finite empirical
distributions. -/
noncomputable def empiricalCdfDistance
    {I J : Type*} [Fintype I] [Fintype J]
    (x : I -> Real) (y : J -> Real) : Real :=
  sSup (Set.range fun t : Real => |empiricalCdf x t - empiricalCdf y t|)

/-- The CDF distance restricted to a closed interval.  Lemma 3.5 in the
manuscript controls this local quantity on `[0, R^2]`, rather than the global
Kolmogorov distance. -/
noncomputable def empiricalCdfDistanceOn
    {I J : Type*} [Fintype I] [Fintype J]
    (u v : Real) (x : I -> Real) (y : J -> Real) : Real :=
  sSup ((fun t : Real => |empiricalCdf x t - empiricalCdf y t|) '' Icc u v)

theorem bddAbove_range_abs_empiricalCdf_sub
    {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (x : I -> Real) (y : J -> Real) :
    BddAbove (Set.range fun t : Real => |empiricalCdf x t - empiricalCdf y t|) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact abs_empiricalCdf_sub_le_one x y t

/-- The set of CDF discrepancies on any interval is bounded above by one. -/
theorem bddAbove_image_Icc_abs_empiricalCdf_sub
    {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (u v : Real) (x : I -> Real) (y : J -> Real) :
    BddAbove
      ((fun t : Real => |empiricalCdf x t - empiricalCdf y t|) '' Icc u v) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨t, _ht, rfl⟩
  exact abs_empiricalCdf_sub_le_one x y t

/-- Every CDF discrepancy at a point of `[u,v]` is bounded by the local CDF
distance on that interval. -/
theorem abs_empiricalCdf_sub_le_distanceOn
    {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    {u v t : Real} (x : I -> Real) (y : J -> Real) (ht : t ∈ Icc u v) :
    |empiricalCdf x t - empiricalCdf y t| <=
      empiricalCdfDistanceOn u v x y := by
  apply le_csSup (bddAbove_image_Icc_abs_empiricalCdf_sub u v x y)
  exact ⟨t, ht, rfl⟩

/-- A local CDF distance is nonnegative whenever its interval is nonempty. -/
theorem empiricalCdfDistanceOn_nonneg
    {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    {u v : Real} (huv : u <= v) (x : I -> Real) (y : J -> Real) :
    0 <= empiricalCdfDistanceOn u v x y := by
  exact (abs_nonneg (empiricalCdf x u - empiricalCdf y u)).trans
    (abs_empiricalCdf_sub_le_distanceOn x y ⟨le_rfl, huv⟩)

/-- Every pointwise CDF difference is bounded by the uniform CDF distance. -/
theorem abs_empiricalCdf_sub_le_distance
    {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (x : I -> Real) (y : J -> Real) (t : Real) :
    |empiricalCdf x t - empiricalCdf y t| <= empiricalCdfDistance x y := by
  apply le_csSup (bddAbove_range_abs_empiricalCdf_sub x y)
  exact ⟨t, rfl⟩

theorem empiricalCdfDistance_nonneg
    {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (x : I -> Real) (y : J -> Real) :
    0 <= empiricalCdfDistance x y := by
  exact (abs_nonneg (empiricalCdf x 0 - empiricalCdf y 0)).trans
    (abs_empiricalCdf_sub_le_distance x y 0)

/-- Deterministic `(3.12)`-type comparison with an explicit uniform CDF
error `delta`:

`|L_[a,R](x) - L_[a,R](y)| <= delta (log R - log a)`.

The two finite families may have different cardinalities. -/
theorem abs_empiricalClippedLog_sub_le_of_cdf
    {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    {a R delta : Real} (ha : 0 < a) (haR : a <= R) (_hdelta : 0 <= delta)
    (x : I -> Real) (y : J -> Real)
    (hcdf : ∀ t ∈ Ico (a ^ 2) (R ^ 2),
      |empiricalCdf x t - empiricalCdf y t| <= delta) :
    |empiricalClippedLog a R x - empiricalClippedLog a R y| <=
      delta * (Real.log R - Real.log a) := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have haR2 : a ^ 2 <= R ^ 2 := by nlinarith
  have hR : 0 < R := ha.trans_le haR
  rw [empiricalClippedLog_sub_eq_integral_cdf_sub ha haR x y,
    abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 1 / 2)]
  have hg : IntegrableOn (fun t : Real => delta * (1 / t))
      (Ico (a ^ 2) (R ^ 2)) :=
    (integrableOn_one_div_Ico ha2).const_mul delta
  have hpoint : ∀ t ∈ Ico (a ^ 2) (R ^ 2),
      ‖(empiricalCdf y t - empiricalCdf x t) * (1 / t)‖ <=
        delta * (1 / t) := by
    intro t ht
    have htpos : 0 < t := ha2.trans_le ht.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (one_div_pos.mpr htpos)]
    have habs : |empiricalCdf y t - empiricalCdf x t| <= delta := by
      simpa [abs_sub_comm] using hcdf t ht
    exact mul_le_mul_of_nonneg_right habs (one_div_pos.mpr htpos).le
  have hnorm :
      ‖∫ t : Real in Ico (a ^ 2) (R ^ 2),
          (empiricalCdf y t - empiricalCdf x t) * (1 / t)‖ <=
        ∫ t : Real in Ico (a ^ 2) (R ^ 2), delta * (1 / t) := by
    exact norm_integral_le_of_norm_le hg
      (ae_restrict_of_forall_mem measurableSet_Ico hpoint)
  calc
    (1 / 2 : Real) *
        |∫ t : Real in Ico (a ^ 2) (R ^ 2),
          (empiricalCdf y t - empiricalCdf x t) * (1 / t)| <=
      (1 / 2 : Real) *
        ∫ t : Real in Ico (a ^ 2) (R ^ 2), delta * (1 / t) := by
          exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hnorm)
            (by norm_num)
    _ = delta * (Real.log R - Real.log a) := by
      rw [integral_const_mul, integral_Ico_one_div_eq_log_sub ha2 haR2,
        Real.log_pow, Real.log_pow]
      ring

/-- Formula `(3.12)` with `delta` specialized to the actual sup CDF
difference.  This theorem has no external hypotheses. -/
theorem abs_empiricalClippedLog_sub_le_cdfDistance
    {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    {a R : Real} (ha : 0 < a) (haR : a <= R)
    (x : I -> Real) (y : J -> Real) :
    |empiricalClippedLog a R x - empiricalClippedLog a R y| <=
      empiricalCdfDistance x y * (Real.log R - Real.log a) := by
  apply abs_empiricalClippedLog_sub_le_of_cdf ha haR
    (empiricalCdfDistance_nonneg x y) x y
  intro t _ht
  exact abs_empiricalCdf_sub_le_distance x y t

/-- Formula `(3.12)` using only the CDF comparison on the clipping interval
`[a^2,R^2]`.  This is the minimal deterministic locality needed by the
layer-cake integral. -/
theorem abs_empiricalClippedLog_sub_le_cdfDistanceOn_clipping
    {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    {a R : Real} (ha : 0 < a) (haR : a <= R)
    (x : I -> Real) (y : J -> Real) :
    |empiricalClippedLog a R x - empiricalClippedLog a R y| <=
      empiricalCdfDistanceOn (a ^ 2) (R ^ 2) x y *
        (Real.log R - Real.log a) := by
  have haR2 : a ^ 2 <= R ^ 2 := by nlinarith
  apply abs_empiricalClippedLog_sub_le_of_cdf ha haR
    (empiricalCdfDistanceOn_nonneg haR2 x y) x y
  intro t ht
  exact abs_empiricalCdf_sub_le_distanceOn x y ⟨ht.1, ht.2.le⟩

/-- Manuscript `(3.12)` in the exact locality supplied by Lemma 3.5:
only `sup_{0 <= t <= R^2} |F_x(t)-F_y(t)|` occurs. -/
theorem abs_empiricalClippedLog_sub_le_cdfDistanceOn_zero_sq
    {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    {a R : Real} (ha : 0 < a) (haR : a <= R)
    (x : I -> Real) (y : J -> Real) :
    |empiricalClippedLog a R x - empiricalClippedLog a R y| <=
      empiricalCdfDistanceOn 0 (R ^ 2) x y *
        (Real.log R - Real.log a) := by
  apply abs_empiricalClippedLog_sub_le_of_cdf ha haR
    (empiricalCdfDistanceOn_nonneg (sq_nonneg R) x y) x y
  intro t ht
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  exact abs_empiricalCdf_sub_le_distanceOn x y
    ⟨(ha2.trans_le ht.1).le, ht.2.le⟩

end ShortRingAnchor
