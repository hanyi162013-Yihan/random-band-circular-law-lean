import ShortRingAnchor.GinibreLowerEdge
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# BC12 (4.9): a polynomial least singular value and a mesoscopic count suffice

This is the deterministic summation step of BC12 Section 4.2, reconstructed
from a CDF estimate rather than from individually indexed intermediate singular values.
The count can therefore be supplied by the already formalized v3 Corollary 3.5.
No Gaussian formula or random-matrix estimate is assumed in the calculus lemmas.
-/

open Set MeasureTheory Filter
open scoped BigOperators Interval Topology ENNReal

noncomputable section
namespace ShortRingAnchor.BC12

/-- BC12 (4.9), power kernel: continuity away from the origin. -/
theorem continuousOn_rpow_positive_interval {a b q : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => t ^ q) (Icc a b) := by
  intro t ht
  exact (Real.continuousAt_rpow_const t q (Or.inl (ne_of_gt (ha.trans_le ht.1)))).continuousWithinAt

/-- BC12 summation: the threshold indicator integrates from the clamped point. -/
theorem integral_lower_indicator_eq_clamp {a b x : ℝ} (_hab : a ≤ b)
    (f : ℝ → ℝ) :
    (∫ t in Ico a b, (Ici x).indicator f t) =
      ∫ t in realClamp a b x..b, f t := by
  rw [intervalIntegral.integral_of_le realClamp_upper, ← integral_Ico_eq_integral_Ioc,
    setIntegral_indicator measurableSet_Ici]
  apply setIntegral_congr_set
  filter_upwards [] with t
  apply propext
  change ((a ≤ t ∧ t < b) ∧ x ≤ t) ↔ (min b (max a x) ≤ t ∧ t < b)
  constructor
  · rintro ⟨⟨hat, htb⟩, hxt⟩
    exact ⟨(min_le_right _ _).trans (max_le hat hxt), htb⟩
  · rintro ⟨h, htb⟩
    have hmax := (min_le_iff.mp h).resolve_left (not_le_of_gt htb)
    exact ⟨⟨(max_le_iff.mp hmax).1, htb⟩, (max_le_iff.mp hmax).2⟩

/-- BC12 power summation: the exact antiderivative on an interval away from zero. -/
theorem integral_negative_power_kernel {y p : ℝ} (hy : 0 < y) (hy1 : y ≤ 1)
    (hp : 0 < p) :
    (∫ t in y..1, p * t ^ (-p - 1)) = y ^ (-p) - 1 := by
  rw [intervalIntegral.integral_const_mul, integral_rpow]
  · have he : -p - 1 + 1 = -p := by ring
    rw [he, Real.one_rpow]
    field_simp
    ring
  · right
    refine ⟨by linarith, ?_⟩
    rw [uIcc_of_le hy1]
    exact fun h => (not_le_of_gt hy) h.1

/-- BC12 (4.9): the clipped negative power is an exact CDF layer cake. -/
theorem clamped_negativePower_layerCake {a p x : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hp : 0 < p) :
    (realClamp a 1 x) ^ (-p) = 1 +
      ∫ t in Ico a 1, (Ici x).indicator (fun t => p * t ^ (-p - 1)) t := by
  rw [integral_lower_indicator_eq_clamp ha1]
  rw [integral_negative_power_kernel (ha.trans_le (realClamp_lower ha1))
    realClamp_upper hp]
  ring

/-- BC12 (4.9): summing the indicators produces the finite CDF exactly. -/
theorem sum_lower_indicators {I : Type*} [Fintype I] (s : I → ℝ) (f : ℝ → ℝ) (t : ℝ) :
    (∑ i, (Ici (s i)).indicator f t) =
      ((Finset.univ.filter fun i => s i ≤ t).card : ℝ) * f t := by
  classical
  change (∑ i, if s i ≤ t then f t else 0) = _
  rw [← Finset.sum_filter]
  simp

/-- BC12 (4.9): the mesoscopic part of the negative moment is uniformly bounded. -/
theorem empirical_clamped_negativePower_le {I : Type*} [Fintype I] [Nonempty I]
    (s : I → ℝ) {a p C : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hp : 0 < p) (hp1 : p < 1) (hC : 0 ≤ C)
    (hcount : ∀ t, a ≤ t → t ≤ 1 → empiricalCdf s t ≤ C * t) :
    empiricalAverage s (fun x => (realClamp a 1 x) ^ (-p)) ≤ 1 + C * p / (1 - p) := by
  classical
  let f : ℝ → ℝ := fun t => p * t ^ (-p - 1)
  have hf : IntegrableOn f (Ico a 1) :=
    ((continuousOn_rpow_positive_interval ha).const_mul p).integrableOn_Icc.mono_set
      Ico_subset_Icc_self
  have hi (i : I) : IntegrableOn ((Ici (s i)).indicator f) (Ico a 1) :=
    hf.indicator measurableSet_Ici
  have hn : (Fintype.card I : ℝ) ≠ 0 := by positivity
  have hsum : IntegrableOn (fun t => ∑ i, (Ici (s i)).indicator f t) (Ico a 1) :=
    integrable_finsetSum _ (fun i _ => hi i)
  have hform : empiricalAverage s (fun x => (realClamp a 1 x) ^ (-p)) =
      1 + ∫ t in Ico a 1, empiricalCdf s t * f t := by
    unfold empiricalAverage
    simp_rw [clamped_negativePower_layerCake ha ha1 hp]
    rw [Finset.sum_add_distrib, ← integral_finsetSum _ (fun i _ => hi i)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [add_div, div_self hn, ← integral_div]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    rw [sum_lower_indicators]
    simp only [empiricalCdf]
    ring
  have hleft : IntegrableOn (fun t => empiricalCdf s t * f t) (Ico a 1) := by
    apply (hsum.div_const (Fintype.card I : ℝ)).congr
    filter_upwards [] with t
    rw [sum_lower_indicators]
    simp only [empiricalCdf]
    ring
  have hright : IntegrableOn (fun t : ℝ => C * p * t ^ (-p)) (Ico a 1) :=
    ((continuousOn_rpow_positive_interval ha).const_mul (C * p)).integrableOn_Icc.mono_set
      Ico_subset_Icc_self
  have hbound : (∫ t in Ico a 1, empiricalCdf s t * f t) ≤
      ∫ t in Ico a 1, C * p * t ^ (-p) := by
    apply setIntegral_mono_on hleft hright measurableSet_Ico
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    calc
      empiricalCdf s t * f t ≤ (C * t) * f t :=
        mul_le_mul_of_nonneg_right (hcount t ht.1 ht.2.le) (by dsimp [f]; positivity)
      _ = C * p * t ^ (-p) := by
        dsimp [f]
        rw [show -p = 1 + (-p - 1) by ring, Real.rpow_add ht0, Real.rpow_one]
        ring
  have hint : (∫ t in Ico a 1, C * p * t ^ (-p)) ≤ C * p / (1 - p) := by
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha1,
      intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < -p))]
    rw [Real.one_rpow, show -p + 1 = 1 - p by ring]
    have hpow : 0 ≤ a ^ (1 - p) := Real.rpow_nonneg ha.le _
    calc
      C * p * ((1 - a ^ (1 - p)) / (1 - p)) ≤ C * p * (1 / (1 - p)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (by linarith) (by linarith)) (mul_nonneg hC hp.le)
      _ = _ := by ring
  rw [hform]
  exact add_le_add le_rfl (hbound.trans hint)

/-- BC12 (4.9): isolate the very smallest values, using only a common lower bound. -/
theorem negativePower_le_clamped_add_low {s a ell p : ℝ}
    (hell : 0 < ell) (hs : ell ≤ s) (ha : 0 < a) (ha1 : a ≤ 1) (hp : 0 < p) :
    s ^ (-p) ≤ (realClamp a 1 s) ^ (-p) +
      if s ≤ a then ell ^ (-p) else 0 := by
  have hs0 : 0 < s := hell.trans_le hs
  by_cases hsa : s ≤ a
  · rw [if_pos hsa]
    exact (Real.rpow_le_rpow_of_nonpos hell hs (by linarith)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg (ha.trans_le (realClamp_lower ha1)).le _))
  · rw [if_neg hsa, add_zero]
    have hac : 0 < realClamp a 1 s := ha.trans_le (realClamp_lower ha1)
    have hcs : realClamp a 1 s ≤ s := by
      unfold realClamp
      rw [max_eq_right (le_of_not_ge hsa)]
      exact min_le_right _ _
    exact Real.rpow_le_rpow_of_nonpos hac hcs (by linarith)

/-- BC12 (4.9), complete finite-family estimate.  No moment integrability hypothesis is needed. -/
theorem normalizedNegativeMoment_le_of_count {I : Type*} [Fintype I] [Nonempty I]
    (s : I → ℝ) {a ell p C : ℝ} (hell : 0 < ell) (hs : ∀ i, ell ≤ s i)
    (ha : 0 < a) (ha1 : a ≤ 1) (hp : 0 < p) (hp1 : p < 1) (hC : 0 ≤ C)
    (hcount : ∀ t, a ≤ t → t ≤ 1 → empiricalCdf s t ≤ C * t) :
    normalizedNegativeMoment p s ≤ 1 + C * p / (1 - p) + C * a * ell ^ (-p) := by
  classical
  have hn : (0 : ℝ) < Fintype.card I := by positivity
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset I))
    (fun i _ => negativePower_le_clamped_add_low hell (hs i) ha ha1 hp)
  have hlow : (∑ i, if s i ≤ a then ell ^ (-p) else 0) =
      ((Finset.univ.filter fun i => s i ≤ a).card : ℝ) * ell ^ (-p) := by
    rw [← Finset.sum_filter]
    simp
  have hbound : normalizedNegativeMoment p s ≤
      empiricalAverage s (fun x => (realClamp a 1 x) ^ (-p)) +
        empiricalCdf s a * ell ^ (-p) := by
    unfold normalizedNegativeMoment empiricalAverage empiricalCdf
    rw [Finset.sum_add_distrib, hlow] at hsum
    exact (div_le_div_of_nonneg_right hsum hn.le).trans_eq (by ring)
  calc
    normalizedNegativeMoment p s ≤ _ := hbound
    _ ≤ (1 + C * p / (1 - p)) + (C * a) * ell ^ (-p) :=
      add_le_add (empirical_clamped_negativePower_le s ha ha1 hp hp1 hC hcount)
        (mul_le_mul_of_nonneg_right (hcount a le_rfl ha1) (Real.rpow_nonneg hell.le _))
    _ = _ := by ring

/-- BC12 probabilistic endpoint: uniform bounds on events of probability tending to one
imply tightness, without imposing a uniform expectation bound on exceptional events. -/
theorem boundedInProbability_of_bound_on_good
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {X : ℕ → Omega → ℝ} {good : ℕ → Set Omega} {K : ℝ}
    (hbad : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0))
    (hbound : ∀ᶠ n in atTop, ∀ sample ∈ good n, ‖X n sample‖ ≤ K) :
    BoundedInProbability mu X := by
  intro delta hdelta
  refine ⟨max 1 (K + 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  filter_upwards [hbound, (tendsto_order.1 hbad).2 delta hdelta] with n hn hprob
  apply lt_of_le_of_lt (measure_mono ?_) hprob
  intro sample hsample
  change sample ∉ good n
  intro hgood
  exact not_lt_of_ge ((hn sample hgood).trans
    ((le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _))) hsample

/-- BC12 (4.9): the complete short route, with only least-value and CDF-count inputs.
The scale condition is deterministic; in the intended use it is `N^(bp-a) ≤ 1`. -/
theorem negativeMomentTightness_of_count_and_lower
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, Nonempty (I n)]
    (s : ∀ n, Omega → I n → ℝ) {a ell : ℕ → ℝ} {p C D : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hC : 0 ≤ C)
    (hs : ∀ n sample i, 0 ≤ s n sample i)
    (good : ℕ → Set Omega)
    (hbad : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0))
    (hscales : ∀ᶠ n in atTop,
      0 < ell n ∧ 0 < a n ∧ a n ≤ 1 ∧ a n * (ell n) ^ (-p) ≤ D)
    (hlower : ∀ n sample, sample ∈ good n → ∀ i, ell n ≤ s n sample i)
    (hcount : ∀ n sample, sample ∈ good n → ∀ t,
      a n ≤ t → t ≤ 1 → empiricalCdf (s n sample) t ≤ C * t) :
    BC12GinibreNegativeMomentTightness mu p s := by
  apply boundedInProbability_of_bound_on_good hbad
    (K := 1 + C * p / (1 - p) + C * D)
  filter_upwards [hscales] with n hn
  intro sample hsample
  rw [Real.norm_eq_abs, abs_of_nonneg (normalizedNegativeMoment_nonneg (hs n sample))]
  exact (normalizedNegativeMoment_le_of_count (s n sample) hn.1
    (hlower n sample hsample) hn.2.1 hn.2.2.1 hp hp1 hC (hcount n sample hsample)).trans
      (by
        rw [mul_assoc]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hn.2.2.2 hC))

/-- BC12 short-route arithmetic: any polynomial lower edge works if `beta*p ≤ alpha`. -/
theorem polynomial_negativeMoment_balance {N alpha beta p : ℝ}
    (hN : 1 ≤ N) (hbalance : beta * p ≤ alpha) :
    N ^ (-alpha) * (N ^ (-beta)) ^ (-p) ≤ 1 := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
  exact Real.rpow_le_one_of_one_le_of_nonpos hN (by nlinarith)

/-- BC12 (4.9), an explicit admissible exponent for the nonoptimal Ginibre shortcut.
The least singular value scale `N^(-4)` and count scale `N^(-1/16)`
already give a bounded negative moment with `p = 1/128`. -/
theorem normalizedNegativeMoment_one_div_128_le {I : Type*}
    [Fintype I] [Nonempty I] (s : I → ℝ) {N C : ℝ}
    (hN : 1 ≤ N) (hC : 0 ≤ C)
    (hlower : ∀ i, N ^ (-(4 : ℝ)) ≤ s i)
    (hcount : ∀ t, N ^ (-(1 / 16 : ℝ)) ≤ t → t ≤ 1 →
      empiricalCdf s t ≤ C * t) :
    normalizedNegativeMoment (1 / 128) s ≤ 1 + C / 127 + C := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hbound := normalizedNegativeMoment_le_of_count s
    (Real.rpow_pos_of_pos hN0 (-(4 : ℝ))) hlower
    (Real.rpow_pos_of_pos hN0 (-(1 / 16 : ℝ)))
    (Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num : -(1 / 16 : ℝ) ≤ 0))
    (by norm_num : (0 : ℝ) < 1 / 128) (by norm_num : (1 / 128 : ℝ) < 1) hC hcount
  have hbalance := polynomial_negativeMoment_balance (alpha := 1 / 16)
    (beta := 4) (p := 1 / 128) hN (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hbalance hC
  calc
    normalizedNegativeMoment (1 / 128) s ≤ _ := hbound
    _ = 1 + C / 127 + C * (N ^ (-(1 / 16 : ℝ)) *
        (N ^ (-(4 : ℝ))) ^ (-(1 / 128 : ℝ))) := by ring
    _ ≤ 1 + C / 127 + C := add_le_add le_rfl (by simpa using hmul)

end ShortRingAnchor.BC12
