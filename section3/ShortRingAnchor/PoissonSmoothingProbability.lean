import ShortRingAnchor.PoissonSmoothingCDF
import ShortRingAnchor.ExternalInputs

/-!
# Lemma 3.5: the verified smoothing theorem supplies the named CDF interface

The inputs below are compact Stieltjes estimates on good events and
deterministic scale bounds, not an assumed CDF, density, or tail theorem.
-/

open Filter Set MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace ShortRingAnchor
open Arxiv2410V3

/-- Lemma 3.5: an eventual deterministic rate bound on good events gives `O_P`.
No measurability of an uncountable supremum is needed for this outer-measure bound. -/
theorem isBigOInProbability_of_bound_on_good
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {X : ℕ → Omega → ℝ} {rate : ℕ → ℝ} {good : ℕ → Set Omega} {K : ℝ}
    (hK : 0 < K) (hbad : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0))
    (hbound : ∀ᶠ n in atTop, ∀ sample ∈ good n, ‖X n sample‖ ≤ K * |rate n|) :
    IsBigOInProbability mu X rate := by
  intro epsilon hepsilon
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, hbad.eventually (Iio_mem_nhds hepsilon)] with n hn hprob
  apply lt_of_le_of_lt (measure_mono ?_) hprob
  intro sample hsample
  change sample ∉ good n
  exact fun hgood => not_lt_of_ge (hn sample hgood) hsample

/-- Lemma 3.5: construct its exact named local squared-CDF comparison input
from compact Stieltjes control and an imaginary-part bound for the reference.
For the paper, choose a positive common power rate dominating both `error_n`
and `sqrt(v_n)`; the preceding horizontal net supplies the good events. -/
theorem lemma35LocalBulkComparisonInput_of_stieltjes
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {I J : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, Nonempty (I n)]
    [∀ n, Fintype (J n)] [∀ n, Nonempty (J n)]
    (s : ∀ n, Omega → I n → ℝ) (t : ∀ n, Omega → J n → ℝ)
    {v error rate : ℕ → ℝ} {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (good : ℕ → Set Omega)
    (hbad : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0))
    (hscales : ∀ᶠ n in atTop,
      0 < v n ∧ 3 * Real.sqrt (v n) ≤ 1 ∧ 0 ≤ error n ∧
        error n ≤ rate n ∧ Real.sqrt (v n) ≤ rate n)
    (hcompare : ∀ n sample, sample ∈ good n → ∀ u ∈ Icc (-R - 1) (R + 1),
      ‖empiricalStieltjes (symmetrizedSpectrum (s n sample)) (spectralParameter u (v n)) -
        empiricalStieltjes (symmetrizedSpectrum (t n sample)) (spectralParameter u (v n))‖ ≤ error n)
    (hreference : ∀ n sample, sample ∈ good n → ∀ u ∈ Icc (-R - 1) (R + 1),
      (empiricalStieltjes (symmetrizedSpectrum (t n sample))
        (spectralParameter u (v n))).im ≤ C) :
    Lemma35LocalBulkComparisonInput mu s t R rate := by
  apply isBigOInProbability_of_bound_on_good
    (K := (2 * R + 8 * C + 18) / Real.pi) (by positivity) hbad
  filter_upwards [hscales] with n hn
  intro sample hsample
  rw [Real.norm_eq_abs, abs_of_nonneg
    (empiricalCdfDistanceOn_nonneg (sq_nonneg R)
      (fun i => s n sample i ^ 2) (fun j => t n sample j ^ 2))]
  have h := squaredCdfDistanceOn_le_of_stieltjes (s n sample) (t n sample)
    hn.1 hR hn.2.1 hn.2.2.1 (hcompare n sample hsample) (hreference n sample hsample)
  refine h.trans ?_
  calc
    ((2 * R + 10) * error n + (8 * C + 8) * Real.sqrt (v n)) / Real.pi ≤
        ((2 * R + 10) * rate n + (8 * C + 8) * rate n) / Real.pi :=
      div_le_div_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_left hn.2.2.2.1 (by positivity))
        (mul_le_mul_of_nonneg_left hn.2.2.2.2 (by positivity))) Real.pi_pos.le
    _ = ((2 * R + 8 * C + 18) / Real.pi) * rate n := by ring
    _ ≤ ((2 * R + 8 * C + 18) / Real.pi) * |rate n| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)

end ShortRingAnchor
