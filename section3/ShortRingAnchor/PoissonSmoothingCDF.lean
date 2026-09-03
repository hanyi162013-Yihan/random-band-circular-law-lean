import ShortRingAnchor.LocalPoissonSmoothing
import ShortRingAnchor.BulkClippedLog

/-!
# Lemma 3.5: Poisson smoothing reaches the local CDF of squared singular values

This module proves the exact finite-family symmetrization identity, including
zero values and endpoint atoms. Matrix identification of this symmetric
finite spectrum with a particular Hermitization is a separate algebraic step.
-/

open Set
open scoped BigOperators

noncomputable section
namespace ShortRingAnchor
open Arxiv2410V3

/-- Lemma 3.5: the symmetric spectrum associated with a finite singular-value family. -/
def symmetrizedSpectrum {I : Type*} (s : I → ℝ) : I ⊕ I → ℝ :=
  Sum.elim s (fun i => -s i)

/-- Lemma 3.5, final interval substitution: closed endpoints correspond exactly
to the squared-value threshold, also at zero. -/
theorem closedIntervalIndicator_sqrt_eq {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    closedIntervalIndicator (-Real.sqrt x) (Real.sqrt x) y =
      if y ^ 2 ≤ x then 1 else 0 := by
  have hiff : (-Real.sqrt x ≤ y ∧ y ≤ Real.sqrt x) ↔ y ^ 2 ≤ x := by
    rw [← abs_le, Real.le_sqrt (abs_nonneg y) hx, sq_abs]
  simp only [closedIntervalIndicator, hiff]

/-- Lemma 3.5: the symmetric empirical interval mass is exactly the CDF of
squared singular values. No nonsingularity assumption is needed. -/
theorem empiricalIntervalMass_symmetrized_sqrt {I : Type*}
    [Fintype I] [Nonempty I] (s : I → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    empiricalIntervalMass (symmetrizedSpectrum s) (-Real.sqrt x) (Real.sqrt x) =
      empiricalCdf (fun i => (s i) ^ 2) x := by
  classical
  have hn : (Fintype.card I : ℝ) ≠ 0 := by positivity
  unfold empiricalIntervalMass empiricalAverage symmetrizedSpectrum
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fintype.card_sum, Nat.cast_add]
  simp_rw [closedIntervalIndicator_sqrt_eq hx, neg_sq]
  unfold empiricalCdf
  rw [Finset.natCast_card_filter]
  field_simp

/-- Lemma 3.5: the complete deterministic Stieltjes-to-local-squared-CDF
smoothing theorem. All comparison and reference bounds concern only a fixed
compact interval; no density, spectral tail, or Gaussian formula is assumed. -/
theorem squaredCdfDistanceOn_le_of_stieltjes {I J : Type*}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (s : I → ℝ) (t : J → ℝ) {v R C E : ℝ}
    (hv : 0 < v) (hR : 0 ≤ R) (hsmall : 3 * Real.sqrt v ≤ 1) (hE : 0 ≤ E)
    (hcompare : ∀ u ∈ Icc (-R - 1) (R + 1),
      ‖empiricalStieltjes (symmetrizedSpectrum s) (spectralParameter u v) -
        empiricalStieltjes (symmetrizedSpectrum t) (spectralParameter u v)‖ ≤ E)
    (hreference : ∀ u ∈ Icc (-R - 1) (R + 1),
      (empiricalStieltjes (symmetrizedSpectrum t) (spectralParameter u v)).im ≤ C) :
    empiricalCdfDistanceOn 0 (R ^ 2) (fun i => s i ^ 2) (fun j => t j ^ 2) ≤
      ((2 * R + 10) * E + (8 * C + 8) * Real.sqrt v) / Real.pi := by
  apply csSup_le
  · exact (nonempty_Icc.mpr (sq_nonneg R)).image _
  · rintro _ ⟨x, hx, rfl⟩
    have hxR : Real.sqrt x ≤ R := (Real.sqrt_le_left hR).mpr hx.2
    have h := compact_interval_comparison_of_stieltjes
      (symmetrizedSpectrum s) (symmetrizedSpectrum t) hv hsmall hE hcompare hreference
      (a := -Real.sqrt x) (b := Real.sqrt x) (by linarith) hxR
      (by linarith [Real.sqrt_nonneg x])
    simpa only [empiricalIntervalMass_symmetrized_sqrt s hx.1,
      empiricalIntervalMass_symmetrized_sqrt t hx.1] using h

/-- Lemma 3.5: for nonnegative spectra the same smoothing theorem directly
controls their (unsquared) CDF on a compact interval. -/
theorem empiricalIntervalMass_zero_eq_cdf {I : Type*} [Fintype I]
    (s : I → ℝ) (hs : ∀ i, 0 ≤ s i) (x : ℝ) :
    empiricalIntervalMass s 0 x = empiricalCdf s x := by
  classical
  unfold empiricalIntervalMass empiricalAverage empiricalCdf
  rw [Finset.natCast_card_filter]
  simp [closedIntervalIndicator, hs]

end ShortRingAnchor
