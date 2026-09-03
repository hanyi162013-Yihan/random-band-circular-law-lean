import ShortRingAnchor.PoissonSmoothingFinite

/-!
# Lemma 3.5: compact Stieltjes control implies compact interval-mass comparison

Endpoint masses are bounded by the same finite empirical Poisson integral.
No density or spectral-tail interface is used. This is the deterministic
smoothing step after the horizontal net, including atoms at interval endpoints.
-/

open Set MeasureTheory

noncomputable section
namespace ShortRingAnchor
open Arxiv2410V3

/-- Lemma 3.5: endpoint-window control directly from the empirical transform,
without constructing a limiting reference density. -/
theorem empiricalIntervalMass_le_length_from_stieltjes {I : Type*}
    [Fintype I] [Nonempty I] (s : I → ℝ) {v delta a b C : ℝ}
    (hv : 0 < v) (hd : 0 < delta) (hab : a ≤ b)
    (hbound : ∀ u ∈ Icc (a - delta) (b + delta),
      (empiricalStieltjes s (spectralParameter u v)).im ≤ C) :
    empiricalIntervalMass s a b ≤ (b - a + 2 * delta) * C / Real.pi +
      2 * (v / delta) / Real.pi := by
  have hm := empiricalIntervalMass_le_smoothed_enlarged s hv hd hab
  have hs := empiricalSmoothedMass_le_length_mul s hv (show a - delta ≤ b + delta by linarith)
    hbound
  exact hm.trans ((add_le_add hs le_rfl).trans_eq (by congr 1; ring))

/-- Lemma 3.5: one-sided comparison of closed interval masses at a fixed positive height.
Only the second empirical transform needs an imaginary-part upper bound. -/
theorem empiricalIntervalMass_le_of_local_stieltjes {I J : Type*}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (s : I → ℝ) (t : J → ℝ) {v delta a b C E : ℝ}
    (hv : 0 < v) (hd : 0 < delta) (hab : a ≤ b)
    (hcompare : ∀ u ∈ Icc (a - delta) (b + delta),
      ‖empiricalStieltjes s (spectralParameter u v) -
        empiricalStieltjes t (spectralParameter u v)‖ ≤ E)
    (hbound : ∀ u ∈ Icc (a - 3 * delta) (b + 3 * delta),
      (empiricalStieltjes t (spectralParameter u v)).im ≤ C) :
    empiricalIntervalMass s a b ≤ empiricalIntervalMass t a b +
      ((b - a + 2 * delta) * E / Real.pi + 8 * delta * C / Real.pi +
        8 * (v / delta) / Real.pi) := by
  have h1 := empiricalIntervalMass_le_smoothed_enlarged s hv hd hab
  have h2 := empiricalSmoothedMass_le_comparison s t hv
    (show a - delta ≤ b + delta by linarith) hcompare
  have h3 : empiricalSmoothedMass t v (a - delta) (b + delta) ≤
      empiricalIntervalMass t (a - 2 * delta) (b + 2 * delta) +
        2 * (v / delta) / Real.pi := by
    simpa only [show a - delta - delta = a - 2 * delta by ring,
      show b + delta + delta = b + 2 * delta by ring] using
      (empiricalSmoothedMass_le_interval_enlarged t (a := a - delta) (b := b + delta) hv hd)
  have h4 := empiricalIntervalMass_enlarged_le t a b delta
  have hl : empiricalIntervalMass t (a - 2 * delta) a ≤
      4 * delta * C / Real.pi + 2 * (v / delta) / Real.pi := by
    have h := empiricalIntervalMass_le_length_from_stieltjes t hv hd
      (show a - 2 * delta ≤ a by linarith)
      (fun u hu => hbound u ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    simpa only [show a - (a - 2 * delta) + 2 * delta = 4 * delta by ring] using h
  have hr : empiricalIntervalMass t b (b + 2 * delta) ≤
      4 * delta * C / Real.pi + 2 * (v / delta) / Real.pi := by
    have h := empiricalIntervalMass_le_length_from_stieltjes t hv hd
      (show b ≤ b + 2 * delta by linarith)
      (fun u hu => hbound u ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    simpa only [show b + 2 * delta - b + 2 * delta = 4 * delta by ring] using h
  calc
    empiricalIntervalMass s a b ≤ empiricalIntervalMass t a b +
        ((b + delta - (a - delta)) * E / Real.pi) +
        2 * (4 * delta * C / Real.pi) + 4 * (2 * (v / delta) / Real.pi) := by
      linarith
    _ = _ := by ring

/-- Lemma 3.5: two-sided local comparison. All spectral mass is retained;
the error consists only of resolvent comparison and Poisson endpoint/tail terms. -/
theorem abs_empiricalIntervalMass_sub_le_of_local_stieltjes {I J : Type*}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (s : I → ℝ) (t : J → ℝ) {v delta a b C E : ℝ}
    (hv : 0 < v) (hd : 0 < delta) (hab : a ≤ b)
    (hcompare : ∀ u ∈ Icc (a - delta) (b + delta),
      ‖empiricalStieltjes s (spectralParameter u v) -
        empiricalStieltjes t (spectralParameter u v)‖ ≤ E)
    (hs : ∀ u ∈ Icc (a - 3 * delta) (b + 3 * delta),
      (empiricalStieltjes s (spectralParameter u v)).im ≤ C)
    (ht : ∀ u ∈ Icc (a - 3 * delta) (b + 3 * delta),
      (empiricalStieltjes t (spectralParameter u v)).im ≤ C) :
    |empiricalIntervalMass s a b - empiricalIntervalMass t a b| ≤
      (b - a + 2 * delta) * E / Real.pi + 8 * delta * C / Real.pi +
        8 * (v / delta) / Real.pi := by
  have hforward := empiricalIntervalMass_le_of_local_stieltjes s t hv hd hab hcompare ht
  have hback := empiricalIntervalMass_le_of_local_stieltjes t s hv hd hab
    (fun u hu => by simpa only [norm_sub_rev] using hcompare u hu) hs
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Lemma 3.5: fully quantitative compact smoothing with `delta=sqrt(v)`.
The only analytic data are the two actual finite Stieltjes transforms on
`[-R-1,R+1]`, their comparison, and an imaginary-part bound for the second.
There is no assumption of bounded density or a spectral-tail bound. -/
theorem compact_interval_comparison_of_stieltjes {I J : Type*}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (s : I → ℝ) (t : J → ℝ) {v R C E : ℝ}
    (hv : 0 < v) (hsmall : 3 * Real.sqrt v ≤ 1) (hE : 0 ≤ E)
    (hcompare : ∀ u ∈ Icc (-R - 1) (R + 1),
      ‖empiricalStieltjes s (spectralParameter u v) -
        empiricalStieltjes t (spectralParameter u v)‖ ≤ E)
    (hreference : ∀ u ∈ Icc (-R - 1) (R + 1),
      (empiricalStieltjes t (spectralParameter u v)).im ≤ C)
    {a b : ℝ} (ha : -R ≤ a) (hb : b ≤ R) (hab : a ≤ b) :
    |empiricalIntervalMass s a b - empiricalIntervalMass t a b| ≤
      ((2 * R + 10) * E + (8 * C + 8) * Real.sqrt v) / Real.pi := by
  have hd : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hsubset (u : ℝ) (hu : u ∈ Icc (a - 3 * Real.sqrt v) (b + 3 * Real.sqrt v)) :
      u ∈ Icc (-R - 1) (R + 1) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hnorm u hu :
      ‖empiricalStieltjes s (spectralParameter u v) -
        empiricalStieltjes t (spectralParameter u v)‖ ≤ E :=
    hcompare u (hsubset u hu)
  have ht u hu : (empiricalStieltjes t (spectralParameter u v)).im ≤ C + E :=
    (hreference u (hsubset u hu)).trans (le_add_of_nonneg_right hE)
  have hs (u : ℝ) (hu : u ∈ Icc (a - 3 * Real.sqrt v) (b + 3 * Real.sqrt v)) :
      (empiricalStieltjes s (spectralParameter u v)).im ≤ C + E := by
    have hi := (Complex.im_le_norm
      (empiricalStieltjes s (spectralParameter u v) -
        empiricalStieltjes t (spectralParameter u v))).trans (hnorm u hu)
    rw [Complex.sub_im] at hi
    linarith [hreference u (hsubset u hu)]
  have h := abs_empiricalIntervalMass_sub_le_of_local_stieltjes s t hv hd hab
    (fun u hu => hnorm u ⟨by linarith [hu.1], by linarith [hu.2]⟩) hs ht
  have hratio : v / Real.sqrt v = Real.sqrt v := by
    apply (div_eq_iff hd.ne').mpr
    nlinarith [Real.sq_sqrt hv.le]
  rw [hratio] at h
  refine h.trans ?_
  rw [← add_div, ← add_div]
  apply (div_le_div_iff_of_pos_right Real.pi_pos).mpr
  have hwidth : b - a + 10 * Real.sqrt v ≤ 2 * R + 10 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hwidth hE
  nlinarith

end ShortRingAnchor
