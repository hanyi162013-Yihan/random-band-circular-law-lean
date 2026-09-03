import ShortRingAnchor.HorizontalPolynomialNet

/-!
# Lemma 3.5: a single finite-grid event controls comparison and reference size

Only the two empirical transforms are interpolated. No continuity or
density premise for the common reference transform is used. The actual
v3 free transform supplies its pointwise norm bound at the grid centers.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace ShortRingAnchor

/-- Lemma 3.5: both transforms are close to the same reference on one grid. -/
def compactStieltjesGridGood {Omega : Type*}
    (f g : Omega → ℝ → ℂ) (reference : ℝ → ℂ) (N R d : ℝ) : Set Omega :=
  {sample | ∀ i : Fin (horizontalGridSize R (N ^ (-(2 : ℝ)))),
    ‖f sample (horizontalGridCenter R (N ^ (-(2 : ℝ))) i) -
      reference (horizontalGridCenter R (N ^ (-(2 : ℝ))) i)‖ ≤ N ^ (-d) ∧
    ‖g sample (horizontalGridCenter R (N ^ (-(2 : ℝ))) i) -
      reference (horizontalGridCenter R (N ^ (-(2 : ℝ))) i)‖ ≤ N ^ (-d)}

/-- Lemma 3.5: union bound for the two actual ensemble comparisons.
The measurable pointwise estimates are supplied by v3 McDiarmid. -/
theorem measure_compactStieltjesGridGood_compl_le
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (f g : Omega → ℝ → ℂ) (reference : ℝ → ℂ)
    {N R d : ℝ} (hN : 1 ≤ N) (hR : 0 ≤ R)
    (hf : ∀ i : Fin (horizontalGridSize R (N ^ (-(2 : ℝ)))),
      mu {sample | N ^ (-d) <
        ‖f sample (horizontalGridCenter R (N ^ (-(2 : ℝ))) i) -
          reference (horizontalGridCenter R (N ^ (-(2 : ℝ))) i)‖} ≤
        ENNReal.ofReal (N ^ (-(10 : ℝ))))
    (hg : ∀ i : Fin (horizontalGridSize R (N ^ (-(2 : ℝ)))),
      mu {sample | N ^ (-d) <
        ‖g sample (horizontalGridCenter R (N ^ (-(2 : ℝ))) i) -
          reference (horizontalGridCenter R (N ^ (-(2 : ℝ))) i)‖} ≤
        ENNReal.ofReal (N ^ (-(10 : ℝ)))) :
    mu (compactStieltjesGridGood f g reference N R d)ᶜ ≤
      2 * ENNReal.ofReal ((2 * R + 2) * N ^ (-(8 : ℝ))) := by
  classical
  let badA := fun i : Fin (horizontalGridSize R (N ^ (-(2 : ℝ)))) =>
    {sample | N ^ (-d) < ‖f sample (horizontalGridCenter R (N ^ (-(2 : ℝ))) i) -
      reference (horizontalGridCenter R (N ^ (-(2 : ℝ))) i)‖}
  let badB := fun i : Fin (horizontalGridSize R (N ^ (-(2 : ℝ)))) =>
    {sample | N ^ (-d) < ‖g sample (horizontalGridCenter R (N ^ (-(2 : ℝ))) i) -
      reference (horizontalGridCenter R (N ^ (-(2 : ℝ))) i)‖}
  have hsub : (compactStieltjesGridGood f g reference N R d)ᶜ ⊆
      ⋃ i, badA i ∪ badB i := by
    intro sample hsample
    by_contra hnot
    apply hsample
    intro i
    constructor
    · exact le_of_not_gt (fun h => hnot (mem_iUnion.mpr ⟨i, Or.inl h⟩))
    · exact le_of_not_gt (fun h => hnot (mem_iUnion.mpr ⟨i, Or.inr h⟩))
  calc
    _ ≤ mu (⋃ i, badA i ∪ badB i) := measure_mono hsub
    _ ≤ ∑ i, mu (badA i ∪ badB i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin (horizontalGridSize R (N ^ (-(2 : ℝ)))),
        (ENNReal.ofReal (N ^ (-(10 : ℝ))) + ENNReal.ofReal (N ^ (-(10 : ℝ)))) := by
      apply Finset.sum_le_sum
      intro i _
      exact (measure_union_le _ _).trans (add_le_add (hf i) (hg i))
    _ = 2 * ((horizontalGridSize R (N ^ (-(2 : ℝ))) : ℝ≥0∞) *
        ENNReal.ofReal (N ^ (-(10 : ℝ)))) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← two_mul]
      ac_rfl
    _ ≤ _ := mul_le_mul' le_rfl (horizontalPolynomial_failure_budget hN hR)

/-- Lemma 3.5: the one common grid event gives compact comparison, with
no regularity assumption on the common reference function. -/
theorem compactStieltjesGridGood_comparison {Omega : Type*}
    (f g : Omega → ℝ → ℂ) (reference : ℝ → ℂ)
    {N R d L : ℝ} (hN : 1 ≤ N) (hL0 : 0 ≤ L) (hL : L ≤ N) (hd : d ≤ 1)
    (hf : ∀ sample u w, ‖f sample u - f sample w‖ ≤ L * |u - w|)
    (hg : ∀ sample u w, ‖g sample u - g sample w‖ ≤ L * |u - w|)
    {sample : Omega} (hgood : sample ∈ compactStieltjesGridGood f g reference N R d)
    {u : ℝ} (hu : u ∈ Icc (-R) R) :
    ‖f sample u - g sample u‖ ≤ 4 * N ^ (-d) := by
  apply horizontalGrid_comparison_polynomial hN hL0 hL hd
    (f sample) (g sample) (hf sample) (hg sample) _ hu
  intro i
  have h := norm_sub_le_norm_sub_add_norm_sub
    (f sample (horizontalGridCenter R (N ^ (-(2 : ℝ))) i))
    (reference (horizontalGridCenter R (N ^ (-(2 : ℝ))) i))
    (g sample (horizontalGridCenter R (N ^ (-(2 : ℝ))) i))
  rw [norm_sub_rev (reference _) (g sample _)] at h
  linarith [(hgood i).1, (hgood i).2]

/-- Lemma 3.5: the same event bounds the reference empirical transform's
imaginary part by `3`; no extra random-matrix input is introduced. -/
theorem compactStieltjesGridGood_reference_im_le_three {Omega : Type*}
    (f g : Omega → ℝ → ℂ) (reference : ℝ → ℂ)
    {N R d L : ℝ} (hN : 1 ≤ N) (hL0 : 0 ≤ L) (hL : L ≤ N)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hg : ∀ sample u w, ‖g sample u - g sample w‖ ≤ L * |u - w|)
    (href : ∀ u, ‖reference u‖ ≤ 1)
    {sample : Omega} (hgood : sample ∈ compactStieltjesGridGood f g reference N R d)
    {u : ℝ} (hu : u ∈ Icc (-R) R) : (g sample u).im ≤ 3 := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  obtain ⟨i, hi⟩ := horizontalGrid_cover (Real.rpow_pos_of_pos hN0 (-(2 : ℝ))) hu
  let w := horizontalGridCenter R (N ^ (-(2 : ℝ))) i
  have hdelta : L * N ^ (-(2 : ℝ)) ≤ N ^ (-d) := by
    have h := horizontalPolynomial_interpolation_error_le hN hL hd1
    linarith
  have hpow : N ^ (-d) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hd0)
  have hclose : ‖g sample u - g sample w‖ ≤ N ^ (-d) :=
    (hg sample u w).trans ((mul_le_mul_of_nonneg_left hi hL0).trans hdelta)
  have hnorm : ‖g sample w‖ ≤ N ^ (-d) + 1 := by
    calc
      ‖g sample w‖ ≤ ‖g sample w - reference w‖ + ‖reference w‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ _ := add_le_add (hgood i).2 (href w)
  have h := norm_le_norm_sub_add (g sample u) (g sample w)
  have him := Complex.im_le_norm (g sample u)
  linarith

end ShortRingAnchor
