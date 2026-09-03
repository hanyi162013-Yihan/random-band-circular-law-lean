import ShortRingAnchor.HorizontalPolynomialNet
import ShortRingAnchor.HermitizationCounting
import ShortRingAnchor.MatrixLocalBulk
import ShortRingAnchor.V3PointwiseProbability
import Vendor.Arxiv2410.V3.FixedZImaginaryBound

/-!
# Corollary 3.5 counting on the imaginary axis

For the symmetric intervals used in Proposition 3.6, a one-dimensional
vertical grid suffices. Its spacing is `N^(-2)`; clipping the grid from
below keeps every point above the hard-edge cutoff. The actual v3
concentration estimate gives failure `4 N^(-8)`. No restriction on `z`
and no additional counting or free-law regularity hypothesis is used.
-/

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace ShortRingAnchor
open Arxiv2410V3

/-- Corollary 3.5 uniformization: clip a mesh point to the admissible heights. -/
def verticalGridHeight (N a : ℝ)
    (i : Fin (horizontalGridSize 1 (N ^ (-(2 : ℝ))))) : ℝ :=
  max a (horizontalGridCenter 1 (N ^ (-(2 : ℝ))) i)

/-- Corollary 3.5: clipping preserves the mesh cover for every `a <= r <= 1`. -/
theorem verticalGrid_cover {N a r : ℝ} (hN : 0 < N) (ha : 0 ≤ a)
    (har : a ≤ r) (hr : r ≤ 1) :
    ∃ i : Fin (horizontalGridSize 1 (N ^ (-(2 : ℝ)))),
      |r - verticalGridHeight N a i| ≤ N ^ (-(2 : ℝ)) := by
  obtain ⟨i, hi⟩ := horizontalGrid_cover (Real.rpow_pos_of_pos hN (-(2 : ℝ)))
    (show r ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, hr⟩)
  refine ⟨i, ?_⟩
  unfold verticalGridHeight
  by_cases h : a ≤ horizontalGridCenter 1 (N ^ (-(2 : ℝ))) i
  · simpa only [max_eq_right h] using hi
  · rw [max_eq_left (le_of_not_ge h), abs_of_nonneg (sub_nonneg.mpr har)]
    have := (abs_le.mp hi).2
    linarith

/-- The finite event used to obtain all symmetric-interval counts at once. -/
def verticalStieltjesGridGood {Omega : Type*} {n : ℕ}
    (X : Omega → Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (a : ℝ) : Set Omega :=
  {sample | ∀ i : Fin (horizontalGridSize 1 ((n : ℝ) ^ (-(2 : ℝ)))),
    ‖stieltjesTrace (X sample) z
      (spectralParameter 0 (verticalGridHeight n a i))‖ ≤ 2}

/-- Corollary 3.5: interpolate the actual matrix trace, not the free reference. -/
theorem verticalStieltjesGridGood_norm_le_three {Omega : Type*} {n : ℕ}
    (hn : 2 ≤ n) (X : Omega → Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {a r : ℝ} (ha : (n : ℝ) ^ (-(1 / 8 : ℝ)) ≤ a)
    (har : a ≤ r) (hr : r ≤ 1) {sample : Omega}
    (hgood : sample ∈ verticalStieltjesGridGood X z a) :
    ‖stieltjesTrace (X sample) z (spectralParameter 0 r)‖ ≤ 3 := by
  let _ : NeZero n := ⟨by omega⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have ha0 : 0 < a := (Real.rpow_pos_of_pos hn0 _).trans_le ha
  obtain ⟨i, hi⟩ := verticalGrid_cover hn0 ha0.le har hr
  have hv : a ≤ verticalGridHeight n a i := le_max_left _ _
  have hdist : dist (spectralParameter 0 r)
      (spectralParameter 0 (verticalGridHeight n a i)) =
      |r - verticalGridHeight n a i| := by
    rw [dist_eq_norm]
    simp [spectralParameter, ← sub_mul, ← Complex.ofReal_sub]
  have hclose := norm_stieltjesTrace_sub_eta_le_of_im_ge (X sample) z ha0
    (show a ≤ (spectralParameter 0 r).im by simpa [spectralParameter] using har)
    (show a ≤ (spectralParameter 0 (verticalGridHeight n a i)).im by
      simpa [spectralParameter] using hv)
  rw [hdist] at hclose
  have hbudget : a⁻¹ ^ 2 * (n : ℝ) ^ (-(2 : ℝ)) ≤ 1 := by
    have h := horizontalPolynomial_interpolation_error_le hn1
      (inverse_height_sq_le_dimension hn1 ha) (show (0 : ℝ) ≤ 1 by norm_num)
    simp only [neg_zero, Real.rpow_zero, mul_one] at h
    linarith
  have hclose1 := hclose.trans
    ((mul_le_mul_of_nonneg_left hi (sq_nonneg _)).trans hbudget)
  have hnorm := norm_le_norm_sub_add
    (stieltjesTrace (X sample) z (spectralParameter 0 r))
    (stieltjesTrace (X sample) z (spectralParameter 0 (verticalGridHeight n a i)))
  linarith [hgood i]

/-- v3 (3.1): the two developments use exactly the same Hermitization spectrum. -/
theorem smallHermitizationEigenvalueIndices_eq_v3 {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (r : ℝ) :
    smallHermitizationEigenvalueIndices (X - z • 1) r =
      eigenvaluesInInterval (Arxiv2410V3.hermitization_isHermitian X z).eigenvalues (-r) r := by
  rfl

/-- Corollary 3.5, specialized to all cutoffs needed before manuscript (3.10).
The explicit bound is `6 N (2r)`; large radii use the total dimension `2N`. -/
theorem verticalStieltjesGridGood_count {Omega : Type*} {n : ℕ}
    (hn : 2 ≤ n) (X : Omega → Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {a : ℝ} (ha : (n : ℝ) ^ (-(1 / 8 : ℝ)) ≤ a)
    {sample : Omega} (hgood : sample ∈ verticalStieltjesGridGood X z a)
    {r : ℝ} (har : a ≤ r) :
    ((smallHermitizationEigenvalueIndices (X sample - z • 1) r).card : ℝ) ≤
      6 * (n : ℝ) * (2 * r) := by
  let _ : NeZero n := ⟨by omega⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr0 : 0 < r := (Real.rpow_pos_of_pos hn0 _).trans_le (ha.trans har)
  by_cases hr : r ≤ 1
  · have hnorm := verticalStieltjesGridGood_norm_le_three hn X z ha har hr hgood
    rw [stieltjesTrace_eq_empiricalHermitizationSpectrum (X sample) z
      (show 0 < (spectralParameter 0 r).im by simpa [spectralParameter] using hr0)] at hnorm
    have h := interval_count_le_of_stieltjes_im_bound_at
      (Arxiv2410V3.hermitization_isHermitian (X sample) z).eigenvalues hr0
      (fun i hi hj => by simpa only [sub_zero, abs_le] using And.intro hi hj)
      ((Complex.im_le_norm _).trans hnorm)
    rw [smallHermitizationEigenvalueIndices_eq_v3]
    convert h using 1 <;> simp [Arxiv2410V3.HermitizationIndex] <;> ring
  · have hcard : (smallHermitizationEigenvalueIndices (X sample - z • 1) r).card ≤ 2 * n := by
      simpa only [smallHermitizationEigenvalueIndices, Finset.card_univ,
        ShortRingAnchor.card_hermitizationIndex] using
        Finset.card_le_card (Finset.filter_subset
          (fun i => -r ≤ hermitizationEigenvalue (X sample - z • 1) i ∧
            hermitizationEigenvalue (X sample - z • 1) i ≤ r) Finset.univ)
    have hcardR : ((smallHermitizationEigenvalueIndices (X sample - z • 1) r).card : ℝ) ≤
        2 * (n : ℝ) := by exact_mod_cast hcard
    nlinarith

/-- v3 proof step (3), vertical union bound: the failure probability is at most `4 N^-8`.
Only the named BBV comparison is external; McDiarmid and BVH are proved inputs. -/
theorem verticalStieltjesGridGood_bad_le
    {Omega OmegaXi : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {n : ℕ} (hn : 2 ≤ n) (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (z : ℂ) {a B C : ℝ} (ha : 0 < a)
    (hB : IsBandwidth model.profile B) (hC : 8 ≤ C)
    (hthird : BVH.atomThirdMoment model + BVH.complexGaussianThirdMomentConstant ≤ C)
    (bbv : ∀ v, a ≤ v → CanonicalBBVAt model z (spectralParameter 0 v) B C)
    (herr : ∀ v, a ≤ v → formula311Error n B v C 32 ≤ 1) :
    mu (verticalStieltjesGridGood model.matrix z a)ᶜ ≤
      ENNReal.ofReal (4 * (n : ℝ) ^ (-(8 : ℝ))) := by
  classical
  let bad := fun i : Fin (horizontalGridSize 1 ((n : ℝ) ^ (-(2 : ℝ)))) =>
    (v3TraceConcentrationGood model z (spectralParameter 0 (verticalGridHeight n a i)))ᶜ
  have hsub : (verticalStieltjesGridGood model.matrix z a)ᶜ ⊆ ⋃ i, bad i := by
    intro sample hs
    by_contra hnot
    apply hs
    intro i
    have hv : a ≤ verticalGridHeight n a i := le_max_left _ _
    have heta : 0 < (spectralParameter 0 (verticalGridHeight n a i)).im := by
      simpa [spectralParameter] using ha.trans_le hv
    have hc : sample ∈ v3TraceConcentrationGood model z
        (spectralParameter 0 (verticalGridHeight n a i)) := by
      by_contra h
      exact hnot (mem_iUnion.mpr ⟨i, h⟩)
    have h := v3_formula311_canonical_on_good hn model z heta hB hC hthird (bbv _ hv) hc
    have he : formula311Error n B (spectralParameter 0 (verticalGridHeight n a i)).im C 32 ≤ 1 := by
      simpa [spectralParameter] using herr _ hv
    have hf := freeDysonStieltjes_norm_lt_one z _ heta
    have ht := norm_le_norm_sub_add
      (stieltjesTrace (model.matrix sample) z (spectralParameter 0 (verticalGridHeight n a i)))
      (freeDysonStieltjes z (spectralParameter 0 (verticalGridHeight n a i)))
    linarith
  calc
    _ ≤ mu (⋃ i, bad i) := measure_mono hsub
    _ ≤ ∑ i, mu (bad i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin (horizontalGridSize 1 ((n : ℝ) ^ (-(2 : ℝ)))),
        ENNReal.ofReal ((n : ℝ) ^ (-(10 : ℝ))) := by
      apply Finset.sum_le_sum
      intro i _
      exact v3_concentration_bad_le hn model z (by
        simpa only [spectralParameter, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
          mul_one, mul_zero, add_zero, zero_add] using
          ha.trans_le (show a ≤ verticalGridHeight n a i from le_max_left _ _))
    _ = (horizontalGridSize 1 ((n : ℝ) ^ (-(2 : ℝ))) : ℝ≥0∞) *
        ENNReal.ofReal ((n : ℝ) ^ (-(10 : ℝ))) := by simp
    _ ≤ _ := by
      simpa only [mul_one, show (2 + 2 : ℝ) = 4 by norm_num] using horizontalPolynomial_failure_budget
        (show (1 : ℝ) ≤ n by exact_mod_cast (show 1 ≤ n by omega))
        (show (0 : ℝ) ≤ 1 by norm_num)

end ShortRingAnchor
