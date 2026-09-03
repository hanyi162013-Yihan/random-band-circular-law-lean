/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/FreeDysonExistence.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.ScalarDysonBound
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# An internally constructed scalar free Stieltjes transform

This file constructs the upper-half-plane solution of the cubic obtained from v3
(3.2)--(3.4).  It uses only the fundamental theorem of algebra over `ℂ` and the Vieta
sum of the three roots.  In particular, existence is not left as an external interface.
-/

namespace Arxiv2410V3

open Polynomial

/-- The cubic in `w = η + m` obtained by clearing denominators in the scalar Dyson equation:
`w³ - η w² + (1 - |z|²)w + |z|²η = 0`. -/
noncomputable def scalarDysonCubic (z eta : ℂ) : ℂ[X] :=
  X ^ 3 +
    (-C eta * X ^ 2 +
      (C (1 - (Complex.normSq z : ℂ)) * X +
        C ((Complex.normSq z : ℂ) * eta)))

/-- The cubic is monic of the claimed exact degree. -/
theorem scalarDysonCubic_isMonicOfDegree (z eta : ℂ) :
    (scalarDysonCubic z eta).IsMonicOfDegree 3 := by
  rw [scalarDysonCubic]
  have hquadratic : (-C eta * X ^ 2 : ℂ[X]).natDegree ≤ 2 := by
    have h := (natDegree_C_mul_le (-eta) (X ^ 2)).trans (natDegree_X_pow_le 2)
    simpa only [map_neg] using h
  have hlinear :
      (C (1 - (Complex.normSq z : ℂ)) * X : ℂ[X]).natDegree ≤ 1 :=
    (natDegree_C_mul_le (1 - (Complex.normSq z : ℂ)) X).trans natDegree_X_le
  have hconstant :
      (C ((Complex.normSq z : ℂ) * eta) : ℂ[X]).natDegree ≤ 0 :=
    by rw [natDegree_C]
  have htail :
      (C (1 - (Complex.normSq z : ℂ)) * X +
        C ((Complex.normSq z : ℂ) * eta) : ℂ[X]).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans
      (max_le hlinear (hconstant.trans (by norm_num)))
  have hmax :
      max (-C eta * X ^ 2 : ℂ[X]).natDegree
          (C (1 - (Complex.normSq z : ℂ)) * X +
            C ((Complex.normSq z : ℂ) * eta) : ℂ[X]).natDegree ≤ 2 :=
    max_le hquadratic (htail.trans (by norm_num))
  have hlower :
      (-C eta * X ^ 2 +
        (C (1 - (Complex.normSq z : ℂ)) * X +
          C ((Complex.normSq z : ℂ) * eta)) : ℂ[X]).natDegree < 3 :=
    (natDegree_add_le _ _).trans_lt
      (hmax.trans_lt (by norm_num : (2 : ℕ) < 3))
  exact (isMonicOfDegree_X_pow ℂ 3).add_right hlower

/-- The cleared scalar Dyson polynomial is monic. -/
theorem scalarDysonCubic_monic (z eta : ℂ) :
    (scalarDysonCubic z eta).Monic :=
  (scalarDysonCubic_isMonicOfDegree z eta).monic

/-- The cleared scalar Dyson polynomial has degree three. -/
@[simp] theorem scalarDysonCubic_natDegree (z eta : ℂ) :
    (scalarDysonCubic z eta).natDegree = 3 := by
  exact (scalarDysonCubic_isMonicOfDegree z eta).natDegree_eq

/-- The coefficient just below the leading coefficient is `-η`. -/
@[simp] theorem scalarDysonCubic_nextCoeff (z eta : ℂ) :
    (scalarDysonCubic z eta).nextCoeff = -eta := by
  classical
  rw [Polynomial.nextCoeff_of_natDegree_pos]
  · rw [scalarDysonCubic_natDegree]
    norm_num
    simp only [scalarDysonCubic, coeff_add, coeff_C_mul,
      coeff_X_pow, coeff_C, coeff_X]
    norm_num
  · rw [scalarDysonCubic_natDegree]
    norm_num

/-- Vieta's relation: the three roots, with multiplicity, sum to `η`. -/
theorem scalarDysonCubic_sum_roots (z eta : ℂ) :
    (scalarDysonCubic z eta).roots.sum = eta := by
  have hsplits : (scalarDysonCubic z eta).Splits :=
    IsAlgClosed.splits (scalarDysonCubic z eta)
  have hvieta := hsplits.nextCoeff_eq_neg_sum_roots_of_monic
    (scalarDysonCubic_monic z eta)
  rw [scalarDysonCubic_nextCoeff] at hvieta
  exact neg_injective hvieta.symm

/-- Evaluation of the cubic in the form used to recover the scalar Dyson equation. -/
theorem scalarDysonCubic_eval (z eta w : ℂ) :
    (scalarDysonCubic z eta).eval w =
      (w - eta) * w ^ 2 - (Complex.normSq z : ℂ) * (w - eta) + w := by
  simp [scalarDysonCubic]
  ring

/-- A nonzero cubic root `w`, with `m = w - η`, satisfies the reciprocal scalar equation.
The second nonzero condition is automatic in the upper-half-plane application and is kept
explicit in this denominator-clearing lemma. -/
theorem scalarDysonEquation_of_cubic_root
    {z eta w : ℂ}
    (hroot : (scalarDysonCubic z eta).eval w = 0)
    (hw : w ≠ 0) (hm : w - eta ≠ 0) :
    ScalarDysonEquation z eta (w - eta) := by
  rw [scalarDysonCubic_eval] at hroot
  unfold ScalarDysonEquation
  have hweta : eta + (w - eta) = w := by ring
  rw [hweta]
  field_simp [hw, hm]
  linear_combination hroot

/-- A finite multiset of complex numbers with nonpositive imaginary parts has a sum with
nonpositive imaginary part. -/
private theorem Multiset.im_sum_nonpos
    (s : Multiset ℂ) (h : ∀ w ∈ s, w.im ≤ 0) : s.sum.im ≤ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons w s ih =>
      rw [Multiset.sum_cons, Complex.add_im]
      exact add_nonpos
        (h w (by simp))
        (ih (fun u hu => h u (by simp [hu])))

/-- A cubic root is either the possible cleared-denominator root `0`, lies below the real
axis, or lies strictly above the horizontal line `Im w = Im η`.  This is the root-sign
content of the imaginary part of v3 (3.2)--(3.4). -/
theorem scalarDysonCubic_root_trichotomy
    {z eta w : ℂ} (heta : 0 < eta.im)
    (hroot : (scalarDysonCubic z eta).eval w = 0) :
    w = 0 ∨ w.im < 0 ∨ eta.im < w.im := by
  by_cases hw : w = 0
  · exact Or.inl hw
  right
  have hm : w - eta ≠ 0 := by
    intro hm0
    have hweta : w = eta := sub_eq_zero.mp hm0
    subst w
    rw [scalarDysonCubic_eval] at hroot
    have heta0 : eta = 0 := by simpa using hroot
    subst eta
    norm_num at heta
  have hdyson := scalarDysonEquation_of_cubic_root hroot hw hm
  by_cases hupper : eta.im < w.im
  · exact Or.inr hupper
  left
  have hm_im_nonpos : (w - eta).im ≤ 0 := by
    simp only [Complex.sub_im]
    exact sub_nonpos.mpr (le_of_not_gt hupper)
  have hm_sq_pos : 0 < Complex.normSq (w - eta) :=
    Complex.normSq_pos.mpr hm
  have hw_sq_pos : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  have him := scalarDyson_imaginary_identity hdyson
  have heta_add : eta + (w - eta) = w := by ring
  rw [heta_add] at him
  have heta_im_add : eta.im + (w - eta).im = w.im := by
    simp only [Complex.sub_im]
    ring
  rw [heta_im_add] at him
  by_contra hw_im_not_neg
  have hw_im_nonneg : 0 ≤ w.im := le_of_not_gt hw_im_not_neg
  have hcorrection_nonneg :
      0 ≤ Complex.normSq z * w.im / Complex.normSq w :=
    div_nonneg
      (mul_nonneg (Complex.normSq_nonneg z) hw_im_nonneg)
      hw_sq_pos.le
  have hratio :
      (w - eta).im / Complex.normSq (w - eta) =
        w.im + Complex.normSq z * w.im / Complex.normSq w := by
    linear_combination -him
  have hratio_nonneg :
      0 ≤ (w - eta).im / Complex.normSq (w - eta) := by
    rw [hratio]
    exact add_nonneg hw_im_nonneg hcorrection_nonneg
  have hm_im_nonneg : 0 ≤ (w - eta).im := by
    have hscaled := (le_div_iff₀ hm_sq_pos).mp hratio_nonneg
    simpa using hscaled
  have hm_im_zero : (w - eta).im = 0 :=
    le_antisymm hm_im_nonpos hm_im_nonneg
  have hw_im_pos : 0 < w.im := by
    simp only [Complex.sub_im] at hm_im_zero
    linarith
  have hratio_pos :
      0 < (w - eta).im / Complex.normSq (w - eta) := by
    rw [hratio]
    exact add_pos_of_pos_of_nonneg hw_im_pos hcorrection_nonneg
  have hm_im_pos : 0 < (w - eta).im := by
    have hscaled := (div_pos_iff).mp hratio_pos
    rcases hscaled with h | h
    · exact h.1
    · exfalso
      linarith
  linarith

/-- For every `η ∈ ℂ₊`, the v3 scalar cubic has a root above `Im η`.  The proof is
Vieta's formula: otherwise every root has nonpositive imaginary part, contradicting that their
sum is `η`. -/
theorem exists_scalarDysonCubic_root_above
    (z eta : ℂ) (heta : 0 < eta.im) :
    ∃ w ∈ (scalarDysonCubic z eta).roots, eta.im < w.im := by
  by_contra hnone
  push Not at hnone
  have hall : ∀ w ∈ (scalarDysonCubic z eta).roots, w.im ≤ 0 := by
    intro w hw
    have hroot : (scalarDysonCubic z eta).eval w = 0 :=
      (Polynomial.isRoot_of_mem_roots hw :
        (scalarDysonCubic z eta).eval w = 0)
    rcases scalarDysonCubic_root_trichotomy heta hroot with hw0 | hwneg | hwabove
    · simp [hw0]
    · exact hwneg.le
    · exact (not_lt_of_ge (hnone w hw) hwabove).elim
  have hsum_nonpos := Multiset.im_sum_nonpos
    (scalarDysonCubic z eta).roots hall
  rw [scalarDysonCubic_sum_roots] at hsum_nonpos
  linarith

/-- Existence of an upper-half-plane scalar solution of v3 (3.2)--(3.4), proved internally
from the cubic rather than postulated as an analytic interface. -/
theorem exists_scalarDysonEquation_solution
    (z eta : ℂ) (heta : 0 < eta.im) :
    ∃ m : ℂ, 0 < m.im ∧ ScalarDysonEquation z eta m := by
  obtain ⟨w, hwroot, hwabove⟩ := exists_scalarDysonCubic_root_above z eta heta
  have hroot : (scalarDysonCubic z eta).eval w = 0 :=
    (Polynomial.isRoot_of_mem_roots hwroot :
      (scalarDysonCubic z eta).eval w = 0)
  have hw : w ≠ 0 := by
    intro hw0
    subst w
    norm_num at hwabove
    linarith
  have hm : w - eta ≠ 0 := by
    intro hm0
    have := sub_eq_zero.mp hm0
    subst w
    linarith
  refine ⟨w - eta, ?_, scalarDysonEquation_of_cubic_root hroot hw hm⟩
  simp only [Complex.sub_im]
  linarith

/-- Canonical internally defined free scalar Stieltjes transform.  Outside `ℂ₊` it is set
to zero; all uses in Proposition 3.4 and Corollary 3.5 are in `ℂ₊`. -/
noncomputable def freeDysonStieltjes (z eta : ℂ) : ℂ :=
  if heta : 0 < eta.im then
    Classical.choose (exists_scalarDysonEquation_solution z eta heta)
  else 0

/-- The canonical free transform has positive imaginary part on `ℂ₊`. -/
theorem freeDysonStieltjes_im_pos
    (z eta : ℂ) (heta : 0 < eta.im) :
    0 < (freeDysonStieltjes z eta).im := by
  rw [freeDysonStieltjes, dif_pos heta]
  exact (Classical.choose_spec
    (exists_scalarDysonEquation_solution z eta heta)).1

/-- The canonical free transform solves the scalar equation v3 (3.2)--(3.4). -/
theorem freeDysonStieltjes_equation
    (z eta : ℂ) (heta : 0 < eta.im) :
    ScalarDysonEquation z eta (freeDysonStieltjes z eta) := by
  rw [freeDysonStieltjes, dif_pos heta]
  exact (Classical.choose_spec
    (exists_scalarDysonEquation_solution z eta heta)).2

/-- Uniform free-transform bound used after v3 formula (3.9), now a proved theorem. -/
theorem freeDysonStieltjes_norm_lt_one
    (z eta : ℂ) (heta : 0 < eta.im) :
    ‖freeDysonStieltjes z eta‖ < 1 :=
  norm_lt_one_of_scalarDysonEquation heta
    (freeDysonStieltjes_im_pos z eta heta)
    (freeDysonStieltjes_equation z eta heta)

/-- Imaginary-part form used by the Poisson-kernel proof of v3 Corollary 3.5. -/
theorem freeDysonStieltjes_im_le_one
    (z eta : ℂ) (heta : 0 < eta.im) :
    (freeDysonStieltjes z eta).im ≤ 1 :=
  im_le_one_of_scalarDysonEquation heta
    (freeDysonStieltjes_im_pos z eta heta)
    (freeDysonStieltjes_equation z eta heta)

end Arxiv2410V3

