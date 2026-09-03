/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/ScalarDysonBound.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Mathlib.Analysis.Complex.Norm

/-!
# The scalar Dyson bound used in arXiv:2410.16457v3, Proposition 3.4

The block Dyson equation in v3 (3.2)--(3.4) reduces, after the symmetry relations are
inserted, to

`m⁻¹ = -(η + m) + |z|² (η + m)⁻¹`.

This file proves directly that every upper-half-plane solution has norm strictly smaller
than one.  Thus the bound needed after v3 (3.9) is algebraic and is not an external
probabilistic input.  The argument is valid for every finite `z : ℂ`; in particular there
is no `|z| ≤ 2.5` assumption.
-/

namespace Arxiv2410V3

/-- Scalar form of the v3 equations (3.2)--(3.4), with `|z|²` written as
`Complex.normSq z`. -/
def ScalarDysonEquation (z eta m : ℂ) : Prop :=
  m⁻¹ = -(eta + m) + (Complex.normSq z : ℂ) * (eta + m)⁻¹

/-- Imaginary-part identity obtained from the scalar Dyson equation in v3 (3.2)--(3.4). -/
theorem scalarDyson_imaginary_identity
    {z eta m : ℂ} (hdyson : ScalarDysonEquation z eta m) :
    -(m.im / Complex.normSq m) =
      -(eta.im + m.im) -
        Complex.normSq z * (eta.im + m.im) / Complex.normSq (eta + m) := by
  have him := congrArg Complex.im hdyson
  simp only [Complex.inv_im, Complex.add_im, Complex.neg_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    mul_neg, neg_div] at him
  convert him using 1
  all_goals ring

/-- The a priori bound read from v3 (3.2)--(3.4): any solution with `Im η > 0` and
`Im m > 0` satisfies `|m| < 1`.  The constant is uniform in the fixed finite `z`. -/
theorem norm_lt_one_of_scalarDysonEquation
    {z eta m : ℂ}
    (heta : 0 < eta.im) (hm : 0 < m.im)
    (hdyson : ScalarDysonEquation z eta m) :
    ‖m‖ < 1 := by
  have hm_ne : m ≠ 0 := by
    intro hm0
    subst m
    norm_num at hm
  have hw_im : 0 < (eta + m).im := by
    simp only [Complex.add_im]
    linarith
  have hw_ne : eta + m ≠ 0 := by
    intro hw0
    have : (eta + m).im = 0 := congrArg Complex.im hw0
    linarith
  have hm_sq_pos : 0 < Complex.normSq m := Complex.normSq_pos.mpr hm_ne
  have hw_sq_pos : 0 < Complex.normSq (eta + m) := Complex.normSq_pos.mpr hw_ne
  have hz_sq_nonneg : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
  have him := scalarDyson_imaginary_identity hdyson
  have hcorrection_nonneg :
      0 ≤ Complex.normSq z * (eta.im + m.im) / Complex.normSq (eta + m) :=
    div_nonneg (mul_nonneg hz_sq_nonneg hw_im.le) hw_sq_pos.le
  have hratio :
      eta.im + m.im ≤ m.im / Complex.normSq m := by
    calc
      eta.im + m.im ≤
          eta.im + m.im +
            Complex.normSq z * (eta.im + m.im) / Complex.normSq (eta + m) :=
        le_add_of_nonneg_right hcorrection_nonneg
      _ = m.im / Complex.normSq m := by linarith only [him]
  have hm_sq_lt_one : Complex.normSq m < 1 := by
    by_contra hnot
    have hone : 1 ≤ Complex.normSq m := le_of_not_gt hnot
    have hscaled :
        (eta.im + m.im) * Complex.normSq m ≤ m.im :=
      (le_div_iff₀ hm_sq_pos).mp hratio
    have hmonotone :
        eta.im + m.im ≤ (eta.im + m.im) * Complex.normSq m := by
      calc
        eta.im + m.im = (eta.im + m.im) * 1 := by ring
        _ ≤ (eta.im + m.im) * Complex.normSq m :=
          mul_le_mul_of_nonneg_left hone hw_im.le
    linarith
  rw [Complex.normSq_eq_norm_sq] at hm_sq_lt_one
  nlinarith [norm_nonneg m]

/-- Non-strict version of the same v3 scalar-Dyson estimate, convenient for formula (3.10). -/
theorem norm_le_one_of_scalarDysonEquation
    {z eta m : ℂ}
    (heta : 0 < eta.im) (hm : 0 < m.im)
    (hdyson : ScalarDysonEquation z eta m) :
    ‖m‖ ≤ 1 :=
  (norm_lt_one_of_scalarDysonEquation heta hm hdyson).le

/-- The imaginary-part bound actually needed for the fixed-`z` proof of v3 Corollary 3.5. -/
theorem im_le_one_of_scalarDysonEquation
    {z eta m : ℂ}
    (heta : 0 < eta.im) (hm : 0 < m.im)
    (hdyson : ScalarDysonEquation z eta m) :
    m.im ≤ 1 := by
  exact (Complex.im_le_norm m).trans
    (norm_le_one_of_scalarDysonEquation heta hm hdyson)

end Arxiv2410V3

