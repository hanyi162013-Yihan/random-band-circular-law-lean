/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/FreeDysonUniqueness.lean
   Local adaptation: only the import path is prefixed with Vendor. -/
import Vendor.Arxiv2410.V3.FreeDysonExistence

/-!
# Uniqueness of the upper-half-plane scalar Dyson solution

This file proves internally the uniqueness assertion used when the block Dyson solution
from v3 (3.2)--(3.4) is identified with the canonical scalar transform constructed in
`FreeDysonExistence.lean`.  No analytic uniqueness theorem is assumed.
-/

namespace Arxiv2410V3

/-- Elementary complex Cauchy inequality used in the uniqueness proof.  For `r ≥ 0`,
`|w₁w₂+r|² ≤ (|w₁|²+r)(|w₂|²+r)`. -/
theorem normSq_mul_add_nonneg_le
    (w1 w2 : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    Complex.normSq (w1 * w2 + (r : ℂ)) ≤
      (Complex.normSq w1 + r) * (Complex.normSq w2 + r) := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
  nlinarith [mul_nonneg hr
    (add_nonneg (sq_nonneg (w1.re - w2.re)) (sq_nonneg (w1.im + w2.im)))]

/-- Strict imaginary-part contraction furnished by each upper-half-plane solution of
the scalar form of v3 (3.2)--(3.4). -/
theorem scalarDyson_strict_contraction
    {z eta m : ℂ}
    (heta : 0 < eta.im) (hm : 0 < m.im)
    (hdyson : ScalarDysonEquation z eta m) :
    Complex.normSq m *
        (Complex.normSq (eta + m) + Complex.normSq z) <
      Complex.normSq (eta + m) := by
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
  have hw_sq_pos : 0 < Complex.normSq (eta + m) :=
    Complex.normSq_pos.mpr hw_ne
  have hz_sq_nonneg : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
  have him := scalarDyson_imaginary_identity hdyson
  have hcleared :
      m.im * Complex.normSq (eta + m) =
        Complex.normSq m * (eta.im + m.im) *
          (Complex.normSq (eta + m) + Complex.normSq z) := by
    field_simp [hm_sq_pos.ne', hw_sq_pos.ne'] at him
    nlinarith only [him]
  have hfactor_pos :
      0 < Complex.normSq m *
        (Complex.normSq (eta + m) + Complex.normSq z) :=
    mul_pos hm_sq_pos (add_pos_of_pos_of_nonneg hw_sq_pos hz_sq_nonneg)
  by_contra hnot
  have hreverse :
      Complex.normSq (eta + m) ≤
        Complex.normSq m *
          (Complex.normSq (eta + m) + Complex.normSq z) :=
    le_of_not_gt hnot
  have hleft :
      Complex.normSq (eta + m) * m.im ≤
        (Complex.normSq m *
          (Complex.normSq (eta + m) + Complex.normSq z)) * m.im :=
    mul_le_mul_of_nonneg_right hreverse hm.le
  have hright :
      (Complex.normSq m *
          (Complex.normSq (eta + m) + Complex.normSq z)) * m.im <
        (Complex.normSq m *
          (Complex.normSq (eta + m) + Complex.normSq z)) *
            (eta.im + m.im) :=
    mul_lt_mul_of_pos_left (by linarith) hfactor_pos
  have hcontra :
      Complex.normSq (eta + m) * m.im <
        m.im * Complex.normSq (eta + m) := by
    calc
      Complex.normSq (eta + m) * m.im ≤
          (Complex.normSq m *
            (Complex.normSq (eta + m) + Complex.normSq z)) * m.im := hleft
      _ < (Complex.normSq m *
            (Complex.normSq (eta + m) + Complex.normSq z)) *
              (eta.im + m.im) := hright
      _ = m.im * Complex.normSq (eta + m) := by
        rw [hcleared]
        ring
  nlinarith

/-- Upper-half-plane uniqueness for the scalar Dyson equation extracted from v3
(3.2)--(3.4). -/
theorem scalarDysonEquation_unique
    {z eta m1 m2 : ℂ}
    (heta : 0 < eta.im)
    (hm1 : 0 < m1.im) (hm2 : 0 < m2.im)
    (hdyson1 : ScalarDysonEquation z eta m1)
    (hdyson2 : ScalarDysonEquation z eta m2) :
    m1 = m2 := by
  by_contra hne
  have hm1_ne : m1 ≠ 0 := by
    intro h
    subst m1
    norm_num at hm1
  have hm2_ne : m2 ≠ 0 := by
    intro h
    subst m2
    norm_num at hm2
  have hw1_ne : eta + m1 ≠ 0 := by
    intro h
    have him : (eta + m1).im = 0 := congrArg Complex.im h
    simp only [Complex.add_im] at him
    linarith
  have hw2_ne : eta + m2 ≠ 0 := by
    intro h
    have him : (eta + m2).im = 0 := congrArg Complex.im h
    simp only [Complex.add_im] at him
    linarith
  have hdiff :
      (eta + m1) * (eta + m2) =
        m1 * m2 *
          ((eta + m1) * (eta + m2) + (Complex.normSq z : ℂ)) := by
    have hsub :
        m1⁻¹ - m2⁻¹ =
          -(m1 - m2) + (Complex.normSq z : ℂ) *
            ((eta + m1)⁻¹ - (eta + m2)⁻¹) := by
      rw [hdyson1, hdyson2]
      ring
    rw [inv_sub_inv hm1_ne hm2_ne,
      inv_sub_inv hw1_ne hw2_ne] at hsub
    field_simp [hm1_ne, hm2_ne, hw1_ne, hw2_ne] at hsub
    have hd_ne : m2 - m1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    apply mul_left_cancel₀ hd_ne
    linear_combination hsub
  have hnorm := congrArg Complex.normSq hdiff
  simp only [Complex.normSq_mul] at hnorm
  have hgeom := normSq_mul_add_nonneg_le
    (eta + m1) (eta + m2) (Complex.normSq_nonneg z)
  have hc1 := scalarDyson_strict_contraction heta hm1 hdyson1
  have hc2 := scalarDyson_strict_contraction heta hm2 hdyson2
  have hw1_sq_pos : 0 < Complex.normSq (eta + m1) :=
    Complex.normSq_pos.mpr hw1_ne
  have hw2_sq_pos : 0 < Complex.normSq (eta + m2) :=
    Complex.normSq_pos.mpr hw2_ne
  have hm1_sq_pos : 0 < Complex.normSq m1 :=
    Complex.normSq_pos.mpr hm1_ne
  have hm2_sq_pos : 0 < Complex.normSq m2 :=
    Complex.normSq_pos.mpr hm2_ne
  have hz_sq_nonneg : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
  have hfactor2_pos :
      0 < Complex.normSq m2 *
        (Complex.normSq (eta + m2) + Complex.normSq z) :=
    mul_pos hm2_sq_pos (add_pos_of_pos_of_nonneg hw2_sq_pos hz_sq_nonneg)
  have hcprod :
      Complex.normSq m1 * Complex.normSq m2 *
          ((Complex.normSq (eta + m1) + Complex.normSq z) *
            (Complex.normSq (eta + m2) + Complex.normSq z)) <
        Complex.normSq (eta + m1) * Complex.normSq (eta + m2) := by
    calc
      Complex.normSq m1 * Complex.normSq m2 *
            ((Complex.normSq (eta + m1) + Complex.normSq z) *
              (Complex.normSq (eta + m2) + Complex.normSq z)) =
          (Complex.normSq m1 *
              (Complex.normSq (eta + m1) + Complex.normSq z)) *
            (Complex.normSq m2 *
              (Complex.normSq (eta + m2) + Complex.normSq z)) := by ring
      _ < Complex.normSq (eta + m1) *
            (Complex.normSq m2 *
              (Complex.normSq (eta + m2) + Complex.normSq z)) :=
        mul_lt_mul_of_pos_right hc1 hfactor2_pos
      _ < Complex.normSq (eta + m1) * Complex.normSq (eta + m2) :=
        mul_lt_mul_of_pos_left hc2 hw1_sq_pos
  have hgeom_scaled :
      Complex.normSq m1 * Complex.normSq m2 *
          Complex.normSq
            ((eta + m1) * (eta + m2) + (Complex.normSq z : ℂ)) ≤
        Complex.normSq m1 * Complex.normSq m2 *
          ((Complex.normSq (eta + m1) + Complex.normSq z) *
            (Complex.normSq (eta + m2) + Complex.normSq z)) :=
    mul_le_mul_of_nonneg_left hgeom
      (mul_nonneg hm1_sq_pos.le hm2_sq_pos.le)
  have hcontra :
      Complex.normSq (eta + m1) * Complex.normSq (eta + m2) <
        Complex.normSq (eta + m1) * Complex.normSq (eta + m2) := by
    calc
      Complex.normSq (eta + m1) * Complex.normSq (eta + m2) =
          Complex.normSq m1 * Complex.normSq m2 *
            Complex.normSq
              ((eta + m1) * (eta + m2) + (Complex.normSq z : ℂ)) := hnorm
      _ ≤ Complex.normSq m1 * Complex.normSq m2 *
          ((Complex.normSq (eta + m1) + Complex.normSq z) *
            (Complex.normSq (eta + m2) + Complex.normSq z)) := hgeom_scaled
      _ < Complex.normSq (eta + m1) * Complex.normSq (eta + m2) := hcprod
  exact (lt_irrefl _ hcontra)

/-- Every upper-half-plane solution is the canonical internally constructed free Dyson
Stieltjes transform. -/
theorem eq_freeDysonStieltjes_of_scalarDysonEquation
    {z eta m : ℂ}
    (heta : 0 < eta.im) (hm : 0 < m.im)
    (hdyson : ScalarDysonEquation z eta m) :
    m = freeDysonStieltjes z eta :=
  scalarDysonEquation_unique heta hm
    (freeDysonStieltjes_im_pos z eta heta) hdyson
    (freeDysonStieltjes_equation z eta heta)

end Arxiv2410V3
