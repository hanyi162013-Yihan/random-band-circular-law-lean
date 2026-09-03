/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealSmallBallNumerics.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.QuadraticLinearization

/-! Elementary comparisons for the nondegenerate and rank-one real small-ball cases. -/

noncomputable section
namespace HighBandLSV.RealSmallBallNumerics

theorem scaled_one_bound {K s c W d a : Real}
    (hK : 0 ≤ K) (hs : 0 ≤ s) (hc : 0 < c) (hW : 0 < W) (hd : 0 < d)
    (ha : Real.sqrt (c / W) * d ≤ a) :
    K * s / a ≤ (K / Real.sqrt c) * Real.sqrt W * s / d := by
  have hq : 0 < Real.sqrt (c / W) := Real.sqrt_pos.2 (div_pos hc hW)
  have hden : 0 < Real.sqrt (c / W) * d := mul_pos hq hd
  calc
    K * s / a ≤ K * s / (Real.sqrt (c / W) * d) :=
      div_le_div_of_nonneg_left (mul_nonneg hK hs) hden ha
    _ = (K / Real.sqrt c) * Real.sqrt W * s / d := by
      rw [Real.sqrt_div hc.le]
      field_simp <;> ring

theorem two_dimensional_bound {K c W x y g d A : Real}
    (hK : 0 ≤ K) (hc : 0 < c) (hW : 0 < W) (hx : 0 < x) (hy : 0 < y)
    (hg : (c / W) * (x * y) ≤ g) (hA : K / c ≤ A) :
    K * d ^ 2 / g ≤ A * W * d ^ 2 / (x * y) := by
  calc
    K * d ^ 2 / g ≤ K * d ^ 2 / ((c / W) * (x * y)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hg
    _ = (K / c) * W * d ^ 2 / (x * y) := by field_simp <;> ring
    _ ≤ A * W * d ^ 2 / (x * y) := by gcongr

theorem rank_one_to_mesh_bound {K c W x a d h A : Real}
    (hK : 0 ≤ K) (hc : 0 < c) (hW : 1 ≤ W) (hx : 0 < x) (hh : 0 < h)
    (hhd : h ≤ d) (ha : Real.sqrt (c / W) * x ≤ a) (hA : K / Real.sqrt c ≤ A) :
    K * d / a ≤ A * W * d ^ 2 / (x * h) := by
  have hW0 : 0 < W := by linarith
  have hd : 0 < d := lt_of_lt_of_le hh hhd
  have hA0 : 0 ≤ A := (by positivity : 0 ≤ K / Real.sqrt c).trans hA
  have hsW : Real.sqrt W ≤ W := by
    have he := Real.sq_sqrt hW0.le
    nlinarith [Real.sqrt_nonneg W, sq_nonneg (W - 1)]
  calc
    K * d / a ≤ (K / Real.sqrt c) * Real.sqrt W * d / x :=
      scaled_one_bound hK hd.le hc hW0 hx ha
    _ ≤ A * W * d / x := by gcongr
    _ = (A * W * d / x) * 1 := by ring
    _ ≤ (A * W * d / x) * (d / h) :=
      mul_le_mul_of_nonneg_left ((le_div_iff₀ hh).2 (by simpa using hhd)) (by positivity)
    _ = A * W * d ^ 2 / (x * h) := by ring

theorem one_axis_energy {a b q d : Real} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq : 0 < q) (hd : 0 ≤ d) (he : q * d ^ 2 ≤ a ^ 2 + b ^ 2) :
    Real.sqrt (q / 2) * d ≤ max a b := by
  have hs : 0 ≤ Real.sqrt (q / 2) := Real.sqrt_nonneg _
  have hs2 := Real.sq_sqrt (by positivity : 0 ≤ q / 2)
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    have hsq : a ^ 2 ≤ b ^ 2 := by nlinarith
    nlinarith [mul_nonneg hs hd, sq_nonneg (Real.sqrt (q / 2) * d - b)]
  · rw [max_eq_left hba]
    have hsq : b ^ 2 ≤ a ^ 2 := by nlinarith
    nlinarith [mul_nonneg hs hd, sq_nonneg (Real.sqrt (q / 2) * d - a)]

end HighBandLSV.RealSmallBallNumerics

#print axioms HighBandLSV.RealSmallBallNumerics.rank_one_to_mesh_bound
#print axioms HighBandLSV.RealSmallBallNumerics.one_axis_energy

