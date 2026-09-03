import CircularLawSection6.LimitingProfileMass
import CircularLawSection6.IteratedSqueeze

/-! # Fourth-root tail cutoff also removes the core normalization error

For complementary masses `v+t=1`, the normalization loss is at most `t`,
and hence at most `sqrt(t)`. Both finite-reference comparison errors are
therefore removed by the same fourth-root cutoff.
-/

open MeasureTheory Filter Topology
open CircularLawSections56.Section6

noncomputable section

namespace CircularLawSection6

theorem abs_sqrt_sub_one_le_one_sub {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    |Real.sqrt v - 1| ≤ 1 - v := by
  have hs := Real.sqrt_nonneg v
  have hs1 := Real.sqrt_le_one.mpr hv1
  have hsq := Real.sq_sqrt hv
  rw [abs_of_nonpos (sub_nonpos.mpr hs1)]
  nlinarith

theorem normalized_tail_error_le_two_fourthRoot {v t : ℝ}
    (hv : 0 ≤ v) (ht : 0 < t) (hmass : v + t = 1) :
    (Real.sqrt t + |Real.sqrt v - 1|) / fourthRoot t ≤ 2 * fourthRoot t := by
  have hv1 : v ≤ 1 := by linarith
  have ht1 : t ≤ 1 := by linarith
  have hnorm : |Real.sqrt v - 1| ≤ t := by
    have h := abs_sqrt_sub_one_le_one_sub hv hv1
    linarith
  have htsqrt : t ≤ Real.sqrt t := by
    have hs0 := Real.sqrt_nonneg t
    have hs1 := Real.sqrt_le_one.mpr ht1
    have hsq := Real.sq_sqrt ht.le
    nlinarith
  calc
    _ ≤ (2 * Real.sqrt t) / fourthRoot t :=
      div_le_div_of_nonneg_right (by linarith) (fourthRoot_nonneg t)
    _ = _ := by rw [mul_div_assoc, sqrt_div_fourthRoot ht]

namespace NoncompactProfile

def unitCoreReferenceErrorLimit (p : NoncompactProfile) (R : ℕ) : ℝ :=
  (Real.sqrt (p.limitingTailMass R) + |Real.sqrt (p.limitingCoreMass R) - 1|) /
    fourthRoot (p.limitingTailMass R)

theorem unitCoreReferenceErrorLimit_tendsto_zero (p : NoncompactProfile) :
    Tendsto p.unitCoreReferenceErrorLimit atTop (𝓝 0) := by
  have hroot : Tendsto (fun R : ℕ => fourthRoot (p.limitingTailMass R)) atTop (𝓝 0) := by
    simpa only [fourthRoot, Real.sqrt_zero] using p.limitingTailMass_integral_tendsto_zero.sqrt.sqrt
  apply squeeze_zero (fun R => div_nonneg (add_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    (fourthRoot_nonneg _))
    (fun R => normalized_tail_error_le_two_fourthRoot (p.limitingCoreMass_nonneg (Nat.cast_nonneg R))
      (p.limitingTailMass_pos R) (p.limitingCoreMass_add_limitingTailMass (Nat.cast_nonneg R)))
  simpa only [mul_zero] using hroot.const_mul 2

theorem limitingTail_fourthRoot_le_one (p : NoncompactProfile) (R : ℕ) :
    fourthRoot (p.limitingTailMass R) ≤ 1 := by
  have hv := p.limitingCoreMass_nonneg (Nat.cast_nonneg R)
  have hm := p.limitingCoreMass_add_limitingTailMass (Nat.cast_nonneg R)
  have ht : p.limitingTailMass R ≤ 1 := by linarith
  exact Real.sqrt_le_one.mpr (Real.sqrt_le_one.mpr ht)

end NoncompactProfile
end CircularLawSection6
