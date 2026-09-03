/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/QuadraticLinearization.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.PlanarSmallBall

/-! The planar quadratic column estimate implies the linear estimate used at the end. -/

namespace HighBandLSV.QuadraticLinearization

theorem min_one_square_le {x : Real} (hx : 0 ≤ x) : min 1 (x ^ 2) ≤ x := by
  by_cases hx1 : x ≤ 1
  · exact (min_le_right _ _).trans (by nlinarith)
  · exact (min_le_left _ _).trans (le_of_lt (lt_of_not_ge hx1))

theorem planar_column_linearization (N W : Nat) {c L delta s : Real}
    (hc : 0 < c) (hW : 0 < W) (hL : 0 ≤ L) (hd : 0 < delta) (hs : 0 ≤ s) :
    min 1 (Real.pi * ((N : Real) * L / ((c / (W : Real)) * delta ^ 2)) * s ^ 2) ≤
      Real.sqrt (Real.pi * L / c) * Real.sqrt (N : Real) *
        Real.sqrt (W : Real) * s / delta := by
  have hWr : 0 < (W : Real) := Nat.cast_pos.mpr hW
  have hroot : 0 ≤ Real.pi * L / c := by positivity
  have hid : (Real.sqrt (Real.pi * L / c) * Real.sqrt (N : Real) *
        Real.sqrt (W : Real) / delta) ^ 2 =
      Real.pi * ((N : Real) * L / ((c / (W : Real)) * delta ^ 2)) := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hroot,
      Real.sq_sqrt (Nat.cast_nonneg N), Real.sq_sqrt (Nat.cast_nonneg W)]
    field_simp
    <;> ring
  calc
    min 1 (Real.pi * ((N : Real) * L / ((c / (W : Real)) * delta ^ 2)) * s ^ 2) =
        min 1 ((Real.sqrt (Real.pi * L / c) * Real.sqrt (N : Real) *
          Real.sqrt (W : Real) / delta * s) ^ 2) := by rw [mul_pow, hid]
    _ ≤ Real.sqrt (Real.pi * L / c) * Real.sqrt (N : Real) *
        Real.sqrt (W : Real) / delta * s := min_one_square_le (by positivity)
    _ = Real.sqrt (Real.pi * L / c) * Real.sqrt (N : Real) *
        Real.sqrt (W : Real) * s / delta := by ring

theorem column_union_prefactor (N : Nat) (W C tau delta : Real) :
    (N : Real) * (C * Real.sqrt (N : Real) * Real.sqrt W *
      (tau * Real.sqrt (N : Real)) / delta) =
        C * dimensionLossColumnPrefactor N W * tau / delta := by
  unfold dimensionLossColumnPrefactor columnPrefactor
  ring

end HighBandLSV.QuadraticLinearization

#print axioms HighBandLSV.QuadraticLinearization.planar_column_linearization

