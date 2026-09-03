import CircularLawSection6.CanonicalCoreBand

/-! # A concrete polynomial mesoscopic scale

The squared band width gives a valid block size and vanishing H/m0 error
whenever the band width diverges. Every requested comparison dimension is
at most twice a quadratic polynomial in H, as required by a local
polynomial-bandwidth comparison rather than a global N-dependent one.
-/

open Filter Topology

namespace CircularLawSection6

def quadraticBlockScale (H : ℕ) : ℕ := (2 * H + 1) ^ 2

theorem quadraticBlockScale_fits (H : ℕ) : 2 * H + 1 ≤ quadraticBlockScale H := by
  unfold quadraticBlockScale
  nlinarith

theorem quadraticBlockScale_ratio_le (H : ℕ) :
    (H : ℝ) / quadraticBlockScale H ≤ 1 / ((H : ℝ) + 1) := by
  simp only [quadraticBlockScale, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  nlinarith

theorem quadraticBlockScale_ratio_tendsto (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) :
    Tendsto (fun n => (H n : ℝ) / quadraticBlockScale (H n)) atTop (𝓝 0) := by
  have hHr : Tendsto (fun n => (H n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => le_add_of_nonneg_right zero_le_one)
      (tendsto_natCast_atTop_atTop.comp hH)
  exact squeeze_zero (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun n => quadraticBlockScale_ratio_le (H n)) (hHr.const_div_atTop 1)

theorem quadraticBlockScale_window_bound {H M : ℕ} (hM : M ≤ 2 * quadraticBlockScale H) :
    M ≤ 8 * H ^ 2 + 8 * H + 2 := by
  unfold quadraticBlockScale at hM
  nlinarith

end CircularLawSection6
