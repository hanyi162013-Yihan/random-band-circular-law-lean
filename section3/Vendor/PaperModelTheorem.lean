/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/PaperModelTheorem.lean
   Upstream commit d20607307ee57f31d77397b34bdb2910bef30936.
   Local adaptation: import paths prefixed with Vendor. -/
import Vendor.ModelStatements

set_option autoImplicit false

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace HighBandLSV.PaperModelTheorem

/-- The bandwidth upper bound is a consequence of one normalized row. -/
theorem profile_bandwidth_upper {N W : Nat} {C : Real}
    (sigma : Fin N → Real) (hW : 0 < W)
    (hrow : ∑ j, sigma j ^ 2 = 1)
    (hupper : ∀ j, sigma j ^ 2 ≤ C / (W : Real)) :
    (W : Real) ≤ C * (N : Real) := by
  have hsum : (1 : Real) ≤ (N : Real) * (C / (W : Real)) := by
    calc
      1 = ∑ j, sigma j ^ 2 := hrow.symm
      _ ≤ ∑ _j : Fin N, C / (W : Real) :=
        Finset.sum_le_sum (fun j _ => hupper j)
      _ = (N : Real) * (C / (W : Real)) := by simp
  have hWreal : (0 : Real) < W := by exact_mod_cast hW
  have hratio : (1 : Real) ≤ ((N : Real) * C) / (W : Real) := by
    simpa only [mul_div_assoc] using hsum
  have hmul := (le_div_iff₀ hWreal).mp hratio
  simpa only [one_mul, mul_one, mul_comm] using hmul

theorem real_profile_bandwidth_upper {N W : Nat} {c C rho : Real}
    (m : RealBandModel N W c C rho) (hN : 0 < N) (hW : 0 < W) :
    (W : Real) ≤ C * (N : Real) := by
  let i : Fin N := ⟨0, hN⟩
  exact profile_bandwidth_upper (m.sigma i) hW
    (m.row_normalization i) (m.variance_upper i)

theorem planar_profile_bandwidth_upper {N W : Nat} {c C L : Real}
    (m : PlanarBandModel N W c C L) (hN : 0 < N) (hW : 0 < W) :
    (W : Real) ≤ C * (N : Real) := by
  let i : Fin N := ⟨0, hN⟩
  exact profile_bandwidth_upper (m.sigma i) hW
    (m.row_normalization i) (m.upper i)

/-- The real model statement with no independent bandwidth-upper-bound input. -/
theorem real_main_statement {c C rho chi kappa R Kz : Real}
    (hGBL : LivshytsProjectionFormalization.RealFiniteGeometricBrascampLieb)
    (hc : 0 < c) (hrho : 0 < rho) (hchi : 0 < chi) (hk : 0 < kappa)
    (hR : 0 ≤ R) (hKz : 0 ≤ Kz) (W : Nat → Nat)
    (m : ∀ N, RealBandModel N (W N) c C rho) (Nband : Nat)
    (hband : ∀ N, Nband ≤ N → (N : Real) ^ (1 / 2 + chi) ≤ (W N : Real)) :
    ∃ N0, Nband ≤ N0 ∧ ∀ N, N0 ≤ N → ∀ z : Complex, ‖z‖ ≤ Kz →
      ∀ t : Real, 0 ≤ t →
        (m N).law
          (leastSingularBadEvent (fun omega => shifted ((m N).matrix omega) z)
              (t * Real.exp (-((N : Real) ^ (3 * kappa) * ((N : Real) / (W N : Real))))) ∩
            {omega | hilbertSchmidt ((m N).matrix omega) ≤ R * Real.sqrt (N : Real)}) ≤
          ENNReal.ofReal (2 * Real.sqrt 2 * Real.exp 1 * rho / Real.sqrt c * t) +
            ENNReal.ofReal (Real.exp (-(N : Real) ^ (1 + kappa / 4))) := by
  have hNpos : ∀ N : Nat, max Nband 1 ≤ N → 0 < N := by
    intro N hN
    have := (le_max_right Nband 1).trans hN
    omega
  have hWp : ∀ N : Nat, max Nband 1 ≤ N → 0 < W N := by
    intro N hN
    have hn : (0 : Real) < N := by exact_mod_cast hNpos N hN
    have hw : (0 : Real) < W N :=
      (Real.rpow_pos_of_pos hn _).trans_le
        (hband N ((le_max_left Nband 1).trans hN))
    exact_mod_cast hw
  have hupper : ∀ N : Nat, max Nband 1 ≤ N → (W N : Real) ≤ max C 1 * N := by
    intro N hN
    exact (real_profile_bandwidth_upper (m N) (hNpos N hN) (hWp N hN)).trans
      (mul_le_mul_of_nonneg_right (le_max_left C 1) (Nat.cast_nonneg N))
  obtain ⟨N0, hN0, hmain⟩ := ModelStatements.real_main_statement
    hGBL hc hrho hchi hk hR hKz (le_max_right C 1) W m (max Nband 1) hWp
    (fun N hN => hband N ((le_max_left Nband 1).trans hN)) hupper
  exact ⟨N0, (le_max_left Nband 1).trans hN0, hmain⟩

/-- The joint-planar-density model statement, with no real/imaginary independence. -/
theorem planar_main_statement {c C L chi kappa R Kz : Real}
    (hc : 0 < c) (hL : 0 ≤ L) (hchi : 0 < chi) (hk : 0 < kappa)
    (hR : 0 ≤ R) (hKz : 0 ≤ Kz) (W : Nat → Nat)
    (m : ∀ N, PlanarBandModel N (W N) c C L) (Nband : Nat)
    (hband : ∀ N, Nband ≤ N → (N : Real) ^ (1 / 2 + chi) ≤ (W N : Real)) :
    ∃ N0, Nband ≤ N0 ∧ ∀ N, N0 ≤ N → ∀ z : Complex, ‖z‖ ≤ Kz →
      ∀ t : Real, 0 ≤ t →
        (m N).law
          (leastSingularBadEvent (fun omega => shifted ((m N).matrix omega) z)
              (t * Real.exp (-((N : Real) ^ (3 * kappa) * ((N : Real) / (W N : Real))))) ∩
            {omega | hilbertSchmidt ((m N).matrix omega) ≤ R * Real.sqrt (N : Real)}) ≤
          ENNReal.ofReal (Real.sqrt (Real.pi * L / c) * t) +
            ENNReal.ofReal (Real.exp (-(N : Real) ^ (1 + kappa / 4))) := by
  have hNpos : ∀ N : Nat, max Nband 1 ≤ N → 0 < N := by
    intro N hN
    have := (le_max_right Nband 1).trans hN
    omega
  have hWp : ∀ N : Nat, max Nband 1 ≤ N → 0 < W N := by
    intro N hN
    have hn : (0 : Real) < N := by exact_mod_cast hNpos N hN
    have hw : (0 : Real) < W N :=
      (Real.rpow_pos_of_pos hn _).trans_le
        (hband N ((le_max_left Nband 1).trans hN))
    exact_mod_cast hw
  have hupper : ∀ N : Nat, max Nband 1 ≤ N → (W N : Real) ≤ max C 1 * N := by
    intro N hN
    exact (planar_profile_bandwidth_upper (m N) (hNpos N hN) (hWp N hN)).trans
      (mul_le_mul_of_nonneg_right (le_max_left C 1) (Nat.cast_nonneg N))
  obtain ⟨N0, hN0, hmain⟩ := ModelStatements.planar_main_statement
    hc hL hchi hk hR hKz (le_max_right C 1) W m (max Nband 1) hWp
    (fun N hN => hband N ((le_max_left Nband 1).trans hN)) hupper
  exact ⟨N0, (le_max_left Nband 1).trans hN0, hmain⟩

end HighBandLSV.PaperModelTheorem

