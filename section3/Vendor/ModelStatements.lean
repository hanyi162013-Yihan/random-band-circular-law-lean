/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/ModelStatements.lean
   Upstream commit d20607307ee57f31d77397b34bdb2910bef30936.
   Local adaptation: import paths prefixed with Vendor. -/
import Vendor.RealModelTheorem
import Vendor.PlanarModelTheorem

/-! Explicit-threshold statements with a natural-number cutoff. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory LivshytsProjectionFormalization
open scoped ENNReal
namespace HighBandLSV.ModelStatements

theorem threshold_formula (N W kappa t : Real) :
    tau N W kappa t = t * Real.exp (-(N ^ (3 * kappa) * (N / W))) := by
  change t * Real.exp _ = t * Real.exp _
  congr 2 <;> ring

theorem real_main_statement
    {c C rho chi kappa R Kz Cw : Real}
    (hGBL : RealFiniteGeometricBrascampLieb) (hc : 0 < c) (hrho : 0 < rho)
    (hchi : 0 < chi) (hk : 0 < kappa) (hR : 0 ≤ R) (hKz : 0 ≤ Kz) (hCw : 1 ≤ Cw)
    (W : Nat → Nat) (m : ∀ N, RealBandModel N (W N) c C rho) (Nband : Nat)
    (hWp : ∀ N, Nband ≤ N → 0 < W N)
    (hband : ∀ N : Nat, Nband ≤ N → (N : Real) ^ (1 / 2 + chi) ≤ W N)
    (hupper : ∀ N : Nat, Nband ≤ N → (W N : Real) ≤ Cw * N) :
    ∃ N0 : Nat, Nband ≤ N0 ∧ ∀ N : Nat, N0 ≤ N → ∀ z : Complex,
      ‖z‖ ≤ Kz → ∀ t : Real, 0 ≤ t →
        (m N).law
          (leastSingularBadEvent (fun omega => shifted ((m N).matrix omega) z)
              (t * Real.exp (-((N : Real) ^ (3 * kappa) * ((N : Real) / W N)))) ∩
            {omega | hilbertSchmidt ((m N).matrix omega) ≤ R * Real.sqrt N}) ≤
          ENNReal.ofReal ((2 * Real.sqrt 2 * Real.exp 1 * rho / Real.sqrt c) * t) +
            ENNReal.ofReal (Real.exp (-(N : Real) ^ (1 + kappa / 4))) := by
  have hp : ∀ᶠ (N : Nat) in Filter.atTop, 0 < W N :=
    Filter.eventually_atTop.mpr ⟨Nband, hWp⟩
  have hb : ∀ᶠ (N : Nat) in Filter.atTop, (N : Real) ^ (1 / 2 + chi) ≤ W N :=
    Filter.eventually_atTop.mpr ⟨Nband, hband⟩
  have hu : ∀ᶠ (N : Nat) in Filter.atTop, (W N : Real) ≤ Cw * N :=
    Filter.eventually_atTop.mpr ⟨Nband, hupper⟩
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
    (eventually_real_band_lsv hGBL hc hrho hchi hk hR hKz hCw W m hp hb hu)
  refine ⟨max N0 Nband, le_max_right _ _, ?_⟩
  intro N hN z hz t ht
  simpa only [threshold_formula, hsEvent] using
    hN0 N ((le_max_left N0 Nband).trans hN) z hz t ht

theorem planar_main_statement
    {c C L chi kappa R Kz Cw : Real}
    (hc : 0 < c) (hL : 0 ≤ L) (hchi : 0 < chi) (hk : 0 < kappa)
    (hR : 0 ≤ R) (hKz : 0 ≤ Kz) (hCw : 1 ≤ Cw)
    (W : Nat → Nat) (m : ∀ N, PlanarBandModel N (W N) c C L) (Nband : Nat)
    (hWp : ∀ N, Nband ≤ N → 0 < W N)
    (hband : ∀ N : Nat, Nband ≤ N → (N : Real) ^ (1 / 2 + chi) ≤ W N)
    (hupper : ∀ N : Nat, Nband ≤ N → (W N : Real) ≤ Cw * N) :
    ∃ N0 : Nat, Nband ≤ N0 ∧ ∀ N : Nat, N0 ≤ N → ∀ z : Complex,
      ‖z‖ ≤ Kz → ∀ t : Real, 0 ≤ t →
        (m N).law
          (leastSingularBadEvent (fun omega => shifted ((m N).matrix omega) z)
              (t * Real.exp (-((N : Real) ^ (3 * kappa) * ((N : Real) / W N)))) ∩
            {omega | hilbertSchmidt ((m N).matrix omega) ≤ R * Real.sqrt N}) ≤
          ENNReal.ofReal (Real.sqrt (Real.pi * L / c) * t) +
            ENNReal.ofReal (Real.exp (-(N : Real) ^ (1 + kappa / 4))) := by
  have hp : ∀ᶠ (N : Nat) in Filter.atTop, 0 < W N :=
    Filter.eventually_atTop.mpr ⟨Nband, hWp⟩
  have hb : ∀ᶠ (N : Nat) in Filter.atTop, (N : Real) ^ (1 / 2 + chi) ≤ W N :=
    Filter.eventually_atTop.mpr ⟨Nband, hband⟩
  have hu : ∀ᶠ (N : Nat) in Filter.atTop, (W N : Real) ≤ Cw * N :=
    Filter.eventually_atTop.mpr ⟨Nband, hupper⟩
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
    (eventually_planar_band_lsv hc hL hchi hk hR hKz hCw W m hp hb hu)
  refine ⟨max N0 Nband, le_max_right _ _, ?_⟩
  intro N hN z hz t ht
  simpa only [threshold_formula, hsEvent] using
    hN0 N ((le_max_left N0 Nband).trans hN) z hz t ht

end HighBandLSV.ModelStatements

#print axioms HighBandLSV.ModelStatements.real_main_statement
#print axioms HighBandLSV.ModelStatements.planar_main_statement

