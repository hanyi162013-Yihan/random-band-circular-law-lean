import ShortRingAnchor.HighBandLSVProbability
import Vendor.RealModelTheorem

/-!
# Reindex the copied real-density Theorem 3.1

The upstream real finite geometric Brascamp--Lieb premise stays explicit.
It is neither asserted here nor replaced by a Lean axiom.
-/

open Filter Set MeasureTheory ProbabilityTheory HighBandLSV LivshytsProjectionFormalization
open scoped Topology ENNReal
noncomputable section
namespace ShortRingAnchor

/-- Theorem 3.1, real branch: call the copied finite-dimensional theorem
with the exact certificates, retaining its explicit geometric BL premise. -/
theorem real_lsv_of_highBandNumericalCertificates
    {N W : ℕ} {c C rho kappa R Kz A : ℝ} (m : RealBandModel N W c C rho)
    (hGBL : RealFiniteGeometricBrascampLieb)
    (num : HighBandNumericalCertificates N W kappa R Kz A 64)
    (hc : 0 < c) (hrho : 0 < rho) (hA : 1024 ≤ A)
    (hAone : 2 * (Real.exp 1 * rho) / Real.sqrt c ≤ A)
    (hAtwo : 8 * (Real.exp 1 * rho ^ 2) / c ≤ A)
    (z : ℂ) (hz : ‖z‖ ≤ Kz) (t : ℝ) (ht : 0 ≤ t) :
    m.law (leastSingularBadEvent (fun sample => shifted (m.matrix sample) z)
      (HighBandLSV.tau N W kappa t) ∩ hsEvent m.matrix R) ≤
      ENNReal.ofReal ((2 * Real.sqrt 2 * Real.exp 1 * rho / Real.sqrt c) * t) +
        ENNReal.ofReal (Real.exp (-(N : ℝ) ^ (1 + kappa / 4))) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt num.2.1.N_pos)
  exact real_model_lsv_of_numerics m hGBL num.1 num.2.1 num.2.2.1 num.2.2.2
    hc hrho hA hAone hAtwo (by norm_num) (by norm_num; linarith) z hz t ht

/-- Theorem 3.1: the proved real conclusion along arbitrary growing dimensions,
with the same sole external analytic premise as the published Lean project. -/
theorem eventually_real_lsv_along_dimensions
    {M W : ℕ → ℕ} {c C rho chi kappa R Kz : ℝ}
    (m : ∀ k, RealBandModel (M k) (W k) c C rho)
    (hGBL : RealFiniteGeometricBrascampLieb)
    (hM : Tendsto M atTop atTop) (hc : 0 < c) (hrho : 0 < rho)
    (hchi : 0 < chi) (hchi1 : chi ≤ 1 / 2) (hk : 0 < kappa)
    (hR : 0 ≤ R) (hKz : 0 ≤ Kz)
    (hWp : ∀ᶠ k in atTop, 0 < W k)
    (hband : ∀ᶠ k in atTop, (M k : ℝ) ^ (1 / 2 + chi) ≤ W k)
    (hupper : ∀ᶠ k in atTop, (W k : ℝ) ≤ M k) :
    ∀ᶠ k in atTop, ∀ z : ℂ, ‖z‖ ≤ Kz → ∀ t : ℝ, 0 ≤ t →
      (m k).law (leastSingularBadEvent (fun sample => shifted ((m k).matrix sample) z)
        (HighBandLSV.tau (M k) (W k) kappa t) ∩ hsEvent (m k).matrix R) ≤
        ENNReal.ofReal ((2 * Real.sqrt 2 * Real.exp 1 * rho / Real.sqrt c) * t) +
          ENNReal.ofReal (Real.exp (-(M k : ℝ) ^ (1 + kappa / 4))) := by
  let A := 1024 + 2 * (Real.exp 1 * rho) / Real.sqrt c + 8 * (Real.exp 1 * rho ^ 2) / c
  have hone : 0 ≤ 2 * (Real.exp 1 * rho) / Real.sqrt c := by positivity
  have htwo : 0 ≤ 8 * (Real.exp 1 * rho ^ 2) / c := by positivity
  have hA : 1024 ≤ A := by dsimp [A]; linarith
  filter_upwards [eventually_highBandNumerics_along_dimensions hM hchi hchi1 hk hR hKz
    (show 0 < A by linarith) (by norm_num : (0 : ℝ) < 64) hWp hband hupper] with k hn
  intro z hz t ht
  exact real_lsv_of_highBandNumericalCertificates (m k) hGBL hn hc hrho hA
    (by dsimp [A]; linarith) (by dsimp [A]; linarith) z hz t ht

end ShortRingAnchor
