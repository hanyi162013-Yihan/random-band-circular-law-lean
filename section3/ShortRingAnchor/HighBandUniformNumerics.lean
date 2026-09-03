import ShortRingAnchor.UniformSequenceSelection
import Vendor.ModelNumerics

/-!
# Reuse Theorem 3.1 along arbitrary growing dimensions

The upstream numerical theorem is quantified over `W : Nat -> Nat` with
dimension `N` itself. Uniformization over admissible widths, followed by
composition with `M -> infinity`, supplies the same certificates here.
The random-matrix argument of Theorem 3.1 is not reproved or postulated.
-/

open Filter HighBandLSV
noncomputable section
namespace ShortRingAnchor

/-- The four certificates consumed by the copied pointwise Theorem 3.1. -/
def HighBandNumericalCertificates (N W : ℕ) (kappa R Kz A C1 : ℝ) : Prop :=
  8 ≤ seedSize N W ∧
  NumericalCertificate N (blockCount N W) (retainedRows N W)
    W kappa R Kz A C1 (1 / (64 * 1)) 1 ∧
  CorrectedSection5NumericalConditions N W kappa (blockCount N W) 28 (1 / (64 * 1)) ∧
  Real.log (dimensionLossColumnPrefactor N W) ≤ Section5Formalization.finalExponentGap N W kappa

/-- Theorem 3.1 numerical preparation: uniform in every width `N^(1/2+chi) <= W <= N`. -/
theorem eventually_highBandNumerics_uniform_width
    {chi kappa R Kz A C1 : ℝ} (hchi : 0 < chi) (hchi1 : chi ≤ 1 / 2)
    (hk : 0 < kappa) (hR : 0 ≤ R) (hKz : 0 ≤ Kz) (hA : 0 < A) (hC1 : 0 < C1) :
    ∀ᶠ N : ℕ in atTop, ∀ W : ℕ, 0 < W →
      (N : ℝ) ^ (1 / 2 + chi) ≤ W → (W : ℝ) ≤ N →
      HighBandNumericalCertificates N W kappa R Kz A C1 := by
  have h := eventually_uniform_of_eventually_every_sequence
    (P := fun N W => 0 < W ∧ (N : ℝ) ^ (1 / 2 + chi) ≤ W ∧ (W : ℝ) ≤ N)
    (Q := fun N W => HighBandNumericalCertificates N W kappa R Kz A C1)
    ?_ ?_
  · filter_upwards [h] with N hn W hw hb hu
    exact hn W ⟨hw, hb, hu⟩
  · filter_upwards [eventually_ge_atTop 1] with N hn
    refine ⟨by omega, ?_, le_rfl⟩
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast hn
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hN (show 1 / 2 + chi ≤ 1 by linarith)
  · intro W hw
    exact eventually_model_numerics hchi hk hR hKz hA hC1 (by norm_num) W
      (hw.mono (fun _ h => h.1)) (hw.mono (fun _ h => h.2.1))
      (hw.mono (fun _ h => by simpa only [one_mul] using h.2.2))

/-- Theorem 3.1 numerical preparation for the manuscript's actual dimension sequence. -/
theorem eventually_highBandNumerics_along_dimensions
    {M W : ℕ → ℕ} {chi kappa R Kz A C1 : ℝ}
    (hM : Tendsto M atTop atTop) (hchi : 0 < chi) (hchi1 : chi ≤ 1 / 2)
    (hk : 0 < kappa) (hR : 0 ≤ R) (hKz : 0 ≤ Kz) (hA : 0 < A) (hC1 : 0 < C1)
    (hWp : ∀ᶠ k in atTop, 0 < W k)
    (hband : ∀ᶠ k in atTop, (M k : ℝ) ^ (1 / 2 + chi) ≤ W k)
    (hupper : ∀ᶠ k in atTop, (W k : ℝ) ≤ M k) :
    ∀ᶠ k in atTop, HighBandNumericalCertificates (M k) (W k) kappa R Kz A C1 := by
  filter_upwards [hM.eventually (eventually_highBandNumerics_uniform_width
    hchi hchi1 hk hR hKz hA hC1), hWp, hband, hupper] with k hn hw hb hu
  exact hn (W k) hw hb hu

end ShortRingAnchor
