import ShortRingAnchor.CyclicVarianceProfile
import ShortRingAnchor.LocalBulkPolynomialScales

/-!
# Lemma 3.5: polynomial bandwidths from the manuscript model

The fixed profile constant is absorbed by reducing the exponent from beta
to beta/2. This supplies the eventual v3 scale without a new hypothesis.
-/

noncomputable section
namespace ShortRingAnchor
open Filter
open scoped Topology

/-- Manuscript (3.1), (3.7): `W >= M^beta` implies exact bandwidth eventually
at least `M^(beta/2)`, despite the fixed profile constant `C0`. -/
theorem eventually_cyclic_bandwidth_ge_half_power
    {M W : ℕ → ℕ} {c0 C0 beta : ℝ}
    (weights : ∀ n, AdmissibleWeights (W n) c0 C0)
    (hM : Tendsto M atTop atTop) (hbeta : 0 < beta)
    (hband : ∀ n, (M n : ℝ) ^ beta ≤ (W n : ℝ)) :
    ∀ᶠ n in atTop, (M n : ℝ) ^ (beta / 2) ≤ (weights n).bandwidthParameter := by
  have hpow : Tendsto (fun n => (M n : ℝ) ^ (beta / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < beta / 2)).comp
      (tendsto_natCast_atTop_atTop.comp hM)
  filter_upwards [hpow.eventually (eventually_ge_atTop C0),
    hM.eventually (eventually_ge_atTop (1 : ℕ))] with n hn hn1
  have hN : (0 : ℝ) < M n := by exact_mod_cast (show 0 < M n by omega)
  have hC : 0 < C0 := (weights n).C0_pos
  calc
    (M n : ℝ) ^ (beta / 2) ≤ (M n : ℝ) ^ beta / C0 := by
      apply (le_div_iff₀ hC).mpr
      calc
        _ ≤ (M n : ℝ) ^ (beta / 2) * (M n : ℝ) ^ (beta / 2) :=
          mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hN.le _)
        _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring
    _ ≤ (W n : ℝ) / C0 := div_le_div_of_nonneg_right (hband n) hC.le
    _ ≤ _ := (weights n).bandwidthParameter_linear_lower

/-- Lemma 3.5 dense scale: `M^(beta/2) <= M` when `beta <= 2` and `M >= 1`. -/
theorem dense_bandwidth_ge_half_power {M : ℕ} (hM : 0 < M)
    {beta : ℝ} (hbeta : beta ≤ 2) : (M : ℝ) ^ (beta / 2) ≤ M := by
  have hN : (1 : ℝ) ≤ M := by exact_mod_cast hM
  calc
    _ ≤ (M : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    _ = _ := Real.rpow_one _

/-- Lemma 3.5: the common explicit CDF exponent for the manuscript bandwidth regime. -/
theorem localBulkRateExponent_half_eq {beta : ℝ} (hbeta : beta ≤ 2) :
    localBulkRateExponent (beta / 2) = beta / 128 := by
  unfold localBulkRateExponent localBulkEffectiveExponent
  rw [min_eq_left (by linarith : beta / 2 ≤ 1)]
  ring

end ShortRingAnchor
