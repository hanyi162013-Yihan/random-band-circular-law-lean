import ShortRingAnchor.SourceScales
import ShortRingAnchor.ConcreteBulkScales

/-! # Dense-profile cutoff bookkeeping for the general Section 3 theorem

The exact spectral bandwidth need not equal the geometric width N. Its
proved lower bound N/C suffices. All cutoffs and polynomial rates below
are deterministic; no matrix limit or singular-value estimate is assumed.
-/

open Filter Topology ShortRingAnchor
noncomputable section
set_option autoImplicit false

namespace CircularLawSection6.DenseProfile

def denseChi : ℝ := 1 / 4
def denseKappa : ℝ := 1 / 256
def denseTau : ℝ := 1 / 64

theorem dense_parameters : HardEdgeAdmissible 1 denseChi denseKappa denseTau := by
  norm_num [HardEdgeAdmissible, denseChi, denseKappa, denseTau]

theorem bandwidth_cutoff_le_power {N : ℕ} {B C τ : ℝ}
    (hN : 0 < N) (hC : 0 < C) (hB : (N : ℝ) / C ≤ B) :
    B ^ (-(1 / 8 : ℝ)) * (N : ℝ) ^ τ ≤
      C ^ (1 / 8 : ℝ) * (N : ℝ) ^ (τ - 1 / 8) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp := Real.rpow_le_rpow_of_nonpos (div_pos hNr hC) hB
    (by norm_num : -(1 / 8 : ℝ) ≤ 0)
  calc
    _ ≤ ((N : ℝ) / C) ^ (-(1 / 8 : ℝ)) * (N : ℝ) ^ τ :=
      mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hNr.le _)
    _ = C ^ (1 / 8 : ℝ) * (N : ℝ) ^ (τ - 1 / 8) := by
      rw [Real.div_rpow hNr.le hC.le, Real.rpow_neg hC.le (1 / 8 : ℝ), div_inv_eq_mul]
      calc
        _ = C ^ (1 / 8 : ℝ) * ((N : ℝ) ^ (-(1 / 8 : ℝ)) * (N : ℝ) ^ τ) := by ring
        _ = _ := by
          rw [← Real.rpow_add hNr]
          congr 2
          ring

theorem bandwidth_cutoff_le_source_eventually
    (M : ℕ → ℕ) (B : ℕ → ℝ) {C : ℝ}
    (hMpos : ∀ n, 0 < M n) (hM : Tendsto M atTop atTop) (hC : 0 < C)
    (hB : ∀ n, (M n : ℝ) / C ≤ B n) :
    ∀ᶠ n in atTop, B n ^ (-(1 / 8 : ℝ)) * (M n : ℝ) ^ denseTau ≤
      sourceCutoff M (C ^ (1 / 8 : ℝ)) 1 denseTau n := by
  filter_upwards [sourceCutoff_eventually_eq_raw
    (K := C ^ (1 / 8 : ℝ)) dense_parameters hM] with n hn
  rw [hn]
  simpa only [sourceRawCutoff, sourceCutoffExponent, one_div] using
    bandwidth_cutoff_le_power (τ := denseTau) (hMpos n) hC (hB n)

theorem eventually_bandwidth_ge_half_power
    (M : ℕ → ℕ) (B : ℕ → ℝ) {C : ℝ}
    (hM : Tendsto M atTop atTop) (hC : 0 < C)
    (hB : ∀ n, (M n : ℝ) / C ≤ B n) :
    ∀ᶠ n in atTop, (M n : ℝ) ^ (1 / 2 : ℝ) ≤ B n := by
  have hp : Tendsto (fun n => (M n : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      (tendsto_natCast_atTop_atTop.comp hM)
  filter_upwards [hp.eventually_ge_atTop C, hM.eventually_ge_atTop 1] with n hn hN
  have hNr : (0 : ℝ) < M n := by exact_mod_cast (show 0 < M n by omega)
  apply le_trans _ (hB n)
  apply (le_div_iff₀ hC).2
  calc
    _ ≤ (M n : ℝ) ^ (1 / 2 : ℝ) * (M n : ℝ) ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hNr.le _)
    _ = (M n : ℝ) := by rw [← Real.rpow_add hNr]; norm_num

theorem dense_cutoff_tendsto_zero (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) (K : ℝ) :
    Tendsto (sourceCutoff M K 1 denseTau) atTop (𝓝 0) :=
  sourceCutoff_tendsto_zero dense_parameters hM

theorem dense_hardEdge_error_tendsto_zero
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) {K C : ℝ} (hK : 0 < K) (hC : 0 ≤ C) :
    Tendsto (fun n => C * sourceCutoff M K 1 denseTau n *
      sourceHardEdgeScale M M denseKappa n) atTop (𝓝 0) := by
  have hband : ∀ᶠ n in atTop, (M n : ℝ) ^ (1 : ℝ) ≤ (M n : ℝ) :=
    Eventually.of_forall fun n => by rw [Real.rpow_one]
  exact sourceHardEdgeError_tendsto_zero dense_parameters hM hband hK hC

theorem dense_bulk_cutoff_tendsto_zero
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) {K R ζ : ℝ}
    (hK : 0 < K) (hR : 0 < R) (hζ : 0 < ζ) :
    Tendsto (fun n => (M n : ℝ) ^ (-ζ) *
      (Real.log R - Real.log (sourceCutoff M K 1 denseTau n))) atTop (𝓝 0) :=
  sourceBulkCutoffBookkeeping_tendsto_zero dense_parameters hM hK hR hζ

end CircularLawSection6.DenseProfile
