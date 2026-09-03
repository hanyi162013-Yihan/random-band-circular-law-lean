/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealRawBound.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.HighBandLSV

/-! The real anisotropic entropy has the same raw bound, with an optional conservative dimension loss. -/

noncomputable section
namespace HighBandLSV.RealRawBound

def fixedEnvelope (N J r : Nat) (A W h d K : Real) : Real :=
  (5 / h) ^ (3 * J) * (1024 / h ^ 2) ^ N *
    (A * (N : Real) * W * d ^ 2) ^ (r * J) * (A * (K + 1) * J * d) ^ r

theorem fixedEnvelope_nonneg (N J r : Nat) {A W h d K : Real}
    (hA : 0 ≤ A) (hW : 0 ≤ W) (hh : 0 < h) (hd : 0 ≤ d) (hK : 0 ≤ K) :
    0 ≤ fixedEnvelope N J r A W h d K := by
  unfold fixedEnvelope
  positivity

theorem fixedEnvelope_le_raw_formula (N J r : Nat) {A W h d K : Real}
    (hA : 1024 ≤ A) (hW : 0 ≤ W) (hh : 0 < h) (hd : 0 ≤ d) (hK : 0 ≤ K) :
    fixedEnvelope N J r A W h d K ≤ (N : Real) ^ (r * J) *
      ((A / h) ^ (3 * J) * A ^ N / h ^ (2 * N) *
        (A * W * d ^ 2) ^ (r * J) * (A * (K + 1) * J * d) ^ r) := by
  have hA0 : 0 ≤ A := by linarith
  have hA5 : 5 ≤ A := by linarith
  have hn : (A / h ^ 2) ^ N = A ^ N / h ^ (2 * N) := by
    rw [div_pow, ← pow_mul]
  have hr : (A * (N : Real) * W * d ^ 2) ^ (r * J) =
      (N : Real) ^ (r * J) * (A * W * d ^ 2) ^ (r * J) := by
    rw [show A * (N : Real) * W * d ^ 2 = (N : Real) * (A * W * d ^ 2) from by ring, mul_pow]
  calc
    fixedEnvelope N J r A W h d K ≤
        (A / h) ^ (3 * J) * (A / h ^ 2) ^ N *
          (A * (N : Real) * W * d ^ 2) ^ (r * J) * (A * (K + 1) * J * d) ^ r := by
      unfold fixedEnvelope
      gcongr
    _ = _ := by rw [hn, hr]; ring

theorem actual_fixedEnvelope_le_raw (N J r : Nat) {A W kappa C1 K : Real}
    (hA : 1024 ≤ A) (hW : 0 ≤ W) (hK : 0 ≤ K)
    (hh : 0 < mesh N W kappa J C1 K) :
    fixedEnvelope N J r A W (mesh N W kappa J C1 K) (delta N W kappa) K ≤
      (N : Real) ^ (r * J) * rawFixedBound N J r W kappa A C1 K := by
  simpa only [rawFixedBound] using fixedEnvelope_le_raw_formula N J r hA hW hh
    (delta_pos N W kappa).le hK

end HighBandLSV.RealRawBound

#print axioms HighBandLSV.RealRawBound.actual_fixedEnvelope_le_raw

