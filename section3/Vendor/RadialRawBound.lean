/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RadialRawBound.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RadialLedger

/-! Comparison of the concrete radial-net bound with Appendix B's raw envelope. -/

noncomputable section

namespace HighBandLSV.RadialRawBound

def fixedEnvelope (N J r : Nat) (A W h delta : Real) : Real :=
  (3 / h) ^ J * (25 / h ^ 2) ^ N * (A * (N : Real) * W * delta ^ 2) ^ (r * J) *
    (4 * (J : Real) * delta ^ 2) ^ r

theorem fixedEnvelope_nonneg (N J r : Nat) {A W h delta : Real}
    (hA : 0 ≤ A) (hW : 0 ≤ W) (hh : 0 < h) :
    0 ≤ fixedEnvelope N J r A W h delta := by
  unfold fixedEnvelope
  positivity

theorem parameter_entropy_bound (J : Nat) {A h : Real}
    (hA : 3 ≤ A) (hh : 0 < h) (hh1 : h ≤ 1) :
    (3 / h) ^ J ≤ (A / h) ^ (3 * J) := by
  have hratio : 1 ≤ A / h := (le_div_iff₀ hh).2 (by linarith)
  calc
    (3 / h) ^ J ≤ (A / h) ^ J := by
      exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hA hh.le) J
    _ ≤ (A / h) ^ (3 * J) := pow_le_pow_right₀ hratio (by omega)

theorem fixedEnvelope_le_raw_formula (N J r : Nat) {A W h delta K : Real}
    (hA : 25 ≤ A) (hW : 0 ≤ W) (hh : 0 < h) (hh1 : h ≤ 1)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 1) (hK : 0 ≤ K) :
    fixedEnvelope N J r A W h delta ≤
      (N : Real) ^ (r * J) *
        ((A / h) ^ (3 * J) * A ^ N / h ^ (2 * N) *
          (A * W * delta ^ 2) ^ (r * J) * (A * (K + 1) * J * delta) ^ r) := by
  have hA0 : 0 ≤ A := by linarith
  have hlabel := parameter_entropy_bound J (by linarith : 3 ≤ A) hh hh1
  have hnet : (25 / h ^ 2) ^ N ≤ A ^ N / h ^ (2 * N) := by
    calc
      (25 / h ^ 2) ^ N ≤ (A / h ^ 2) ^ N := by gcongr
      _ = A ^ N / h ^ (2 * N) := by rw [div_pow, ← pow_mul]
  have hend : (4 * (J : Real) * delta ^ 2) ^ r ≤ (A * (K + 1) * J * delta) ^ r :=
    pow_le_pow_left₀ (by positivity)
      (RadialLedger.endpoint_factor_le (by linarith : 4 ≤ A) hK hd hd1) r
  have hnoise : (A * (N : Real) * W * delta ^ 2) ^ (r * J) =
      (N : Real) ^ (r * J) * (A * W * delta ^ 2) ^ (r * J) := by
    rw [show A * (N : Real) * W * delta ^ 2 = (N : Real) * (A * W * delta ^ 2) by ring,
      mul_pow]
  unfold fixedEnvelope
  rw [hnoise]
  calc
    (3 / h) ^ J * (25 / h ^ 2) ^ N *
        ((N : Real) ^ (r * J) * (A * W * delta ^ 2) ^ (r * J)) *
        (4 * (J : Real) * delta ^ 2) ^ r ≤
      (A / h) ^ (3 * J) * (A ^ N / h ^ (2 * N)) *
        ((N : Real) ^ (r * J) * (A * W * delta ^ 2) ^ (r * J)) *
        (A * (K + 1) * J * delta) ^ r := by
      gcongr
    _ = (N : Real) ^ (r * J) *
        ((A / h) ^ (3 * J) * A ^ N / h ^ (2 * N) *
          (A * W * delta ^ 2) ^ (r * J) * (A * (K + 1) * J * delta) ^ r) := by ring

theorem actual_fixedEnvelope_le_raw (N J r : Nat) {A W kappa C1 K : Real}
    (hA : 25 ≤ A) (hW : 0 ≤ W) (hK : 0 ≤ K)
    (hh : 0 < mesh N W kappa J C1 K) (hh1 : mesh N W kappa J C1 K ≤ 1)
    (hd : 0 ≤ delta N W kappa) (hd1 : delta N W kappa ≤ 1) :
    fixedEnvelope N J r A W (mesh N W kappa J C1 K) (delta N W kappa) ≤
      (N : Real) ^ (r * J) * rawFixedBound N J r W kappa A C1 K := by
  exact fixedEnvelope_le_raw_formula N J r hA hW hh hh1 hd hd1 hK

end HighBandLSV.RadialRawBound

#print axioms HighBandLSV.RadialRawBound.actual_fixedEnvelope_le_raw

