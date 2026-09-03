/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/Section5Formalization/ExponentLedger.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Section5Formalization.DeterministicCompletion

namespace Section5Formalization

/-! # Explicit exponent calculations for corrected Section 5 -/

/-- The manuscript's quantity `D = N^κ N/W`. -/
noncomputable def section5Scale (N W κ : ℝ) : ℝ :=
  N ^ κ * (N / W)

/-- The leading small-ball gain is exactly `N^(1+κ)`. -/
theorem bandwidth_gain_identity {N W κ : ℝ} (hN : 0 < N) (hW : 0 < W) :
    W * section5Scale N W κ = N ^ (1 + κ) := by
  unfold section5Scale
  calc
    W * (N ^ κ * (N / W)) = N ^ κ * N := by
      field_simp [hW.ne']
      <;> ring
    _ = N ^ (1 + κ) := by
      rw [Real.rpow_add hN, Real.rpow_one]
      ring

/-- Substitution of `L ≤ C₀N/W` into the block-entropy term `LD`. -/
theorem block_count_scale_bound {N W κ L C₀ : ℝ}
    (hN : 0 ≤ N) (hW : 0 < W) (hC₀ : 0 ≤ C₀)
    (hL : L ≤ C₀ * N / W) :
    L * section5Scale N W κ ≤ C₀ * N ^ κ * N ^ 2 / W ^ 2 := by
  have hscale : 0 ≤ section5Scale N W κ := by
    unfold section5Scale
    positivity
  calc
    L * section5Scale N W κ ≤ (C₀ * N / W) * section5Scale N W κ :=
      mul_le_mul_of_nonneg_right hL hscale
    _ = C₀ * N ^ κ * N ^ 2 / W ^ 2 := by
      unfold section5Scale
      field_simp [hW.ne']
      <;> ring

/-- Squaring the bandwidth hypothesis gives the exponent used in the ledger. -/
theorem bandwidth_square_lower {N W c : ℝ} (hN : 0 < N) (hW : 0 ≤ W)
    (hband : N ^ (1 / 2 + c) ≤ W) :
    N ^ (1 + 2 * c) ≤ W ^ 2 := by
  have hsquare :=
    (sq_le_sq₀ (Real.rpow_nonneg hN.le _) hW).2 hband
  calc
    N ^ (1 + 2 * c) = N ^ ((1 / 2 + c) * (2 : ℝ)) := by
      congr 1
      ring
    _ = (N ^ (1 / 2 + c)) ^ (2 : ℕ) := by
      simpa using Real.rpow_mul_natCast hN.le (1 / 2 + c) 2
    _ ≤ W ^ 2 := hsquare

/-- The bandwidth hypothesis turns the raw `W⁻²` bound into `N⁻²c`. -/
theorem bandwidth_suppresses_block_entropy {N W κ c C₀ : ℝ}
    (hN : 0 < N) (hW : 0 < W) (hC₀ : 0 ≤ C₀)
    (hband : N ^ (1 / 2 + c) ≤ W) :
    C₀ * N ^ κ * N ^ 2 / W ^ 2 ≤ C₀ * N ^ (1 + κ - 2 * c) := by
  have hWsq : N ^ (1 + 2 * c) ≤ W ^ 2 :=
    bandwidth_square_lower hN hW.le hband
  have hnum : 0 ≤ C₀ * N ^ κ * N ^ 2 := by positivity
  have hden : 0 < N ^ (1 + 2 * c) := Real.rpow_pos_of_pos hN _
  have hpowtwo : N ^ κ * N ^ 2 = N ^ (κ + 2) := by
    simpa using (Real.rpow_add hN κ 2).symm
  calc
    C₀ * N ^ κ * N ^ 2 / W ^ 2 ≤
        C₀ * N ^ κ * N ^ 2 / N ^ (1 + 2 * c) :=
      div_le_div_of_nonneg_left hnum hden hWsq
    _ = C₀ * ((N ^ κ * N ^ 2) / N ^ (1 + 2 * c)) := by ring
    _ = C₀ * (N ^ (κ + 2) / N ^ (1 + 2 * c)) := by
      rw [hpowtwo]
    _ = C₀ * N ^ (κ + 2 - (1 + 2 * c)) := by
      rw [Real.rpow_sub hN]
    _ = C₀ * N ^ (1 + κ - 2 * c) := by
      congr 2
      ring

/-- An explicit threshold which makes the lower-order block power cost one quarter of the gain. -/
theorem block_power_small_of_threshold {N κ c C C₀ cmain : ℝ}
    (hN : 0 < N) (hthreshold : 4 * C * C₀ ≤ cmain * N ^ (2 * c)) :
    4 * C * (C₀ * N ^ (1 + κ - 2 * c)) ≤ cmain * N ^ (1 + κ) := by
  have hp : 0 ≤ N ^ (1 + κ - 2 * c) := Real.rpow_nonneg hN.le _
  calc
    4 * C * (C₀ * N ^ (1 + κ - 2 * c)) =
        (4 * C * C₀) * N ^ (1 + κ - 2 * c) := by ring
    _ ≤ (cmain * N ^ (2 * c)) * N ^ (1 + κ - 2 * c) :=
      mul_le_mul_of_nonneg_right hthreshold hp
    _ = cmain * N ^ (2 * c + (1 + κ - 2 * c)) := by
      rw [Real.rpow_add hN]
      ring
    _ = cmain * N ^ (1 + κ) := by
      congr 2
      ring

/--
An explicit threshold for `N log N = o(N^(1+κ))`.  The hypothesis on
`N^(κ/2)` is a concrete sufficient-large-`N` condition.
-/
theorem logarithmic_entropy_small_of_threshold {N κ C cmain : ℝ}
    (hN : 0 < N) (hκ : 0 < κ) (hC : 0 ≤ C)
    (hthreshold : 4 * C / (κ / 2) ≤ cmain * N ^ (κ / 2)) :
    4 * C * (N * Real.log N) ≤ cmain * N ^ (1 + κ) := by
  have he : 0 < κ / 2 := by positivity
  have hlog : Real.log N ≤ N ^ (κ / 2) / (κ / 2) :=
    Real.log_le_rpow_div hN.le he
  have hcoeff : 0 ≤ 4 * C * N := by positivity
  have hpowdouble : N ^ (κ / 2) * N ^ (κ / 2) = N ^ κ := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have hpowsucc : N * N ^ κ = N ^ (1 + κ) := by
    rw [Real.rpow_add hN, Real.rpow_one]
  calc
    4 * C * (N * Real.log N) ≤ 4 * C * (N * (N ^ (κ / 2) / (κ / 2))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlog hN.le) (mul_nonneg (by positivity) hC)
    _ = N * (4 * C / (κ / 2)) * N ^ (κ / 2) := by ring
    _ ≤ N * (cmain * N ^ (κ / 2)) * N ^ (κ / 2) := by
      gcongr
    _ = cmain * (N * (N ^ (κ / 2) * N ^ (κ / 2))) := by ring
    _ = cmain * (N * N ^ κ) := by rw [hpowdouble]
    _ = cmain * N ^ (1 + κ) := by rw [hpowsucc]

/-- The corrected entropy ledger with explicit one-quarter allocations. -/
theorem corrected_section5_entropy_bound {N W κ L C cmain : ℝ}
    (hN : 0 < N) (hW : 0 < W) (hcmain : 0 ≤ cmain)
    (hlog : 4 * C * (N * Real.log N) ≤ cmain * N ^ (1 + κ))
    (hblock : 4 * C * (L * section5Scale N W κ) ≤ cmain * N ^ (1 + κ)) :
    -(cmain * W * section5Scale N W κ) +
        C * (N * Real.log N + L * section5Scale N W κ) ≤
      -(cmain / 4 * N ^ (1 + κ)) := by
  have hgain : cmain * W * section5Scale N W κ = cmain * N ^ (1 + κ) := by
    calc
      cmain * W * section5Scale N W κ =
          cmain * (W * section5Scale N W κ) := by ring
      _ = cmain * N ^ (1 + κ) := by rw [bandwidth_gain_identity hN hW]
  rw [hgain]
  have hmain : 0 ≤ cmain * N ^ (1 + κ) :=
    mul_nonneg hcmain (Real.rpow_nonneg hN.le _)
  nlinarith

/-- The exponent gap occurring in `t/δ` in the final column argument. -/
noncomputable def finalExponentGap (N W κ : ℝ) : ℝ :=
  (N ^ (3 * κ) - N ^ κ) * (N / W)

noncomputable def normalDelta (N W κ : ℝ) : ℝ :=
  Real.exp (-section5Scale N W κ)

noncomputable def leastSingularThreshold (N W κ ε : ℝ) : ℝ :=
  ε * Real.exp (-(N ^ (3 * κ) * (N / W)))

/-- Exact cancellation of the two exponential scales in `t/δ`. -/
theorem threshold_div_delta {N W κ ε : ℝ} :
    leastSingularThreshold N W κ ε / normalDelta N W κ =
      ε * Real.exp (-finalExponentGap N W κ) := by
  unfold leastSingularThreshold normalDelta section5Scale finalExponentGap
  rw [mul_div_assoc, ← Real.exp_sub]
  congr 2
  ring

/-- A logarithmic domination hypothesis absorbs any positive prefactor into the exponent. -/
theorem exponential_prefactor_absorption {P ε gap : ℝ}
    (hP : 0 < P) (hε : 0 ≤ ε) (hlog : Real.log P ≤ gap) :
    P * (ε * Real.exp (-gap)) ≤ ε := by
  have hfactor : P * Real.exp (-gap) ≤ 1 := by
    calc
      P * Real.exp (-gap) = Real.exp (Real.log P) * Real.exp (-gap) := by
        rw [Real.exp_log hP]
      _ = Real.exp (Real.log P + -gap) := (Real.exp_add _ _).symm
      _ = Real.exp (Real.log P - gap) := by ring_nf
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (sub_nonpos.mpr hlog)
      _ = 1 := Real.exp_zero
  calc
    P * (ε * Real.exp (-gap)) = ε * (P * Real.exp (-gap)) := by ring
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hfactor hε
    _ = ε := mul_one ε

/-- Final deterministic prefactor estimate after substituting the manuscript's `t` and `δ`. -/
theorem final_lsv_prefactor_bound {N W κ ε P : ℝ}
    (hP : 0 < P) (hε : 0 ≤ ε)
    (hlog : Real.log P ≤ finalExponentGap N W κ) :
    P * (leastSingularThreshold N W κ ε / normalDelta N W κ) ≤ ε := by
  rw [threshold_div_delta]
  exact exponential_prefactor_absorption hP hε hlog

/--
The small-block/large-block ratio from the corrected mesh choice.  This is the
exact algebra behind `zeta_k / zeta_l <= C_K L delta`; the displayed constant
is `C * C1 * (K + 1) / c`.
-/
theorem zeta_ratio_from_corrected_scales
    {L delta h zetaSmall zetaLarge C C1 K c : ℝ}
    (hL : 0 < L) (hdelta : 0 ≤ delta) (hC : 0 ≤ C)
    (hC1 : 0 < C1) (hK : 0 < K + 1) (hc : 0 < c)
    (hzetaLarge : 0 < zetaLarge)
    (hmesh : h = delta / (C1 * (K + 1) * Real.sqrt L))
    (hsmall : zetaSmall ≤ C * delta ^ 2)
    (hlarge : c * h / Real.sqrt L ≤ zetaLarge) :
    zetaSmall / zetaLarge ≤
      (C * C1 * (K + 1) / c) * L * delta := by
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hcoefficient : 0 ≤ (C * C1 * (K + 1) / c) * L * delta := by
    positivity
  apply (div_le_iff₀ hzetaLarge).2
  calc
    zetaSmall ≤ C * delta ^ 2 := hsmall
    _ = ((C * C1 * (K + 1) / c) * L * delta) *
        (c * h / Real.sqrt L) := by
      rw [hmesh]
      field_simp [hc.ne', hC1.ne', hK.ne', hsqrt.ne']
      rw [Real.sq_sqrt hL.le]
    _ ≤ ((C * C1 * (K + 1) / c) * L * delta) * zetaLarge :=
      mul_le_mul_of_nonneg_left hlarge hcoefficient

end Section5Formalization

