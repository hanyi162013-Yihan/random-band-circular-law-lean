import BernoulliSection9.TerminalConcreteConclusion
import Mathlib.Tactic

set_option maxHeartbeats 100000

/-!
# Discharging the canonical large-width arithmetic

This file removes `PacketTerminalCanonicalLargeWConditions` from the paper-facing
input.  For a fixed subgaussian parameter bound `Ksg`, it takes the canonical
choice `t = W` and gives one explicit width threshold, depending only on
`Ksg`, `Kz`, and Cook's fixed exponent function.
-/

noncomputable section

namespace BernoulliSection9

open MeasureTheory BernoulliLinearAlgebra
open TerminalAssembly

namespace TerminalAssembly

/-- The numerical constant left in the perturbed-pivot Neumann estimate. -/
def terminalCanonicalPivotConstant : Nat := 2 ^ 17 * 3 ^ 2

/-- An explicit paper-level width threshold.  The last term absorbs the
constant `12 ^ beta` which occurs when the first Cook inverse is compared
with a square of side `W / 3`. -/
def terminalCanonicalLargeWThreshold
    (cook : CookDeformedSquareInput) (Kz : Nat) (Ksg : Real) : Nat :=
  max (2 * terminalCanonicalPivotConstant)
    (max 64
      (max (Nat.ceil Ksg)
        (3 * Nat.ceil
          ((12 : Real) ^
            cook.beta (terminalCanonicalFirstCookExponent Kz)))))

private theorem real_pow_mono_exponent
    {x : Real} (hx : 1 <= x) {a b : Nat} (hab : a <= b) :
    x ^ a <= x ^ b := by
  exact pow_le_pow_right₀ hx hab

private theorem add_le_next_power
    {x a b : Real} {N : Nat} (hx : 2 <= x)
    (ha : a <= x ^ N) (hb : b <= x ^ N) :
    a + b <= x ^ (N + 1) := by
  rw [pow_succ]
  have hp : 0 <= x ^ N := by positivity
  nlinarith

private theorem terminalConcreteExposureThreshold_le_sq
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (Ksg : Real) (hW : 64 <= W)
    (hsg : (X.subgaussianParameter : Real) <= Ksg)
    (hKsg : 0 <= Ksg) (hKsgW : Ksg <= (W : Real)) :
    terminalConcreteExposureThreshold X (W : Real) <= (W : Real) ^ 2 := by
  let w : Real := W
  let N : Nat := Fintype.card (ThreeBlockVariable (Fin W))
  have hWposNat : 0 < W := by omega
  letI : Nonempty (Fin W) := Fin.pos_iff_nonempty.mp hWposNat
  letI : Nonempty (ThreeBlockVariable (Fin W)) := threeBlockVariable_nonempty
  have hw : 64 <= w := by dsimp [w]; exact_mod_cast hW
  have hw0 : 0 <= w := by positivity
  have hw1 : 1 <= w := by linarith
  have hNposNat : 0 < N := Fintype.card_pos
  have hcard : N <= 9 * W ^ 2 := by
    calc
      N <= Fintype.card (ThreeBlockIndex (Fin W)) *
          Fintype.card (ThreeBlockIndex (Fin W)) :=
        card_threeBlockVariable_le_index_sq
      _ = 9 * W ^ 2 := by
        simp [ThreeBlockIndex]
        ring
  have hNreal : (N : Real) <= 9 * w ^ 2 := by
    dsimp [N, w]
    exact_mod_cast hcard
  have htwoNpos : 0 < (2 * (N : Real)) := by positivity
  have hlog : Real.log (2 * (N : Real)) <= 18 * w ^ 2 := by
    calc
      Real.log (2 * (N : Real)) <= 2 * (N : Real) - 1 :=
        Real.log_le_sub_one_of_pos htwoNpos
      _ <= 18 * w ^ 2 := by nlinarith
  have hinside :
      2 * (X.subgaussianParameter : Real) *
          ((w : Real) + Real.log (2 * (N : Real))) <= w ^ 4 := by
    have hsg0 : 0 <= (X.subgaussianParameter : Real) := by positivity
    have hsum0 : 0 <= w + Real.log (2 * (N : Real)) := by
      have : 1 <= 2 * (N : Real) := by exact_mod_cast (show 1 <= 2 * N by omega)
      exact add_nonneg hw0 (Real.log_nonneg this)
    calc
      2 * (X.subgaussianParameter : Real) *
          (w + Real.log (2 * (N : Real))) <=
          2 * Ksg * (w + Real.log (2 * (N : Real))) := by
            gcongr
      _ <= 2 * w * (w + 18 * w ^ 2) := by
            gcongr
      _ <= w ^ 4 := by nlinarith [sq_nonneg (w - 38)]
  unfold terminalConcreteExposureThreshold packetCoordinateMaxThreshold
  apply max_le
  · nlinarith [sq_nonneg w]
  · unfold familyCoordinateMaxThreshold
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · convert hinside using 1 <;> simp [w, N] <;> ring

private theorem terminalUniformCoefficientScale_le_pow
    {W : Nat} (hW : 3 <= W) :
    terminalUniformCoefficientScale W <= (W : Real) ^ 36 := by
  let w : Real := W
  have hw : 3 <= w := by dsimp [w]; exact_mod_cast hW
  have h2 : 2 * w <= w ^ 2 := by nlinarith
  have h3 : 3 * w <= w ^ 2 := by nlinarith
  unfold terminalUniformCoefficientScale
  simp only [strongRRQRExponent, Nat.cast_mul, Nat.cast_ofNat]
  calc
    2 * w * (3 * w) * (2 * w) ^ 16 <=
        w ^ 2 * w ^ 2 * (w ^ 2) ^ 16 := by gcongr
    _ = w ^ 36 := by ring

private theorem terminalUniformErrorScale_le_pow
    {W Kz : Nat} (hW : 3 <= W) :
    terminalUniformErrorScale W (terminalCanonicalThreshold W Kz) <=
      (W : Real) ^ (Kz + 64) := by
  let w : Real := W
  have hw : 3 <= w := by dsimp [w]; exact_mod_cast hW
  have h2 : 2 * w <= w ^ 2 := by nlinarith
  have h3 : 3 * w <= w ^ 2 := by nlinarith
  unfold terminalUniformErrorScale terminalCanonicalThreshold
    terminalCanonicalThresholdExponent
  simp only [strongRRQRExponent, Nat.cast_mul, Nat.cast_ofNat]
  calc
    (3 * w) ^ 2 * ((2 * w) ^ 16 * w ^ (Kz + 16 + 12)) <=
        (w ^ 2) ^ 2 * ((w ^ 2) ^ 16 * w ^ (Kz + 16 + 12)) := by
          gcongr
    _ = w ^ (Kz + 64) := by
      simp only [pow_add]
      ring

private theorem terminalUniformDeltaScale_le_pow
    {W Kz : Nat} {z : Complex} {M : Real}
    (hW : 3 <= W) (hM0 : 0 <= M) (hM : M <= (W : Real) ^ 2)
    (hz : ‖z‖ <= (W : Real) ^ Kz) :
    terminalUniformDeltaScale W z M <= (W : Real) ^ (Kz + 7) := by
  let w : Real := W
  have hw : 3 <= w := by dsimp [w]; exact_mod_cast hW
  have hw1 : 1 <= w := by linarith
  have h3 : 3 * w <= w ^ 2 := by nlinarith
  have hpowK : 1 <= w ^ Kz := one_le_pow₀ hw1
  have hM' : M <= w ^ (Kz + 2) := by
    rw [pow_add]
    nlinarith [sq_nonneg w]
  have hz' : ‖z‖ <= w ^ (Kz + 2) := by
    rw [pow_add]
    have : 1 <= w ^ 2 := one_le_pow₀ hw1
    nlinarith [norm_nonneg z, pow_nonneg (show 0 <= w by linarith) Kz]
  have hsum : M + ‖z‖ <= w ^ (Kz + 3) := by
    rw [show Kz + 3 = (Kz + 2) + 1 by omega, pow_succ]
    have hp : 0 <= w ^ (Kz + 2) := by positivity
    nlinarith
  have hsum0 : 0 <= M + ‖z‖ := add_nonneg hM0 (norm_nonneg z)
  unfold terminalUniformDeltaScale
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    (3 * w) ^ 2 * (M + ‖z‖) <= (w ^ 2) ^ 2 * w ^ (Kz + 3) := by
      gcongr
    _ = w ^ (Kz + 7) := by
      simp only [pow_add]
      ring

private theorem terminalPivotInverseScale_le_pow
    {W Kz : Nat} (hW : 3 <= W) :
    terminalPivotInverseScale W (terminalCanonicalThreshold W Kz) <=
      (W : Real) ^ 32 := by
  let w : Real := W
  have hw : 3 <= w := by dsimp [w]; exact_mod_cast hW
  have hw0 : 0 <= w := by linarith
  have hw1 : 1 <= w := by linarith
  have h2 : 2 * w <= w ^ 2 := by nlinarith
  have htau : 1 <= terminalCanonicalThreshold W Kz :=
    terminalCanonicalThreshold_one_le (by omega)
  unfold terminalPivotInverseScale
  calc
    (((2 * W : Nat) : Real) ^ strongRRQRExponent) /
        terminalCanonicalThreshold W Kz <=
        (((2 * W : Nat) : Real) ^ strongRRQRExponent) := by
          exact div_le_self (by positivity) htau
    _ <= (w ^ 2) ^ 16 := by
      simp only [strongRRQRExponent, Nat.cast_mul, Nat.cast_ofNat]
      exact (pow_le_pow_left₀ (by positivity) h2) 16
    _ = w ^ 32 := by ring

private theorem terminalUniformFScale_le_pow
    {W Kz : Nat} {z : Complex} {M : Real}
    (hW : 3 <= W) (hM0 : 0 <= M) (hM : M <= (W : Real) ^ 2)
    (hz : ‖z‖ <= (W : Real) ^ Kz) :
    terminalUniformFScale W (terminalCanonicalThreshold W Kz) M z <=
      (W : Real) ^ (2 * Kz + 125) := by
  let w : Real := W
  let B := terminalUniformCoefficientScale W
  let E := terminalUniformErrorScale W (terminalCanonicalThreshold W Kz)
  let D := terminalUniformDeltaScale W z M
  let I := terminalPivotInverseScale W (terminalCanonicalThreshold W Kz)
  have hw : 3 <= w := by dsimp [w]; exact_mod_cast hW
  have hw0 : 0 <= w := by linarith
  have hw1 : 1 <= w := by linarith
  have hw2 : 2 <= w := by linarith
  have hB : B <= w ^ 36 := terminalUniformCoefficientScale_le_pow hW
  have hE : E <= w ^ (Kz + 64) := terminalUniformErrorScale_le_pow hW
  have hD : D <= w ^ (Kz + 7) :=
    terminalUniformDeltaScale_le_pow hW hM0 hM hz
  have hI : I <= w ^ 32 := terminalPivotInverseScale_le_pow hW
  have hB0 : 0 <= B := by
    dsimp [B, terminalUniformCoefficientScale]
    positivity
  have hE0 : 0 <= E := by
    dsimp [E, terminalUniformErrorScale, terminalCanonicalThreshold]
    positivity
  have hD0 : 0 <= D := by
    dsimp [D, terminalUniformDeltaScale]
    positivity
  have hI0 : 0 <= I := by
    dsimp [I, terminalPivotInverseScale]
    have htau0 : 0 <= terminalCanonicalThreshold W Kz :=
      zero_le_one.trans (terminalCanonicalThreshold_one_le (by omega))
    exact div_nonneg (by positivity) htau0
  let N : Nat := 2 * Kz + 121
  have hpromote {a p : Nat} (hp : p <= N) (ha : (a : Real) <= w ^ p) :
      (a : Real) <= w ^ N := ha.trans (real_pow_mono_exponent hw1 hp)
  have hE_N : E <= w ^ N :=
    hE.trans (real_pow_mono_exponent hw1 (by dsimp [N]; omega))
  have hBD : B * D <= w ^ (Kz + 43) := by
    calc
      B * D <= w ^ 36 * w ^ (Kz + 7) :=
        mul_le_mul hB hD hD0 (by positivity)
      _ = w ^ (Kz + 43) := by simp only [pow_add]; ring
  have hDB : D * B <= w ^ (Kz + 43) := by
    calc
      D * B <= w ^ (Kz + 7) * w ^ 36 :=
        mul_le_mul hD hB hB0 (by positivity)
      _ = w ^ (Kz + 43) := by simp only [pow_add]; ring
  have hBDB : B * D * B <= w ^ (Kz + 79) := by
    calc
      B * D * B <= w ^ (Kz + 43) * w ^ 36 :=
        mul_le_mul hBD hB hB0 (by positivity)
      _ = w ^ (Kz + 79) := by simp only [pow_add]; ring
  have hA : D + B * D <= w ^ (Kz + 44) := by
    exact add_le_next_power hw2
      (hD.trans (real_pow_mono_exponent hw1 (by omega))) hBD
  have hA' : D + D * B <= w ^ (Kz + 44) := by
    exact add_le_next_power hw2
      (hD.trans (real_pow_mono_exponent hw1 (by omega))) hDB
  have h2I : 2 * I <= w ^ 33 := by
    rw [show 33 = 32 + 1 by omega, pow_succ]
    have hp : 0 <= w ^ 32 := by positivity
    nlinarith
  have hlast :
      (D + B * D) * (2 * I) * (D + D * B) <= w ^ N := by
    calc
      (D + B * D) * (2 * I) * (D + D * B) <=
          w ^ (Kz + 44) * w ^ 33 * w ^ (Kz + 44) := by
            gcongr
      _ = w ^ N := by
        dsimp [N]
        simp only [pow_add]
        ring
  have hBD_N : B * D <= w ^ N :=
    hBD.trans (real_pow_mono_exponent hw1 (by dsimp [N]; omega))
  have hDB_N : D * B <= w ^ N :=
    hDB.trans (real_pow_mono_exponent hw1 (by dsimp [N]; omega))
  have hBDB_N : B * D * B <= w ^ N :=
    hBDB.trans (real_pow_mono_exponent hw1 (by dsimp [N]; omega))
  have h1 : E + B * D <= w ^ (N + 1) :=
    add_le_next_power hw2 hE_N hBD_N
  have h2 : E + B * D + D * B <= w ^ (N + 2) := by
    exact add_le_next_power hw2 h1
      (hDB_N.trans (real_pow_mono_exponent hw1 (by omega)))
  have h3 : E + B * D + D * B + B * D * B <= w ^ (N + 3) := by
    exact add_le_next_power hw2 h2
      (hBDB_N.trans (real_pow_mono_exponent hw1 (by omega)))
  have h4 : E + B * D + D * B + B * D * B +
      (D + B * D) * (2 * I) * (D + D * B) <= w ^ (N + 4) := by
    exact add_le_next_power hw2 h3
      (hlast.trans (real_pow_mono_exponent hw1 (by omega)))
  simpa [terminalUniformFScale, terminalFPolynomialScale, B, E, D, I, N,
    add_assoc] using h4

private theorem terminalUniformFScale_nonneg
    {W : Nat} {tau M : Real} {z : Complex} (hM : 0 <= M)
    (htau : 0 <= tau) :
    0 <= terminalUniformFScale W tau M z := by
  unfold terminalUniformFScale
  apply terminalFPolynomialScale_nonneg
  · unfold terminalUniformCoefficientScale
    positivity
  · unfold terminalUniformErrorScale
    positivity
  · unfold terminalUniformDeltaScale
    positivity
  · unfold terminalPivotInverseScale
    apply div_nonneg <;> positivity

private theorem terminalUniformFirstDeformationScale_le_pow
    {W Kz : Nat} {z : Complex} {M : Real}
    (hW : 3 <= W) (hM0 : 0 <= M) (hM : M <= (W : Real) ^ 2)
    (hz : ‖z‖ <= (W : Real) ^ Kz) :
    terminalUniformFirstDeformationScale W
        (terminalCanonicalThreshold W Kz) M z <=
      (W : Real) ^ (2 * Kz + 130) := by
  let w : Real := W
  have hw : 3 <= w := by dsimp [w]; exact_mod_cast hW
  have hw1 : 1 <= w := by linarith
  have hw2 : 2 <= w := by linarith
  have h3 : 3 * w <= w ^ 2 := by nlinarith
  have hF := terminalUniformFScale_le_pow hW hM0 hM hz
  have hz' : ‖z‖ <= w ^ (2 * Kz + 125) :=
    hz.trans (real_pow_mono_exponent hw1 (by omega))
  have hsum : ‖z‖ + terminalUniformFScale W
      (terminalCanonicalThreshold W Kz) M z <= w ^ (2 * Kz + 126) :=
    add_le_next_power hw2 hz' hF
  have hsum0 : 0 <= ‖z‖ + terminalUniformFScale W
      (terminalCanonicalThreshold W Kz) M z :=
    add_nonneg (norm_nonneg z)
      (terminalUniformFScale_nonneg hM0 (by
        unfold terminalCanonicalThreshold
        positivity))
  unfold terminalUniformFirstDeformationScale
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    (3 * w) ^ 2 *
        (‖z‖ + terminalUniformFScale W
          (terminalCanonicalThreshold W Kz) M z) <=
        (w ^ 2) ^ 2 * w ^ (2 * Kz + 126) := by gcongr
    _ = w ^ (2 * Kz + 130) := by simp only [pow_add]; ring

private theorem terminalUniformCrossScale_le_pow
    {W Kz : Nat} {z : Complex} {M : Real}
    (hW : 3 <= W) (hM0 : 0 <= M) (hM : M <= (W : Real) ^ 2)
    (hz : ‖z‖ <= (W : Real) ^ Kz) :
    terminalUniformCrossScale W (terminalCanonicalThreshold W Kz) M z <=
      (W : Real) ^ (2 * Kz + 131) := by
  let w : Real := W
  have hw : 3 <= w := by dsimp [w]; exact_mod_cast hW
  have hw1 : 1 <= w := by linarith
  have hw2 : 2 <= w := by linarith
  have h3 : 3 * w <= w ^ 2 := by nlinarith
  have hF := terminalUniformFScale_le_pow hW hM0 hM hz
  have hM' : M <= w ^ (2 * Kz + 125) :=
    hM.trans (real_pow_mono_exponent hw1 (by omega))
  have hz' : ‖z‖ <= w ^ (2 * Kz + 125) :=
    hz.trans (real_pow_mono_exponent hw1 (by omega))
  have hMz : M + ‖z‖ <= w ^ (2 * Kz + 126) :=
    add_le_next_power hw2 hM' hz'
  have hsum : M + ‖z‖ + terminalUniformFScale W
      (terminalCanonicalThreshold W Kz) M z <= w ^ (2 * Kz + 127) :=
    add_le_next_power hw2 hMz
      (hF.trans (real_pow_mono_exponent hw1 (by omega)))
  have hsum0 : 0 <= M + ‖z‖ + terminalUniformFScale W
      (terminalCanonicalThreshold W Kz) M z :=
    add_nonneg (add_nonneg hM0 (norm_nonneg z))
      (terminalUniformFScale_nonneg hM0 (by
        unfold terminalCanonicalThreshold
        positivity))
  unfold terminalUniformCrossScale
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    (3 * w) ^ 2 *
        (M + ‖z‖ + terminalUniformFScale W
          (terminalCanonicalThreshold W Kz) M z) <=
        (w ^ 2) ^ 2 * w ^ (2 * Kz + 127) := by gcongr
    _ = w ^ (2 * Kz + 131) := by simp only [pow_add]; ring

private theorem terminalCanonicalPivot_small
    {W Kz : Nat} {z : Complex} {M : Real}
    (hW : 2 * terminalCanonicalPivotConstant <= W)
    (hM : M <= (W : Real) ^ 2)
    (hz : ‖z‖ <= (W : Real) ^ Kz) :
    terminalPivotInverseScale W (terminalCanonicalThreshold W Kz) *
        terminalUniformDeltaScale W z M <= (2 : Real)⁻¹ := by
  let w : Real := W
  have hCpos : 0 < terminalCanonicalPivotConstant := by
    norm_num [terminalCanonicalPivotConstant]
  have hw : (2 * terminalCanonicalPivotConstant : Nat) <= w := by
    dsimp [w]
    exact_mod_cast hW
  have hwpos : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hw1 : 1 <= w := by
    have hone : (1 : Real) <= (2 * terminalCanonicalPivotConstant : Nat) := by
      exact_mod_cast (show 1 <= 2 * terminalCanonicalPivotConstant by
        norm_num [terminalCanonicalPivotConstant])
    exact hone.trans hw
  have hM' : M <= w ^ (Kz + 2) := by
    rw [pow_add]
    have hp : 1 <= w ^ Kz := one_le_pow₀ hw1
    nlinarith [sq_nonneg w]
  have hz' : ‖z‖ <= w ^ (Kz + 2) := by
    rw [pow_add]
    have hp2 : 1 <= w ^ 2 := one_le_pow₀ hw1
    have hp0 : 0 <= w ^ Kz := by positivity
    nlinarith [norm_nonneg z]
  have hsum : M + ‖z‖ <= 2 * w ^ (Kz + 2) := by linarith
  have hnum :
      (((2 * W : Nat) : Real) ^ strongRRQRExponent) *
          (((3 * W : Nat) : Real) ^ 2 * (M + ‖z‖)) <=
        (terminalCanonicalPivotConstant : Real) * w ^ (Kz + 20) := by
    simp only [strongRRQRExponent, Nat.cast_mul, Nat.cast_ofNat]
    calc
      (2 * w) ^ 16 * ((3 * w) ^ 2 * (M + ‖z‖)) <=
          (2 * w) ^ 16 * ((3 * w) ^ 2 *
            (2 * w ^ (Kz + 2))) := by gcongr
      _ = (terminalCanonicalPivotConstant : Real) * w ^ (Kz + 20) := by
        simp [terminalCanonicalPivotConstant, pow_add]
        ring
  have htaupos : 0 < terminalCanonicalThreshold W Kz := by
    unfold terminalCanonicalThreshold
    positivity
  have hquotient :
      (terminalCanonicalPivotConstant : Real) * w ^ (Kz + 20) /
          w ^ (Kz + 28) =
        (terminalCanonicalPivotConstant : Real) / w ^ 8 := by
    rw [show Kz + 28 = (Kz + 20) + 8 by omega, pow_add]
    field_simp
    simp only [pow_add]
    ring
  have hhalf :
      (terminalCanonicalPivotConstant : Real) / w ^ 8 <= (2 : Real)⁻¹ := by
    rw [div_le_iff₀ (pow_pos hwpos 8)]
    have hw8 : w <= w ^ 8 := by
      simpa only [pow_one] using real_pow_mono_exponent hw1 (show 1 <= 8 by omega)
    have hwC : 2 * (terminalCanonicalPivotConstant : Real) <= w := by
      dsimp [w]
      exact_mod_cast hW
    have hinv : (2 : Real)⁻¹ = (1 : Real) / 2 := by norm_num
    rw [hinv]
    nlinarith
  unfold terminalPivotInverseScale terminalUniformDeltaScale
    terminalCanonicalThreshold terminalCanonicalThresholdExponent
  rw [div_mul_eq_mul_div]
  calc
    (((2 * W : Nat) : Real) ^ strongRRQRExponent *
          (((3 * W : Nat) : Real) ^ 2 * (M + ‖z‖))) /
        (W : Real) ^ (Kz + strongRRQRExponent + 12) <=
      ((terminalCanonicalPivotConstant : Real) * w ^ (Kz + 20)) /
        (W : Real) ^ (Kz + strongRRQRExponent + 12) := by
          gcongr
    _ = (terminalCanonicalPivotConstant : Real) / w ^ 8 := by
      simpa [strongRRQRExponent, w, add_assoc] using hquotient
    _ <= (2 : Real)⁻¹ := hhalf

private theorem width_le_floorSquare
    {W : Nat} (hW : 64 <= W) :
    let n := W / 3
    (W : Real) <= (n : Real) ^ 2 := by
  dsimp only
  have hn : 4 <= W / 3 := by omega
  have hWn : W <= 4 * (W / 3) := by omega
  exact_mod_cast (calc
    W <= 4 * (W / 3) := hWn
    _ <= (W / 3) ^ 2 := by nlinarith)

private theorem terminalCanonical_first_polynomial
    {W Kz : Nat} {z : Complex} {M : Real}
    (hW : 64 <= W) (hM0 : 0 <= M) (hM : M <= (W : Real) ^ 2)
    (hz : ‖z‖ <= (W : Real) ^ Kz) :
    terminalUniformFirstDeformationScale W
        (terminalCanonicalThreshold W Kz) M z <=
      ((W / 3 : Nat) : Real) ^ terminalCanonicalFirstCookExponent Kz := by
  let w : Real := W
  let n : Real := (W / 3 : Nat)
  have hnNat : 4 <= W / 3 := by omega
  have hn : 4 <= n := by dsimp [n]; exact_mod_cast hnNat
  have hn0 : 0 <= n := by linarith
  have hn1 : 1 <= n := by linarith
  have hwn2 : w <= n ^ 2 := by
    simpa [w, n] using width_le_floorSquare hW
  have hscale := terminalUniformFirstDeformationScale_le_pow
    (W := W) (Kz := Kz) (z := z) (M := M) (by omega) hM0 hM hz
  have htoN :
      w ^ (2 * Kz + 130) <= n ^ (4 * Kz + 260) := by
    calc
      w ^ (2 * Kz + 130) <= (n ^ 2) ^ (2 * Kz + 130) :=
        (pow_le_pow_left₀ (by positivity) hwn2) _
      _ = n ^ (4 * Kz + 260) := by ring
  have hexp : 4 * Kz + 260 <= 16 * Kz + 416 := by omega
  have htargetNat : n ^ (4 * Kz + 260) <= n ^ (16 * Kz + 416) :=
    real_pow_mono_exponent hn1 hexp
  calc
    terminalUniformFirstDeformationScale W
        (terminalCanonicalThreshold W Kz) M z <= w ^ (2 * Kz + 130) := hscale
    _ <= n ^ (4 * Kz + 260) := htoN
    _ <= n ^ (16 * Kz + 416) := htargetNat
    _ = ((W / 3 : Nat) : Real) ^ terminalCanonicalFirstCookExponent Kz := by
      have hL : terminalCanonicalFirstCookExponent Kz =
          ((16 * Kz + 416 : Nat) : Real) := by
        unfold terminalCanonicalFirstCookExponent
          terminalCanonicalThresholdExponent
        simp only [strongRRQRExponent]
        push_cast
        ring
      rw [hL, Real.rpow_natCast]

private theorem terminalCanonical_second_polynomial
    (cook : CookDeformedSquareInput)
    {W Kz : Nat} {z : Complex} {M : Real}
    (hW : 64 <= W) (hM0 : 0 <= M) (hM : M <= (W : Real) ^ 2)
    (hz : ‖z‖ <= (W : Real) ^ Kz)
    (hbetaFloor :
      (12 : Real) ^ cook.beta (terminalCanonicalFirstCookExponent Kz) <=
        ((W / 3 : Nat) : Real)) :
    terminalUniformSecondDeformationScale cook W Kz
        (terminalCanonicalThreshold W Kz) M z <=
      ((W / 3 : Nat) : Real) ^
        terminalCanonicalSecondCookExponent cook Kz := by
  let w : Real := W
  let n : Real := (W / 3 : Nat)
  let beta : Real := cook.beta (terminalCanonicalFirstCookExponent Kz)
  have hnNat : 4 <= W / 3 := by omega
  have hn : 4 <= n := by dsimp [n]; exact_mod_cast hnNat
  have hn0 : 0 <= n := by linarith
  have hn1 : 1 <= n := by linarith
  have hwn2 : w <= n ^ 2 := by
    simpa [w, n] using width_le_floorSquare hW
  have hWnNat : W <= 4 * (W / 3) := by omega
  have h3W12n : (3 * W : Nat) <= (12 : Real) * n := by
    dsimp [n]
    exact_mod_cast (show 3 * W <= 12 * (W / 3) by omega)
  have hbeta0 : 0 <= beta := by
    dsimp [beta]
    exact (cook.beta_pos _).le
  have hfirstW := terminalUniformFirstDeformationScale_le_pow
    (W := W) (Kz := Kz) (z := z) (M := M) (by omega) hM0 hM hz
  have hcrossW := terminalUniformCrossScale_le_pow
    (W := W) (Kz := Kz) (z := z) (M := M) (by omega) hM0 hM hz
  have hfirst : terminalUniformFirstDeformationScale W
      (terminalCanonicalThreshold W Kz) M z <= n ^ (4 * Kz + 260) := by
    exact hfirstW.trans (calc
      w ^ (2 * Kz + 130) <= (n ^ 2) ^ (2 * Kz + 130) :=
        (pow_le_pow_left₀ (by positivity) hwn2) _
      _ = n ^ (4 * Kz + 260) := by ring)
  have hcross : terminalUniformCrossScale W
      (terminalCanonicalThreshold W Kz) M z <= n ^ (4 * Kz + 262) := by
    exact hcrossW.trans (calc
      w ^ (2 * Kz + 131) <= (n ^ 2) ^ (2 * Kz + 131) :=
        (pow_le_pow_left₀ (by positivity) hwn2) _
      _ = n ^ (4 * Kz + 262) := by ring)
  have hinverse : terminalUniformFirstCookInverseScale cook W Kz <=
      n * n ^ beta := by
    have hbase : (0 : Real) <= ((3 * W : Nat) : Real) := by positivity
    calc
      terminalUniformFirstCookInverseScale cook W Kz =
          (((3 * W : Nat) : Real) ^ beta) := by
            rfl
      _ <= ((12 : Real) * n) ^ beta := by
        exact Real.rpow_le_rpow hbase h3W12n hbeta0
      _ = (12 : Real) ^ beta * n ^ beta := by
        rw [Real.mul_rpow (by norm_num : (0 : Real) <= 12) hn0]
      _ <= n * n ^ beta := by
        gcongr
  have hinverse0 : 0 <= terminalUniformFirstCookInverseScale cook W Kz := by
    unfold terminalUniformFirstCookInverseScale
    exact Real.rpow_nonneg (by positivity) _
  have hcross0 : 0 <= terminalUniformCrossScale W
      (terminalCanonicalThreshold W Kz) M z := by
    unfold terminalUniformCrossScale
    have htau0 : 0 <= terminalCanonicalThreshold W Kz :=
      zero_le_one.trans (terminalCanonicalThreshold_one_le (by omega))
    have hF0 := terminalUniformFScale_nonneg
      (W := W) (tau := terminalCanonicalThreshold W Kz)
      (M := M) (z := z) hM0 htau0
    positivity
  let A : Nat := 4 * Kz + 260
  let B : Nat := 4 * Kz + 262
  let C : Nat := 2 * B + 1
  have hprod :
      terminalUniformCrossScale W (terminalCanonicalThreshold W Kz) M z *
          terminalUniformFirstCookInverseScale cook W Kz *
          terminalUniformCrossScale W (terminalCanonicalThreshold W Kz) M z <=
        n ^ C * n ^ beta := by
    calc
      terminalUniformCrossScale W (terminalCanonicalThreshold W Kz) M z *
          terminalUniformFirstCookInverseScale cook W Kz *
          terminalUniformCrossScale W (terminalCanonicalThreshold W Kz) M z <=
        n ^ B * (n * n ^ beta) * n ^ B := by
          gcongr
      _ = n ^ C * n ^ beta := by
        dsimp [B, C]
        ring
  have hfirst' :
      terminalUniformFirstDeformationScale W
          (terminalCanonicalThreshold W Kz) M z <= n ^ C * n ^ beta := by
    have hAC : A <= C := by dsimp [A, B, C]; omega
    have hpowAC : n ^ A <= n ^ C := real_pow_mono_exponent hn1 hAC
    have honebeta : 1 <= n ^ beta := Real.one_le_rpow hn1 hbeta0
    exact hfirst.trans (hpowAC.trans (by
      have hp : 0 <= n ^ C := by positivity
      simpa only [mul_one] using mul_le_mul_of_nonneg_left honebeta hp))
  have hsum :
      terminalUniformFirstDeformationScale W
          (terminalCanonicalThreshold W Kz) M z +
        terminalUniformCrossScale W (terminalCanonicalThreshold W Kz) M z *
          terminalUniformFirstCookInverseScale cook W Kz *
          terminalUniformCrossScale W (terminalCanonicalThreshold W Kz) M z <=
        n ^ (C + 1) * n ^ beta := by
    rw [pow_succ]
    have hp : 0 <= n ^ C * n ^ beta := by positivity
    nlinarith
  have hCR : C + 1 <= 32 * Kz + 840 := by
    dsimp [B, C]
    omega
  have hpromote : n ^ (C + 1) * n ^ beta <=
      n ^ (32 * Kz + 840) * n ^ beta := by
    exact mul_le_mul_of_nonneg_right
      (real_pow_mono_exponent hn1 hCR) (Real.rpow_nonneg hn0 beta)
  unfold terminalUniformSecondDeformationScale
  calc
    terminalUniformFirstDeformationScale W
          (terminalCanonicalThreshold W Kz) M z +
        terminalUniformCrossScale W (terminalCanonicalThreshold W Kz) M z *
          terminalUniformFirstCookInverseScale cook W Kz *
          terminalUniformCrossScale W (terminalCanonicalThreshold W Kz) M z <=
        n ^ (C + 1) * n ^ beta := hsum
    _ <= n ^ (32 * Kz + 840) * n ^ beta := hpromote
    _ = ((W / 3 : Nat) : Real) ^
        terminalCanonicalSecondCookExponent cook Kz := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_add (by linarith : 0 < n)]
      congr 1
      dsimp [n, beta]
      unfold terminalCanonicalSecondCookExponent
        terminalCanonicalFirstCookExponent
        terminalCanonicalThresholdExponent
      simp only [strongRRQRExponent]
      norm_num
      ring

/-- The scalar large-width package follows from a fixed subgaussian bound
and one explicit width inequality.  No matrix, RRQR, mask, or Cook-event
certificate occurs among the assumptions. -/
theorem packetTerminalCanonicalLargeWConditions_of_ge_threshold
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W : Nat}
    (cook : CookDeformedSquareInput) (Kz : Nat) (Ksg : Real)
    (hKsg : 1 <= Ksg)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (hsubg : (X.subgaussianParameter : Real) <= Ksg)
    (hCook : (X.subgaussianParameter : Real) <= cook.subgaussianBound)
    (hW : terminalCanonicalLargeWThreshold cook Kz Ksg <= W)
    (hz : ‖z‖ <= (W : Real) ^ Kz) :
    PacketTerminalCanonicalLargeWConditions cook z X Kz (W : Real) := by
  have hWpivot : 2 * terminalCanonicalPivotConstant <= W :=
    le_trans (le_max_left _ _) hW
  have hW64 : 64 <= W :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hW)
  have hWceil : Nat.ceil Ksg <= W := by
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hW))
  have hKsgW : Ksg <= (W : Real) := by
    exact (Nat.le_ceil Ksg).trans (by exact_mod_cast hWceil)
  have hWbeta :
      3 * Nat.ceil ((12 : Real) ^
        cook.beta (terminalCanonicalFirstCookExponent Kz)) <= W := by
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hW))
  have hceilBeta :
      Nat.ceil ((12 : Real) ^
        cook.beta (terminalCanonicalFirstCookExponent Kz)) <= W / 3 := by
    omega
  have hbetaFloor :
      (12 : Real) ^ cook.beta (terminalCanonicalFirstCookExponent Kz) <=
        ((W / 3 : Nat) : Real) := by
    have hc : (12 : Real) ^
        cook.beta (terminalCanonicalFirstCookExponent Kz) <=
        (Nat.ceil ((12 : Real) ^
          cook.beta (terminalCanonicalFirstCookExponent Kz)) : Nat) :=
      Nat.le_ceil _
    have hcast :
        (Nat.ceil ((12 : Real) ^
          cook.beta (terminalCanonicalFirstCookExponent Kz)) : Real) <=
          ((W / 3 : Nat) : Real) := by
      exact_mod_cast hceilBeta
    exact hc.trans hcast
  let M := terminalConcreteExposureThreshold X (W : Real)
  have hM0 : 0 <= M := by
    dsimp [M, terminalConcreteExposureThreshold, packetCoordinateMaxThreshold]
    exact (by norm_num : (0 : Real) <= 1).trans (le_max_left _ _)
  have hM : M <= (W : Real) ^ 2 :=
    terminalConcreteExposureThreshold_le_sq X Ksg hW64 hsubg
      ((by norm_num : (0 : Real) <= 1).trans hKsg) hKsgW
  exact
    { subgaussian_bound := by exact_mod_cast hCook
      W_large := by omega
      t_nonneg := by positivity
      shift_bound := hz
      pivot_small := by
        simpa [M] using terminalCanonicalPivot_small hWpivot hM hz
      first_polynomial := by
        simpa [M] using terminalCanonical_first_polynomial hW64 hM0 hM hz
      second_polynomial := by
        simpa [M] using terminalCanonical_second_polynomial cook hW64 hM0 hM hz
          hbetaFloor }

/-- Eventual paper form: `W₀` is explicitly the preceding threshold. -/
theorem exists_width_for_packetTerminalCanonicalLargeWConditions
    (cook : CookDeformedSquareInput) (Kz : Nat) (Ksg : Real)
    (hKsg : 1 <= Ksg) :
    exists W0 : Nat, forall
      {Omega : Type*} [MeasurableSpace Omega]
      {mu : Measure Omega} {W : Nat}
      (z : Complex)
      (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W))),
      (X.subgaussianParameter : Real) <= Ksg ->
      (X.subgaussianParameter : Real) <= cook.subgaussianBound ->
      W0 <= W -> ‖z‖ <= (W : Real) ^ Kz ->
      PacketTerminalCanonicalLargeWConditions cook z X Kz (W : Real) := by
  refine ⟨terminalCanonicalLargeWThreshold cook Kz Ksg, ?_⟩
  intro Omega _ mu W z X hsubg hCook hW hz
  exact packetTerminalCanonicalLargeWConditions_of_ge_threshold
    cook Kz Ksg hKsg z X hsubg hCook hW hz

end TerminalAssembly

end BernoulliSection9
