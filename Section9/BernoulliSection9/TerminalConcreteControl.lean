import BernoulliSection9.TerminalConcreteFinal
import BernoulliSection9.TerminalConcreteCrossBounds
import Mathlib.Tactic

/-!
# Concrete terminal good-event control

This module performs the literal RRQR/CUR/two-Cook assembly.  Every RRQR
selection, residual ordering, deformation, conditioning sigma-field and
truncation is computed internally from the paper data.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

set_option maxHeartbeats 6000000

namespace BernoulliSection9

open MeasureTheory ProbabilityTheory BernoulliLinearAlgebra
open TerminalAssembly

universe u

/-- The canonical RRQR pivot lower scale before the perturbative `2^{-r}`
loss. -/
def packetTerminalRRQRPivotLower {W : Nat}
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (tau : Real) : Real :=
  let r := packetLargeSingularValueCount Q tau
  ((((2 * W : Nat) : Real) ^ strongRRQRExponent)⁻¹ ^ r) *
    largeSingularProduct (Matrix.toEuclideanLin (packetOuterFinMatrix Q)) r

/-- The pivot stability lemma with an arbitrary finite residual index type.
The pivot itself is still the exact complex `Fin r` matrix produced by RRQR. -/
private theorem terminalPivot_stable_residualIndex
    {r : Nat} {q : Type*} [Fintype q] [DecidableEq q]
    (hr : 0 < r) (S : BlockSkeletonData (Fin r) q)
    (Delta : Matrix (Fin r ⊕ q) (Fin r ⊕ q) Complex)
    (D I pivotLower : Real)
    (hK : IsUnit S.Kpiv.det)
    (hD : ‖delta11 Delta‖ <= D) (hI : ‖S.Kpiv⁻¹‖ <= I)
    (hsmall : I * D <= (2 : Real)⁻¹)
    (hpivotLower : 0 <= pivotLower)
    (hpivot : pivotLower <= ‖S.Kpiv.det‖) :
    IsUnit (KDelta S Delta).det ∧
      ‖(KDelta S Delta)⁻¹‖ <= 2 * I ∧
      (2 : Real)⁻¹ ^ r * pivotLower <= ‖(KDelta S Delta).det‖ := by
  have hpert := norm_inv_mul_delta11_le_half_of_bounds
    S Delta D I hD hI hsmall
  have hdet := pivot_add_det_lower hr S.Kpiv (delta11 Delta) hK hpert
    hpivotLower hpivot
  have hdetpos : 0 < ‖(KDelta S Delta).det‖ := by
    have hfactor : 0 < (2 : Real)⁻¹ ^ r := pow_pos (by norm_num) _
    have hKpos : 0 < ‖S.Kpiv.det‖ := norm_pos_iff.mpr
      (isUnit_iff_ne_zero.mp hK)
    have hraw := pivot_add_det_lower_of_inv_mul_norm_le_half hr
      S.Kpiv (delta11 Delta) hK hpert
    exact (mul_pos hfactor hKpos).trans_le (by simpa [KDelta] using hraw)
  refine ⟨isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hdetpos), ?_, ?_⟩
  · exact (norm_pivot_add_inv_le_two_mul_of_inv_mul_norm_le_half hr
      S.Kpiv (delta11 Delta) hK hpert).trans
        (mul_le_mul_of_nonneg_left hI (by norm_num))
  · simpa [KDelta] using hdet

/-- Deterministic output available on the maximum-coordinate exposure
event.  It is an internal proof package, never a caller premise. -/
structure PacketTerminalExposureBounds
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W : Nat}
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (tau : Real) (hn : 2 <= 2 * W) (htau : 1 <= tau)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (M : Real) (omega : Omega) where
  pivot_unit : IsUnit
    (KDelta
      (terminalExtendedSkeletonData
        (packetRRQRRowEquiv Q tau hn htau)
        (packetRRQRColEquiv Q tau hn htau)
        (packetRRQRSkeleton Q tau hn htau))
      (terminalBalancedPerturbation
        (packetRRQRRowEquiv Q tau hn htau)
        (packetRRQRColEquiv Q tau hn htau) z X omega)).det
  pivot_inverse :
    ‖(KDelta
      (terminalExtendedSkeletonData
        (packetRRQRRowEquiv Q tau hn htau)
        (packetRRQRColEquiv Q tau hn htau)
        (packetRRQRSkeleton Q tau hn htau))
      (terminalBalancedPerturbation
        (packetRRQRRowEquiv Q tau hn htau)
        (packetRRQRColEquiv Q tau hn htau) z X omega))⁻¹‖ <=
      2 * terminalPivotInverseScale W tau
  pivot_determinant :
    (2 : Real)⁻¹ ^ packetLargeSingularValueCount Q tau *
        packetTerminalRRQRPivotLower Q tau <=
      ‖(KDelta
        (terminalExtendedSkeletonData
          (packetRRQRRowEquiv Q tau hn htau)
          (packetRRQRColEquiv Q tau hn htau)
          (packetRRQRSkeleton Q tau hn htau))
        (terminalBalancedPerturbation
          (packetRRQRRowEquiv Q tau hn htau)
          (packetRRQRColEquiv Q tau hn htau) z X omega)).det‖
  F_norm :
    ‖F
      (terminalExtendedSkeletonData
        (packetRRQRRowEquiv Q tau hn htau)
        (packetRRQRColEquiv Q tau hn htau)
        (packetRRQRSkeleton Q tau hn htau))
      (terminalBalancedPerturbation
        (packetRRQRRowEquiv Q tau hn htau)
        (packetRRQRColEquiv Q tau hn htau) z X omega)‖ <=
      terminalUniformFScale W tau M z

/-- All deterministic RRQR/CUR estimates on the literal maximum-coordinate
event.  The empty-pivot branch is discharged here, not excluded by a caller
hypothesis. -/
theorem packetTerminalExposureBounds
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W : Nat}
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (tau : Real) (hn : 2 <= 2 * W) (htau : 1 <= tau)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (M : Real) (hM : 0 <= M)
    (hsmall : terminalPivotInverseScale W tau *
      terminalUniformDeltaScale W z M <= (2 : Real)⁻¹)
    (omega : Omega) (homega : omega ∈ coordinatewiseBoundedEvent X M) :
    PacketTerminalExposureBounds Q tau hn htau z X M omega := by
  let r := packetLargeSingularValueCount Q tau
  let q := 2 * W - r
  let R := packetStrongRRQRConclusion Q tau hn htau
  let row := packetRRQRRowEquiv Q tau hn htau
  let col := packetRRQRColEquiv Q tau hn htau
  let S := packetRRQRSkeleton Q tau hn htau
  let Sext := terminalExtendedSkeletonData row col S
  let Delta := terminalBalancedPerturbation row col z X omega
  let B := terminalUniformCoefficientScale W
  let E := terminalUniformErrorScale W tau
  let D := terminalUniformDeltaScale W z M
  let I := terminalPivotInverseScale W tau
  let pivotLower := packetTerminalRRQRPivotLower Q tau
  have htau0 : 0 <= tau := zero_le_one.trans htau
  have hB0 : 0 <= B := by dsimp [B, terminalUniformCoefficientScale]; positivity
  have hE0 : 0 <= E := by
    dsimp [E, terminalUniformErrorScale]
    positivity
  have hD0 : 0 <= D := by
    dsimp [D, terminalUniformDeltaScale]
    positivity
  have hI0 : 0 <= I := by
    dsimp [I, terminalPivotInverseScale]
    positivity
  have hF0 : 0 <= terminalUniformFScale W tau M z :=
    terminalFPolynomialScale_nonneg hB0 hE0 hD0 hI0
  have hblocks := terminalDelta_blocks_norm_le row col z X M hM omega homega
  have h11 : ‖delta11 Delta‖ <= D := by
    simpa [Delta, D, terminalDeltaBlockScale_eq_uniform] using hblocks.1
  have h12 : ‖delta12 Delta‖ <= D := by
    simpa [Delta, D, terminalDeltaBlockScale_eq_uniform] using hblocks.2.1
  have h21 : ‖delta21 Delta‖ <= D := by
    simpa [Delta, D, terminalDeltaBlockScale_eq_uniform] using hblocks.2.2.1
  have hXbase : ‖S.Xskel‖ <= ((2 * W : Nat) : Real) ^ strongRRQRExponent := by
    have h := R.coefficient_bound
    change ‖S.Xskel‖ + ‖S.Yskel‖ <=
      ((2 * W : Nat) : Real) ^ strongRRQRExponent at h
    exact (le_add_of_nonneg_right (norm_nonneg S.Yskel)).trans h
  have hYbase : ‖S.Yskel‖ <= ((2 * W : Nat) : Real) ^ strongRRQRExponent := by
    have h := R.coefficient_bound
    change ‖S.Xskel‖ + ‖S.Yskel‖ <=
      ((2 * W : Nat) : Real) ^ strongRRQRExponent at h
    exact (le_add_of_nonneg_left (norm_nonneg S.Xskel)).trans h
  have hX : ‖Sext.Xskel‖ <= B := by
    calc
      ‖Sext.Xskel‖ <= (r : Real) *
          Fintype.card (TerminalBalancedResidualIndex row col) * ‖S.Xskel‖ := by
        simpa [Sext, terminalExtendedSkeletonData] using
          norm_terminalExtendedX_le row col S.Xskel
      _ <= (r : Real) *
          Fintype.card (TerminalBalancedResidualIndex row col) *
            (((2 * W : Nat) : Real) ^ strongRRQRExponent) := by
        gcongr
      _ = terminalExtendedCoefficientScale row col := rfl
      _ <= B := by
        simpa [B] using terminalExtendedCoefficientScale_le_uniform row col
  have hY : ‖Sext.Yskel‖ <= B := by
    calc
      ‖Sext.Yskel‖ <=
          Fintype.card (TerminalBalancedResidualIndex row col) *
            (r : Real) * ‖S.Yskel‖ := by
        simpa [Sext, terminalExtendedSkeletonData] using
          norm_terminalExtendedY_le row col S.Yskel
      _ <= Fintype.card (TerminalBalancedResidualIndex row col) *
          (r : Real) * (((2 * W : Nat) : Real) ^ strongRRQRExponent) := by
        gcongr
      _ = terminalExtendedCoefficientScale row col := by
        unfold terminalExtendedCoefficientScale
        ring
      _ <= B := by
        simpa [B] using terminalExtendedCoefficientScale_le_uniform row col
  have hE : ‖Sext.E0‖ <= E := by
    calc
      ‖Sext.E0‖ <=
          (Fintype.card (TerminalBalancedResidualIndex row col) : Real) ^ 2 *
            ‖S.E0‖ := by
        simpa [Sext, terminalExtendedSkeletonData] using
          norm_terminalExtendedE_le row col S.E0
      _ <= (Fintype.card (TerminalBalancedResidualIndex row col) : Real) ^ 2 *
          ((((2 * W : Nat) : Real) ^ strongRRQRExponent) * tau) := by
        gcongr
        have h := R.error_bound
        change ‖S.E0‖ <=
          ((2 * W : Nat) : Real) ^ strongRRQRExponent * tau at h
        exact h
      _ = terminalExtendedErrorScale row col tau := rfl
      _ <= E := by
        simpa [E] using terminalExtendedErrorScale_le_uniform row col htau0
  have hK : IsUnit Sext.Kpiv.det := by
    simpa [Sext, S, terminalExtendedSkeletonData] using
      packetRRQR_pivot_isUnit Q tau hn htau
  have hI : ‖Sext.Kpiv⁻¹‖ <= I := by
    by_cases hr0 : r = 0
    · have hempty : S.Kpiv = 0 := by
        have h := (R.empty_pivot hr0).1
        change S.Kpiv = 0 at h
        exact h
      have hzero : Sext.Kpiv = 0 := by
        simpa [Sext, terminalExtendedSkeletonData] using hempty
      rw [hzero]
      simpa using hI0
    · have hr : 0 < r := Nat.pos_of_ne_zero hr0
      have hraw := strongRRQRPivot_inv_norm_le_pow_div_threshold
        (packetOuterFinMatrix Q) tau R hr htau
      change ‖S.Kpiv⁻¹‖ <=
        ((2 * W : Nat) : Real) ^ strongRRQRExponent / tau at hraw
      simpa [Sext, terminalExtendedSkeletonData, I,
        terminalPivotInverseScale] using hraw
  have hpivot : pivotLower <= ‖Sext.Kpiv.det‖ := by
    have hraw := rrqrPivot_det_lower_canonicalLargeSingularProduct
      (packetOuterFinMatrix Q) tau R
    change packetTerminalRRQRPivotLower Q tau <= ‖S.Kpiv.det‖ at hraw
    simpa [pivotLower, Sext, terminalExtendedSkeletonData] using hraw
  have hpivot0 : 0 <= pivotLower := by
    dsimp [pivotLower, packetTerminalRRQRPivotLower]
    exact mul_nonneg (pow_nonneg (inv_nonneg.mpr (pow_nonneg (by positivity) _)) _)
      (largeSingularProduct_nonneg _ _)
  have hpkg : IsUnit (KDelta Sext Delta).det ∧
      ‖(KDelta Sext Delta)⁻¹‖ <= 2 * I ∧
      (2 : Real)⁻¹ ^ r * pivotLower <= ‖(KDelta Sext Delta).det‖ := by
    by_cases hr0 : r = 0
    · have hdelta11 : delta11 Delta = 0 := by
        ext i
        exact Fin.elim0 (hr0 ▸ i)
      have hKDelta : KDelta Sext Delta = Sext.Kpiv := by
        simp [KDelta, hdelta11]
      constructor
      · rw [hKDelta]
        exact hK
      constructor
      · rw [hKDelta]
        exact hI.trans (by nlinarith [hI0])
      · rw [hKDelta]
        simpa [hr0] using hpivot
    · exact terminalPivot_stable_residualIndex
        (Nat.pos_of_ne_zero hr0) Sext Delta D I pivotLower hK h11 hI
        (by simpa [I, D] using hsmall) hpivot0 hpivot
  have hFnorm : ‖F Sext Delta‖ <= terminalUniformFScale W tau M z := by
    exact F_norm_le_terminalFPolynomialScale Sext Delta B E D I
      hX hY hE h11 h12 h21 hpkg.2.1 hB0 hD0 hI0
  refine
    { pivot_unit := ?_
      pivot_inverse := ?_
      pivot_determinant := ?_
      F_norm := ?_ }
  · simpa [Sext, Delta] using hpkg.1
  · simpa [Sext, Delta, I] using hpkg.2.1
  · simpa [Sext, Delta, pivotLower, r] using hpkg.2.2
  · simpa [Sext, Delta] using hFnorm

end BernoulliSection9
