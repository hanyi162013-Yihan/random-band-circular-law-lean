import BernoulliSection9.TerminalConcreteConclusion
import BernoulliSection9.TerminalConcreteCrossBounds
import BernoulliSection9.TerminalCoefficientBounds
import Mathlib.Tactic

/-!
# Final certificate-free terminal assembly: uniform numerical bridges

This module is deliberately separate from `TerminalConcreteConclusion`.
The lemmas below close the logarithmic and reindexing bookkeeping needed by
the concrete two-Cook assembly.  Every quantity is computed from the paper
data; no RRQR, mask, elimination, or deformation certificate is an input.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

open MeasureTheory BernoulliLinearAlgebra
open TerminalAssembly

/-- The uniform determinant factor is strictly positive at every positive
packet width. -/
theorem terminalUniformDeterminantFactor_pos
    (cook : CookDeformedSquareInput) {W Kz : Nat} (hW : 0 < W) :
    0 < terminalUniformDeterminantFactor cook W Kz := by
  unfold terminalUniformDeterminantFactor
  have h2W : 0 < ((2 * W : Nat) : Real) := by positivity
  have h3W : 0 < ((3 * W : Nat) : Real) := by positivity
  have hbeta₁ : 0 < cook.beta (terminalCanonicalFirstCookExponent Kz) :=
    cook.beta_pos _
  have hbeta₂ : 0 <
      cook.beta (terminalCanonicalSecondCookExponent cook Kz) :=
    cook.beta_pos _
  positivity

/-- The threshold-to-Gram-volume factor is positive at positive width. -/
theorem terminalUniformGramThresholdFactor_pos
    {W Kz : Nat} (hW : 0 < W) :
    0 < terminalUniformGramThresholdFactor W Kz := by
  unfold terminalUniformGramThresholdFactor terminalCanonicalThreshold
  have hWreal : 0 < (W : Real) := by exact_mod_cast hW
  positivity

/-- Exact reindexing bridge for the packet matrix used internally by RRQR. -/
theorem gramVolume_packetOuterFinMatrix {W : Nat}
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex) :
    gramVolume (packetOuterFinMatrix Q) = gramVolume Q := by
  exact gramVolume_submatrix_equiv (packetOuterFinEquiv W).symm Q

/-- The `Fin r` product used by the RRQR pivot estimate is exactly the
canonical filtered product when `r` is in range. -/
theorem prod_singularValues_castLE_eq_largeSingularProduct
    {n r : Nat} (A : Matrix (Fin n) (Fin n) Complex) (hr : r <= n) :
    (∏ j : Fin r, (Matrix.toEuclideanLin A).singularValues
        (Fin.castLE hr j)) =
      largeSingularProduct (Matrix.toEuclideanLin A) r := by
  classical
  unfold largeSingularProduct
  symm
  apply Finset.prod_bij (fun i _ => ⟨i, by simp_all⟩)
  · intro i hi
    simp only [Finset.mem_univ]
  · intro i hi j hj hij
    apply Fin.ext
    exact congrArg (fun x : Fin r => x.val) hij
  · intro j hj
    have hr' : r <= Module.finrank Complex
        (EuclideanSpace Complex (Fin n)) := by
      simpa [finrank_euclideanSpace] using hr
    refine ⟨Fin.castLE hr' j, ?_, ?_⟩
    · simp
    · exact Fin.ext rfl
  · intro i hi
    rfl

/-- RRQR's pivot determinant lower bound, rewritten with the canonical
large-singular-value product rather than a selected-coordinate product. -/
theorem rrqrPivot_det_lower_canonicalLargeSingularProduct
    {n r : Nat} (A : Matrix (Fin n) (Fin n) Complex) (tau : Real)
    (R : StrongRRQRConclusion A tau r) :
    ((n : Real) ^ strongRRQRExponent)⁻¹ ^ r *
        largeSingularProduct (Matrix.toEuclideanLin A) r <=
      ‖R.data.Kpiv.det‖ := by
  rw [← prod_singularValues_castLE_eq_largeSingularProduct A R.r_le_n]
  exact rrqrPivot_det_lower_selectedProduct A tau R

/-- The chosen uniform loss has precisely the direction needed by the
terminal lower bound: after paying it, Gram volume is bounded by the fixed
determinant factor times the canonical large-singular-value product.

This statement contains neither the RRQR output nor its selected row and
column sets.  The cutoff is definitionally the canonical threshold count of
the internally reindexed packet matrix. -/
theorem exp_neg_terminalUniformValueLoss_mul_gramVolume_le
    (cook : CookDeformedSquareInput) {W Kz : Nat} (hW : 0 < W)
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex) :
    Real.exp (-terminalUniformValueLoss cook W Kz) * gramVolume Q <=
      terminalUniformDeterminantFactor cook W Kz *
        largeSingularProduct (Matrix.toEuclideanLin (packetOuterFinMatrix Q))
          (packetLargeSingularValueCount Q
            (terminalCanonicalThreshold W Kz)) := by
  let d := terminalUniformDeterminantFactor cook W Kz
  let g := terminalUniformGramThresholdFactor W Kz
  let A := packetOuterFinMatrix Q
  let tau := terminalCanonicalThreshold W Kz
  let P := largeSingularProduct (Matrix.toEuclideanLin A)
    (largeSingularValueCount A tau)
  have hd : 0 < d := terminalUniformDeterminantFactor_pos cook hW
  have hg : 0 < g := terminalUniformGramThresholdFactor_pos hW
  have htau : 1 <= tau :=
    terminalCanonicalThreshold_one_le (Nat.one_le_iff_ne_zero.mpr hW.ne')
  have hvolumeA : gramVolume A <= g * P := by
    simpa [g, terminalUniformGramThresholdFactor, A, tau, P] using
      gramVolume_le_threshold_factor_mul_canonicalLargeSingularProduct A tau htau
  have hvolume : gramVolume Q <= g * P := by
    rw [← gramVolume_packetOuterFinMatrix Q]
    exact hvolumeA
  have hloss : -Real.log d + Real.log g <=
      terminalUniformValueLoss cook W Kz := by
    exact le_max_right _ _
  have hexp : Real.exp (-terminalUniformValueLoss cook W Kz) * g <= d := by
    have hneg : -terminalUniformValueLoss cook W Kz <=
        Real.log d - Real.log g := by linarith
    have hraw := Real.exp_le_exp.mpr hneg
    have hcancel : Real.exp (Real.log d - Real.log g) * g = d := by
      rw [Real.exp_sub, Real.exp_log hd, Real.exp_log hg]
      field_simp
    calc
      Real.exp (-terminalUniformValueLoss cook W Kz) * g <=
          Real.exp (Real.log d - Real.log g) * g :=
        mul_le_mul_of_nonneg_right hraw hg.le
      _ = d := hcancel
  have hP : 0 <= P := largeSingularProduct_nonneg _ _
  calc
    Real.exp (-terminalUniformValueLoss cook W Kz) * gramVolume Q <=
        Real.exp (-terminalUniformValueLoss cook W Kz) * (g * P) :=
      mul_le_mul_of_nonneg_left hvolume (Real.exp_nonneg _)
    _ = (Real.exp (-terminalUniformValueLoss cook W Kz) * g) * P := by ring
    _ <= d * P := mul_le_mul_of_nonneg_right hexp hP
    _ = terminalUniformDeterminantFactor cook W Kz *
        largeSingularProduct (Matrix.toEuclideanLin (packetOuterFinMatrix Q))
          (packetLargeSingularValueCount Q
            (terminalCanonicalThreshold W Kz)) := rfl

end BernoulliSection9
