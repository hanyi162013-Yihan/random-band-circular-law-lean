import BernoulliLinearAlgebra.ConcreteBoundaryGlobal
import BernoulliLinearAlgebra.ThreeBlockShiftTranslation
import BernoulliLinearAlgebra.ChartPerturbation

/-!
# Squarefree support of the global boundary determinant

The literal five-block determinant is multiaffine in the seven fresh packet
blocks.  On the chart where the upper-left boundary block is invertible, this
follows from the concrete second elimination and the already proved
squarefree support of the three-block terminal determinant.  Perturbing only
that upper-left block and using coefficientwise continuity removes the chart
assumption.

Consequently, `globalBoundaryCoeffVector` contains every nonzero coefficient
of `globalBoundaryDetPolynomial`, rather than merely a selected family of
coefficients.
-/

open Filter Topology
open scoped Matrix Topology

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix MvPolynomial

section ElementarySupport

variable {v : Type*} [Fintype v] [DecidableEq v]

/-- A polynomial reconstructed from squarefree coefficients has squarefree
support. -/
theorem hasSquarefreeSupport_squarefreePolynomial (c : CoeffSpace v) :
    HasSquarefreeSupport (squarefreePolynomial c) := by
  intro m hm
  simp only [squarefreePolynomial, coeff_sum, coeff_monomial]
  apply Finset.sum_eq_zero
  intro S _
  rw [if_neg]
  exact fun h => hm ⟨S, h.symm⟩

omit [Fintype v] in
/-- Multiplication by a constant polynomial preserves squarefree support. -/
theorem hasSquarefreeSupport_C_mul (a : ℂ) (p : MvPolynomial v ℂ)
    (hp : HasSquarefreeSupport p) :
    HasSquarefreeSupport (C a * p) := by
  intro m hm
  rw [MvPolynomial.coeff_C_mul, hp m hm, mul_zero]

end ElementarySupport

section ShiftedTerminalSupport

variable {w : Type*} [Fintype w] [DecidableEq w]

/-- The actual three-block determinant has squarefree support at every
spectral parameter, not only at zero shift. -/
theorem hasSquarefreeSupport_threeBlockDetPolynomial
    (Q : Matrix (ThreeBlockOuter w) (ThreeBlockOuter w) ℂ) (z : ℂ) :
    HasSquarefreeSupport (threeBlockDetPolynomial Q z) := by
  rw [threeBlockDetPolynomial_eq_translatePolynomialList,
    threeBlockDetPolynomial_zero_eq_squarefreePolynomial,
    translatePolynomialList_squarefreePolynomial]
  exact hasSquarefreeSupport_squarefreePolynomial _

end ShiftedTerminalSupport

section GlobalBoundarySupport

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Squarefree support of the literal five-block determinant on the
upper-left-invertible chart. -/
theorem hasSquarefreeSupport_globalBoundaryDetPolynomial_of_isUnit
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (h11 : IsUnit Theta.toBlocks₁₁.det) :
    HasSquarefreeSupport (globalBoundaryDetPolynomial z CL BR Theta) := by
  change HasSquarefreeSupport
    ((threeBlockConcreteKPolynomialShifted z CL BR
      Theta.toBlocks₁₁ Theta.toBlocks₁₂
      Theta.toBlocks₂₁ Theta.toBlocks₂₂).det)
  rw [threeBlockConcreteKPolynomialShifted_det_eq z CL BR
    Theta.toBlocks₁₁ Theta.toBlocks₁₂
    Theta.toBlocks₂₁ Theta.toBlocks₂₂ h11]
  apply hasSquarefreeSupport_C_mul
  exact hasSquarefreeSupport_threeBlockDetPolynomial _ z

/-- The global literal five-block determinant is squarefree for every
boundary matrix.  No invertibility assumption on the full matrix or on its
upper-left block remains. -/
theorem hasSquarefreeSupport_globalBoundaryDetPolynomial
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    HasSquarefreeSupport (globalBoundaryDetPolynomial z CL BR Theta) := by
  intro m hm
  rcases exists_scalarPerturbationSequence (upperLeftBlock Theta) with
    ⟨eps, heps0, hepsGood⟩
  let ThetaSeq : ℕ → Matrix (W ⊕ W) (W ⊕ W) ℂ :=
    fun q => upperLeftPerturb Theta (eps q)
  have hThetaSeq : Tendsto ThetaSeq atTop (nhds Theta) := by
    change Tendsto (upperLeftPerturb Theta ∘ eps) atTop (nhds Theta)
    have h := (continuous_upperLeftPerturb Theta).continuousAt.tendsto.comp
      heps0
    simpa only [upperLeftPerturb_zero] using h
  have hcoeffContinuous : Continuous (fun T : Matrix (W ⊕ W) (W ⊕ W) ℂ =>
      coeff m (globalBoundaryDetPolynomial z CL BR T)) :=
    (coeffwiseContinuous_globalBoundaryDetPolynomial z CL BR) m
  have hcoeff : Tendsto
      (fun q => coeff m (globalBoundaryDetPolynomial z CL BR (ThetaSeq q)))
      atTop (nhds (coeff m (globalBoundaryDetPolynomial z CL BR Theta))) :=
    hcoeffContinuous.continuousAt.tendsto.comp hThetaSeq
  have hzero (q : ℕ) :
      coeff m (globalBoundaryDetPolynomial z CL BR (ThetaSeq q)) = 0 := by
    have hunit : IsUnit (ThetaSeq q).toBlocks₁₁.det := by
      change IsUnit (upperLeftBlock (ThetaSeq q)).det
      rw [show upperLeftBlock (ThetaSeq q) =
          scalarPerturb (upperLeftBlock Theta) (eps q) by
        simp [ThetaSeq, upperLeftBlock_upperLeftPerturb]]
      exact isUnit_iff_ne_zero.mpr (hepsGood q)
    exact (hasSquarefreeSupport_globalBoundaryDetPolynomial_of_isUnit
      z CL BR (ThetaSeq q) hunit) m hm
  have hzeroLimit : Tendsto
      (fun q => coeff m (globalBoundaryDetPolynomial z CL BR (ThetaSeq q)))
      atTop (nhds 0) := by
    exact tendsto_const_nhds.congr (fun q => (hzero q).symm)
  exact tendsto_nhds_unique hcoeff hzeroLimit

/-- Exact reconstruction from `globalBoundaryCoeffVector`.  In particular,
that finite vector contains all coefficients of the global boundary
determinant. -/
theorem globalBoundaryDetPolynomial_eq_squarefreePolynomial
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    globalBoundaryDetPolynomial z CL BR Theta =
      squarefreePolynomial (globalBoundaryCoeffVector z CL BR Theta) := by
  symm
  simpa [globalBoundaryCoeffVector] using
    (squarefreePolynomial_coefficients_eq
      (globalBoundaryDetPolynomial z CL BR Theta)
      (hasSquarefreeSupport_globalBoundaryDetPolynomial z CL BR Theta))

end GlobalBoundarySupport

end BernoulliLinearAlgebra
