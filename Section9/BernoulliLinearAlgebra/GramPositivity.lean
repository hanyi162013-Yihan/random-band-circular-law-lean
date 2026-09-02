import BernoulliLinearAlgebra.BoundaryVolume
import Mathlib.Analysis.Matrix.PosDef

/-!
# Strict positivity of Gram energies and coefficient norms

Section 9.5 takes square roots of Gram determinants and uses positive lower
coefficient comparisons.  This file records that these Gram quantities are
never zero.  In fact, the degree-zero compound contributes exactly one, so
`gramEnergy A ≥ 1` for every finite complex square matrix.
-/

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.Frobenius

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix Set Set.powersetCard

section Gram

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `I + Aᴴ A` is positive definite. -/
theorem one_add_gram_posDef (A : Matrix ι ι ℂ) :
    (1 + Aᴴ * A).PosDef :=
  Matrix.PosDef.one.add_posSemidef
    (Matrix.posSemidef_conjTranspose_mul_self A)

/-- The complex Gram determinant is strictly positive in the standard
`ComplexOrder`. -/
theorem det_one_add_gram_pos (A : Matrix ι ι ℂ) :
    (0 : ℂ) < det (1 + Aᴴ * A) :=
  (one_add_gram_posDef A).det_pos

section DegreeZero

variable [LinearOrder ι]

/-- The degree-zero compound has squared Frobenius energy one. -/
theorem compoundEnergyReal_zero (A : Matrix ι ι ℂ) :
    compoundEnergyReal 0 A = 1 := by
  let emptySubset : powersetCard ι 0 := ⟨∅, rfl⟩
  have hunique (s : powersetCard ι 0) : s = emptySubset := by
    apply Subtype.ext
    exact Finset.card_eq_zero.mp s.prop
  rw [compoundEnergyReal_eq_sum_normSq,
    Fintype.sum_eq_single emptySubset]
  · rw [Fintype.sum_eq_single emptySubset]
    · simp [minor]
    · intro t ht
      exact (ht (hunique t)).elim
  · intro s hs
    exact (hs (hunique s)).elim

/-- Strong positivity: the Gram energy is at least its degree-zero term. -/
theorem one_le_gramEnergy (A : Matrix ι ι ℂ) : 1 ≤ gramEnergy A := by
  rw [gramEnergy_eq_sum_compoundEnergyReal]
  calc
    1 = compoundEnergyReal 0 A := (compoundEnergyReal_zero A).symm
    _ ≤ ∑ k ∈ Finset.range (Fintype.card ι + 1),
        compoundEnergyReal k A := by
      exact Finset.single_le_sum
        (fun k _ ↦ sq_nonneg ‖compound k A‖) (by simp)

end DegreeZero

/-- The real Gram energy is strictly positive.  This also follows from
`one_le_gramEnergy`; the proof here records the positive-definite determinant
argument used in Section 9.5. -/
theorem gramEnergy_pos (A : Matrix ι ι ℂ) : 0 < gramEnergy A := by
  simpa only [gramEnergy] using (Complex.pos_iff.mp (det_one_add_gram_pos A)).1

/-- The square-root Gram volume is strictly positive. -/
theorem gramVolume_pos (A : Matrix ι ι ℂ) : 0 < gramVolume A := by
  exact Real.sqrt_pos.2 (gramEnergy_pos A)

/-- A positive multiple of a Gram volume cannot have a zero upper target. -/
theorem coefficient_pos_of_gramVolume_lower
    (A : Matrix ι ι ℂ) {lower coefficient : ℝ}
    (hlower : 0 < lower)
    (hbound : lower * gramVolume A ≤ coefficient) :
    0 < coefficient :=
  (mul_pos hlower (gramVolume_pos A)).trans_le hbound

end Gram

section Terminal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The terminal coefficient norm is automatically positive under the lower
half of `TerminalCoefficientComparison`. -/
theorem TerminalCoefficientComparison.coefficient_pos
    {F : Matrix ι ι ℂ → ℝ} {K : ℝ}
    (h : TerminalCoefficientComparison F K) (Q : Matrix ι ι ℂ) :
    0 < F Q := by
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one h.one_le
  exact coefficient_pos_of_gramVolume_lower Q (inv_pos.mpr hK) (h.lower Q)

end Terminal

section Boundary

variable {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]

local instance boundaryPositivitySumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift'
    (fun x : W ⊕ W => (toLex x : W ⊕ₗ W)) toLex.injective

/-- Positivity corollary for the complete dense-chart boundary comparison in
Section 9.5. -/
theorem boundary_coefficient_pos_on_chart
    (Θ11 Θ12 Θ21 Θ22 : Matrix W W ℂ)
    (E : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (boundaryCoefficient : ℝ)
    (terminalCoefficient : Matrix (W ⊕ W) (W ⊕ W) ℂ → ℝ)
    (Kc Ke : ℝ) (h11 : IsUnit Θ11.det)
    (hE : ExteriorConditioning E Ke)
    (hTerminal : TerminalCoefficientComparison terminalCoefficient Kc)
    (hScale : boundaryCoefficient = ‖Θ11.det‖ *
      terminalCoefficient (E * boundaryGraphS Θ11 Θ12 Θ21 Θ22)) :
    0 < boundaryCoefficient := by
  have hbounds := boundary_coefficient_volume_on_chart
    Θ11 Θ12 Θ21 Θ22 E boundaryCoefficient terminalCoefficient
    Kc Ke h11 hE hTerminal hScale
  have hKc : 0 < Kc := lt_of_lt_of_le zero_lt_one hTerminal.one_le
  have hKe : 0 < Ke := lt_of_lt_of_le zero_lt_one hE.one_le
  exact coefficient_pos_of_gramVolume_lower
    (boundaryRelation Θ11 Θ12 Θ21 Θ22)
    (inv_pos.mpr (mul_pos hKc hKe)) hbounds.1

end Boundary

end BernoulliLinearAlgebra
