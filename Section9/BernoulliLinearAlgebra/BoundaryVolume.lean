import BernoulliLinearAlgebra.BoundaryGram
import BernoulliLinearAlgebra.TransferCoordinate
import BernoulliLinearAlgebra.VolumeComparison
import Mathlib.Tactic

/-!
# Boundary coefficient and Gram-volume comparison

This file closes the deterministic chain in Section 9.5 on the chart
`det Θ₁₁ ≠ 0`.  The exact graph Gram identity first gives

`‖det Θ₁₁‖ * gramVolume (S Θ) = gramVolume Θ`.

Combining this with the terminal all-minor estimate and removal of the left
endpoint matrix `E` makes the factor `‖det Θ₁₁‖` cancel exactly.  The terminal
coefficient estimate is represented by `TerminalCoefficientComparison`; it
can be supplied by the mask-expansion results in `MaskCoefficient`.
-/

open scoped Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix

section GraphVolume

variable {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]

-- The exterior-power implementation needs a linear order on the doubled
-- index.  We use the lexicographic sum order.
local instance graphSumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift'
    (fun x : W ⊕ W => (toLex x : W ⊕ₗ W)) toLex.injective

omit [LinearOrder W] in
/-- The coordinate map in Section 9.4 is the graph map used in Section 9.5. -/
theorem boundaryGraphS_eq_transferCoordinateMap
    (Θ11 Θ12 Θ21 Θ22 : Matrix W W ℂ) :
    boundaryGraphS Θ11 Θ12 Θ21 Θ22 =
      transferCoordinateMap Θ11 Θ12 Θ21 Θ22 := rfl

omit [LinearOrder W] in
/-- Real-energy form of the exact boundary graph Gram determinant identity. -/
theorem boundaryGraph_gramEnergy
    (Θ11 Θ12 Θ21 Θ22 : Matrix W W ℂ)
    (h11 : IsUnit Θ11.det) :
    ‖Θ11.det‖ ^ 2 *
        gramEnergy (boundaryGraphS Θ11 Θ12 Θ21 Θ22) =
      gramEnergy (boundaryRelation Θ11 Θ12 Θ21 Θ22) := by
  have hdet := explicit_boundary_gram_determinant_normSq
    Θ11 Θ12 Θ21 Θ22 h11
  have hre := congrArg Complex.re hdet
  simpa [gramEnergy, Complex.sq_norm] using hre

/-- Square-root form of the graph Gram identity.  This is the exact
`‖det Θ₁₁‖` cancellation used in Section 9.5. -/
theorem boundaryGraph_gramVolume
    (Θ11 Θ12 Θ21 Θ22 : Matrix W W ℂ)
    (h11 : IsUnit Θ11.det) :
    ‖Θ11.det‖ *
        gramVolume (boundaryGraphS Θ11 Θ12 Θ21 Θ22) =
      gramVolume (boundaryRelation Θ11 Θ12 Θ21 Θ22) := by
  have henergy := boundaryGraph_gramEnergy Θ11 Θ12 Θ21 Θ22 h11
  have hs := gramVolume_sq (boundaryGraphS Θ11 Θ12 Θ21 Θ22)
  have ht := gramVolume_sq (boundaryRelation Θ11 Θ12 Θ21 Θ22)
  have hsquare :
      (‖Θ11.det‖ *
        gramVolume (boundaryGraphS Θ11 Θ12 Θ21 Θ22)) ^ 2 =
          gramVolume (boundaryRelation Θ11 Θ12 Θ21 Θ22) ^ 2 := by
    rw [mul_pow, hs, ht]
    exact henergy
  exact (sq_eq_sq₀
    (mul_nonneg (norm_nonneg _)
      (gramVolume_nonneg (boundaryGraphS Θ11 Θ12 Θ21 Θ22)))
    (gramVolume_nonneg (boundaryRelation Θ11 Θ12 Θ21 Θ22))).mp hsquare

end GraphVolume

section TerminalComparison

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- Uniform coefficient-versus-Gram-volume bounds for the normalized
terminal polynomial.  Lemma 7.5 supplies this structure after the finite mask
and affine-translation losses have been bounded by one common constant. -/
structure TerminalCoefficientComparison
    (F : Matrix ι ι ℂ → ℝ) (K : ℝ) : Prop where
  one_le : 1 ≤ K
  lower : ∀ Q, K⁻¹ * gramVolume Q ≤ F Q
  upper : ∀ Q, F Q ≤ K * gramVolume Q

end TerminalComparison

section BoundaryComparison

variable {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]

local instance boundarySumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift'
    (fun x : W ⊕ W => (toLex x : W ⊕ₗ W)) toLex.injective

/-- Section 9.5 on the dense chart.  If the boundary coefficient norm is
`‖det Θ₁₁‖` times the terminal coefficient at `E S(Θ)`, the terminal
all-minor comparison and the exterior conditioning of `E` imply the desired
two-sided comparison with the boundary Gram volume. -/
theorem boundary_coefficient_volume_on_chart
    (Θ11 Θ12 Θ21 Θ22 : Matrix W W ℂ)
    (E : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (boundaryCoefficient : ℝ)
    (terminalCoefficient : Matrix (W ⊕ W) (W ⊕ W) ℂ → ℝ)
    (Kc Ke : ℝ) (h11 : IsUnit Θ11.det)
    (hE : ExteriorConditioning E Ke)
    (hTerminal : TerminalCoefficientComparison terminalCoefficient Kc)
    (hScale : boundaryCoefficient = ‖Θ11.det‖ *
      terminalCoefficient (E * boundaryGraphS Θ11 Θ12 Θ21 Θ22)) :
    (Kc * Ke)⁻¹ *
        gramVolume (boundaryRelation Θ11 Θ12 Θ21 Θ22) ≤
      boundaryCoefficient ∧
    boundaryCoefficient ≤ (Kc * Ke) *
      gramVolume (boundaryRelation Θ11 Θ12 Θ21 Θ22) := by
  let S := boundaryGraphS Θ11 Θ12 Θ21 Θ22
  let Θ := boundaryRelation Θ11 Θ12 Θ21 Θ22
  have hgraph : ‖Θ11.det‖ * gramVolume S = gramVolume Θ := by
    simpa [S, Θ] using boundaryGraph_gramVolume Θ11 Θ12 Θ21 Θ22 h11
  have hremove := gramVolume_remove_left hE (S := S)
  have hKcInv : 0 ≤ Kc⁻¹ :=
    inv_nonneg.mpr (le_trans zero_le_one hTerminal.one_le)
  have hKc : 0 ≤ Kc := le_trans zero_le_one hTerminal.one_le
  have hdet : 0 ≤ ‖Θ11.det‖ := norm_nonneg _
  constructor
  · rw [hScale]
    calc
      (Kc * Ke)⁻¹ * gramVolume Θ =
          ‖Θ11.det‖ * (Kc⁻¹ * (Ke⁻¹ * gramVolume S)) := by
            rw [← hgraph, _root_.mul_inv_rev]
            ring
      _ ≤ ‖Θ11.det‖ * (Kc⁻¹ * gramVolume (E * S)) := by
        gcongr
        exact hremove.1
      _ ≤ ‖Θ11.det‖ * terminalCoefficient (E * S) := by
        gcongr
        exact hTerminal.lower _
  · rw [hScale]
    calc
      ‖Θ11.det‖ * terminalCoefficient (E * S) ≤
          ‖Θ11.det‖ * (Kc * gramVolume (E * S)) := by
        gcongr
        exact hTerminal.upper _
      _ ≤ ‖Θ11.det‖ * (Kc * (Ke * gramVolume S)) := by
        gcongr
        exact hremove.2
      _ = (Kc * Ke) * gramVolume Θ := by rw [← hgraph]; ring

end BoundaryComparison

end BernoulliLinearAlgebra
