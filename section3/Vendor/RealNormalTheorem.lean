/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealNormalTheorem.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RealFixedNormalProbability
import Vendor.MeshParameters

/-! The actual real model satisfies the exponentially small bad-normal bound. -/

noncomputable section
open MeasureTheory LivshytsProjectionFormalization
open scoped ENNReal
namespace HighBandLSV

theorem real_bad_normals_from_numerics
    {N J W r : Nat} {c C rho kappa R Kz A C1 cmain Cw : Real}
    (m : RealBandModel N W c C rho) (hGBL : RealFiniteGeometricBrascampLieb)
    (p : BlockGeometry.Partition N J) (hband : PathGeometry.LocalBand p W)
    (hsize : ∀ j, r + 1 ≤ (p.blocks j).card)
    (num : NumericalCertificate N J r W kappa R Kz A C1 cmain Cw)
    (entropy : CorrectedSection5NumericalConditions N W kappa J 28 cmain)
    (hc : 0 < c) (hrho : 0 < rho) (hA : 1024 ≤ A)
    (hAone : 2 * (Real.exp 1 * rho) / Real.sqrt c ≤ A)
    (hAtwo : 8 * (Real.exp 1 * rho ^ 2) / c ≤ A)
    (hC1 : 4 ≤ C1) (hAC1 : 4 * C1 ≤ A) (z : Complex) :
    m.law ((fun omega => shifted (m.matrix omega) z) ⁻¹'
      (NormalNetEvents.columnCap (hsCap N R Kz) \ NormalNetEvents.normalSpread p (delta N W kappa))) ≤
      ENNReal.ofReal (Real.exp (-(N : Real) ^ (1 + kappa / 4))) := by
  let K := hsCap N R Kz
  have hK : 0 ≤ K := by
    dsimp [K, hsCap]
    exact mul_nonneg (by linarith [num.R_nonneg, num.Kz_nonneg]) (Real.sqrt_nonneg _)
  have hJ : (1 : Real) ≤ J := by exact_mod_cast num.J_pos
  have hN : 1 ≤ N := num.N_pos
  have hW : 0 < W := by exact_mod_cast entropy.W_pos
  have hm : ∀ j, r ≤ (p.blocks j).card := by
    intro j
    have := hsize j
    omega
  obtain ⟨hh, hhd, hh1, _, herror⟩ :=
    MeshParameters.actual_mesh_bounds (kappa := kappa) (Nat.cast_nonneg N)
      entropy.W_pos hJ (by linarith : 2 ≤ C1) hK
  have hquarter := Anisotropic.actual_mesh_quarter (kappa := kappa)
    (Nat.cast_nonneg N) entropy.W_pos hJ hC1 hK
  have hfixed : ∀ (i : Fin N) (k l : Fin J),
      m.law ((fun omega => shifted (m.matrix omega) z) ⁻¹'
        NormalNetEvents.fixedBad p i k l K (delta N W kappa)) ≤
      ENNReal.ofReal ((N : Real) ^ (r * J) * rawFixedBound N J r W kappa A C1 K) := by
    intro i k l
    exact RealFixedNormalProbability.actual_fixed_probability m hGBL hrho hc hW hN
      hA hAone hAtwo num.C1_pos hAC1 hK p hband num.J_pos hm i k l
      (BlockGeometry.chooseRows p i r hsize) hh1 hhd hquarter herror z
  apply (RealFixedNormalProbability.bad_normals_union m.law
    (fun omega => shifted (m.matrix omega) z) p num.J_pos (delta_pos _ _ _) hfixed).trans
  apply ENNReal.ofReal_le_ofReal
  simpa only [K, mul_assoc] using certificate_dimension_loss_union num entropy

end HighBandLSV

#print axioms HighBandLSV.real_bad_normals_from_numerics

