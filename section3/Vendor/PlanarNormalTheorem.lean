/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/PlanarNormalTheorem.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.FixedNormalProbability
import Vendor.ModelNumerics
import Vendor.ModelPartition
import Vendor.MeshParameters

/-! The exponentially small bad-normal probability proved from the entry model. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HighBandLSV

theorem planar_bad_normals_from_numerics
    {N J W r : Nat} {c C L kappa R Kz A C1 cmain Cw : Real}
    (m : PlanarBandModel N W c C L) (p : BlockGeometry.Partition N J)
    (hband : PathGeometry.LocalBand p W) (hsize : ∀ j, r + 1 ≤ (p.blocks j).card)
    (num : NumericalCertificate N J r W kappa R Kz A C1 cmain Cw)
    (entropy : CorrectedSection5NumericalConditions N W kappa J 28 cmain)
    (hc : 0 < c) (hL : 0 ≤ L) (hA25 : 25 ≤ A) (hA : Real.pi * L / c ≤ A)
    (hC1 : 2 ≤ C1) (z : Complex) :
    m.law ((fun omega => shifted (m.matrix omega) z) ⁻¹'
      (NormalNetEvents.columnCap (hsCap N R Kz) \
        NormalNetEvents.normalSpread p (delta N W kappa))) ≤
      ENNReal.ofReal (Real.exp (-(N : Real) ^ (1 + kappa / 4))) := by
  have hW : 0 < W := by exact_mod_cast num.entropy.W_pos
  have hJ : (1 : Real) ≤ J := by exact_mod_cast num.J_pos
  have hK0 : 0 ≤ R + Kz + 1 := by linarith [num.R_nonneg, num.Kz_nonneg]
  have hK : 0 ≤ hsCap N R Kz := by unfold hsCap; positivity
  have hmesh := MeshParameters.actual_mesh_bounds (kappa := kappa) (Nat.cast_nonneg N)
    num.entropy.W_pos hJ hC1 hK
  have hA1 : 1 ≤ A := by linarith
  have hb := FixedNormalProbability.bad_normal_probability m p hband z
    num.N_pos num.J_pos hc hW hL hA1 hA hmesh.1 hmesh.2.2.1 hK hmesh.2.1 hsize
    hmesh.2.2.2.1 hmesh.2.2.2.2
  have hd1 : delta N W kappa ≤ 1 := by
    unfold delta
    apply Real.exp_le_one_iff.mpr
    have hscale : 0 ≤ Section5Formalization.section5Scale N W kappa := by
      unfold Section5Formalization.section5Scale
      positivity
    exact neg_nonpos.mpr hscale
  have hraw : RadialRawBound.fixedEnvelope N J r A W
      (mesh N W kappa J C1 (hsCap N R Kz)) (delta N W kappa) ≤
        (N : Real) ^ (r * J) * rawFixedBound N J r W kappa A C1 (hsCap N R Kz) := by
    apply RadialRawBound.actual_fixedEnvelope_le_raw
    all_goals first | assumption | exact num.J_pos | exact num.entropy.W_pos |
      exact num.C1_pos | exact num.C_pos | positivity | linarith
  have hnum := certificate_dimension_loss_union num entropy
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    (N : Real) * J * J * RadialRawBound.fixedEnvelope N J r A W
        (mesh N W kappa J C1 (hsCap N R Kz)) (delta N W kappa) ≤
      (N : Real) * J * J * ((N : Real) ^ (r * J) *
        rawFixedBound N J r W kappa A C1 (hsCap N R Kz)) :=
          mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = ((N : Real) * J * J) * (N : Real) ^ (r * J) *
        rawFixedBound N J r W kappa A C1 (hsCap N R Kz) := by ring
    _ ≤ Real.exp (-(N : Real) ^ (1 + kappa / 4)) := hnum

end HighBandLSV

#print axioms HighBandLSV.planar_bad_normals_from_numerics

