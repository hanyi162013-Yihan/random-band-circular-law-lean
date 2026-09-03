/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealNetProbability.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RealNetCost

/-! Actual model probabilities for all centers and all anisotropic labels. -/

noncomputable section
open MeasureTheory LivshytsProjectionFormalization
open scoped BigOperators ENNReal
namespace HighBandLSV.RealNetProbability
open HighBandLSV.Anisotropic

theorem center_union_bound {N J W r : Nat} {c C rho A h d K : Real}
    (m : RealBandModel N W c C rho) (hGBL : RealFiniteGeometricBrascampLieb)
    (hrho : 0 < rho) (hc : 0 < c) (hW : 0 < W) (hN : 1 ≤ N)
    (hA : 1024 ≤ A) (hAone : 2 * (Real.exp 1 * rho) / Real.sqrt c ≤ A)
    (hAtwo : 8 * (Real.exp 1 * rho ^ 2) / c ≤ A)
    (hh : 0 < h) (hh1 : h ≤ 1) (hhd : h ≤ d)
    (p : BlockGeometry.Partition N J) (hband : PathGeometry.LocalBand p W)
    (hm : ∀ j, r ≤ (p.blocks j).card)
    {i : Fin N} {k l : Fin J} (path : NeighborPath.Path k l)
    (net : System p h) (q : Labels J h) (sel : BlockGeometry.RowSelection p i r)
    (hend : labelWeight (q k).val / labelWeight (q l).val ≤ A * (K + 1) * J * d)
    (z : Complex) :
    m.law (⋃ v : net.Centers q, (fun omega => shifted (m.matrix omega) z) ⁻¹'
      NormalNetEvents.constraint (net.vector q v) sel.allRows d) ≤
      ENNReal.ofReal ((1024 / h ^ 2) ^ N * (A * N * W * d ^ 2) ^ (r * J) *
        (A * (K + 1) * J * d) ^ r) := by
  have hA0 : 0 ≤ A := by linarith
  have hAN : A ≤ A * (N : Real) :=
    le_mul_of_one_le_right hA0 (by exact_mod_cast hN)
  have hAN1 : 1 ≤ A * (N : Real) := (by linarith : 1 ≤ A).trans hAN
  apply (RealTensorization.center_union_probability m hGBL hrho hc hW hAN1
    (hAone.trans hAN) (hAtwo.trans hAN) hh hhd p hband path net q sel z).trans
  exact ENNReal.ofReal_le_ofReal
    (RealNetCost.center_cost_bound p net path q hA (Nat.cast_nonneg W) hh hh1 hm hend)

theorem label_union_bound {N J W r : Nat} {c C rho A h d K : Real}
    (m : RealBandModel N W c C rho) (hGBL : RealFiniteGeometricBrascampLieb)
    (hrho : 0 < rho) (hc : 0 < c) (hW : 0 < W) (hN : 1 ≤ N)
    (hA : 1024 ≤ A) (hAone : 2 * (Real.exp 1 * rho) / Real.sqrt c ≤ A)
    (hAtwo : 8 * (Real.exp 1 * rho ^ 2) / c ≤ A)
    (hh : 0 < h) (hh1 : h ≤ 1) (hhd : h ≤ d) (hK : 0 ≤ K)
    (p : BlockGeometry.Partition N J) (hband : PathGeometry.LocalBand p W)
    (hm : ∀ j, r ≤ (p.blocks j).card)
    {i : Fin N} {k l : Fin J} (path : NeighborPath.Path k l)
    (net : System p h) (sel : BlockGeometry.RowSelection p i r)
    {Q : Type*} [Fintype Q] (q : Q → Labels J h)
    (hcard : (Fintype.card Q : Real) ≤ (5 / h) ^ (3 * J))
    (hend : ∀ s, labelWeight (q s k).val / labelWeight (q s l).val ≤
      A * (K + 1) * J * d) (z : Complex) :
    m.law (⋃ s : Q, ⋃ v : net.Centers (q s),
      (fun omega => shifted (m.matrix omega) z) ⁻¹'
        NormalNetEvents.constraint (net.vector (q s) v) sel.allRows d) ≤
      ENNReal.ofReal (RealRawBound.fixedEnvelope N J r A W h d K) := by
  let B := (1024 / h ^ 2) ^ N * (A * N * W * d ^ 2) ^ (r * J) *
    (A * (K + 1) * J * d) ^ r
  have hA0 : 0 ≤ A := by linarith
  have hd : 0 ≤ d := hh.le.trans hhd
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hu : m.law (⋃ s : Q, ⋃ v : net.Centers (q s),
      (fun omega => shifted (m.matrix omega) z) ⁻¹'
        NormalNetEvents.constraint (net.vector (q s) v) sel.allRows d) ≤
      ENNReal.ofReal ((Fintype.card Q : Real) * B) := by
    apply FiniteProbability.finite_union
    intro s
    exact center_union_bound m hGBL hrho hc hW hN hA hAone hAtwo hh hh1 hhd
      p hband hm path net (q s) sel (hend s) z
  apply hu.trans
  apply ENNReal.ofReal_le_ofReal
  simpa only [B, RealRawBound.fixedEnvelope, mul_assoc] using
    mul_le_mul_of_nonneg_right hcard hB

end HighBandLSV.RealNetProbability

#print axioms HighBandLSV.RealNetProbability.label_union_bound

