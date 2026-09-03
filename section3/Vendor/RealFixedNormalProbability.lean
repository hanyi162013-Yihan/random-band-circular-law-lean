/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealFixedNormalProbability.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RealNetProbability
import Vendor.RealNormalNetEvents
import Vendor.AnisotropicMesh
import Vendor.ModelNumerics

/-! Closing the anisotropic net union in the actual real-entry model. -/

noncomputable section
open MeasureTheory LivshytsProjectionFormalization
open scoped ENNReal BigOperators
namespace HighBandLSV.RealFixedNormalProbability
open HighBandLSV.Anisotropic

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem fixed_probability {N J W r : Nat} {c C rho A h d K : Real}
    (m : RealBandModel N W c C rho) (hGBL : RealFiniteGeometricBrascampLieb)
    (hrho : 0 < rho) (hc : 0 < c) (hW : 0 < W) (hN : 1 ≤ N)
    (hA : 1024 ≤ A) (hAone : 2 * (Real.exp 1 * rho) / Real.sqrt c ≤ A)
    (hAtwo : 8 * (Real.exp 1 * rho ^ 2) / c ≤ A)
    (hh : 0 < h) (hh1 : h ≤ 1) (hhd : h ≤ d) (hK : 0 ≤ K)
    (p : BlockGeometry.Partition N J) (hband : PathGeometry.LocalBand p W)
    (hJ : 0 < J) (hm : ∀ j, r ≤ (p.blocks j).card)
    (net : System p h) (i : Fin N) (k l : Fin J)
    (sel : BlockGeometry.RowSelection p i r)
    (hmesh : h * Real.sqrt J ≤ 1 / 4) (herror : Real.sqrt J * h * K ≤ d)
    (hend : ∀ q : RealNormalNetEvents.EndpointLabels h d k l,
      labelWeight (q.val k).val / labelWeight (q.val l).val ≤ A * (K + 1) * J * d)
    (z : Complex) :
    m.law ((fun omega => shifted (m.matrix omega) z) ⁻¹'
      NormalNetEvents.fixedBad p i k l K d) ≤
      ENNReal.ofReal (RealRawBound.fixedEnvelope N J r A W h d K) := by
  let Q := RealNormalNetEvents.EndpointLabels h d k l
  have hcover : (fun omega => shifted (m.matrix omega) z) ⁻¹'
      NormalNetEvents.fixedBad p i k l K d ⊆
      ⋃ q : Q, ⋃ v : net.Centers q.val,
        (fun omega => shifted (m.matrix omega) z) ⁻¹'
          NormalNetEvents.constraint (net.vector q.val v) sel.allRows d := by
    intro omega homega
    have h := RealNormalNetEvents.fixedBad_subset_net_union p net i k l sel
      hJ hh hK hhd hmesh herror homega
    simpa only [Set.mem_iUnion, Set.mem_preimage] using h
  apply (measure_mono hcover).trans
  exact RealNetProbability.label_union_bound m hGBL hrho hc hW hN hA hAone hAtwo
    hh hh1 hhd hK p hband hm (NeighborPath.between k l) net sel
    (fun q : Q => q.val) (RealNormalNetEvents.endpoint_labels_card k l hh hh1) hend z

theorem actual_fixed_probability {N J W r : Nat} {c C rho A kappa C1 K : Real}
    (m : RealBandModel N W c C rho) (hGBL : RealFiniteGeometricBrascampLieb)
    (hrho : 0 < rho) (hc : 0 < c) (hW : 0 < W) (hN : 1 ≤ N)
    (hA : 1024 ≤ A) (hAone : 2 * (Real.exp 1 * rho) / Real.sqrt c ≤ A)
    (hAtwo : 8 * (Real.exp 1 * rho ^ 2) / c ≤ A)
    (hC1 : 0 < C1) (hAC1 : 4 * C1 ≤ A) (hK : 0 ≤ K)
    (p : BlockGeometry.Partition N J) (hband : PathGeometry.LocalBand p W)
    (hJ : 0 < J) (hm : ∀ j, r ≤ (p.blocks j).card)
    (i : Fin N) (k l : Fin J) (sel : BlockGeometry.RowSelection p i r)
    (hh1 : mesh N W kappa J C1 K ≤ 1)
    (hhd : mesh N W kappa J C1 K ≤ delta N W kappa)
    (hmesh : mesh N W kappa J C1 K * Real.sqrt J ≤ 1 / 4)
    (herror : Real.sqrt J * mesh N W kappa J C1 K * K ≤ delta N W kappa)
    (z : Complex) :
    m.law ((fun omega => shifted (m.matrix omega) z) ⁻¹'
      NormalNetEvents.fixedBad p i k l K (delta N W kappa)) ≤
      ENNReal.ofReal ((N : Real) ^ (r * J) * rawFixedBound N J r W kappa A C1 K) := by
  have hh : 0 < mesh N W kappa J C1 K :=
    mesh_pos (by exact_mod_cast hJ) hC1 (by linarith)
  let net := chooseSystem p (mesh N W kappa J C1 K) hh
  have hend : ∀ q : RealNormalNetEvents.EndpointLabels
      (mesh N W kappa J C1 K) (delta N W kappa) k l,
      labelWeight (q.val k).val / labelWeight (q.val l).val ≤
        A * (K + 1) * J * delta N W kappa := by
    intro q
    exact RealNetCost.actual_endpoint_bound (Nat.cast_nonneg N)
      (by exact_mod_cast hW) (by exact_mod_cast hJ) hC1 hK hAC1
      (labelWeight_pos hh (q.val k).val).le q.property.1 q.property.2
  apply (fixed_probability m hGBL hrho hc hW hN hA hAone hAtwo hh hh1 hhd hK
    p hband hJ hm net i k l sel hmesh herror hend z).trans
  exact ENNReal.ofReal_le_ofReal
    (RealRawBound.actual_fixedEnvelope_le_raw N J r hA (Nat.cast_nonneg W) hK hh)

/-- The final finite union over the excluded column and the two endpoint blocks. -/
theorem bad_normals_union {Omega : Type*} [MeasurableSpace Omega]
    {N J : Nat} (mu : Measure Omega) (X : Omega → NormalEvents.Mat N)
    (p : BlockGeometry.Partition N J) {K d B : Real} (hJ : 0 < J) (hd : 0 < d)
    (hfixed : ∀ (i : Fin N) (k l : Fin J),
      mu (X ⁻¹' NormalNetEvents.fixedBad p i k l K d) ≤ ENNReal.ofReal B) :
    mu (X ⁻¹' (NormalNetEvents.columnCap K \ NormalNetEvents.normalSpread p d)) ≤
      ENNReal.ofReal ((N : Real) * J * J * B) := by
  have hcover : X ⁻¹' (NormalNetEvents.columnCap K \ NormalNetEvents.normalSpread p d) ⊆
      ⋃ i : Fin N, ⋃ k : Fin J, ⋃ l : Fin J, X ⁻¹' NormalNetEvents.fixedBad p i k l K d := by
    intro omega homega
    have h := NormalNetEvents.normal_cover p hJ (K := K) hd homega
    simpa only [Set.mem_iUnion, Set.mem_preimage] using h
  have h1 := fun (i : Fin N) (k : Fin J) =>
    FiniteProbability.finite_union mu (fun l : Fin J =>
      X ⁻¹' NormalNetEvents.fixedBad p i k l K d) (hfixed i k)
  have h2 := fun (i : Fin N) =>
    FiniteProbability.finite_union mu (fun k : Fin J =>
      ⋃ l : Fin J, X ⁻¹' NormalNetEvents.fixedBad p i k l K d) (h1 i)
  have h3 := FiniteProbability.finite_union mu (fun i : Fin N =>
    ⋃ k : Fin J, ⋃ l : Fin J, X ⁻¹' NormalNetEvents.fixedBad p i k l K d) h2
  apply (measure_mono hcover).trans
  simpa only [Fintype.card_fin, mul_assoc] using h3

end HighBandLSV.RealFixedNormalProbability

#print axioms HighBandLSV.RealFixedNormalProbability.actual_fixed_probability
#print axioms HighBandLSV.RealFixedNormalProbability.bad_normals_union

