/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/AnisotropicMesh.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.MeshParameters

/-! The quarter-mesh threshold and the real anisotropic path endpoint ratio. -/

noncomputable section
namespace HighBandLSV.Anisotropic

theorem actual_mesh_quarter {N W kappa J C1 K : Real}
    (hN : 0 ≤ N) (hW : 0 < W) (hJ : 1 ≤ J) (hC1 : 4 ≤ C1) (hK : 0 ≤ K) :
    mesh N W kappa J C1 K * Real.sqrt J ≤ 1 / 4 := by
  have hJ0 : 0 < J := by linarith
  have hs : 0 < Real.sqrt J := Real.sqrt_pos.2 hJ0
  have hbase : 4 ≤ C1 * (K + 1) := by nlinarith
  have hbase0 : 0 < C1 * (K + 1) := by linarith
  have hd : delta N W kappa ≤ 1 := by
    unfold delta
    apply Real.exp_le_one_iff.mpr
    have hl : 0 ≤ Section5Formalization.section5Scale N W kappa := by
      unfold Section5Formalization.section5Scale
      positivity
    exact neg_nonpos.mpr hl
  have he : mesh N W kappa J C1 K * Real.sqrt J = delta N W kappa / (C1 * (K + 1)) := by
    unfold mesh
    field_simp
  rw [he]
  exact (div_le_iff₀ hbase0).2 (by nlinarith)

theorem actual_endpoint_ratio {N W kappa J C1 K wk wl : Real}
    (hJ : 0 < J) (hC1 : 0 < C1) (hK : 0 ≤ K) (hwk : 0 ≤ wk)
    (hsmall : wk ≤ delta N W kappa ^ 2)
    (hlarge : mesh N W kappa J C1 K / (4 * Real.sqrt J) ≤ wl) :
    wk / wl ≤ 4 * C1 * (K + 1) * J * delta N W kappa := by
  have hs : 0 < Real.sqrt J := Real.sqrt_pos.2 hJ
  have hh : 0 < mesh N W kappa J C1 K := mesh_pos hJ hC1 (by linarith)
  have hl : 0 < wl := lt_of_lt_of_le (div_pos hh (by positivity)) hlarge
  have hfactor : 0 ≤ 4 * C1 * (K + 1) * J * delta N W kappa := by
    have hd := delta_pos N W kappa
    positivity
  have he : (4 * C1 * (K + 1) * J * delta N W kappa) *
      (mesh N W kappa J C1 K / (4 * Real.sqrt J)) = delta N W kappa ^ 2 := by
    unfold mesh
    have hs2 := Real.sq_sqrt hJ.le
    field_simp
    nlinarith
  apply (div_le_iff₀ hl).2
  calc
    wk ≤ delta N W kappa ^ 2 := hsmall
    _ = (4 * C1 * (K + 1) * J * delta N W kappa) *
        (mesh N W kappa J C1 K / (4 * Real.sqrt J)) := he.symm
    _ ≤ (4 * C1 * (K + 1) * J * delta N W kappa) * wl :=
      mul_le_mul_of_nonneg_left hlarge hfactor

end HighBandLSV.Anisotropic

#print axioms HighBandLSV.Anisotropic.actual_endpoint_ratio

