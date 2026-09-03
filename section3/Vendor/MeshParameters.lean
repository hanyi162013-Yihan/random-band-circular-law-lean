/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/MeshParameters.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.PlanarSmallBall

/-! The paper's actual mesh meets every deterministic net-cover requirement. -/

namespace HighBandLSV.MeshParameters

theorem geometric_mesh_bounds {d J C1 K : Real}
    (hd : 0 < d) (hd1 : d ≤ 1) (hJ : 1 ≤ J) (hC1 : 2 ≤ C1) (hK : 0 ≤ K) :
    let h := d / (C1 * (K + 1) * Real.sqrt J)
    0 < h ∧ h ≤ d ∧ h ≤ 1 ∧ h * Real.sqrt J ≤ 1 / 2 ∧
      (Real.sqrt J * h) * K ≤ d := by
  have hJ0 : 0 < J := by linarith
  have hs : 0 < Real.sqrt J := Real.sqrt_pos.2 hJ0
  have hs1 : 1 ≤ Real.sqrt J := (Real.le_sqrt (by norm_num) hJ0.le).2 (by simpa using hJ)
  have hbase : 2 ≤ C1 * (K + 1) := by nlinarith
  have hbase0 : 0 < C1 * (K + 1) := by linarith
  have hden' := mul_le_mul_of_nonneg_right
    (show 1 ≤ C1 * (K + 1) from by linarith) hs.le
  have hden : 1 ≤ C1 * (K + 1) * Real.sqrt J :=
    hs1.trans (by simpa using hden')
  have hh : 0 < d / (C1 * (K + 1) * Real.sqrt J) := by positivity
  have hhd : d / (C1 * (K + 1) * Real.sqrt J) ≤ d := by
    apply (div_le_iff₀ (mul_pos hbase0 hs)).2
    nlinarith [mul_le_mul_of_nonneg_left hden hd.le]
  have hcancel : d / (C1 * (K + 1) * Real.sqrt J) * Real.sqrt J =
      d / (C1 * (K + 1)) := by field_simp
  refine ⟨hh, hhd, hhd.trans hd1, ?_, ?_⟩
  · rw [hcancel]
    exact (div_le_iff₀ hbase0).2 (by nlinarith)
  · have hratio : K ≤ C1 * (K + 1) := by nlinarith
    calc
      (Real.sqrt J * (d / (C1 * (K + 1) * Real.sqrt J))) * K =
          (d / (C1 * (K + 1))) * K := by rw [mul_comm (Real.sqrt J), hcancel]
      _ = d * K / (C1 * (K + 1)) := by ring
      _ ≤ d := (div_le_iff₀ hbase0).2 (mul_le_mul_of_nonneg_left hratio hd.le)

theorem actual_mesh_bounds {N W kappa J C1 K : Real}
    (hN : 0 ≤ N) (hW : 0 < W) (hJ : 1 ≤ J) (hC1 : 2 ≤ C1) (hK : 0 ≤ K) :
    0 < mesh N W kappa J C1 K ∧
      mesh N W kappa J C1 K ≤ delta N W kappa ∧
      mesh N W kappa J C1 K ≤ 1 ∧
      mesh N W kappa J C1 K * Real.sqrt J ≤ 1 / 2 ∧
      (Real.sqrt J * mesh N W kappa J C1 K) * K ≤ delta N W kappa := by
  have hdelta : 0 < delta N W kappa := Real.exp_pos _
  have hdelta1 : delta N W kappa ≤ 1 := by
    unfold delta
    apply Real.exp_le_one_iff.mpr
    have hl : 0 ≤ Section5Formalization.section5Scale N W kappa := by
      unfold Section5Formalization.section5Scale
      positivity
    exact neg_nonpos.mpr hl
  exact geometric_mesh_bounds hdelta hdelta1 hJ hC1 hK

end HighBandLSV.MeshParameters

#print axioms HighBandLSV.MeshParameters.actual_mesh_bounds

