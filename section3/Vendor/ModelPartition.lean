/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/ModelPartition.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.BlockGeometry
import Vendor.PathGeometry

/-! The actual balanced partition, row deletion sizes, and column neighborhoods. -/

noncomputable section
namespace HighBandLSV.ModelPartition
open BlockGeometry

variable {N W : Nat}

def actual (hseed : 8 ≤ seedSize N W) : Partition N (blockCount N W) where
  blocks := Section5Formalization.balancedIntervalBlock N (blockCount N W)
  cover := (actual_partition_geometry hseed).1
  disjoint := (actual_partition_geometry hseed).2.1

theorem retained_rows_fit (hseed : 8 ≤ seedSize N W) (j : Fin (blockCount N W)) :
    retainedRows N W + 1 ≤ ((actual hseed).blocks j).card := by
  obtain ⟨_, _, _, _, hr, _, _, _⟩ :=
    ceiling_partition_arithmetic hseed (seed_size_bounds hseed).1
  change seedSize N W ≤ 4 * (blockSize N W - 1) at hr
  have hd : 0 < blockSize N W := by omega
  change retainedRows N W + 1 ≤
    (Section5Formalization.balancedIntervalBlock N (blockCount N W) j).card
  rw [(actual_partition_geometry hseed).2.2.1 j]
  unfold retainedRows
  split_ifs <;> omega

theorem local_band (hseed : 8 ≤ seedSize N W) :
    PathGeometry.LocalBand (actual hseed) W := by
  intro a b hab i hi j hj
  exact (actual_partition_geometry hseed).2.2.2 hi hj hab

def columnBlock (hseed : 8 ≤ seedSize N W) (j : Fin N) : Finset (Fin N) :=
  (actual hseed).blocks (Classical.choose ((actual hseed).cover j))

theorem mem_columnBlock (hseed : 8 ≤ seedSize N W) (j : Fin N) :
    j ∈ columnBlock hseed j := Classical.choose_spec ((actual hseed).cover j)

theorem columnBlock_local (hseed : 8 ≤ seedSize N W) (j i : Fin N)
    (hi : i ∈ columnBlock hseed j) : Section5Formalization.cyclicDist N i j ≤ W := by
  exact (actual_partition_geometry hseed).2.2.2 hi (mem_columnBlock hseed j) (Or.inl rfl)

end HighBandLSV.ModelPartition

#print axioms HighBandLSV.ModelPartition.local_band
#print axioms HighBandLSV.ModelPartition.retained_rows_fit

