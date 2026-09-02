import BernoulliSection9.SubgaussianMaxTail
import BernoulliSection9.TerminalAssembly
import BernoulliSection9.ValidMatchingCardinality

/-!
# Probability of the terminal coordinate-maximum event

This is the probabilistic half of the reverse estimate.  It is derived from
the atom's subgaussian MGF and a finite union bound, not supplied as an
external input.
-/

noncomputable section

namespace BernoulliSection9

open MeasureTheory BernoulliLinearAlgebra

namespace TerminalAssembly

theorem threeBlockVariable_nonempty
    {w : Type*} [Fintype w] [DecidableEq w] [Nonempty w] :
    Nonempty (ThreeBlockVariable w) := by
  let i : w := Classical.choice inferInstance
  exact ⟨threeBlockDiagonalVariable (Sum.inr i)⟩

theorem coordinatewiseBoundedEvent_eq_family
    {Omega iota : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega}
    (X : IidSubgaussianFamily Omega mu iota) (M : Real) :
    coordinatewiseBoundedEvent X M =
      familyCoordinatewiseBoundedEvent X M := rfl

theorem measurableSet_coordinatewiseBoundedEvent
    {Omega iota : Type*} [MeasurableSpace Omega]
    [Fintype iota]
    {mu : Measure Omega}
    (X : IidSubgaussianFamily Omega mu iota) (M : Real) :
    MeasurableSet (coordinatewiseBoundedEvent X M) := by
  rw [coordinatewiseBoundedEvent_eq_family]
  exact measurableSet_familyCoordinatewiseBoundedEvent X M

/-- Exact finite-coordinate subgaussian union bound for `E_max`. -/
theorem measureReal_compl_coordinatewiseBoundedEvent_le
    {Omega iota : Type*} [MeasurableSpace Omega]
    [Fintype iota]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (X : IidSubgaussianFamily Omega mu iota)
    (M : Real) (hM : 0 <= M) :
    mu.real (coordinatewiseBoundedEvent X M)ᶜ <=
      (Fintype.card iota : Real) *
        (2 * Real.exp
          (-M ^ 2 / (2 * (X.subgaussianParameter : Real)))) := by
  rw [coordinatewiseBoundedEvent_eq_family]
  exact measureReal_compl_familyCoordinatewiseBoundedEvent_le mu X M hM

/-- For the literal packet mask, the number of coordinates is at most the
square of the `3W` full row count. -/
theorem measureReal_compl_packetCoordinatewiseBoundedEvent_le
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable w))
    (M : Real) (hM : 0 <= M) :
    mu.real (coordinatewiseBoundedEvent X M)ᶜ <=
      ((Fintype.card (ThreeBlockIndex w) *
          Fintype.card (ThreeBlockIndex w) : Nat) : Real) *
        (2 * Real.exp
          (-M ^ 2 / (2 * (X.subgaussianParameter : Real)))) := by
  have hbase := measureReal_compl_coordinatewiseBoundedEvent_le mu X M hM
  refine hbase.trans ?_
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast card_threeBlockVariable_le_index_sq (w := w)
  · positivity

/-- Pure exponential packet `E_max` bound at the canonical subgaussian
threshold. -/
theorem measureReal_compl_packetCoordinatewiseBoundedEvent_threshold_le
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w] [Nonempty w]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable w))
    (t : Real) (ht : 0 <= t) :
    mu.real
        (coordinatewiseBoundedEvent X
          (familyCoordinateMaxThreshold X t))ᶜ <=
      Real.exp (-t) := by
  letI : Nonempty (ThreeBlockVariable w) := threeBlockVariable_nonempty
  rw [coordinatewiseBoundedEvent_eq_family]
  exact measureReal_compl_familyCoordinatewiseBoundedEvent_threshold_le
    mu X t ht

end TerminalAssembly

end BernoulliSection9
