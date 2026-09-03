import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Source statement for the finite-moment short-ring anchor

This file records the notation in Proposition 3.6 of
`Circular_Law_Combined_Manuscript.pdf`.  It contains no random-matrix input.
In particular, `circularLogPotential` is formula (2.1), while
`normalizedShiftLogDet` is the left-hand side of formula (3.8).

Lean's real logarithm is total (`Real.log 0 = 0`).  The least-singular-value
input in `ExternalInputs.lean` supplies the source-faithful non-singularity
guard on the high-probability event where the proof uses a logarithmic
singular-value expansion.
-/

open Filter MeasureTheory

noncomputable section

namespace ShortRingAnchor

/-- The checked manuscript used for the formalization. -/
def sourceManuscriptTitle : String :=
  "The circular law for non-Hermitian random band matrices: optimal bandwidth, periodic profile and discrete law"

/-- The source result reconstructed by this project. -/
def sourcePropositionNumber : String := "Proposition 3.6"

/-- Formula (2.1): the logarithmic potential of normalized area measure on
the unit disk.

The value at `‖z‖ = 1` is zero in either branch; the weak inequality follows
the displayed piecewise formula in the manuscript. -/
def circularLogPotential (z : ℂ) : ℝ :=
  if ‖z‖ ≤ 1 then (‖z‖ ^ 2 - 1) / 2 else Real.log ‖z‖

@[simp]
theorem circularLogPotential_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    circularLogPotential z = (‖z‖ ^ 2 - 1) / 2 := by
  simp [circularLogPotential, hz]

@[simp]
theorem circularLogPotential_of_one_lt_norm {z : ℂ} (hz : 1 < ‖z‖) :
    circularLogPotential z = Real.log ‖z‖ := by
  simp [circularLogPotential, not_le_of_gt hz]

@[simp]
theorem circularLogPotential_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    circularLogPotential z = 0 := by
  simp [circularLogPotential, hz]

/-- The left side of manuscript formula (3.8):
`M⁻¹ log |det(A-zI_M)|`.

This definition is deliberately for an already variance-normalized matrix;
unlike the Tao--Vu replacement principle, there is no extra `M⁻¹ᐟ²` matrix
scaling here. -/
def normalizedShiftLogDet {M : ℕ}
    (A : Matrix (Fin M) (Fin M) ℂ) (z : ℂ) : ℝ :=
  Real.log ‖(A - z • (1 : Matrix (Fin M) (Fin M) ℂ)).det‖ / (M : ℝ)

/-- Exact convergence conclusion of Proposition 3.6 for a sequence of
matrices of sizes `k+1`.  Writing the positive dimension this way avoids a
spurious zero-dimensional case while representing every `M ≥ 1`.

The assumptions that the matrices are the short-ring models, that their
bandwidths satisfy (3.7), and that the atom satisfies Assumption 2.1 are kept
outside this conclusion predicate. -/
def Proposition36Conclusion
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega)
    (H : ∀ k : ℕ, Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (z : ℂ) : Prop :=
  TendstoInMeasure P
    (fun k omega => normalizedShiftLogDet (H k omega) z)
    atTop (fun _ => circularLogPotential z)

/-- Exact sequential form of Proposition 3.6.

The manuscript allows an arbitrary sequence of pairs `(M,W)` tending to
infinity.  Unlike `Proposition36Conclusion`, this predicate therefore keeps
the dimension sequence explicit rather than specializing to `M=k+1`. -/
def Proposition36SequenceConclusion
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (M : Nat -> Nat)
    (H : forall k : Nat,
      Omega -> Matrix (Fin (M k)) (Fin (M k)) ℂ)
    (z : ℂ) : Prop :=
  TendstoInMeasure P
    (fun k omega => normalizedShiftLogDet (H k omega) z)
    atTop (fun _ => circularLogPotential z)

end ShortRingAnchor
