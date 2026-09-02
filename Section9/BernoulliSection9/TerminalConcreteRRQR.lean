import BernoulliSection9.StrongRRQR
import BernoulliSection9.TerminalConcreteResidual
import Mathlib.Tactic

/-!
# Internal RRQR data for the packet outer matrix

The caller supplies only the paper's outer matrix and threshold.  This file
reindexes the two packet sides to `Fin (2W)`, invokes the proved complex
strong RRQR theorem, and transports its internally constructed row/column
equivalences and skeleton back to `Fin W ⊕ Fin W`.
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

open BernoulliLinearAlgebra

/-- Canonical identification of the two outer packet sides with `Fin (2W)`. -/
def packetOuterFinEquiv (W : Nat) : Fin W ⊕ Fin W ≃ Fin (2 * W) :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- The outer packet matrix in the index type expected by `strongRRQRConclusion`. -/
def packetOuterFinMatrix {W : Nat}
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex) :
    Matrix (Fin (2 * W)) (Fin (2 * W)) Complex :=
  Q.submatrix (packetOuterFinEquiv W).symm (packetOuterFinEquiv W).symm

/-- The threshold count used by the internally constructed packet RRQR. -/
abbrev packetLargeSingularValueCount {W : Nat}
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex) (tau : Real) : Nat :=
  largeSingularValueCount (packetOuterFinMatrix Q) tau

/-- The actual proved RRQR conclusion for the outer packet matrix. -/
def packetStrongRRQRConclusion {W : Nat}
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (tau : Real) (hn : 2 ≤ 2 * W) (htau : 1 ≤ tau) :=
  strongRRQRConclusion (packetOuterFinMatrix Q) tau hn htau

/-- Internally selected row ordering, transported back to the two packet
sides. -/
def packetRRQRRowEquiv {W : Nat}
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (tau : Real) (hn : 2 ≤ 2 * W) (htau : 1 ≤ tau) :
    Fin (packetLargeSingularValueCount Q tau) ⊕
        Fin (2 * W - packetLargeSingularValueCount Q tau) ≃
      Fin W ⊕ Fin W :=
  (packetStrongRRQRConclusion Q tau hn htau).rowEquiv.trans
    (packetOuterFinEquiv W).symm

/-- Internally selected column ordering. -/
def packetRRQRColEquiv {W : Nat}
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (tau : Real) (hn : 2 ≤ 2 * W) (htau : 1 ≤ tau) :
    Fin (packetLargeSingularValueCount Q tau) ⊕
        Fin (2 * W - packetLargeSingularValueCount Q tau) ≃
      Fin W ⊕ Fin W :=
  (packetStrongRRQRConclusion Q tau hn htau).colEquiv.trans
    (packetOuterFinEquiv W).symm

/-- The internally proved packet skeleton; it is output of RRQR, not a
caller-provided certificate. -/
def packetRRQRSkeleton {W : Nat}
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (tau : Real) (hn : 2 ≤ 2 * W) (htau : 1 ≤ tau) :
    BlockSkeletonData (Fin (packetLargeSingularValueCount Q tau))
      (Fin (2 * W - packetLargeSingularValueCount Q tau)) :=
  (packetStrongRRQRConclusion Q tau hn htau).data

/-- Literal outer block identity produced entirely from `Q` and `tau`. -/
theorem packetRRQR_block_identity {W : Nat}
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (tau : Real) (hn : 2 ≤ 2 * W) (htau : 1 ≤ tau) :
    Q.submatrix (packetRRQRRowEquiv Q tau hn htau)
        (packetRRQRColEquiv Q tau hn htau) =
      skeletonMatrix (packetRRQRSkeleton Q tau hn htau) := by
  have h := (packetStrongRRQRConclusion Q tau hn htau).block_identity
  change Q.submatrix
      (fun x => (packetOuterFinEquiv W).symm
        ((packetStrongRRQRConclusion Q tau hn htau).rowEquiv x))
      (fun x => (packetOuterFinEquiv W).symm
        ((packetStrongRRQRConclusion Q tau hn htau).colEquiv x)) =
    skeletonMatrix (packetRRQRSkeleton Q tau hn htau)
  change Q.submatrix
      (fun x => (packetOuterFinEquiv W).symm
        ((packetStrongRRQRConclusion Q tau hn htau).rowEquiv x))
      (fun x => (packetOuterFinEquiv W).symm
        ((packetStrongRRQRConclusion Q tau hn htau).colEquiv x)) =
    skeletonMatrix (packetRRQRSkeleton Q tau hn htau) at h
  exact h

/-- The unperturbed packet pivot is invertible, including the empty-pivot
convention. -/
theorem packetRRQR_pivot_isUnit {W : Nat}
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (tau : Real) (hn : 2 ≤ 2 * W) (htau : 1 ≤ tau) :
    IsUnit (packetRRQRSkeleton Q tau hn htau).Kpiv.det :=
  (packetStrongRRQRConclusion Q tau hn htau).pivot_isUnit

/-- Literal three-block skeleton identity with every RRQR choice internal. -/
theorem packetRRQR_threeBlockEmb_identity {W : Nat}
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (tau : Real) (hn : 2 ≤ 2 * W) (htau : 1 ≤ tau) :
    (threeBlockEmb (threeBlockOuterOfPacket Q)).submatrix
        (terminalBalancedRowEquiv
          (packetRRQRRowEquiv Q tau hn htau)
          (packetRRQRColEquiv Q tau hn htau))
        (terminalBalancedColEquiv
          (packetRRQRRowEquiv Q tau hn htau)
          (packetRRQRColEquiv Q tau hn htau)) =
      skeletonMatrix (terminalExtendedSkeletonData
        (packetRRQRRowEquiv Q tau hn htau)
        (packetRRQRColEquiv Q tau hn htau)
        (packetRRQRSkeleton Q tau hn htau)) :=
  threeBlockEmb_reindexed_eq_terminalExtendedSkeleton Q
    (packetRRQRRowEquiv Q tau hn htau)
    (packetRRQRColEquiv Q tau hn htau)
    (packetRRQRSkeleton Q tau hn htau)
    (packetRRQR_block_identity Q tau hn htau)

/-- Exact terminal determinant factorization after internally constructing
RRQR.  The only remaining pointwise premise is the paper's small-perturbation
fact that the *perturbed* pivot is invertible. -/
theorem norm_packetTerminal_det_eq_internalRRQR_pivot_mul_residual
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W : Nat}
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (tau : Real) (hn : 2 ≤ 2 * W) (htau : 1 ≤ tau)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (omega : Omega)
    (hK : IsUnit
      (KDelta
        (terminalExtendedSkeletonData
          (packetRRQRRowEquiv Q tau hn htau)
          (packetRRQRColEquiv Q tau hn htau)
          (packetRRQRSkeleton Q tau hn htau))
        (terminalBalancedPerturbation
          (packetRRQRRowEquiv Q tau hn htau)
          (packetRRQRColEquiv Q tau hn htau) z X omega)).det) :
    norm (threeBlockH (threeBlockOuterOfPacket Q) z
        (fun i => (X.atom i omega : Complex))).det =
      norm (KDelta
        (terminalExtendedSkeletonData
          (packetRRQRRowEquiv Q tau hn htau)
          (packetRRQRColEquiv Q tau hn htau)
          (packetRRQRSkeleton Q tau hn htau))
        (terminalBalancedPerturbation
          (packetRRQRRowEquiv Q tau hn htau)
          (packetRRQRColEquiv Q tau hn htau) z X omega)).det *
      norm (terminalCURResidual (packetRRQRSkeleton Q tau hn htau)
        (packetRRQRRowEquiv Q tau hn htau)
        (packetRRQRColEquiv Q tau hn htau) z X omega).det := by
  exact norm_threeBlockH_det_eq_pivot_mul_residual Q
    (packetRRQRRowEquiv Q tau hn htau)
    (packetRRQRColEquiv Q tau hn htau)
    (packetRRQRSkeleton Q tau hn htau)
    (packetRRQR_block_identity Q tau hn htau) z X omega hK

end BernoulliSection9
