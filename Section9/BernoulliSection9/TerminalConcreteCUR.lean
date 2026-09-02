import BernoulliSection9.TerminalConcreteReindex
import BernoulliSection9.TerminalCUR
import BernoulliLinearAlgebra.ThreeBlockMaskComparison
import Mathlib.Tactic

/-!
# Extending an outer skeleton to the literal terminal matrix

The centre coordinates are never selected by RRQR.  This module extends an
outer `BlockSkeletonData` by zero centre rows/columns, in the balanced
residual ordering constructed in `TerminalConcreteReindex`, and proves that
its skeleton matrix is literally the independently row/column-reindexed
`Emb_O(Q)`.
-/

open scoped Matrix

noncomputable section

namespace BernoulliSection9

open BernoulliLinearAlgebra

@[simp] theorem threeBlockEmb_packetIndex_outer
    {W : Nat} (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (i j : Fin W ⊕ Fin W) :
    threeBlockEmb (threeBlockOuterOfPacket Q)
        (packetIndexEquiv W (Sum.inl i))
        (packetIndexEquiv W (Sum.inl j)) = Q i j := by
  change threeBlockOuterOfPacket Q
      ((threeBlockOuterEquiv (Fin W)).symm i)
      ((threeBlockOuterEquiv (Fin W)).symm j) = Q i j
  simp [threeBlockOuterOfPacket]

@[simp] theorem threeBlockEmb_packetIndex_center_row
    {W : Nat} (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (i : Fin W) (j : (Fin W ⊕ Fin W) ⊕ Fin W) :
    threeBlockEmb (threeBlockOuterOfPacket Q)
        (packetIndexEquiv W (Sum.inr i)) (packetIndexEquiv W j) = 0 := by
  rcases j with j | j
  · exact threeBlockEmb_center_row _ _ _
  · exact threeBlockEmb_center_row _ _ _

@[simp] theorem threeBlockEmb_packetIndex_center_col
    {W : Nat} (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (i : (Fin W ⊕ Fin W) ⊕ Fin W) (j : Fin W) :
    threeBlockEmb (threeBlockOuterOfPacket Q)
        (packetIndexEquiv W i) (packetIndexEquiv W (Sum.inr j)) = 0 := by
  rcases i with i | i
  · exact threeBlockEmb_center_col _ _ _
  · exact threeBlockEmb_center_col _ _ _

@[simp] theorem outerResidualEmbedding_apply
    {W r q : Nat} (e : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (i : Fin (outerResidualLeftCount e) ⊕
      Fin (outerResidualRightCount e)) :
    outerResidualEmbedding e i =
      e (Sum.inr (outerResidualFinEquiv e i)) := rfl

/-- Common residual coordinate type after the two Cook squares have been
placed consecutively. -/
abbrev TerminalBalancedResidualIndex {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W) :=
  Fin (terminalBalancedSize rowEquiv colEquiv) ⊕
    Fin (W + outerResidualLeftCount rowEquiv +
      outerResidualRightCount rowEquiv -
        terminalBalancedSize rowEquiv colEquiv)

/-- Extend `X_skel` by zero columns on the central coordinates and reorder
the remaining outer columns into the balanced residual order. -/
def terminalExtendedX {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (X : Matrix (Fin r) (Fin q) Complex) :
    Matrix (Fin r) (TerminalBalancedResidualIndex rowEquiv colEquiv) Complex :=
  fun i j => match terminalBalancedResidualColEquiv rowEquiv colEquiv j with
    | Sum.inl k => X i (outerResidualFinEquiv colEquiv k)
    | Sum.inr _ => 0

/-- Extend `Y_skel` by zero rows on the central coordinates. -/
def terminalExtendedY {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (Y : Matrix (Fin q) (Fin r) Complex) :
    Matrix (TerminalBalancedResidualIndex rowEquiv colEquiv) (Fin r) Complex :=
  fun i j => match terminalBalancedResidualRowEquiv rowEquiv colEquiv i with
    | Sum.inl k => Y (outerResidualFinEquiv rowEquiv k) j
    | Sum.inr _ => 0

/-- Extend `E₀` by zero rows and columns involving the centre. -/
def terminalExtendedE {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (E : Matrix (Fin q) (Fin q) Complex) :
    Matrix (TerminalBalancedResidualIndex rowEquiv colEquiv)
      (TerminalBalancedResidualIndex rowEquiv colEquiv) Complex :=
  fun i j =>
    match terminalBalancedResidualRowEquiv rowEquiv colEquiv i,
        terminalBalancedResidualColEquiv rowEquiv colEquiv j with
    | Sum.inl k, Sum.inl l =>
        E (outerResidualFinEquiv rowEquiv k)
          (outerResidualFinEquiv colEquiv l)
    | _, _ => 0

/-- The canonical zero-centre extension of outer skeleton data. -/
def terminalExtendedSkeletonData {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (S : BlockSkeletonData (Fin r) (Fin q)) :
    BlockSkeletonData (Fin r)
      (TerminalBalancedResidualIndex rowEquiv colEquiv) where
  Kpiv := S.Kpiv
  Xskel := terminalExtendedX rowEquiv colEquiv S.Xskel
  Yskel := terminalExtendedY rowEquiv colEquiv S.Yskel
  E0 := terminalExtendedE rowEquiv colEquiv S.E0

/-- The zero-centre extension preserves the pivot verbatim. -/
@[simp] theorem terminalExtendedSkeletonData_Kpiv {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (S : BlockSkeletonData (Fin r) (Fin q)) :
    (terminalExtendedSkeletonData rowEquiv colEquiv S).Kpiv = S.Kpiv := rfl

/-- Literal deterministic bridge: an exact outer skeleton identity extends
to an exact skeleton identity for the terminal outer embedding, with the
balanced residual ordering on rows and columns. -/
theorem threeBlockEmb_reindexed_eq_terminalExtendedSkeleton
    {W r q : Nat}
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (S : BlockSkeletonData (Fin r) (Fin q))
    (houter : Q.submatrix rowEquiv colEquiv = skeletonMatrix S) :
    (threeBlockEmb (threeBlockOuterOfPacket Q)).submatrix
        (terminalBalancedRowEquiv rowEquiv colEquiv)
        (terminalBalancedColEquiv rowEquiv colEquiv) =
      skeletonMatrix (terminalExtendedSkeletonData rowEquiv colEquiv S) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · have hij := congrFun (congrFun houter (Sum.inl i)) (Sum.inl j)
    simpa [skeletonMatrix] using hij
  · rcases hcol : terminalBalancedResidualColEquiv rowEquiv colEquiv j with k | k
    · have hij := congrFun (congrFun houter (Sum.inl i))
          (Sum.inr (outerResidualFinEquiv colEquiv k))
      simpa [skeletonMatrix, Matrix.mul_apply, terminalExtendedSkeletonData,
        terminalExtendedX, terminalResidualIndexEmbedding, hcol] using hij
    · simp [skeletonMatrix, Matrix.mul_apply, terminalExtendedSkeletonData,
        terminalExtendedX, terminalResidualIndexEmbedding, hcol]
  · rcases hrow : terminalBalancedResidualRowEquiv rowEquiv colEquiv i with k | k
    · have hij := congrFun (congrFun houter
          (Sum.inr (outerResidualFinEquiv rowEquiv k))) (Sum.inl j)
      simpa [skeletonMatrix, Matrix.mul_apply, terminalExtendedSkeletonData,
        terminalExtendedY, terminalResidualIndexEmbedding, hrow] using hij
    · simp [skeletonMatrix, Matrix.mul_apply, terminalExtendedSkeletonData,
        terminalExtendedY, terminalResidualIndexEmbedding, hrow]
  · rcases hrow : terminalBalancedResidualRowEquiv rowEquiv colEquiv i with k | k <;>
      rcases hcol : terminalBalancedResidualColEquiv rowEquiv colEquiv j with l | l
    · have hij := congrFun (congrFun houter
          (Sum.inr (outerResidualFinEquiv rowEquiv k)))
          (Sum.inr (outerResidualFinEquiv colEquiv l))
      simpa [skeletonMatrix, Matrix.mul_apply, terminalExtendedSkeletonData,
        terminalExtendedX, terminalExtendedY, terminalExtendedE,
        terminalResidualIndexEmbedding, hrow, hcol]
        using hij
    · simp [skeletonMatrix, Matrix.mul_apply, terminalExtendedSkeletonData,
        terminalExtendedX, terminalExtendedY, terminalExtendedE,
        terminalResidualIndexEmbedding, hrow, hcol]
    · simp [skeletonMatrix, Matrix.mul_apply, terminalExtendedSkeletonData,
        terminalExtendedX, terminalExtendedY, terminalExtendedE,
        terminalResidualIndexEmbedding, hrow, hcol]
    · simp [skeletonMatrix, Matrix.mul_apply, terminalExtendedSkeletonData,
        terminalExtendedX, terminalExtendedY, terminalExtendedE,
        terminalResidualIndexEmbedding, hrow, hcol]

/-! ## The literal perturbation and determinant identity -/

/-- The random packet matrix together with its spectral shift, in the exact
pivot/balanced-residual coordinates. -/
def terminalBalancedPerturbation
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (omega : Omega) :
    Matrix
      (Fin r ⊕ TerminalBalancedResidualIndex rowEquiv colEquiv)
      (Fin r ⊕ TerminalBalancedResidualIndex rowEquiv colEquiv) Complex :=
  (threeBlockDelta (fun i => (X.atom i omega : Complex)) -
      z • (1 : Matrix (ThreeBlockIndex (Fin W))
        (ThreeBlockIndex (Fin W)) Complex)).submatrix
    (terminalBalancedRowEquiv rowEquiv colEquiv)
    (terminalBalancedColEquiv rowEquiv colEquiv)

/-- The independently reindexed literal terminal matrix is exactly the
extended skeleton plus `terminalBalancedPerturbation`. -/
theorem threeBlockH_reindexed_eq_skeleton_add_perturbation
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (S : BlockSkeletonData (Fin r) (Fin q))
    (houter : Q.submatrix rowEquiv colEquiv = skeletonMatrix S)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (omega : Omega) :
    (threeBlockH (threeBlockOuterOfPacket Q) z
        (fun i => (X.atom i omega : Complex))).submatrix
      (terminalBalancedRowEquiv rowEquiv colEquiv)
      (terminalBalancedColEquiv rowEquiv colEquiv) =
    skeletonMatrix (terminalExtendedSkeletonData rowEquiv colEquiv S) +
      terminalBalancedPerturbation rowEquiv colEquiv z X omega := by
  have hemb := threeBlockEmb_reindexed_eq_terminalExtendedSkeleton
    Q rowEquiv colEquiv S houter
  ext i j
  have hembij := congrFun (congrFun hemb i) j
  simp only [threeBlockH, Matrix.submatrix_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply] at hembij ⊢
  rw [hembij]
  simp only [terminalBalancedPerturbation, Matrix.submatrix_apply,
    Matrix.sub_apply, Matrix.smul_apply]
  abel

/-- Exact norm factorization of the literal terminal determinant into its
perturbed RRQR pivot and its balanced residual determinant.  Independent
row/column permutations disappear after taking the complex norm. -/
theorem norm_threeBlockH_det_eq_pivot_mul_residual
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (S : BlockSkeletonData (Fin r) (Fin q))
    (houter : Q.submatrix rowEquiv colEquiv = skeletonMatrix S)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (omega : Omega)
    (hK : IsUnit
      (KDelta (terminalExtendedSkeletonData rowEquiv colEquiv S)
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega)).det) :
    norm (threeBlockH (threeBlockOuterOfPacket Q) z
        (fun i => (X.atom i omega : Complex))).det =
      norm (KDelta (terminalExtendedSkeletonData rowEquiv colEquiv S)
          (terminalBalancedPerturbation rowEquiv colEquiv z X omega)).det *
        norm (delta22 (terminalBalancedPerturbation rowEquiv colEquiv z X omega) +
          F (terminalExtendedSkeletonData rowEquiv colEquiv S)
            (terminalBalancedPerturbation rowEquiv colEquiv z X omega)).det := by
  let H := threeBlockH (threeBlockOuterOfPacket Q) z
    (fun i => (X.atom i omega : Complex))
  let Sfull := terminalExtendedSkeletonData rowEquiv colEquiv S
  let Delta := terminalBalancedPerturbation rowEquiv colEquiv z X omega
  have hreindex := threeBlockH_reindexed_eq_skeleton_add_perturbation
    Q rowEquiv colEquiv S houter z X omega
  have hnorm := norm_det_submatrix_equiv_equiv_complex
    (terminalBalancedRowEquiv rowEquiv colEquiv)
    (terminalBalancedColEquiv rowEquiv colEquiv) H
  have hdet := det_skeleton_add_eq_det_KDelta_mul_det_residual
    Sfull Delta hK
  calc
    norm H.det = norm ((H.submatrix
        (terminalBalancedRowEquiv rowEquiv colEquiv)
        (terminalBalancedColEquiv rowEquiv colEquiv)).det) := hnorm.symm
    _ = norm ((skeletonMatrix Sfull + Delta).det) := by rw [hreindex]
    _ = norm ((KDelta Sfull Delta).det *
        (delta22 Delta + F Sfull Delta).det) := by rw [hdet]
    _ = norm (KDelta Sfull Delta).det *
        norm (delta22 Delta + F Sfull Delta).det := norm_mul _ _

/-- Inequality form used by the upper probability assembly. -/
theorem pivotLower_mul_residual_det_le_terminal
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega} {W r q : Nat}
    (Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (rowEquiv colEquiv : Fin r ⊕ Fin q ≃ Fin W ⊕ Fin W)
    (S : BlockSkeletonData (Fin r) (Fin q))
    (houter : Q.submatrix rowEquiv colEquiv = skeletonMatrix S)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (omega : Omega)
    (hK : IsUnit
      (KDelta (terminalExtendedSkeletonData rowEquiv colEquiv S)
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega)).det)
    (pivotLower : Real)
    (hpivot : pivotLower ≤
      norm (KDelta (terminalExtendedSkeletonData rowEquiv colEquiv S)
        (terminalBalancedPerturbation rowEquiv colEquiv z X omega)).det) :
    pivotLower *
        norm (delta22 (terminalBalancedPerturbation rowEquiv colEquiv z X omega) +
          F (terminalExtendedSkeletonData rowEquiv colEquiv S)
            (terminalBalancedPerturbation rowEquiv colEquiv z X omega)).det ≤
      norm (threeBlockH (threeBlockOuterOfPacket Q) z
        (fun i => (X.atom i omega : Complex))).det := by
  rw [norm_threeBlockH_det_eq_pivot_mul_residual
    Q rowEquiv colEquiv S houter z X omega hK]
  exact mul_le_mul_of_nonneg_right hpivot (norm_nonneg _)

end BernoulliSection9
