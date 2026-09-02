import CircularLawSection4.PaperPressureObservable
import Mathlib.Data.Fin.Tuple.Take

/-!
# Leave-one-row decomposition for the paper pressure

For the chronological convention used in the manuscript, the factors after
row `i` form its left history and the factors before row `i` form its right
history.  This file proves the exact split, proves that both histories are
unchanged when row `i` is replaced, and transports the original/replacement
products to one common operator-affine coefficient family.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

section ChronologicalSplit

variable {R : Type*} [CommRing R]
variable {k : Type*} [Fintype k] [DecidableEq k]

/-- Split a chronological product at a specified valid list position. -/
theorem chronologicalProduct_split_get (Ts : List (Matrix k k R))
    (i : ℕ) (hi : i < Ts.length) :
    chronologicalProduct Ts =
      chronologicalProduct (Ts.drop (i + 1)) * Ts.get ⟨i, hi⟩ *
        chronologicalProduct (Ts.take i) := by
  have hsplit :
      Ts = (Ts.take i ++ [Ts.get ⟨i, hi⟩]) ++ Ts.drop (i + 1) := by
    calc
      Ts = Ts.take i ++ Ts.drop i := (List.take_append_drop i Ts).symm
      _ = Ts.take i ++ (Ts.get ⟨i, hi⟩ :: Ts.drop (i + 1)) := by
        rw [List.cons_get_drop_succ]
      _ = (Ts.take i ++ [Ts.get ⟨i, hi⟩]) ++ Ts.drop (i + 1) := by
        simp only [List.append_assoc, List.singleton_append]
  calc
    chronologicalProduct Ts = chronologicalProduct
        ((Ts.take i ++ [Ts.get ⟨i, hi⟩]) ++ Ts.drop (i + 1)) :=
      congrArg chronologicalProduct hsplit
    _ = chronologicalProduct (Ts.drop (i + 1)) * Ts.get ⟨i, hi⟩ *
          chronologicalProduct (Ts.take i) := by
      rw [chronologicalProduct_append, chronologicalProduct_append]
      simp only [chronologicalProduct_cons, chronologicalProduct_nil, Matrix.one_mul]
      rw [Matrix.mul_assoc]

end ChronologicalSplit

section OfFnUpdate

variable {α : Type*}

/-- Replacing coordinate `i` does not change the part of `List.ofFn` before
`i`. -/
theorem take_ofFn_update_at {n : ℕ} (f : Fin n → α) (i : Fin n) (a : α) :
    (List.ofFn (Function.update f i a)).take i.val =
      (List.ofFn f).take i.val := by
  rw [← Fin.ofFn_take_eq_take_ofFn i.isLt.le,
    Fin.take_update_of_ge i.val i.isLt.le f i (le_refl i.val) a,
    Fin.ofFn_take_eq_take_ofFn]

/-- Replacing coordinate `i` does not change the part of `List.ofFn` after
`i`. -/
theorem drop_ofFn_update_at {n : ℕ} (f : Fin n → α) (i : Fin n) (a : α) :
    (List.ofFn (Function.update f i a)).drop (i.val + 1) =
      (List.ofFn f).drop (i.val + 1) := by
  apply List.ext_get (by simp)
  intro j hj₁ hj₂
  simp only [List.get_eq_getElem, List.getElem_drop, List.getElem_ofFn]
  rw [Function.update_of_ne]
  intro h
  have hval := congrArg Fin.val h
  simp only at hval
  omega

end OfFnUpdate

namespace PaperIndicatorWeights

variable {m n : ℕ} {c₀ C₀ : ℝ}

/-- Exterior-row factors in their natural row order. -/
def paperPressureExteriorRowList
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin n → PaperIndicatorAtomRow m) :
    List (Matrix (ExteriorIndex (m + 1) q)
      (ExteriorIndex (m + 1) q) ℂ) :=
  List.ofFn fun j =>
    profile.paperIndicatorOpenExteriorRow center z q (rows j)

/-- In the chronological convention, rows strictly after `i` multiply on
the left of row `i`. -/
def paperPressureLeftHistory
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin n → PaperIndicatorAtomRow m) (i : Fin n) :
    Matrix (ExteriorIndex (m + 1) q) (ExteriorIndex (m + 1) q) ℂ :=
  chronologicalProduct
    ((profile.paperPressureExteriorRowList center z q rows).drop (i.val + 1))

/-- Rows strictly before `i` multiply on the right of row `i`. -/
def paperPressureRightHistory
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin n → PaperIndicatorAtomRow m) (i : Fin n) :
    Matrix (ExteriorIndex (m + 1) q) (ExteriorIndex (m + 1) q) ℂ :=
  chronologicalProduct
    ((profile.paperPressureExteriorRowList center z q rows).take i.val)

/-- Exact leave-one-row factorization of the full open exterior product. -/
theorem paperIndicatorOpenExteriorProduct_eq_leaveOneOut
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin n → PaperIndicatorAtomRow m) (i : Fin n) :
    profile.paperIndicatorOpenExteriorProduct center z q rows =
      profile.paperPressureLeftHistory center z q rows i *
        profile.paperIndicatorOpenExteriorRow center z q (rows i) *
          profile.paperPressureRightHistory center z q rows i := by
  let Ts := profile.paperPressureExteriorRowList center z q rows
  have hi : i.val < Ts.length := by simp [Ts, paperPressureExteriorRowList]
  have hsplit := chronologicalProduct_split_get Ts i.val hi
  have hget : Ts.get ⟨i.val, hi⟩ =
      profile.paperIndicatorOpenExteriorRow center z q (rows i) := by
    dsimp only [Ts, paperPressureExteriorRowList]
    rw [List.get_ofFn]
    congr 2
  rw [hget] at hsplit
  simpa only [paperIndicatorOpenExteriorProduct, paperPressureExteriorRowList,
    paperPressureLeftHistory, paperPressureRightHistory, Ts] using hsplit

/-- The exterior-row factor function of an updated sample is the pointwise
update of the original factor function. -/
theorem paperPressureExteriorRowFunction_update
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin n → PaperIndicatorAtomRow m) (i : Fin n)
    (newRow : PaperIndicatorAtomRow m) :
    (fun j => profile.paperIndicatorOpenExteriorRow center z q
      (Function.update rows i newRow j)) =
      Function.update
        (fun j => profile.paperIndicatorOpenExteriorRow center z q (rows j))
        i (profile.paperIndicatorOpenExteriorRow center z q newRow) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [Function.update_of_ne hji]

/-- Replacing row `i` leaves its left history unchanged. -/
theorem paperPressureLeftHistory_update
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin n → PaperIndicatorAtomRow m) (i : Fin n)
    (newRow : PaperIndicatorAtomRow m) :
    profile.paperPressureLeftHistory center z q
        (Function.update rows i newRow) i =
      profile.paperPressureLeftHistory center z q rows i := by
  unfold paperPressureLeftHistory paperPressureExteriorRowList
  rw [profile.paperPressureExteriorRowFunction_update center z q rows i newRow,
    drop_ofFn_update_at]

/-- Replacing row `i` leaves its right history unchanged. -/
theorem paperPressureRightHistory_update
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin n → PaperIndicatorAtomRow m) (i : Fin n)
    (newRow : PaperIndicatorAtomRow m) :
    profile.paperPressureRightHistory center z q
        (Function.update rows i newRow) i =
      profile.paperPressureRightHistory center z q rows i := by
  unfold paperPressureRightHistory paperPressureExteriorRowList
  rw [profile.paperPressureExteriorRowFunction_update center z q rows i newRow,
    take_ofFn_update_at]

/-- Consequently, the common logarithmic row scale is unchanged by replacing
the row that has been left out of the histories. -/
theorem paperPressureRowScale_update
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin n → PaperIndicatorAtomRow m) (i : Fin n)
    (newRow : PaperIndicatorAtomRow m) :
    profile.paperPressureRowScale center q
        (profile.paperPressureLeftHistory center z q
          (Function.update rows i newRow) i)
        (profile.paperPressureRightHistory center z q
          (Function.update rows i newRow) i) =
      profile.paperPressureRowScale center q
        (profile.paperPressureLeftHistory center z q rows i)
        (profile.paperPressureRightHistory center z q rows i) := by
  rw [profile.paperPressureLeftHistory_update center z q rows i newRow,
    profile.paperPressureRightHistory_update center z q rows i newRow]

/-- The old and replacement open products are two evaluations of one common
operator-affine family.  Its frozen coefficient matrices, distinguished
spectral coefficient, and scale depend only on the rows other than `i`. -/
theorem old_new_openExteriorProduct_eq_same_operatorAffine
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin n → PaperIndicatorAtomRow m) (i : Fin n)
    (newRow : PaperIndicatorAtomRow m) :
    let L := profile.paperPressureLeftHistory center z q rows i
    let R := profile.paperPressureRightHistory center z q rows i
    Matrix.toEuclideanCLM (n := ExteriorIndex (m + 1) q) (𝕜 := ℂ)
        (profile.paperIndicatorOpenExteriorProduct center z q rows) =
        operatorAffine profile.orderedResetWeight
          (paperIndicatorOpenRowAtoms (rows i))
          (paperPressureFrozenCoefficientCLM q L R) z
          (paperPressureFrozenCoefficientCLM q L R (some center)) ∧
      Matrix.toEuclideanCLM (n := ExteriorIndex (m + 1) q) (𝕜 := ℂ)
        (profile.paperIndicatorOpenExteriorProduct center z q
          (Function.update rows i newRow)) =
        operatorAffine profile.orderedResetWeight
          (paperIndicatorOpenRowAtoms newRow)
          (paperPressureFrozenCoefficientCLM q L R) z
          (paperPressureFrozenCoefficientCLM q L R (some center)) := by
  classical
  dsimp only
  let L := profile.paperPressureLeftHistory center z q rows i
  let R := profile.paperPressureRightHistory center z q rows i
  have hrow (row : PaperIndicatorAtomRow m) :
      Matrix.toEuclideanCLM (n := ExteriorIndex (m + 1) q) (𝕜 := ℂ)
          (L * profile.paperIndicatorOpenExteriorRow center z q row * R) =
        operatorAffine profile.orderedResetWeight
          (paperIndicatorOpenRowAtoms row)
          (paperPressureFrozenCoefficientCLM q L R) z
          (paperPressureFrozenCoefficientCLM q L R (some center)) := by
    rw [profile.paperIndicatorOpenExteriorRow_eq_freshExteriorRow]
    simpa using
      (profile.toEuclideanCLM_mul_freshExteriorRow_mul_eq_operatorAffine
        center z (fun _ => paperIndicatorOpenRowAtoms row) q
        (0 : Fin (m + 1)) L R)
  constructor
  · rw [profile.paperIndicatorOpenExteriorProduct_eq_leaveOneOut
      center z q rows i]
    exact hrow (rows i)
  · rw [profile.paperIndicatorOpenExteriorProduct_eq_leaveOneOut
      center z q (Function.update rows i newRow) i,
      profile.paperPressureLeftHistory_update center z q rows i newRow,
      profile.paperPressureRightHistory_update center z q rows i newRow,
      Function.update_self]
    exact hrow newRow

end PaperIndicatorWeights

end CircularLawSection4
