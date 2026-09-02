import BernoulliSection9.CoordinateTwoCook

/-!
# Measurable norm truncation for Cook deformations

Cook's input asks for an almost-everywhere polynomial norm bound, whereas the
raw terminal CUR deformation is polynomially bounded only on the exposure
event.  We therefore truncate each deformation by its own operator norm,
apply Cook to the globally bounded truncation, and use equality with the raw
deformation on the exposure event.  The construction and its measurability
are internal.
-/

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

open MeasureTheory

/-- Replace a matrix-valued function by zero wherever its norm exceeds `R`. -/
def matrixNormTruncation
    {Omega : Type*} {n : Nat}
    (R : Real) (D : Omega → Matrix (Fin n) (Fin n) Complex) :
    Omega → Matrix (Fin n) (Fin n) Complex :=
  fun omega => if ‖D omega‖ ≤ R then D omega else 0

@[simp] theorem matrixNormTruncation_eq_of_norm_le
    {Omega : Type*} {n : Nat} {R : Real}
    (D : Omega → Matrix (Fin n) (Fin n) Complex) (omega : Omega)
    (h : ‖D omega‖ ≤ R) :
    matrixNormTruncation R D omega = D omega := by
  simp [matrixNormTruncation, h]

@[simp] theorem matrixNormTruncation_eq_zero_of_not_norm_le
    {Omega : Type*} {n : Nat} {R : Real}
    (D : Omega → Matrix (Fin n) (Fin n) Complex) (omega : Omega)
    (h : ¬‖D omega‖ ≤ R) :
    matrixNormTruncation R D omega = 0 := by
  simp [matrixNormTruncation, h]

/-- The truncated deformation satisfies its bound pointwise. -/
theorem norm_matrixNormTruncation_le
    {Omega : Type*} {n : Nat} (R : Real) (hR : 0 ≤ R)
    (D : Omega → Matrix (Fin n) (Fin n) Complex) (omega : Omega) :
    ‖matrixNormTruncation R D omega‖ ≤ R := by
  by_cases h : ‖D omega‖ ≤ R
  · simpa [matrixNormTruncation, h] using h
  · simp [matrixNormTruncation, h, hR]

/-- Entrywise strong measurability is preserved by norm truncation. -/
theorem measurableSet_matrix_norm_le
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {n : Nat} (m : MeasurableSpace Omega)
    (R : Real) (D : Omega → Matrix (Fin n) (Fin n) Complex)
    (hD : ∀ i j,
      @StronglyMeasurable Omega Complex _ m (fun omega => D omega i j)) :
    @MeasurableSet Omega m {omega | ‖D omega‖ ≤ R} := by
  classical
  letI : MeasurableSpace Omega := m
  have hDstrong : StronglyMeasurable D := by
    have hsum : StronglyMeasurable
        (fun omega => ∑ i : Fin n, ∑ j : Fin n,
          D omega i j • Matrix.single i j (1 : Complex)) := by
      fun_prop
    convert hsum using 1
    funext omega
    calc
      D omega = ∑ i : Fin n, ∑ j : Fin n,
          Matrix.single i j (D omega i j) := Matrix.matrix_eq_sum_single (D omega)
      _ = ∑ i : Fin n, ∑ j : Fin n,
          D omega i j • Matrix.single i j (1 : Complex) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ext i' j'
        simp [Matrix.single]
  exact measurableSet_le hDstrong.norm.measurable measurable_const

/-- Entrywise strong measurability is preserved by norm truncation. -/
theorem matrixNormTruncation_stronglyMeasurable_entry
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {n : Nat} (m : MeasurableSpace Omega)
    (R : Real) (D : Omega → Matrix (Fin n) (Fin n) Complex)
    (hD : ∀ i j,
      @StronglyMeasurable Omega Complex _ m (fun omega => D omega i j))
    (i j : Fin n) :
      @StronglyMeasurable Omega Complex _ m
      (fun omega => matrixNormTruncation R D omega i j) := by
  classical
  letI : MeasurableSpace Omega := m
  have hs : MeasurableSet {omega | ‖D omega‖ ≤ R} :=
    measurableSet_matrix_norm_le m R D hD
  have hentry : StronglyMeasurable
      (fun omega => if ‖D omega‖ ≤ R then D omega i j else (0 : Complex)) :=
    StronglyMeasurable.ite hs (hD i j)
      (stronglyMeasurable_const (b := (0 : Complex)))
  convert hentry using 1
  funext omega
  by_cases h : ‖D omega‖ ≤ R <;> simp [matrixNormTruncation, h]

/-- The pointwise truncation bound in the almost-everywhere form expected by
`CookDeformedSquareInput`. -/
theorem eventually_norm_matrixNormTruncation_le
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {n : Nat} (R : Real) (hR : 0 ≤ R)
    (D : Omega → Matrix (Fin n) (Fin n) Complex) :
    ∀ᵐ omega ∂mu, ‖matrixNormTruncation R D omega‖ ≤ R :=
  Filter.Eventually.of_forall (norm_matrixNormTruncation_le R hR D)

end BernoulliSection9
