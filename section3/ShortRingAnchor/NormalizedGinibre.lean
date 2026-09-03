import ShortRingAnchor.SecondMoment

/-!
# Normalized dense comparison matrices

This file isolates the elementary normalization used for the dense comparison
matrix in Proposition 3.6.  Given an `M n \times M n` family of complex atom
copies, `normalizedDenseMatrixProcess` divides every entry by `sqrt (M n)`.

For the upper-edge estimate only the one-entry first and second moments are
needed: integrability, centering, and unit second moment imply that every row
of the normalized matrix has total second moment exactly one.  In particular,
neither independence nor a Gaussian-law construction is used here.
-/

open scoped BigOperators

noncomputable section

namespace ShortRingAnchor

open MeasureTheory

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The normalized dense matrix process associated with a square array of
complex atom copies: formulaically, `G_ij = atom_ij / sqrt M`.

The name deliberately does not assert that the supplied atoms are Gaussian;
the usual normalized Ginibre process is the specialization to standard
complex Gaussian atom copies. -/
def normalizedDenseMatrixProcess {M : Nat -> Nat}
    (atom : forall n, Omega -> Fin (M n) -> Fin (M n) -> Complex) :
    forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) Complex :=
  fun n omega i j =>
    atom n omega i j / (Real.sqrt (M n : Real) : Complex)

omit [MeasurableSpace Omega] in
@[simp]
theorem normalizedDenseMatrixProcess_apply {M : Nat -> Nat}
    (atom : forall n, Omega -> Fin (M n) -> Fin (M n) -> Complex)
    (n : Nat) (omega : Omega) (i j : Fin (M n)) :
    normalizedDenseMatrixProcess atom n omega i j =
      atom n omega i j / (Real.sqrt (M n : Real) : Complex) := rfl

/-- Dividing a complex random variable by `sqrt m` divides its second moment
by `m`.  Positivity of `m` is the only dimension hypothesis. -/
theorem integral_norm_sq_div_sqrt_nat
    {X : Omega -> Complex} {m : Nat} (hm : 0 < m)
    (hXsq : Integrable (fun omega => ‖X omega‖ ^ 2) mu) :
    Integrable
        (fun omega => ‖X omega / (Real.sqrt (m : Real) : Complex)‖ ^ 2) mu ∧
      (∫ omega,
          ‖X omega / (Real.sqrt (m : Real) : Complex)‖ ^ 2 ∂mu) =
        (∫ omega, ‖X omega‖ ^ 2 ∂mu) / (m : Real) := by
  have hm0 : (m : Real) ≠ 0 := by exact_mod_cast ne_of_gt hm
  have hsqrt : Real.sqrt (m : Real) ≠ 0 := by positivity
  have hpoint : (fun omega =>
      ‖X omega / (Real.sqrt (m : Real) : Complex)‖ ^ 2) =
      (fun omega => ‖X omega‖ ^ 2 / (m : Real)) := by
    funext omega
    rw [Complex.norm_div, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow,
      Real.sq_sqrt (Nat.cast_nonneg m)]
  rw [hpoint]
  constructor
  · exact hXsq.div_const (m : Real)
  · rw [integral_div]

/-- Unit-variance centered atoms yield the exact elementary input required by
the Hilbert--Schmidt upper-edge estimate (source formula (3.13)) for the
normalized dense/Ginibre comparison process.

No independence assumption is needed for this conclusion. -/
theorem normalizedDenseMatrixProcess_centeredRowSecondMomentInputs
    {M : Nat -> Nat} [forall n, Nonempty (Fin (M n))]
    (atom : forall n, Omega -> Fin (M n) -> Fin (M n) -> Complex)
    (hentry : forall n i j,
      Integrable (fun omega => atom n omega i j) mu)
    (hentrySq : forall n i j,
      Integrable (fun omega => ‖atom n omega i j‖ ^ 2) mu)
    (hcentered : forall n i j,
      ∫ omega, atom n omega i j ∂mu = 0)
    (hunitSecondMoment : forall n i j,
      ∫ omega, ‖atom n omega i j‖ ^ 2 ∂mu = 1) :
    CenteredMatrixRowSecondMomentInputs mu
      (normalizedDenseMatrixProcess atom) 1 := by
  have hMpos : forall n, 0 < M n := by
    intro n
    exact Fin.pos_iff_nonempty.mpr (inferInstance : Nonempty (Fin (M n)))
  constructor
  · norm_num
  · intro n i j
    exact (hentry n i j).div_const _
  · intro n i j
    exact (integral_norm_sq_div_sqrt_nat
      (X := fun omega => atom n omega i j)
      (hMpos n) (hentrySq n i j)).1
  · intro n i j
    simp only [normalizedDenseMatrixProcess_apply, integral_div,
      hcentered, zero_div]
  · intro n i
    have hm : 0 < M n := hMpos n
    have hscaled : forall j : Fin (M n),
        (∫ omega,
            ‖normalizedDenseMatrixProcess atom n omega i j‖ ^ 2 ∂mu) =
          1 / (M n : Real) := by
      intro j
      change (∫ omega,
          ‖atom n omega i j /
            (Real.sqrt (M n : Real) : Complex)‖ ^ 2 ∂mu) = _
      rw [(integral_norm_sq_div_sqrt_nat hm (hentrySq n i j)).2,
        hunitSecondMoment]
    simp_rw [hscaled]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [nsmul_eq_mul, hm.ne']

end ShortRingAnchor
