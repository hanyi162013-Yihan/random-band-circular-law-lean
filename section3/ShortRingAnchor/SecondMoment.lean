import ShortRingAnchor.SingularValues
import ShortRingAnchor.ExternalInputs
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The elementary Hilbert--Schmidt input in Proposition 3.6

This file formalizes the deterministic and probabilistic second-moment
calculation used in source formula (3.13).  In particular, the squared
singular values of a finite complex matrix sum to its entrywise squared
Frobenius norm.  Thus the upper-edge input does not require a random-matrix
comparison theorem.
-/

open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius

noncomputable section

namespace ShortRingAnchor

open Module InnerProductSpace MeasureTheory

/-! ## Deterministic Hilbert--Schmidt identity -/

/-- The sum of the squared singular values equals the sum of the squared
norms of all entries.  This is the finite-dimensional Hilbert--Schmidt
identity underlying formula (3.13). -/
theorem sum_sq_matrixSingularValue_eq_sum_norm_sq_entries {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ j : Fin n, matrixSingularValue A j ^ 2) =
      ∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2 := by
  let T := A.toEuclideanLin
  have hn : finrank ℂ (EuclideanSpace ℂ (Fin n)) = n := by simp
  have heig :
      (∑ j : Fin n, matrixSingularValue A j ^ 2) =
        ∑ j : Fin n,
          T.isSymmetric_adjoint_comp_self.eigenvalues hn j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact T.sq_singularValues_fin hn j
  rw [heig, ← T.isSymmetric_adjoint_comp_self.re_trace_eq_sum_eigenvalues hn]
  have htrace :
      RCLike.re ((T.adjoint ∘ₗ T).trace ℂ (EuclideanSpace ℂ (Fin n))) =
        ∑ j : Fin n, ‖T (EuclideanSpace.basisFun (Fin n) ℂ j)‖ ^ 2 := by
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℂ)]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [LinearMap.adjoint_inner_right, inner_self_eq_norm_sq]
  rw [htrace]
  have hcol : ∀ j : Fin n,
      ‖T (EuclideanSpace.basisFun (Fin n) ℂ j)‖ ^ 2 =
        ∑ i : Fin n, ‖A i j‖ ^ 2 := by
    intro j
    rw [EuclideanSpace.norm_sq_eq]
    simp [T, Matrix.toLpLin_apply]
  rw [Finset.sum_congr rfl (fun j _ => hcol j)]
  exact Finset.sum_comm

/-- Formula (3.13)'s second moment, rewritten exactly as the normalized
entrywise squared norm of the shifted matrix. -/
theorem empiricalSecondMoment_shiftedSingularValueFamily {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    empiricalAverage (shiftedSingularValueFamily A z) (fun t => t ^ 2) =
      (∑ i : Fin n, ∑ j : Fin n,
        ‖(A - z • (1 : Matrix (Fin n) (Fin n) ℂ)) i j‖ ^ 2) /
          (n : ℝ) := by
  unfold empiricalAverage shiftedSingularValueFamily shiftedSingularValue
  rw [sum_sq_matrixSingularValue_eq_sum_norm_sq_entries]
  simp only [Fintype.card_fin]

/-! ## Centering and the scalar second-moment calculation -/

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- A centered integrable complex random variable has zero expected real
inner product against every deterministic vector.  This is the cross-term
cancellation in the Hilbert--Schmidt calculation. -/
theorem integral_re_inner_const_eq_zero_of_centered
    {X : Omega -> ℂ} (z : ℂ)
    (hX : Integrable X mu) (hcentered : ∫ omega, X omega ∂mu = 0) :
    ∫ omega, RCLike.re (inner ℂ (X omega) z) ∂mu = 0 := by
  calc
    ∫ omega, RCLike.re (inner ℂ (X omega) z) ∂mu =
        ∫ omega, RCLike.re (inner ℂ z (X omega)) ∂mu := by
          apply integral_congr_ae
          filter_upwards [] with omega
          exact inner_re_symm _ _
    _ = RCLike.re (∫ omega, inner ℂ z (X omega) ∂mu) :=
      integral_re (Integrable.const_inner z hX)
    _ = RCLike.re (inner ℂ z (∫ omega, X omega ∂mu)) := by
      rw [integral_inner hX z]
    _ = 0 := by simp [hcentered]

/-- Integrability of the shifted square follows from integrability of the
first and second moments. -/
theorem integrable_norm_sq_sub_const
    [IsFiniteMeasure mu]
    {X : Omega -> ℂ} (z : ℂ)
    (hX : Integrable X mu)
    (hXsq : Integrable (fun omega => ‖X omega‖ ^ 2) mu) :
    Integrable (fun omega => ‖X omega - z‖ ^ 2) mu := by
  have hcross : Integrable
      (fun omega => RCLike.re (inner ℂ (X omega) z)) mu :=
    (hX.inner_const z).re
  have hbase : Integrable
      (fun omega => ‖X omega‖ ^ 2 -
        2 * RCLike.re (inner ℂ (X omega) z) + ‖z‖ ^ 2) mu :=
    (hXsq.sub (hcross.const_mul 2)).add (integrable_const (‖z‖ ^ 2))
  refine hbase.congr ?_
  filter_upwards [] with omega
  exact (norm_sub_sq (X omega) z).symm

/-- Exact scalar expectation identity used entrywise in (3.13). -/
theorem integral_norm_sq_sub_const_of_centered
    [IsProbabilityMeasure mu]
    {X : Omega -> ℂ} (z : ℂ)
    (hX : Integrable X mu)
    (hXsq : Integrable (fun omega => ‖X omega‖ ^ 2) mu)
    (hcentered : ∫ omega, X omega ∂mu = 0) :
    ∫ omega, ‖X omega - z‖ ^ 2 ∂mu =
      (∫ omega, ‖X omega‖ ^ 2 ∂mu) + ‖z‖ ^ 2 := by
  have hcross : Integrable
      (fun omega => RCLike.re (inner ℂ (X omega) z)) mu :=
    (hX.inner_const z).re
  have hcrossZero :=
    integral_re_inner_const_eq_zero_of_centered z hX hcentered
  have hscaled : Integrable
      (fun omega => 2 * RCLike.re (inner ℂ (X omega) z)) mu :=
    hcross.const_mul 2
  have hsub : Integrable
      (fun omega => ‖X omega‖ ^ 2 -
        2 * RCLike.re (inner ℂ (X omega) z)) mu :=
    hXsq.sub hscaled
  have hconst : Integrable (fun _ : Omega => ‖z‖ ^ 2) mu :=
    integrable_const _
  rw [show (fun omega => ‖X omega - z‖ ^ 2) =
      (fun omega => ‖X omega‖ ^ 2 -
        2 * RCLike.re (inner ℂ (X omega) z) + ‖z‖ ^ 2) by
    funext omega
    exact norm_sub_sq _ _]
  calc
    ∫ omega, (‖X omega‖ ^ 2 -
        2 * RCLike.re (inner ℂ (X omega) z)) + ‖z‖ ^ 2 ∂mu =
        (∫ omega, ‖X omega‖ ^ 2 -
          2 * RCLike.re (inner ℂ (X omega) z) ∂mu) +
          ∫ _ : Omega, ‖z‖ ^ 2 ∂mu := integral_add hsub hconst
    _ = ((∫ omega, ‖X omega‖ ^ 2 ∂mu) -
          ∫ omega, 2 * RCLike.re (inner ℂ (X omega) z) ∂mu) +
          ∫ _ : Omega, ‖z‖ ^ 2 ∂mu := by rw [integral_sub hXsq hscaled]
    _ = (∫ omega, ‖X omega‖ ^ 2 ∂mu) + ‖z‖ ^ 2 := by
      rw [integral_const_mul, hcrossZero]
      simp

/-! ## Matrix expectation and an `UpperSecondMomentInputs` constructor -/

/-- Entrywise first- and second-moment integrability implies integrability of
the empirical squared singular-value average of the shifted matrix. -/
theorem integrable_empiricalSecondMoment_shiftedSingularValueFamily
    [IsFiniteMeasure mu] {n : ℕ}
    (A : Omega -> Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (hentry : forall i j, Integrable (fun omega => A omega i j) mu)
    (hentrySq : forall i j,
      Integrable (fun omega => ‖A omega i j‖ ^ 2) mu) :
    Integrable (fun omega =>
      empiricalAverage (shiftedSingularValueFamily (A omega) z)
        (fun t => t ^ 2)) mu := by
  have hshift : forall i j, Integrable (fun omega =>
      ‖(A omega - z • (1 : Matrix (Fin n) (Fin n) ℂ)) i j‖ ^ 2) mu := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa [Matrix.one_apply] using
        (integrable_norm_sq_sub_const z (hentry i i) (hentrySq i i))
    · simpa [Matrix.one_apply, hij] using hentrySq i j
  have hsum : Integrable (fun omega =>
      ∑ i : Fin n, ∑ j : Fin n,
        ‖(A omega - z • (1 : Matrix (Fin n) (Fin n) ℂ)) i j‖ ^ 2) mu := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact hshift i j
  have hdiv : Integrable (fun omega =>
      (∑ i : Fin n, ∑ j : Fin n,
        ‖(A omega - z • (1 : Matrix (Fin n) (Fin n) ℂ)) i j‖ ^ 2) /
          (n : ℝ)) mu := hsum.div_const n
  refine hdiv.congr ?_
  filter_upwards [] with omega
  exact (empiricalSecondMoment_shiftedSingularValueFamily (A omega) z).symm

/-- Exact expected Hilbert--Schmidt identity.  If every row has total
second moment `C` and all entries are centered, then the empirical second
moment of the singular values of `A-zI` has expectation `C+‖z‖²`.

No independence assumption is used. -/
theorem integral_empiricalSecondMoment_shiftedSingularValueFamily
    [IsProbabilityMeasure mu] {n : ℕ} [Nonempty (Fin n)]
    (A : Omega -> Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (C : ℝ)
    (hentry : forall i j, Integrable (fun omega => A omega i j) mu)
    (hentrySq : forall i j,
      Integrable (fun omega => ‖A omega i j‖ ^ 2) mu)
    (hcentered : forall i j, ∫ omega, A omega i j ∂mu = 0)
    (hrow : forall i,
      ∑ j : Fin n, ∫ omega, ‖A omega i j‖ ^ 2 ∂mu = C) :
    ∫ omega,
        empiricalAverage (shiftedSingularValueFamily (A omega) z)
          (fun t => t ^ 2) ∂mu = C + ‖z‖ ^ 2 := by
  have hshift : forall i j, Integrable (fun omega =>
      ‖(A omega - z • (1 : Matrix (Fin n) (Fin n) ℂ)) i j‖ ^ 2) mu := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa [Matrix.one_apply] using
        (integrable_norm_sq_sub_const z (hentry i i) (hentrySq i i))
    · simpa [Matrix.one_apply, hij] using hentrySq i j
  have hshiftIntegral : forall i j,
      ∫ omega,
          ‖(A omega - z • (1 : Matrix (Fin n) (Fin n) ℂ)) i j‖ ^ 2 ∂mu =
        (∫ omega, ‖A omega i j‖ ^ 2 ∂mu) +
          if i = j then ‖z‖ ^ 2 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa [Matrix.one_apply] using
        (integral_norm_sq_sub_const_of_centered z
          (hentry i i) (hentrySq i i) (hcentered i i))
    · simp [hij]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun omega =>
    empiricalSecondMoment_shiftedSingularValueFamily (A omega) z)]
  rw [integral_div]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hshift i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hshift _ j),
    hshiftIntegral]
  simp_rw [Finset.sum_add_distrib]
  simp [hrow]
  have hn : (n : ℝ) ≠ 0 := by
    have hnNat : n ≠ 0 := by
      simpa only [Fintype.card_fin] using
        (Fintype.card_ne_zero : Fintype.card (Fin n) ≠ 0)
    exact_mod_cast hnNat
  rw [div_eq_iff hn]
  ring

/-- Elementary entrywise hypotheses sufficient for the upper-edge
Hilbert--Schmidt estimate.  This is a package of ordinary first and second
moment facts, not a random-matrix comparison input. -/
structure CenteredMatrixRowSecondMomentInputs
    {M : Nat -> Nat}
    (mu : Measure Omega)
    (A : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (C : ℝ) : Prop where
  C_nonneg : 0 <= C
  entry_integrable : forall n i j,
    Integrable (fun omega => A n omega i j) mu
  entry_sq_integrable : forall n i j,
    Integrable (fun omega => ‖A n omega i j‖ ^ 2) mu
  centered : forall n i j, ∫ omega, A n omega i j ∂mu = 0
  row_secondMoment : forall n i,
    ∑ j : Fin (M n), ∫ omega, ‖A n omega i j‖ ^ 2 ∂mu = C

/-- Two elementary centered-entry moment packages construct the complete
`UpperSecondMomentInputs` used in (3.13), with the exact constants
`C_H + ‖z‖²` and `C_G + ‖z‖²`. -/
theorem upperSecondMomentInputs_of_centered_matrix_entries
    [IsProbabilityMeasure mu]
    {M N : Nat -> Nat}
    [forall n, Nonempty (Fin (M n))]
    [forall n, Nonempty (Fin (N n))]
    (H : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (G : forall n, Omega -> Matrix (Fin (N n)) (Fin (N n)) ℂ)
    (z : ℂ) (CH CG : ℝ)
    (hH : CenteredMatrixRowSecondMomentInputs mu H CH)
    (hG : CenteredMatrixRowSecondMomentInputs mu G CG) :
    UpperSecondMomentInputs mu
      (shiftedSingularValueProcess H z)
      (shiftedSingularValueProcess G z)
      (CH + ‖z‖ ^ 2) (CG + ‖z‖ ^ 2) := by
  constructor
  · exact add_nonneg hH.C_nonneg (sq_nonneg _)
  · exact add_nonneg hG.C_nonneg (sq_nonneg _)
  · intro n
    simpa [shiftedSingularValueProcess] using
      integrable_empiricalSecondMoment_shiftedSingularValueFamily
        (H n) z (hH.entry_integrable n) (hH.entry_sq_integrable n)
  · intro n
    simpa [shiftedSingularValueProcess] using
      integrable_empiricalSecondMoment_shiftedSingularValueFamily
        (G n) z (hG.entry_integrable n) (hG.entry_sq_integrable n)
  · intro n
    exact (integral_empiricalSecondMoment_shiftedSingularValueFamily
      (H n) z CH (hH.entry_integrable n) (hH.entry_sq_integrable n)
      (hH.centered n) (hH.row_secondMoment n)).le
  · intro n
    exact (integral_empiricalSecondMoment_shiftedSingularValueFamily
      (G n) z CG (hG.entry_integrable n) (hG.entry_sq_integrable n)
      (hG.centered n) (hG.row_secondMoment n)).le

/-- `UpperSecondMomentInputs` is unchanged when each singular-value family
is modified on a null set.  This is needed for the everywhere-positive
representative used by the logarithmic truncation proof. -/
theorem UpperSecondMomentInputs.congr_ae
    {M N : Nat -> Nat}
    [forall n, Fintype (Fin (M n))]
    [forall n, Fintype (Fin (N n))]
    {h h' : forall n, Omega -> Fin (M n) -> Real}
    {g g' : forall n, Omega -> Fin (N n) -> Real}
    {CH CG : Real}
    (hInput : UpperSecondMomentInputs mu h g CH CG)
    (hh : forall n, h n =ᵐ[mu] h' n)
    (hg : forall n, g n =ᵐ[mu] g' n) :
    UpperSecondMomentInputs mu h' g' CH CG := by
  have hhAverage : forall n,
      (fun omega => empiricalAverage (h n omega) (fun t => t ^ 2)) =ᵐ[mu]
      (fun omega => empiricalAverage (h' n omega) (fun t => t ^ 2)) := by
    intro n
    filter_upwards [hh n] with omega homega
    rw [homega]
  have hgAverage : forall n,
      (fun omega => empiricalAverage (g n omega) (fun t => t ^ 2)) =ᵐ[mu]
      (fun omega => empiricalAverage (g' n omega) (fun t => t ^ 2)) := by
    intro n
    filter_upwards [hg n] with omega homega
    rw [homega]
  constructor
  · exact hInput.CH_nonneg
  · exact hInput.CG_nonneg
  · intro n
    exact (hInput.h_integrable n).congr (hhAverage n)
  · intro n
    exact (hInput.g_integrable n).congr (hgAverage n)
  · intro n
    rw [← integral_congr_ae (hhAverage n)]
    exact hInput.h_mean n
  · intro n
    rw [← integral_congr_ae (hgAverage n)]
    exact hInput.g_mean n

/-- Centered entry moments also construct the upper-edge input for the
positive singular-value representatives, assuming only a.e.
nonsingularity. -/
theorem upperSecondMomentInputs_positiveProcess_of_centered_matrix_entries
    [IsProbabilityMeasure mu]
    {M N : Nat -> Nat}
    [forall n, Nonempty (Fin (M n))]
    [forall n, Nonempty (Fin (N n))]
    (H : forall n, Omega -> Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (G : forall n, Omega -> Matrix (Fin (N n)) (Fin (N n)) ℂ)
    (z : ℂ) (CH CG : ℝ)
    (hH : CenteredMatrixRowSecondMomentInputs mu H CH)
    (hG : CenteredMatrixRowSecondMomentInputs mu G CG)
    (hdetH : forall n, ∀ᵐ omega ∂mu,
      (H n omega - z •
        (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0)
    (hdetG : forall n, ∀ᵐ omega ∂mu,
      (G n omega - z •
        (1 : Matrix (Fin (N n)) (Fin (N n)) ℂ)).det ≠ 0) :
    UpperSecondMomentInputs mu
      (positiveShiftedSingularValueProcess H z)
      (positiveShiftedSingularValueProcess G z)
      (CH + ‖z‖ ^ 2) (CG + ‖z‖ ^ 2) := by
  have hbase := upperSecondMomentInputs_of_centered_matrix_entries
    H G z CH CG hH hG
  exact hbase.congr_ae
    (fun n => (positiveShiftedSingularValueProcess_ae_eq H z hdetH n).symm)
    (fun n => (positiveShiftedSingularValueProcess_ae_eq G z hdetG n).symm)

end ShortRingAnchor
