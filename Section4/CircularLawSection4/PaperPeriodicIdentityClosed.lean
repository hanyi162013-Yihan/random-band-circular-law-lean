import CircularLawSection4.PaperBandMatrixIdentification
import CircularLawSection4.PaperCyclicMonodromyBridge

/-!
# Closed paper-specific periodic determinant identity

The two notation interfaces in the manuscript's periodic determinant proof
are now available separately:

* `PaperBandMatrixIdentification` identifies the raw band matrix with the
  literal matrix `X_N - z I_N`;
* `PaperCyclicMonodromyBridge` identifies its state-copy determinant with the
  determinant of the chronological companion monodromy.

This module composes them with the denominator-cleared exterior Floquet
identity.  The resulting theorem mentions only the shifted scalar band
matrix, an explicit list of cleared companion steps, and one deterministic
sign.  In particular, no raw-band, state-copy, or determinant-comparison
hypothesis remains in its statement.

For the symmetric scalar band in the manuscript, specialize `m + 1 = 2W`
and `center.val = W`.  The full coefficient index then runs through the
offsets `-W, ..., W`, while the final coefficient is `beta_i`.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix

/-- The canonical denominator-cleared steps in the ordinary `Fin N` order.
At site `p` the scalar is the right-edge coefficient `beta_i`, and the matrix
is the companion transfer at the corresponding raw cyclic site
`i = ZMod.finEquiv N p`. -/
def paperCyclicClearedSteps
    (N m : ℕ) [NeZero N]
    (βraw : ZMod N → ℂ) (a : ZMod N → Fin (m + 1) → ℂ) :
    List (ℂ × Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :=
  List.ofFn fun p : Fin N =>
    (βraw (ZMod.finEquiv N p),
      paperCyclicTransferMatrix N m βraw a (ZMod.finEquiv N p))

/-- Forgetting the clearing scalars from the canonical steps gives exactly
the paper's chronological transfer list. -/
theorem transferList_paperCyclicClearedSteps
    (N m : ℕ) [NeZero N]
    (βraw : ZMod N → ℂ) (a : ZMod N → Fin (m + 1) → ℂ) :
    transferList (paperCyclicClearedSteps N m βraw a) =
      paperCyclicTransferList N m βraw a := by
  simp [transferList, paperCyclicClearedSteps, paperCyclicTransferList,
    Function.comp_def]

/-- The clearing factor of the canonical list is the product of the raw
right-edge coefficients in the standard finite cyclic order. -/
theorem clearingFactor_paperCyclicClearedSteps
    (N m : ℕ) [NeZero N]
    (βraw : ZMod N → ℂ) (a : ZMod N → Fin (m + 1) → ℂ) :
    clearingFactor (paperCyclicClearedSteps N m βraw a) =
      ∏ p : Fin N, βraw (ZMod.finEquiv N p) := by
  simp [clearingFactor, paperCyclicClearedSteps, List.prod_ofFn]

/-- The product arising from the physical state-copy row order is the same
as the canonical clearing factor.  The two orders differ only by the explicit
cyclic row equivalence used in `PaperCyclicBandReindex`. -/
theorem paperCyclicOrderedScaling_prod_eq_clearingFactor
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (βraw : ZMod N → ℂ) (a : ZMod N → Fin (m + 1) → ℂ) :
    (∏ p, paperCyclicOrderedScaling N m offset βraw p) =
      clearingFactor (paperCyclicClearedSteps N m βraw a) := by
  rw [clearingFactor_paperCyclicClearedSteps]
  change
    (∏ p : Fin N, βraw (cyclicAnchorEquationRawSite N m offset p)) =
      ∏ p : Fin N, βraw (ZMod.finEquiv N p)
  calc
    (∏ p : Fin N, βraw (cyclicAnchorEquationRawSite N m offset p)) =
        ∏ i : ZMod N, βraw i := by
      simpa only [paperCyclicBandRowEquiv_symm_apply] using
        (paperCyclicBandRowEquiv N m offset).symm.prod_comp βraw
    _ = ∏ p : Fin N, βraw (ZMod.finEquiv N p) :=
      ((ZMod.finEquiv N).prod_comp βraw).symm

/-- Closed raw-band form: physical state-copy elimination, cyclic monodromy
elimination, and denominator-cleared exterior algebra have all been composed.
The only assumption is the pointwise nonvanishing needed to solve each row
for its right-edge coordinate. -/
theorem paperCyclicRawBandMatrix_det_eq_clearedSignedCompoundTrace
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (βraw : ZMod N → ℂ) (hβ : ∀ i, βraw i ≠ 0)
    (a : ZMod N → Fin (m + 1) → ℂ) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      (paperCyclicRawBandMatrix N m offset βraw a).det =
        σ * clearedSignedCompoundTrace
          (paperCyclicClearedSteps N m βraw a) := by
  obtain ⟨σ, hσ, hraw⟩ :=
    paperCyclicRawBandMatrix_det_eq_monodromy
      N m offset βraw hβ a
  refine ⟨σ, hσ, ?_⟩
  calc
    (paperCyclicRawBandMatrix N m offset βraw a).det =
        σ * (∏ p, paperCyclicOrderedScaling N m offset βraw p) *
          (1 - chronologicalProduct
            (paperCyclicTransferList N m βraw a)).det := hraw
    _ = σ *
        clearingFactor (paperCyclicClearedSteps N m βraw a) *
          (1 - chronologicalProduct
            (transferList (paperCyclicClearedSteps N m βraw a))).det := by
      rw [paperCyclicOrderedScaling_prod_eq_clearingFactor,
        transferList_paperCyclicClearedSteps]
    _ = σ * clearedSignedCompoundTrace
          (paperCyclicClearedSteps N m βraw a) := by
      rw [cleared_floquet_exterior_identity]
      ring

/-- Canonical cleared steps attached directly to the literal shifted scalar
band matrix. -/
def paperShiftedScalarClearedSteps
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (x : ZMod N → Fin (m + 2) → ℂ) (z : ℂ) :
    List (ℂ × Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :=
  paperCyclicClearedSteps N m
    (paperRightEdgeCoefficient m x)
    (paperShiftedInteriorCoefficient m center x z)

/-- **Closed periodic determinant identity for `X_N - z I_N`.**

The determinant of the literal shifted cyclic scalar band matrix is a
deterministic sign times the alternating trace of the canonical
denominator-cleared exterior companion products.  All intermediate raw-band
and state-copy matrices have disappeared from the statement. -/
theorem paperShiftedScalarBandMatrix_det_eq_clearedSignedCompoundTrace
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (x : ZMod N → Fin (m + 2) → ℂ) (z : ℂ)
    (hβ : ∀ i, paperRightEdgeCoefficient m x i ≠ 0) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      (paperShiftedScalarBandMatrix N m center x z).det =
        σ * clearedSignedCompoundTrace
          (paperShiftedScalarClearedSteps N m center x z) := by
  obtain ⟨σ, hσ, hraw⟩ :=
    paperCyclicRawBandMatrix_det_eq_clearedSignedCompoundTrace
      N m (-(center.val : ZMod N))
      (paperRightEdgeCoefficient m x) hβ
      (paperShiftedInteriorCoefficient m center x z)
  refine ⟨σ, hσ, ?_⟩
  rw [← paperCyclicRawBandMatrix_eq_paperShiftedScalarBandMatrix
    (R := ℂ) N m center x z]
  exact hraw

/-- The same closed identity with the manuscript's factorized coefficients
`x_{i,k} = b_k xi_{i,k}` written explicitly. -/
theorem paperXSubZI_det_eq_clearedSignedCompoundTrace
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (b : Fin (m + 2) → ℂ) (xi : ZMod N → Fin (m + 2) → ℂ) (z : ℂ)
    (hβ : ∀ i,
      b (Fin.last (m + 1)) * xi i (Fin.last (m + 1)) ≠ 0) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      (paperShiftedScalarBandMatrix N m center
        (fun i k ↦ b k * xi i k) z).det =
        σ * clearedSignedCompoundTrace
          (paperShiftedScalarClearedSteps N m center
            (fun i k ↦ b k * xi i k) z) := by
  apply paperShiftedScalarBandMatrix_det_eq_clearedSignedCompoundTrace
  exact hβ

end CircularLawSection4
