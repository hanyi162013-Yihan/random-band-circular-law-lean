import CircularLawSection4.PaperConditionalCompletion
import CircularLawSections56.Section5.NearEndToEnd
import Mathlib.Data.Fin.Tuple.Take

/-!
# Literal determinant/fresh-block adapters

This file records the thin pieces of the Section 4-to-Section 5 adapter which follow
directly from the literal finite-coordinate definitions.

The first deterministic chain identifies Section 4's abstract `paperIndicatorFreshZ`
with the alternating exterior trace of an actually sampled fresh block.  For the
nonwrapping block at `start = 0`, this file also proves the full-list split, the
finset-to-exterior-degree regrouping, and the literal determinant/log-norm identity; no
external split premise remains.  The arbitrary cyclic-start theorem retains an explicit
`hSplit` compatibility premise because its additional list rotation and trace-cyclicity
reindexing are not packaged here.

The final two theorems transport Bochner integrals and the quantitative two-step `L¹`
receiver used by `NearEndToEnd` along an arbitrary measure-preserving map.  They are the
probability-space part of the adapter: after a literal coordinate split/reassembly has
been proved measure preserving, its estimates can be moved without changing either
error rate.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

/-- The compound matrix of the identity is the identity in every degree. -/
@[simp] theorem compound_one_adapter
    {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] (k : ℕ) :
    compound k (1 : Matrix n n ℂ) = 1 := by
  unfold compound
  rw [Matrix.toLin'_one, exteriorPower.map_id]
  exact LinearMap.toMatrix_id _

/-- The cleared exterior product has the same reverse-order append law as
`chronologicalProduct`.  This discharges the purely multiplicative part of the missing
full-trace block split.
-/
theorem clearedCompoundProduct_append
    {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (k : ℕ) (fresh outside : List (ℂ × Matrix n n ℂ)) :
    clearedCompoundProduct k (fresh ++ outside) =
      clearedCompoundProduct k outside * clearedCompoundProduct k fresh := by
  induction fresh with
  | nil => simp [clearedCompoundProduct]
  | cons x fresh ih =>
      rcases x with ⟨beta, T⟩
      simp only [List.cons_append, clearedCompoundProduct]
      rw [ih, Matrix.mul_assoc]

/-- A cleared compound product is the chronological product of the individually cleared
compound matrices. -/
theorem clearedCompoundProduct_eq_chronologicalProduct_map
    {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (k : ℕ) (xs : List (ℂ × Matrix n n ℂ)) :
    clearedCompoundProduct k xs =
      chronologicalProduct
        (xs.map fun step ↦ clearedCompound k step.1 step.2) := by
  induction xs with
  | nil => simp [clearedCompoundProduct]
  | cons x xs ih =>
      rcases x with ⟨beta, T⟩
      simp only [clearedCompoundProduct, List.map_cons,
        chronologicalProduct_cons]
      rw [ih]

/-- Reindex all finsets by their cardinality and their membership in the corresponding
`powersetCard`.  This is the finite coordinate equivalence underlying the passage from
Section 4's bundled `Finset` sum to an exterior-degree/trace sum.
-/
def exteriorIndexSigmaEquivFinset (d : ℕ) :
    (Σ q : ExteriorDegree d, ↑(ExteriorIndex d q)) ≃ Finset (Fin d) :=
  Equiv.ofBijective (fun qi ↦ qi.2.1) (by
    constructor
    · rintro ⟨q, I⟩ ⟨r, J⟩ h
      have hval : q.val = r.val := by
        calc
          q.val = I.1.card := I.2.symm
          _ = J.1.card := congrArg Finset.card h
          _ = r.val := J.2
      have hqr : q = r := Fin.ext hval
      subst r
      have hIJ : I = J := Subtype.ext h
      subst J
      rfl
    · intro s
      let q : ExteriorDegree d :=
        ⟨s.card, Nat.lt_succ_of_le (by
          simpa only [Finset.card_univ, Fintype.card_fin] using
            Finset.card_le_univ s)⟩
      exact ⟨⟨q, ⟨s, rfl⟩⟩, rfl⟩)

@[simp] theorem exteriorIndexSigmaEquivFinset_apply
    (d : ℕ) (q : ExteriorDegree d) (I : ExteriorIndex d q) :
    exteriorIndexSigmaEquivFinset d ⟨q, I⟩ = I.1 := rfl

/-- Section 4's finset-bundled cleared trace is the usual sum, over exterior degrees,
of the matrix traces of the cleared products.
-/
theorem clearedSignedCompoundTrace_eq_sum_trace (d : ℕ)
    (xs : List (ℂ × Matrix (Fin d) (Fin d) ℂ)) :
    clearedSignedCompoundTrace xs =
      ∑ q : ExteriorDegree d, (-1 : ℂ) ^ q.val *
        Matrix.trace (clearedCompoundProduct q.val xs) := by
  classical
  unfold clearedSignedCompoundTrace
  rw [← (exteriorIndexSigmaEquivFinset d).sum_comp]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _
  rw [Matrix.trace, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  simp only [exteriorIndexSigmaEquivFinset_apply]
  rcases q with ⟨q, hq⟩
  rcases I with ⟨s, hs⟩
  dsimp only at hs ⊢
  change s.card = q at hs
  subst q
  rfl

/-- Full algebraic block split for cleared traces.  The order is the one needed by the
fresh scalar: the frozen outside product multiplies the fresh product on the left.
-/
theorem clearedSignedCompoundTrace_append_eq_sum_trace (d : ℕ)
    (fresh outside : List (ℂ × Matrix (Fin d) (Fin d) ℂ)) :
    clearedSignedCompoundTrace (fresh ++ outside) =
      ∑ q : ExteriorDegree d, (-1 : ℂ) ^ q.val *
        Matrix.trace
          (clearedCompoundProduct q.val outside *
            clearedCompoundProduct q.val fresh) := by
  rw [clearedSignedCompoundTrace_eq_sum_trace]
  apply Finset.sum_congr rfl
  intro q _
  rw [clearedCompoundProduct_append]

/-- On the nonwrapping prefix, ordinary `Fin N` order agrees with the paper's fresh-row
sites starting at zero. -/
theorem zmod_finEquiv_castLE_eq_paperIndicatorFreshRowSite_zero
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N) (t : Fin (m + 1)) :
    ZMod.finEquiv N (Fin.castLE hsize t) =
      paperIndicatorFreshRowSite N m 0 t := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N =>
      simp only [paperIndicatorFreshRowSite, ZMod.finEquiv, zero_add]
      apply Fin.ext
      exact (Nat.mod_eq_of_lt (lt_of_lt_of_le t.isLt hsize)).symm

/-- For a fresh block starting at zero, mapping the first `m+1` literal cleared steps to
degree `q` gives exactly Section 4's sampled fresh exterior rows.
-/
theorem paperIndicatorClearedSteps_take_map_eq_freshRows_zero
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (ω : Fin (N * (m + 2)) → ℂ) (q : ExteriorDegree (m + 1)) :
    ((paperIndicatorClearedSteps N m center profile.b ω z).take (m + 1)).map
        (fun step ↦ clearedCompound q.val step.1 step.2) =
      paperIndicatorFreshClearedExteriorRows
        N m profile center z 0 ω q := by
  unfold paperIndicatorClearedSteps paperShiftedScalarClearedSteps
    paperCyclicClearedSteps
  rw [← Fin.ofFn_take_eq_take_ofFn hsize]
  simp only [List.map_ofFn]
  unfold paperIndicatorFreshClearedExteriorRows
  apply List.ofFn_inj.2
  funext t
  simp only [Function.comp_apply, Fin.take_apply, clearedCompound]
  rw [zmod_finEquiv_castLE_eq_paperIndicatorFreshRowSite_zero N m hsize t]
  rfl

namespace PaperIndicatorWeights

/-- The abstract fresh scalar is exactly the alternating trace of the genuine sampled
fresh block.  Only nonvanishing of the clearing coefficient on the fresh sites is used.
-/
theorem paperIndicatorFreshZ_eq_freshBlockAlternatingTrace
    (N m : ℕ) [NeZero N] {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (start : ZMod N) (ω : Fin (N * (m + 2)) → ℂ)
    (B : (q : ExteriorDegree (m + 1)) →
      Matrix (ExteriorIndex (m + 1) q) (ExteriorIndex (m + 1) q) ℂ)
    (hβ : ∀ t : Fin (m + 1),
      paperIndicatorBetaRaw N m profile ω
        (paperIndicatorFreshRowSite N m start t) ≠ 0) :
    profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtoms N m start ω) B =
      paperIndicatorFreshBlockAlternatingTrace
        N m profile center z start ω B := by
  classical
  unfold paperIndicatorFreshZ paperIndicatorFreshBlockAlternatingTrace
  apply Finset.sum_congr rfl
  intro q _
  apply congrArg (fun X ↦ (-1 : ℂ) ^ q.val * Matrix.trace (B q * X))
  apply congrArg chronologicalProduct
  apply List.ofFn_inj.2
  funext t
  exact paperIndicatorFreshExteriorRow_eq_clearedCompound_transfer
    N m profile center z start ω q t (hβ t)

/-- The frozen exterior family obtained from all literal cleared steps after the first
`m+1` rows.  This is the outside product for the nonwrapping fresh block at `start = 0`.
-/
def paperIndicatorOutsideClearedProductZero
    (N m : ℕ) [NeZero N] {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (ω : Fin (N * (m + 2)) → ℂ)
    (q : ExteriorDegree (m + 1)) :
    Matrix (ExteriorIndex (m + 1) q) (ExteriorIndex (m + 1) q) ℂ :=
  clearedCompoundProduct q.val
    ((paperIndicatorClearedSteps N m center profile.b ω z).drop (m + 1))

/-- Exact paper-specific full-trace split for the nonwrapping fresh block starting at
zero.  Unlike the arbitrary-start compatibility theorem below, this has no `hSplit`
premise: the frozen family is the explicit product of the remaining literal steps.
-/
theorem paperIndicator_clearedSignedCompoundTrace_eq_freshBlock_zero
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (ω : Fin (N * (m + 2)) → ℂ) :
    clearedSignedCompoundTrace
        (paperIndicatorClearedSteps N m center profile.b ω z) =
      paperIndicatorFreshBlockAlternatingTrace
        N m profile center z 0 ω
          (paperIndicatorOutsideClearedProductZero
            N m profile center z ω) := by
  let full := paperIndicatorClearedSteps N m center profile.b ω z
  rw [show paperIndicatorClearedSteps N m center profile.b ω z = full by rfl]
  rw [← List.take_append_drop (m + 1) full]
  rw [clearedSignedCompoundTrace_append_eq_sum_trace]
  unfold paperIndicatorFreshBlockAlternatingTrace
  apply Finset.sum_congr rfl
  intro q _
  unfold paperIndicatorOutsideClearedProductZero
  rw [show paperIndicatorClearedSteps N m center profile.b ω z = full by rfl]
  rw [clearedCompoundProduct_eq_chronologicalProduct_map
    q.val (full.take (m + 1))]
  rw [show full.take (m + 1) =
      (paperIndicatorClearedSteps N m center profile.b ω z).take (m + 1) by rfl]
  rw [paperIndicatorClearedSteps_take_map_eq_freshRows_zero
    N m hsize profile center z ω q]

/-- Literal determinant-to-FreshZ identity for the block at `start = 0`, with no
external split premise. -/
theorem paperIndicatorXSubZI_det_eq_sign_mul_freshZ_zero
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (ω : Fin (N * (m + 2)) → ℂ)
    (hβ : ∀ i : ZMod N,
      profile.b (Fin.last (m + 1)) *
        paperIndicatorXi N m ω i (Fin.last (m + 1)) ≠ 0) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      (paperIndicatorXSubZI N m center profile.b ω z).det =
        σ * profile.paperIndicatorFreshZ center z
          (paperIndicatorFreshAtoms N m 0 ω)
          (paperIndicatorOutsideClearedProductZero
            N m profile center z ω) := by
  let B := paperIndicatorOutsideClearedProductZero N m profile center z ω
  have hFreshβ : ∀ t : Fin (m + 1),
      paperIndicatorBetaRaw N m profile ω
        (paperIndicatorFreshRowSite N m 0 t) ≠ 0 := by
    intro t
    simpa only [paperIndicatorBetaRaw_apply] using
      hβ (paperIndicatorFreshRowSite N m 0 t)
  have hFresh := profile.paperIndicatorFreshZ_eq_freshBlockAlternatingTrace
    N m center z 0 ω B hFreshβ
  have hSplit :=
    profile.paperIndicator_clearedSignedCompoundTrace_eq_freshBlock_zero
      N m hsize center z ω
  obtain ⟨σ, hσ, hDet⟩ :=
    paperIndicatorXSubZI_det_eq_clearedSignedCompoundTrace
      N m center profile.b ω z hβ
  refine ⟨σ, hσ, ?_⟩
  change (paperIndicatorXSubZI N m center profile.b ω z).det =
    σ * profile.paperIndicatorFreshZ center z
      (paperIndicatorFreshAtoms N m 0 ω) B
  calc
    (paperIndicatorXSubZI N m center profile.b ω z).det =
        σ * clearedSignedCompoundTrace
          (paperIndicatorClearedSteps N m center profile.b ω z) := hDet
    _ = σ * paperIndicatorFreshBlockAlternatingTrace
          N m profile center z 0 ω B := congrArg (σ * ·) hSplit
    _ = σ * profile.paperIndicatorFreshZ center z
          (paperIndicatorFreshAtoms N m 0 ω) B := congrArg (σ * ·) hFresh.symm

/-- Log-norm form of `paperIndicatorXSubZI_det_eq_sign_mul_freshZ_zero`.  It uses
Lean's totalized logarithm and therefore remains an equality when both sides vanish.
-/
theorem log_norm_paperIndicatorXSubZI_det_eq_log_norm_freshZ_zero
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (ω : Fin (N * (m + 2)) → ℂ)
    (hβ : ∀ i : ZMod N,
      profile.b (Fin.last (m + 1)) *
        paperIndicatorXi N m ω i (Fin.last (m + 1)) ≠ 0) :
    Real.log ‖(paperIndicatorXSubZI N m center profile.b ω z).det‖ =
      Real.log ‖profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtoms N m 0 ω)
        (paperIndicatorOutsideClearedProductZero
          N m profile center z ω)‖ := by
  obtain ⟨σ, hσ, hDet⟩ :=
    profile.paperIndicatorXSubZI_det_eq_sign_mul_freshZ_zero
      N m hsize center z ω hβ
  have hNormσ : ‖σ‖ = (1 : ℝ) := by
    rcases hσ with rfl | rfl <;> simp
  rw [hDet, norm_mul, hNormσ, one_mul]

/-- Literal determinant-to-fresh-scalar bridge, conditional only on the presently
unpackaged full-trace block split `hSplit`.

The sign is the genuine sign supplied by Section 4's pointwise determinant identity;
`hSplit` is the remaining deterministic list/regrouping seam and is not presented as a
probabilistic or analytic hypothesis.
-/
theorem paperIndicatorXSubZI_det_eq_sign_mul_freshZ_of_blockSplit
    (N m : ℕ) [NeZero N] {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (start : ZMod N) (ω : Fin (N * (m + 2)) → ℂ)
    (B : (q : ExteriorDegree (m + 1)) →
      Matrix (ExteriorIndex (m + 1) q) (ExteriorIndex (m + 1) q) ℂ)
    (hβ : ∀ i : ZMod N,
      profile.b (Fin.last (m + 1)) *
        paperIndicatorXi N m ω i (Fin.last (m + 1)) ≠ 0)
    (hSplit :
      clearedSignedCompoundTrace
          (paperIndicatorClearedSteps N m center profile.b ω z) =
        paperIndicatorFreshBlockAlternatingTrace
          N m profile center z start ω B) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      (paperIndicatorXSubZI N m center profile.b ω z).det =
        σ * profile.paperIndicatorFreshZ center z
          (paperIndicatorFreshAtoms N m start ω) B := by
  have hFreshβ : ∀ t : Fin (m + 1),
      paperIndicatorBetaRaw N m profile ω
        (paperIndicatorFreshRowSite N m start t) ≠ 0 := by
    intro t
    simpa only [paperIndicatorBetaRaw_apply] using
      hβ (paperIndicatorFreshRowSite N m start t)
  have hFresh := profile.paperIndicatorFreshZ_eq_freshBlockAlternatingTrace
    N m center z start ω B hFreshβ
  obtain ⟨σ, hσ, hDet⟩ :=
    paperIndicatorXSubZI_det_eq_clearedSignedCompoundTrace
      N m center profile.b ω z hβ
  refine ⟨σ, hσ, ?_⟩
  calc
    (paperIndicatorXSubZI N m center profile.b ω z).det =
        σ * clearedSignedCompoundTrace
          (paperIndicatorClearedSteps N m center profile.b ω z) := hDet
    _ = σ * paperIndicatorFreshBlockAlternatingTrace
          N m profile center z start ω B := congrArg (σ * ·) hSplit
    _ = σ * profile.paperIndicatorFreshZ center z
          (paperIndicatorFreshAtoms N m start ω) B := congrArg (σ * ·) hFresh.symm

/-- Taking norms removes Section 4's determinant sign.  The statement remains valid at
zero because both sides use Lean's totalized `Real.log`; no nonzero-log convention is
silently assumed.
-/
theorem log_norm_paperIndicatorXSubZI_det_eq_log_norm_freshZ_of_blockSplit
    (N m : ℕ) [NeZero N] {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (start : ZMod N) (ω : Fin (N * (m + 2)) → ℂ)
    (B : (q : ExteriorDegree (m + 1)) →
      Matrix (ExteriorIndex (m + 1) q) (ExteriorIndex (m + 1) q) ℂ)
    (hβ : ∀ i : ZMod N,
      profile.b (Fin.last (m + 1)) *
        paperIndicatorXi N m ω i (Fin.last (m + 1)) ≠ 0)
    (hSplit :
      clearedSignedCompoundTrace
          (paperIndicatorClearedSteps N m center profile.b ω z) =
        paperIndicatorFreshBlockAlternatingTrace
          N m profile center z start ω B) :
    Real.log ‖(paperIndicatorXSubZI N m center profile.b ω z).det‖ =
      Real.log ‖profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtoms N m start ω) B‖ := by
  obtain ⟨σ, hσ, hDet⟩ :=
    profile.paperIndicatorXSubZI_det_eq_sign_mul_freshZ_of_blockSplit
      N m center z start ω B hβ hSplit
  have hNormσ : ‖σ‖ = (1 : ℝ) := by
    rcases hσ with rfl | rfl <;> simp
  rw [hDet, norm_mul, hNormσ, one_mul]

/-- Direct complex-law Section 4 input for the Section 5 raw seam.

The first two conjuncts are the unnormalized joint `L¹` certificate used before the
Section 5 length normalization.  The last two conjuncts retain Section 4's canonical
conditional-expectation identification and its almost-everywhere bound; no generic
transport premise is substituted for the literal FreshZ theorem.
-/
theorem complex_paperIndicatorFlatFreshZ_rawJointClosure_withDensity
    {Past : Type*} [MeasurableSpace Past]
    (muPast : Measure Past) [IsProbabilityMeasure muPast]
    (N d : ℕ) [NeZero N] (hsize : d + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1)) (z : ℂ) (start : ZMod N)
    (B : Past → (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hBpos : ∀ a, 0 < exteriorFamilyMaxL2OpNorm (B a))
    (hBmeas : ∀ q i j, Measurable (fun a ↦ B a q i j))
    (hBnorm : ∀ q, Measurable (fun a ↦ ‖B a q‖))
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : ℂ ↦ ‖u‖ ^ 2)
      (volume.withDensity f))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(volume.withDensity f) ≤ 1) :
    let muFresh := paperIndicatorSampleMeasure N d (volume.withDensity f)
    let radius := fun w : Past × (Fin (N * (d + 2)) → ℂ) ↦
      ‖profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtoms N d start w.2) (B w.1)‖
    let scale := fun a : Past ↦ exteriorFamilyMaxL2OpNorm (B a)
    let g := fun w ↦ |Real.log (radius w) - Real.log (scale w.1)|
    let C := paperIsolatedCoefficientLoss d c₀ +
      complexFreshNegativeBound d L + paperFreshPositiveBound d z
    Integrable g (muPast.prod muFresh) ∧
      ∫ w, g w ∂(muPast.prod muFresh) ≤ C ∧
      (muPast.prod muFresh)[g |
          (inferInstance : MeasurableSpace Past).comap Prod.fst] =ᵐ[
            muPast.prod muFresh]
        (fun w ↦ ∫ x, g (w.1, x) ∂muFresh) ∧
      (muPast.prod muFresh)[g |
          (inferInstance : MeasurableSpace Past).comap Prod.fst] ≤ᵐ[
            muPast.prod muFresh] (fun _ ↦ C) := by
  exact profile.complex_paperIndicatorFlatFreshZ_joint_absLog_condExp_withDensity
    muPast N d hsize hc₀ hsqrt center z start B hBpos hBmeas hBnorm
    f hL hf hsecondInt hsecond

/-- Real-law analogue of
`complex_paperIndicatorFlatFreshZ_rawJointClosure_withDensity`. -/
theorem real_paperIndicatorFlatFreshZ_rawJointClosure_withDensity
    {Past : Type*} [MeasurableSpace Past]
    (muPast : Measure Past) [IsProbabilityMeasure muPast]
    (N d : ℕ) [NeZero N] (hsize : d + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1)) (z : ℂ) (start : ZMod N)
    (B : Past → (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hBpos : ∀ a, 0 < exteriorFamilyMaxL2OpNorm (B a))
    (hBmeas : ∀ q i j, Measurable (fun a ↦ B a q i j))
    (hBnorm : ∀ q, Measurable (fun a ↦ ‖B a q‖))
    (f : ℝ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ x ∂(volume : Measure ℝ), f x ≤ ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : ℝ ↦ u ^ 2) (volume.withDensity f))
    (hsecond : ∫ u : ℝ, u ^ 2 ∂(volume.withDensity f) ≤ 1) :
    let muFresh := paperIndicatorRealSampleMeasure N d (volume.withDensity f)
    let radius := fun w : Past × (Fin (N * (d + 2)) → ℝ) ↦
      ‖profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtomsOfReal N d start w.2) (B w.1)‖
    let scale := fun a : Past ↦ exteriorFamilyMaxL2OpNorm (B a)
    let g := fun w ↦ |Real.log (radius w) - Real.log (scale w.1)|
    let C := paperIsolatedCoefficientLoss d c₀ +
      realFreshNegativeBound d L + paperFreshPositiveBound d z
    Integrable g (muPast.prod muFresh) ∧
      ∫ w, g w ∂(muPast.prod muFresh) ≤ C ∧
      (muPast.prod muFresh)[g |
          (inferInstance : MeasurableSpace Past).comap Prod.fst] =ᵐ[
            muPast.prod muFresh]
        (fun w ↦ ∫ x, g (w.1, x) ∂muFresh) ∧
      (muPast.prod muFresh)[g |
          (inferInstance : MeasurableSpace Past).comap Prod.fst] ≤ᵐ[
            muPast.prod muFresh] (fun _ ↦ C) := by
  exact profile.real_paperIndicatorFlatFreshZ_joint_absLog_condExp_withDensity
    muPast N d hsize hc₀ hsqrt center z start B hBpos hBmeas hBnorm
    f hL hf hsecondInt hsecond

end PaperIndicatorWeights

end CircularLawSection4

open MeasureTheory

namespace CircularLawSections56.Section5

universe u v

/-- A Bochner integral is unchanged when its integrand is pulled back along a
measure-preserving map.  Unlike `MeasurePreserving.integral_comp`, no measurable
embedding is required; integrability supplies the needed strong measurability.
-/
theorem integral_comp_of_measurePreserving
    {A : Type u} {B : Type v} [MeasurableSpace A] [MeasurableSpace B]
    {mu : Measure A} {nu : Measure B} {e : A → B}
    (he : MeasurePreserving e mu nu) (g : B → ℝ)
    (hg : Integrable g nu) :
    (∫ x, g (e x) ∂mu) = ∫ y, g y ∂nu := by
  have hgMap : AEStronglyMeasurable g (Measure.map e mu) := by
    rw [he.map_eq]
    exact hg.aestronglyMeasurable
  calc
    (∫ x, g (e x) ∂mu) = ∫ y, g y ∂Measure.map e mu :=
      (MeasureTheory.integral_map he.measurable.aemeasurable hgMap).symm
    _ = ∫ y, g y ∂nu := by rw [he.map_eq]

/-- Pull a two-step `L¹` approximation back to another triangular-array probability
space.  Both error functions and both convergence proofs are preserved verbatim.

This is the intended receiver for the literal coordinate reassembly map between Section
4's outside/fresh product law and the finite iid sample law.
-/
def TwoStepL1ApproximationTri.compMeasurePreserving
    {Omega : ℕ → Type u} {Omega' : ℕ → Type v}
    [∀ n, MeasurableSpace (Omega n)] [∀ n, MeasurableSpace (Omega' n)]
    {mu : ∀ n, Measure (Omega n)} {mu' : ∀ n, Measure (Omega' n)}
    {observable : ∀ n, Omega n → ℝ} {center : ℕ → ℝ}
    (h : TwoStepL1ApproximationTri mu observable center)
    (e : ∀ n, Omega' n → Omega n)
    (he : ∀ n, MeasurePreserving (e n) (mu' n) (mu n)) :
    TwoStepL1ApproximationTri mu'
      (fun n omega ↦ observable n (e n omega)) center := by
  let pulledIntermediate : ∀ n, Omega' n → ℝ :=
    fun n omega ↦ h.intermediate n (e n omega)
  refine
    { intermediate := pulledIntermediate
      seamError := h.seamError
      fluctuationError := h.fluctuationError
      seamIntegrable := ?_
      seamIntegral_le := ?_
      fluctuationIntegrable := ?_
      fluctuationIntegral_le := ?_
      seamError_tendsto_zero := h.seamError_tendsto_zero
      fluctuationError_tendsto_zero := h.fluctuationError_tendsto_zero }
  · intro n
    simpa only [Function.comp_def, pulledIntermediate] using
      (he n).integrable_comp_of_integrable (h.seamIntegrable n)
  · intro n
    calc
      (∫ omega, |observable n (e n omega) - pulledIntermediate n omega| ∂mu' n) =
          ∫ omega, |observable n omega - h.intermediate n omega| ∂mu n := by
            simpa only [pulledIntermediate] using
              integral_comp_of_measurePreserving (he n)
                (fun omega ↦ |observable n omega - h.intermediate n omega|)
                (h.seamIntegrable n)
      _ ≤ h.seamError n := h.seamIntegral_le n
  · intro n
    simpa only [Function.comp_def, pulledIntermediate] using
      (he n).integrable_comp_of_integrable (h.fluctuationIntegrable n)
  · intro n
    calc
      (∫ omega, |pulledIntermediate n omega - center n| ∂mu' n) =
          ∫ omega, |h.intermediate n omega - center n| ∂mu n := by
            simpa only [pulledIntermediate] using
              integral_comp_of_measurePreserving (he n)
                (fun omega ↦ |h.intermediate n omega - center n|)
                (h.fluctuationIntegrable n)
      _ ≤ h.fluctuationError n := h.fluctuationIntegral_le n

end CircularLawSections56.Section5
