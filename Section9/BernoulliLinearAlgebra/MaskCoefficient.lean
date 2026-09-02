import BernoulliLinearAlgebra.AllMinors
import BernoulliLinearAlgebra.CoefficientTranslation
import Mathlib.Tactic

/-!
# Finite mask coefficients and all-minor energy

This file supplies the zero-shift part of Lemma 7.5.  A monomial mask
`a : α` selects a minor `f a : β`; its coefficient is

`w a * m (f a)`.

The exact fiber expansion below is completely finite.  A surjectivity
certificate, two-sided bounds for `‖w a‖²`, and an upper bound for the size of
each fiber then compare coefficient energy with the energy of all minors.
The last section feeds this comparison directly into the list-translation
theorems in `CoefficientTranslation`.
-/

open scoped BigOperators

noncomputable section

namespace BernoulliLinearAlgebra

section GenericMask

variable {alpha beta : Type*}
variable [Fintype alpha] [DecidableEq alpha]
variable [Fintype beta] [DecidableEq beta]

/-- Squared finite `ℓ²` energy of a complex-valued family. -/
def finiteEnergy {gamma : Type*} [Fintype gamma] (v : gamma → ℂ) : ℝ :=
  ∑ i, ‖v i‖ ^ 2

/-- The corresponding finite `ℓ²` norm, written without choosing a
particular `PiLp` model. -/
def finiteL2Norm {gamma : Type*} [Fintype gamma] (v : gamma → ℂ) : ℝ :=
  √(finiteEnergy v)

/-- A mask coefficient: the mask contributes a scalar weight and chooses
one member of the minor family. -/
def maskCoefficient (f : alpha → beta) (w : alpha → ℂ)
    (m : beta → ℂ) (a : alpha) : ℂ :=
  w a * m (f a)

/-- Total squared energy of all mask coefficients. -/
def maskCoefficientEnergy (f : alpha → beta) (w : alpha → ℂ)
    (m : beta → ℂ) : ℝ :=
  finiteEnergy (maskCoefficient f w m)

/-- Squared weight accumulated over the fiber selecting a fixed minor. -/
def fiberWeightEnergy (f : alpha → beta) (w : alpha → ℂ)
    (b : beta) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a ↦ f a = b), ‖w a‖ ^ 2

omit [DecidableEq alpha] in
/-- Exact regrouping of mask coefficients by the minor they select. -/
theorem maskCoefficientEnergy_eq_sum_fibers
    (f : alpha → beta) (w : alpha → ℂ) (m : beta → ℂ) :
    maskCoefficientEnergy f w m =
      ∑ b, fiberWeightEnergy f w b * ‖m b‖ ^ 2 := by
  classical
  unfold maskCoefficientEnergy finiteEnergy maskCoefficient fiberWeightEnergy
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (g := f) (by simp)]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have hfa : f a = b := (Finset.mem_filter.mp ha).2
  rw [hfa, norm_mul]
  ring

/-- The finite hypotheses needed for the mask-to-minor comparison.  These
are directly checkable for a concrete mask expansion.

`fiberBound` is allowed to be non-sharp; in the paper it records the bounded
number of monomial masks which may represent the same square minor.
-/
structure MaskExpansionCertificate (f : alpha → beta) (w : alpha → ℂ) where
  lowerWeight : ℝ
  upperWeight : ℝ
  fiberBound : ℕ
  lowerWeight_nonneg : 0 ≤ lowerWeight
  upperWeight_nonneg : 0 ≤ upperWeight
  onto : Function.Surjective f
  weight_lower : ∀ a, lowerWeight ≤ ‖w a‖ ^ 2
  weight_upper : ∀ a, ‖w a‖ ^ 2 ≤ upperWeight
  fiber_card_le : ∀ b,
    (Finset.univ.filter (fun a ↦ f a = b)).card ≤ fiberBound

omit [DecidableEq alpha] [Fintype beta] in
/-- Every minor contributes at least one mask term of the certified lower
weight. -/
theorem fiberWeightEnergy_lower (f : alpha → beta) (w : alpha → ℂ)
    (c : MaskExpansionCertificate f w) (b : beta) :
    c.lowerWeight ≤ fiberWeightEnergy f w b := by
  classical
  obtain ⟨a, ha⟩ := c.onto b
  unfold fiberWeightEnergy
  calc
    c.lowerWeight ≤ ‖w a‖ ^ 2 := c.weight_lower a
    _ ≤ ∑ x ∈ Finset.univ.filter (fun x ↦ f x = b), ‖w x‖ ^ 2 := by
      apply Finset.single_le_sum (fun x _ ↦ sq_nonneg ‖w x‖)
      simp [ha]

omit [DecidableEq alpha] [Fintype beta] in
/-- A fiber has at most `fiberBound` terms, each of certified upper weight. -/
theorem fiberWeightEnergy_upper (f : alpha → beta) (w : alpha → ℂ)
    (c : MaskExpansionCertificate f w) (b : beta) :
    fiberWeightEnergy f w b ≤ (c.fiberBound : ℝ) * c.upperWeight := by
  classical
  let s : Finset alpha := Finset.univ.filter (fun a ↦ f a = b)
  calc
    fiberWeightEnergy f w b = ∑ a ∈ s, ‖w a‖ ^ 2 := rfl
    _ ≤ ∑ _a ∈ s, c.upperWeight := by
      apply Finset.sum_le_sum
      intro a _
      exact c.weight_upper a
    _ = (s.card : ℝ) * c.upperWeight := by simp
    _ ≤ (c.fiberBound : ℝ) * c.upperWeight := by
      apply mul_le_mul_of_nonneg_right _ c.upperWeight_nonneg
      exact_mod_cast c.fiber_card_le b

omit [DecidableEq alpha] in
/-- Lower coefficient-energy comparison in the zero-shift mask expansion. -/
theorem maskCoefficientEnergy_lower (f : alpha → beta) (w : alpha → ℂ)
    (m : beta → ℂ) (c : MaskExpansionCertificate f w) :
    c.lowerWeight * finiteEnergy m ≤ maskCoefficientEnergy f w m := by
  rw [maskCoefficientEnergy_eq_sum_fibers]
  unfold finiteEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_right (fiberWeightEnergy_lower f w c b)
    (sq_nonneg ‖m b‖)

omit [DecidableEq alpha] in
/-- Upper coefficient-energy comparison, including the mask multiplicity. -/
theorem maskCoefficientEnergy_upper (f : alpha → beta) (w : alpha → ℂ)
    (m : beta → ℂ) (c : MaskExpansionCertificate f w) :
    maskCoefficientEnergy f w m ≤
      ((c.fiberBound : ℝ) * c.upperWeight) * finiteEnergy m := by
  rw [maskCoefficientEnergy_eq_sum_fibers]
  unfold finiteEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_right (fiberWeightEnergy_upper f w c b)
    (sq_nonneg ‖m b‖)

omit [DecidableEq alpha] in
/-- The two zero-shift comparisons bundled as one theorem. -/
theorem maskCoefficientEnergy_bounds (f : alpha → beta) (w : alpha → ℂ)
    (m : beta → ℂ) (c : MaskExpansionCertificate f w) :
    c.lowerWeight * finiteEnergy m ≤ maskCoefficientEnergy f w m ∧
      maskCoefficientEnergy f w m ≤
        ((c.fiberBound : ℝ) * c.upperWeight) * finiteEnergy m :=
  ⟨maskCoefficientEnergy_lower f w m c, maskCoefficientEnergy_upper f w m c⟩

omit [DecidableEq alpha] in
/-- Square-root (`ℓ²` norm) form of the mask comparison. -/
theorem maskCoefficientL2Norm_bounds (f : alpha → beta) (w : alpha → ℂ)
    (m : beta → ℂ) (c : MaskExpansionCertificate f w) :
    √c.lowerWeight * finiteL2Norm m ≤
        finiteL2Norm (maskCoefficient f w m) ∧
      finiteL2Norm (maskCoefficient f w m) ≤
        √((c.fiberBound : ℝ) * c.upperWeight) * finiteL2Norm m := by
  have hminor : 0 ≤ finiteEnergy m := by
    unfold finiteEnergy
    positivity
  constructor
  · have h := Real.sqrt_le_sqrt (maskCoefficientEnergy_lower f w m c)
    simpa [finiteL2Norm, maskCoefficientEnergy, Real.sqrt_mul c.lowerWeight_nonneg]
      using h
  · have h := Real.sqrt_le_sqrt (maskCoefficientEnergy_upper f w m c)
    have hfactor : 0 ≤ (c.fiberBound : ℝ) * c.upperWeight :=
      mul_nonneg (Nat.cast_nonneg _) c.upperWeight_nonneg
    simpa [finiteL2Norm, maskCoefficientEnergy, Real.sqrt_mul hfactor]
      using h

end GenericMask

section SquareMinorIndex

open Matrix Set Set.powersetCard

variable {iota : Type*} [Fintype iota] [DecidableEq iota] [LinearOrder iota]

/-- A concrete index type for every square minor: first choose its column
finset, then a row finset of the same cardinality. -/
abbrev SquareMinorIndex (iota : Type*) [Fintype iota] :=
  Σ t : Finset iota, powersetCard iota t.card

/-- The complex value of the square minor represented by
`SquareMinorIndex`. -/
def squareMinorValue (A : Matrix iota iota ℂ) : SquareMinorIndex iota → ℂ
  | ⟨t, s⟩ => minor t.card A s (ofCard rfl)

/-- The real all-square-minor energy used by the mask comparison. -/
def squareMinorEnergy (A : Matrix iota iota ℂ) : ℝ :=
  finiteEnergy (squareMinorValue A)

omit [DecidableEq iota] in
/-- The concrete real energy is the real part of `AllMinors.allMinorEnergy`.
Thus a mask certificate with `beta = SquareMinorIndex iota` is literally a
coefficient-to-all-square-minor comparison, not merely an abstract family
bound. -/
theorem allMinorEnergy_re_eq_squareMinorEnergy (A : Matrix iota iota ℂ) :
    (allMinorEnergy A).re = squareMinorEnergy A := by
  unfold allMinorEnergy squareMinorEnergy finiteEnergy squareMinorValue
  simp_rw [Complex.re_sum]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro s _
  let z := minor t.card A s (ofCard rfl)
  change (star z * z).re = ‖z‖ ^ 2
  have hz : (Complex.normSq z : ℂ) = star z * z := by
    simpa only [← Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := z))
  rw [← hz, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

omit [DecidableEq iota] in
theorem squareMinorEnergy_nonneg (A : Matrix iota iota ℂ) :
    0 ≤ squareMinorEnergy A := by
  unfold squareMinorEnergy finiteEnergy
  positivity

end SquareMinorIndex

section TranslationCorollary

variable {iota beta : Type*}
variable [Fintype iota] [DecidableEq iota]
variable [Fintype beta] [DecidableEq beta]

/-- The zero-shift coefficient vector associated with a finite mask
expansion of a multiaffine polynomial. -/
def maskCoeffVector (f : Finset iota → beta) (w : Finset iota → ℂ)
    (m : beta → ℂ) : CoeffSpace iota :=
  WithLp.toLp 2 (maskCoefficient f w m)

omit [DecidableEq iota] [Fintype beta] [DecidableEq beta] in
@[simp] theorem coeffEnergy_maskCoeffVector
    (f : Finset iota → beta) (w : Finset iota → ℂ) (m : beta → ℂ) :
    coeffEnergy (maskCoeffVector f w m) = maskCoefficientEnergy f w m := by
  rfl

/-- Structured energy form of Lemma 7.5: first compare zero-shift mask
coefficients with all minor values, then apply the triangular list
translation. -/
theorem lemma35_mask_translate_energy_bounds
    (shifts : List (iota × ℂ))
    (f : Finset iota → beta) (w : Finset iota → ℂ) (m : beta → ℂ)
    (c : MaskExpansionCertificate f w) :
    (translationFactor shifts)⁻¹ ^ 2 *
        (c.lowerWeight * finiteEnergy m) ≤
          coeffEnergy (translateCoeffList shifts (maskCoeffVector f w m)) ∧
      coeffEnergy (translateCoeffList shifts (maskCoeffVector f w m)) ≤
        (translationFactor shifts) ^ 2 *
          (((c.fiberBound : ℝ) * c.upperWeight) * finiteEnergy m) := by
  apply lemma35_translateCoeffList_energy_bounds
  · simpa using maskCoefficientEnergy_lower f w m c
  · simpa using maskCoefficientEnergy_upper f w m c

/-- Norm/square-root form of the structured Lemma 7.5 corollary. -/
theorem lemma35_mask_translate_norm_bounds
    (shifts : List (iota × ℂ))
    (f : Finset iota → beta) (w : Finset iota → ℂ) (m : beta → ℂ)
    (c : MaskExpansionCertificate f w) :
    (translationFactor shifts)⁻¹ * √c.lowerWeight * √(finiteEnergy m) ≤
        ‖translateCoeffList shifts (maskCoeffVector f w m)‖ ∧
      ‖translateCoeffList shifts (maskCoeffVector f w m)‖ ≤
        translationFactor shifts *
          √((c.fiberBound : ℝ) * c.upperWeight) * √(finiteEnergy m) := by
  apply lemma35_translateCoeffList_norm_bounds
  · unfold finiteEnergy
    positivity
  · exact c.lowerWeight_nonneg
  · exact mul_nonneg (Nat.cast_nonneg _) c.upperWeight_nonneg
  · simpa using maskCoefficientEnergy_lower f w m c
  · simpa using maskCoefficientEnergy_upper f w m c

end TranslationCorollary

section SquareMinorTranslationCorollary

open Matrix Set Set.powersetCard

variable {vars iota : Type*}
variable [Fintype vars] [DecidableEq vars]
variable [Fintype iota] [DecidableEq iota] [LinearOrder iota]

/-- Lemma 7.5 specialized all the way to the family of every square minor
of a concrete matrix.  The comparison quantity is written using
`AllMinors.allMinorEnergy` itself (its real part, since coefficient energy
is real-valued). -/
theorem lemma35_squareMinor_mask_translate_energy_bounds
    (shifts : List (vars × ℂ))
    (A : Matrix iota iota ℂ)
    (f : Finset vars → SquareMinorIndex iota)
    (w : Finset vars → ℂ)
    (c : MaskExpansionCertificate f w) :
    (translationFactor shifts)⁻¹ ^ 2 *
        (c.lowerWeight * (allMinorEnergy A).re) ≤
          coeffEnergy (translateCoeffList shifts
            (maskCoeffVector f w (squareMinorValue A))) ∧
      coeffEnergy (translateCoeffList shifts
          (maskCoeffVector f w (squareMinorValue A))) ≤
        (translationFactor shifts) ^ 2 *
          (((c.fiberBound : ℝ) * c.upperWeight) *
            (allMinorEnergy A).re) := by
  rw [allMinorEnergy_re_eq_squareMinorEnergy]
  simpa [squareMinorEnergy] using
    (lemma35_mask_translate_energy_bounds shifts f w (squareMinorValue A) c)

/-- Square-root norm form of the preceding all-square-minor theorem. -/
theorem lemma35_squareMinor_mask_translate_norm_bounds
    (shifts : List (vars × ℂ))
    (A : Matrix iota iota ℂ)
    (f : Finset vars → SquareMinorIndex iota)
    (w : Finset vars → ℂ)
    (c : MaskExpansionCertificate f w) :
    (translationFactor shifts)⁻¹ * √c.lowerWeight *
        √((allMinorEnergy A).re) ≤
          ‖translateCoeffList shifts
            (maskCoeffVector f w (squareMinorValue A))‖ ∧
      ‖translateCoeffList shifts
          (maskCoeffVector f w (squareMinorValue A))‖ ≤
        translationFactor shifts *
          √((c.fiberBound : ℝ) * c.upperWeight) *
            √((allMinorEnergy A).re) := by
  rw [allMinorEnergy_re_eq_squareMinorEnergy]
  simpa [squareMinorEnergy] using
    (lemma35_mask_translate_norm_bounds shifts f w (squareMinorValue A) c)

end SquareMinorTranslationCorollary

end BernoulliLinearAlgebra
