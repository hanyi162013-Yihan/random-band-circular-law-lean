import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Translation of multiaffine coefficient vectors

A multiaffine polynomial in variables indexed by a finite type `ι` has one
coefficient for each finite subset of `ι`.  This file records the triangular
change of coefficients caused by replacing one variable `xᵢ` by `xᵢ + t`,
its inverse, and quantitative `ℓ²` bounds.  Iterating the construction gives
the deterministic translation step used in Lemma 7.5 of the paper.
-/

open scoped BigOperators

noncomputable section

namespace BernoulliLinearAlgebra

/-- The coefficient space of multiaffine polynomials in finitely many variables. -/
abbrev CoeffSpace (ι : Type*) [Fintype ι] := EuclideanSpace ℂ (Finset ι)

/-- Squared `ℓ²` energy of a multiaffine coefficient vector. -/
def coeffEnergy {ι : Type*} [Fintype ι] (c : CoeffSpace ι) : ℝ :=
  ∑ S : Finset ι, ‖c S‖ ^ 2

/-- Coefficient form of the Euclidean norm identity. -/
theorem coeffEnergy_eq_norm_sq {ι : Type*} [Fintype ι] (c : CoeffSpace ι) :
    coeffEnergy c = ‖c‖ ^ 2 := by
  exact (EuclideanSpace.norm_sq_eq c).symm

/-- Multiplying a polynomial by a scalar multiplies the squared coefficient
energy by the scalar norm squared.  This is the coefficient-vector step
used after determinant row scaling and after extracting `det Θ₁₁`. -/
theorem coeffEnergy_smul {ι : Type*} [Fintype ι]
    (a : ℂ) (c : CoeffSpace ι) :
    coeffEnergy (a • c) = ‖a‖ ^ 2 * coeffEnergy c := by
  rw [coeffEnergy_eq_norm_sq, coeffEnergy_eq_norm_sq, norm_smul, mul_pow]

/-- Norm form of scalar coefficient scaling. -/
theorem coeffNorm_smul {ι : Type*} [Fintype ι]
    (a : ℂ) (c : CoeffSpace ι) :
    ‖a • c‖ = ‖a‖ * ‖c‖ :=
  norm_smul a c

/-- The part of a coefficient vector which is shifted down across the `i`th
coordinate: a coefficient indexed by `insert i S` is placed at `S`. -/
def shiftCoeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (c : CoeffSpace ι) : CoeffSpace ι :=
  WithLp.toLp 2 (fun S ↦ if i ∈ S then 0 else c (insert i S))

/-- Translation of one variable by `t` on multiaffine coefficients. -/
def singleTranslateCoeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (t : ℂ) (c : CoeffSpace ι) : CoeffSpace ι :=
  WithLp.toLp 2 (fun S ↦ if i ∈ S then c S else c S + t * c (insert i S))

theorem singleTranslateCoeff_eq_add_shift {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i : ι) (t : ℂ) (c : CoeffSpace ι) :
    singleTranslateCoeff i t c = c + t • shiftCoeff i c := by
  ext S
  by_cases h : i ∈ S <;> simp [singleTranslateCoeff, shiftCoeff, h]

/-- Shifting coefficients down in one Boolean coordinate does not increase
their squared `ℓ²` energy. -/
theorem coeffEnergy_shiftCoeff_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (c : CoeffSpace ι) :
    coeffEnergy (shiftCoeff i c) ≤ coeffEnergy c := by
  classical
  let withoutI : Finset (Finset ι) := Finset.univ.filter (fun S ↦ i ∉ S)
  let withI : Finset (Finset ι) := Finset.univ.filter (fun S ↦ i ∈ S)
  have hsum :
      (∑ S ∈ withoutI, ‖c (insert i S)‖ ^ 2) =
        ∑ T ∈ withI, ‖c T‖ ^ 2 := by
    refine Finset.sum_bij (fun S _ ↦ insert i S) ?_ ?_ ?_ ?_
    · intro S hS
      simp only [withoutI, Finset.mem_filter, Finset.mem_univ, true_and] at hS
      simp [withI]
    · intro S₁ hS₁ S₂ hS₂ hEq
      simp only [withoutI, Finset.mem_filter, Finset.mem_univ, true_and] at hS₁ hS₂
      have := congrArg (fun S : Finset ι ↦ S.erase i) hEq
      simpa [Finset.erase_insert, hS₁, hS₂] using this
    · intro T hT
      simp only [withI, Finset.mem_filter, Finset.mem_univ, true_and] at hT
      refine ⟨T.erase i, ?_, ?_⟩
      · simp [withoutI]
      · exact Finset.insert_erase hT
    · intro S hS
      rfl
  calc
    coeffEnergy (shiftCoeff i c) =
        ∑ S ∈ withoutI, ‖c (insert i S)‖ ^ 2 := by
          unfold coeffEnergy shiftCoeff
          unfold withoutI
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro S _
          by_cases h : i ∈ S <;> simp [h]
    _ = ∑ T ∈ withI, ‖c T‖ ^ 2 := hsum
    _ ≤ ∑ T : Finset ι, ‖c T‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro T _ _
      positivity
    _ = coeffEnergy c := rfl

/-- The coefficient-lowering operator is a contraction in `ℓ²`. -/
theorem norm_shiftCoeff_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (c : CoeffSpace ι) :
    ‖shiftCoeff i c‖ ≤ ‖c‖ := by
  have h := coeffEnergy_shiftCoeff_le i c
  rw [coeffEnergy_eq_norm_sq, coeffEnergy_eq_norm_sq] at h
  nlinarith [norm_nonneg (shiftCoeff i c), norm_nonneg c]

/-- Explicit upper bound for a one-variable translation. -/
theorem norm_singleTranslateCoeff_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i : ι) (t : ℂ) (c : CoeffSpace ι) :
    ‖singleTranslateCoeff i t c‖ ≤ (1 + ‖t‖) * ‖c‖ := by
  rw [singleTranslateCoeff_eq_add_shift]
  calc
    ‖c + t • shiftCoeff i c‖ ≤ ‖c‖ + ‖t • shiftCoeff i c‖ := norm_add_le _ _
    _ = ‖c‖ + ‖t‖ * ‖shiftCoeff i c‖ := by rw [norm_smul]
    _ ≤ ‖c‖ + ‖t‖ * ‖c‖ := by
      gcongr
      exact norm_shiftCoeff_le i c
    _ = (1 + ‖t‖) * ‖c‖ := by ring

/-- Translation by `-t` is the inverse of translation by `t`. -/
theorem singleTranslateCoeff_inverse {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i : ι) (t : ℂ) (c : CoeffSpace ι) :
    singleTranslateCoeff i (-t) (singleTranslateCoeff i t c) = c := by
  ext S
  by_cases h : i ∈ S
  · simp [singleTranslateCoeff, h]
  · simp [singleTranslateCoeff, h]

/-- Explicit lower bound for a one-variable translation, obtained from its inverse. -/
theorem norm_singleTranslateCoeff_lower {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i : ι) (t : ℂ) (c : CoeffSpace ι) :
    (1 + ‖t‖)⁻¹ * ‖c‖ ≤ ‖singleTranslateCoeff i t c‖ := by
  have hp : 0 < (1 + ‖t‖ : ℝ) := by positivity
  rw [inv_mul_le_iff₀ hp]
  simpa [singleTranslateCoeff_inverse] using
    norm_singleTranslateCoeff_le i (-t) (singleTranslateCoeff i t c)

/-- Squared-energy upper bound for a one-variable translation. -/
theorem coeffEnergy_singleTranslateCoeff_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i : ι) (t : ℂ) (c : CoeffSpace ι) :
    coeffEnergy (singleTranslateCoeff i t c) ≤
      (1 + ‖t‖) ^ 2 * coeffEnergy c := by
  rw [coeffEnergy_eq_norm_sq, coeffEnergy_eq_norm_sq]
  have h := norm_singleTranslateCoeff_le i t c
  have hsq :
      ‖singleTranslateCoeff i t c‖ ^ 2 ≤ ((1 + ‖t‖) * ‖c‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 h
  calc
    ‖singleTranslateCoeff i t c‖ ^ 2 ≤ ((1 + ‖t‖) * ‖c‖) ^ 2 := hsq
    _ = (1 + ‖t‖) ^ 2 * ‖c‖ ^ 2 := by ring

/-- Squared-energy lower bound for a one-variable translation. -/
theorem coeffEnergy_singleTranslateCoeff_lower {ι : Type*} [Fintype ι]
    [DecidableEq ι] (i : ι) (t : ℂ) (c : CoeffSpace ι) :
    ((1 + ‖t‖)⁻¹) ^ 2 * coeffEnergy c ≤
      coeffEnergy (singleTranslateCoeff i t c) := by
  rw [coeffEnergy_eq_norm_sq, coeffEnergy_eq_norm_sq]
  have h := norm_singleTranslateCoeff_lower i t c
  have hsq :
      ((1 + ‖t‖)⁻¹ * ‖c‖) ^ 2 ≤ ‖singleTranslateCoeff i t c‖ ^ 2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 h
  calc
    ((1 + ‖t‖)⁻¹) ^ 2 * ‖c‖ ^ 2 =
        ((1 + ‖t‖)⁻¹ * ‖c‖) ^ 2 := by ring
    _ ≤ ‖singleTranslateCoeff i t c‖ ^ 2 := hsq

/-- Successive translations of finitely many variables, in list order. -/
def translateCoeffList {ι : Type*} [Fintype ι] [DecidableEq ι] :
    List (ι × ℂ) → CoeffSpace ι → CoeffSpace ι
  | [], c => c
  | (i, t) :: shifts, c =>
      translateCoeffList shifts (singleTranslateCoeff i t c)

/-- The inverse operation: undo the translations in reverse order. -/
def inverseTranslateCoeffList {ι : Type*} [Fintype ι] [DecidableEq ι] :
    List (ι × ℂ) → CoeffSpace ι → CoeffSpace ι
  | [], c => c
  | (i, t) :: shifts, c =>
      singleTranslateCoeff i (-t) (inverseTranslateCoeffList shifts c)

/-- Product of the explicit one-coordinate norm losses. -/
def translationFactor {ι : Type*} (shifts : List (ι × ℂ)) : ℝ :=
  (shifts.map (fun it ↦ 1 + ‖it.2‖)).prod

@[simp]
theorem translationFactor_nil {ι : Type*} :
    translationFactor ([] : List (ι × ℂ)) = 1 := rfl

@[simp]
theorem translationFactor_cons {ι : Type*} (i : ι) (t : ℂ)
    (shifts : List (ι × ℂ)) :
    translationFactor ((i, t) :: shifts) =
      (1 + ‖t‖) * translationFactor shifts := rfl

/-- Every translation factor is strictly positive. -/
theorem translationFactor_pos {ι : Type*} (shifts : List (ι × ℂ)) :
    0 < translationFactor shifts := by
  induction shifts with
  | nil => simp
  | cons it shifts ih =>
      rcases it with ⟨i, t⟩
      simp only [translationFactor_cons]
      positivity

/-- Undoing a list translation after applying it recovers the original vector. -/
theorem inverseTranslateCoeffList_translateCoeffList {ι : Type*} [Fintype ι]
    [DecidableEq ι] (shifts : List (ι × ℂ)) (c : CoeffSpace ι) :
    inverseTranslateCoeffList shifts (translateCoeffList shifts c) = c := by
  induction shifts generalizing c with
  | nil => rfl
  | cons it shifts ih =>
      rcases it with ⟨i, t⟩
      simp only [translateCoeffList, inverseTranslateCoeffList]
      rw [ih, singleTranslateCoeff_inverse]

/-- Applying a list translation after its inverse also recovers the vector. -/
theorem translateCoeffList_inverseTranslateCoeffList {ι : Type*} [Fintype ι]
    [DecidableEq ι] (shifts : List (ι × ℂ)) (c : CoeffSpace ι) :
    translateCoeffList shifts (inverseTranslateCoeffList shifts c) = c := by
  induction shifts generalizing c with
  | nil => rfl
  | cons it shifts ih =>
      rcases it with ⟨i, t⟩
      simp only [translateCoeffList, inverseTranslateCoeffList]
      rw [show singleTranslateCoeff i t
          (singleTranslateCoeff i (-t) (inverseTranslateCoeffList shifts c)) =
          inverseTranslateCoeffList shifts c by
        simpa using singleTranslateCoeff_inverse i (-t)
          (inverseTranslateCoeffList shifts c)]
      exact ih c

/-- Upper `ℓ²` bound for an iterated translation. -/
theorem norm_translateCoeffList_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (shifts : List (ι × ℂ)) (c : CoeffSpace ι) :
    ‖translateCoeffList shifts c‖ ≤ translationFactor shifts * ‖c‖ := by
  induction shifts generalizing c with
  | nil => simp [translateCoeffList]
  | cons it shifts ih =>
      rcases it with ⟨i, t⟩
      simp only [translateCoeffList, translationFactor_cons]
      calc
        ‖translateCoeffList shifts (singleTranslateCoeff i t c)‖ ≤
            translationFactor shifts * ‖singleTranslateCoeff i t c‖ := ih _
        _ ≤ translationFactor shifts * ((1 + ‖t‖) * ‖c‖) := by
          exact mul_le_mul_of_nonneg_left (norm_singleTranslateCoeff_le i t c)
            (translationFactor_pos shifts).le
        _ = ((1 + ‖t‖) * translationFactor shifts) * ‖c‖ := by ring

/-- The inverse list transformation has the same explicit upper bound. -/
theorem norm_inverseTranslateCoeffList_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] (shifts : List (ι × ℂ)) (c : CoeffSpace ι) :
    ‖inverseTranslateCoeffList shifts c‖ ≤ translationFactor shifts * ‖c‖ := by
  induction shifts generalizing c with
  | nil => simp [inverseTranslateCoeffList]
  | cons it shifts ih =>
      rcases it with ⟨i, t⟩
      simp only [inverseTranslateCoeffList, translationFactor_cons]
      calc
        ‖singleTranslateCoeff i (-t) (inverseTranslateCoeffList shifts c)‖ ≤
            (1 + ‖t‖) * ‖inverseTranslateCoeffList shifts c‖ := by
              simpa using norm_singleTranslateCoeff_le i (-t)
                (inverseTranslateCoeffList shifts c)
        _ ≤ (1 + ‖t‖) * (translationFactor shifts * ‖c‖) := by
          gcongr
          exact ih _
        _ = ((1 + ‖t‖) * translationFactor shifts) * ‖c‖ := by ring

/-- Lower `ℓ²` bound for an iterated translation. -/
theorem norm_translateCoeffList_lower {ι : Type*} [Fintype ι]
    [DecidableEq ι] (shifts : List (ι × ℂ)) (c : CoeffSpace ι) :
    (translationFactor shifts)⁻¹ * ‖c‖ ≤ ‖translateCoeffList shifts c‖ := by
  have hp := translationFactor_pos shifts
  rw [inv_mul_le_iff₀ hp]
  simpa [inverseTranslateCoeffList_translateCoeffList] using
    norm_inverseTranslateCoeffList_le shifts (translateCoeffList shifts c)

/-- Squared-energy upper bound for an iterated translation. -/
theorem coeffEnergy_translateCoeffList_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] (shifts : List (ι × ℂ)) (c : CoeffSpace ι) :
    coeffEnergy (translateCoeffList shifts c) ≤
      (translationFactor shifts) ^ 2 * coeffEnergy c := by
  rw [coeffEnergy_eq_norm_sq, coeffEnergy_eq_norm_sq]
  have h := norm_translateCoeffList_le shifts c
  have hsq : ‖translateCoeffList shifts c‖ ^ 2 ≤
      (translationFactor shifts * ‖c‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (translationFactor_pos shifts).le (norm_nonneg c))).2 h
  calc
    ‖translateCoeffList shifts c‖ ^ 2 ≤
        (translationFactor shifts * ‖c‖) ^ 2 := hsq
    _ = (translationFactor shifts) ^ 2 * ‖c‖ ^ 2 := by ring

/-- Squared-energy lower bound for an iterated translation. -/
theorem coeffEnergy_translateCoeffList_lower {ι : Type*} [Fintype ι]
    [DecidableEq ι] (shifts : List (ι × ℂ)) (c : CoeffSpace ι) :
    ((translationFactor shifts)⁻¹) ^ 2 * coeffEnergy c ≤
      coeffEnergy (translateCoeffList shifts c) := by
  rw [coeffEnergy_eq_norm_sq, coeffEnergy_eq_norm_sq]
  have h := norm_translateCoeffList_lower shifts c
  have hsq : ((translationFactor shifts)⁻¹ * ‖c‖) ^ 2 ≤
      ‖translateCoeffList shifts c‖ ^ 2 :=
    (sq_le_sq₀
      (mul_nonneg (inv_nonneg.mpr (translationFactor_pos shifts).le) (norm_nonneg c))
      (norm_nonneg _)).2 h
  calc
    ((translationFactor shifts)⁻¹) ^ 2 * ‖c‖ ^ 2 =
        ((translationFactor shifts)⁻¹ * ‖c‖) ^ 2 := by ring
    _ ≤ ‖translateCoeffList shifts c‖ ^ 2 := hsq

/-- Abstract deterministic energy packaging for Lemma 7.5.  It deliberately
separates the paper-specific comparison of zero-shift coefficients with the
all-minor energy from the universal translation estimate. -/
theorem lemma35_deterministic_energy_bounds
    {zeroEnergy shiftedEnergy allMinorEnergyValue lower upper factor : ℝ}
    (hzeroLower : lower * allMinorEnergyValue ≤ zeroEnergy)
    (hzeroUpper : zeroEnergy ≤ upper * allMinorEnergyValue)
    (hshiftLower : factor⁻¹ ^ 2 * zeroEnergy ≤ shiftedEnergy)
    (hshiftUpper : shiftedEnergy ≤ factor ^ 2 * zeroEnergy) :
    factor⁻¹ ^ 2 * (lower * allMinorEnergyValue) ≤ shiftedEnergy ∧
      shiftedEnergy ≤ factor ^ 2 * (upper * allMinorEnergyValue) := by
  constructor
  · exact (mul_le_mul_of_nonneg_left hzeroLower (sq_nonneg factor⁻¹)).trans hshiftLower
  · exact hshiftUpper.trans
      (mul_le_mul_of_nonneg_left hzeroUpper (sq_nonneg factor))

/-- Lemma 7.5's deterministic conclusion specialized to an actual list of
affine coordinate shifts. -/
theorem lemma35_translateCoeffList_energy_bounds {ι : Type*} [Fintype ι]
    [DecidableEq ι] (shifts : List (ι × ℂ)) (zeroCoeff : CoeffSpace ι)
    (allMinorEnergyValue lower upper : ℝ)
    (hzeroLower : lower * allMinorEnergyValue ≤ coeffEnergy zeroCoeff)
    (hzeroUpper : coeffEnergy zeroCoeff ≤ upper * allMinorEnergyValue) :
    ((translationFactor shifts)⁻¹) ^ 2 *
        (lower * allMinorEnergyValue) ≤
          coeffEnergy (translateCoeffList shifts zeroCoeff) ∧
      coeffEnergy (translateCoeffList shifts zeroCoeff) ≤
        (translationFactor shifts) ^ 2 *
          (upper * allMinorEnergyValue) := by
  exact lemma35_deterministic_energy_bounds hzeroLower hzeroUpper
    (coeffEnergy_translateCoeffList_lower shifts zeroCoeff)
    (coeffEnergy_translateCoeffList_le shifts zeroCoeff)

/-- Norm form of the deterministic Lemma 7.5 packaging.  If the zero-shift
coefficient energy lies between `lower * A` and `upper * A`, and a triangular
translation changes norms by at most `factor` in either direction, then the
translated norm lies between the corresponding square-root bounds. -/
theorem lemma35_deterministic_norm_bounds {ι : Type*} [Fintype ι]
    (zeroCoeff shiftedCoeff : CoeffSpace ι)
    (allMinorEnergyValue lower upper factor : ℝ)
    (hA : 0 ≤ allMinorEnergyValue) (hLower : 0 ≤ lower)
    (hUpper : 0 ≤ upper) (hFactor : 0 < factor)
    (hzeroLower : lower * allMinorEnergyValue ≤ coeffEnergy zeroCoeff)
    (hzeroUpper : coeffEnergy zeroCoeff ≤ upper * allMinorEnergyValue)
    (hshiftLower : factor⁻¹ * ‖zeroCoeff‖ ≤ ‖shiftedCoeff‖)
    (hshiftUpper : ‖shiftedCoeff‖ ≤ factor * ‖zeroCoeff‖) :
    factor⁻¹ * √lower * √allMinorEnergyValue ≤ ‖shiftedCoeff‖ ∧
      ‖shiftedCoeff‖ ≤ factor * √upper * √allMinorEnergyValue := by
  have hzeroLowerNorm : √(lower * allMinorEnergyValue) ≤ ‖zeroCoeff‖ := by
    have hsqrt := Real.sqrt_le_sqrt hzeroLower
    rw [coeffEnergy_eq_norm_sq, Real.sqrt_sq (norm_nonneg zeroCoeff)] at hsqrt
    exact hsqrt
  have hzeroUpperNorm : ‖zeroCoeff‖ ≤ √(upper * allMinorEnergyValue) := by
    rw [Real.le_sqrt (norm_nonneg zeroCoeff) (mul_nonneg hUpper hA)]
    simpa [coeffEnergy_eq_norm_sq] using hzeroUpper
  constructor
  · calc
      factor⁻¹ * √lower * √allMinorEnergyValue =
          factor⁻¹ * √(lower * allMinorEnergyValue) := by
            rw [Real.sqrt_mul hLower]
            ring
      _ ≤ factor⁻¹ * ‖zeroCoeff‖ := by
        exact mul_le_mul_of_nonneg_left hzeroLowerNorm (inv_nonneg.mpr hFactor.le)
      _ ≤ ‖shiftedCoeff‖ := hshiftLower
  · calc
      ‖shiftedCoeff‖ ≤ factor * ‖zeroCoeff‖ := hshiftUpper
      _ ≤ factor * √(upper * allMinorEnergyValue) := by
        gcongr
      _ = factor * √upper * √allMinorEnergyValue := by
        rw [Real.sqrt_mul hUpper]
        ring

/-- Norm-form Lemma 7.5 conclusion for the concrete iterated translation. -/
theorem lemma35_translateCoeffList_norm_bounds {ι : Type*} [Fintype ι]
    [DecidableEq ι] (shifts : List (ι × ℂ)) (zeroCoeff : CoeffSpace ι)
    (allMinorEnergyValue lower upper : ℝ)
    (hA : 0 ≤ allMinorEnergyValue) (hLower : 0 ≤ lower)
    (hUpper : 0 ≤ upper)
    (hzeroLower : lower * allMinorEnergyValue ≤ coeffEnergy zeroCoeff)
    (hzeroUpper : coeffEnergy zeroCoeff ≤ upper * allMinorEnergyValue) :
    (translationFactor shifts)⁻¹ * √lower * √allMinorEnergyValue ≤
        ‖translateCoeffList shifts zeroCoeff‖ ∧
      ‖translateCoeffList shifts zeroCoeff‖ ≤
        translationFactor shifts * √upper * √allMinorEnergyValue := by
  exact lemma35_deterministic_norm_bounds zeroCoeff
    (translateCoeffList shifts zeroCoeff) allMinorEnergyValue lower upper
    (translationFactor shifts) hA hLower hUpper (translationFactor_pos shifts)
    hzeroLower hzeroUpper (norm_translateCoeffList_lower shifts zeroCoeff)
    (norm_translateCoeffList_le shifts zeroCoeff)

end BernoulliLinearAlgebra
