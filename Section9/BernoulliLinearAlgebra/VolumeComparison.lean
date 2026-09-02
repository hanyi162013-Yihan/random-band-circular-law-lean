import BernoulliLinearAlgebra.AllMinors
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Compound energies and Gram-volume comparison

This file formalizes the deterministic linear-algebraic part of Section 9.4.1.
The exact all-minor Cauchy--Binet identity from `AllMinors` is converted to a
nonnegative real energy, and functoriality of compound matrices is combined
with submultiplicativity of the Frobenius norm.

The paper obtains uniform bounds for the compounds of a boundary matrix and
its inverse from a Hodge--Jacobi complementary-minor formula.  Mathlib does
not currently expose that formula with the conventions used here.  We
therefore package precisely its deterministic output in
`ExteriorConditioning`: invertibility together with uniform Frobenius bounds
for every exterior degree of the matrix and its nonsingular inverse.  No
analytic or probabilistic estimate is hidden in the comparison theorems.
-/

open scoped BigOperators Matrix Matrix.Norms.Frobenius

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix Set Set.powersetCard

section GramEnergy

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- The real all-minor energy: the sum of the squared moduli of every square
minor, with the degree bundled by the column finset. -/
def realAllMinorEnergy (A : Matrix ι ι ℂ) : ℝ :=
  ∑ t : Finset ι, ∑ s : powersetCard ι t.card,
    Complex.normSq (minor t.card A s (ofCard rfl))

/-- The Gram energy whose square root is the volume used in Section 9.4.1. -/
def gramEnergy (A : Matrix ι ι ℂ) : ℝ :=
  (det (1 + Aᴴ * A)).re

/-- The Gram volume `det (I + Aᴴ A)^{1/2}`, represented as a real square
root. -/
def gramVolume (A : Matrix ι ι ℂ) : ℝ :=
  Real.sqrt (gramEnergy A)

/-- The Gram determinant is exactly the real all-minor energy. -/
theorem gramEnergy_eq_realAllMinorEnergy (A : Matrix ι ι ℂ) :
    gramEnergy A = realAllMinorEnergy A := by
  rw [gramEnergy, det_one_add_gram_eq_sum_compoundEnergy]
  simp only [allMinorEnergy, realAllMinorEnergy]
  rw [← Complex.reCLM_apply, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Complex.reCLM_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self]
  simp

/-- Every Gram energy is nonnegative. -/
theorem gramEnergy_nonneg (A : Matrix ι ι ℂ) : 0 ≤ gramEnergy A := by
  rw [gramEnergy_eq_realAllMinorEnergy, realAllMinorEnergy]
  exact Finset.sum_nonneg fun t _ ↦
    Finset.sum_nonneg fun s _ ↦ Complex.normSq_nonneg _

omit [LinearOrder ι] in
/-- Every Gram volume is nonnegative. -/
theorem gramVolume_nonneg (A : Matrix ι ι ℂ) : 0 ≤ gramVolume A :=
  Real.sqrt_nonneg _

/-- Squaring the Gram volume recovers the Gram energy. -/
theorem gramVolume_sq (A : Matrix ι ι ℂ) :
    gramVolume A ^ 2 = gramEnergy A := by
  exact Real.sq_sqrt (gramEnergy_nonneg A)

end GramEnergy

section FrobeniusCompound

variable {ι κ μ : Type*}
variable [Fintype ι] [DecidableEq ι] [LinearOrder ι]
variable [Fintype κ] [DecidableEq κ] [LinearOrder κ]
variable [Fintype μ] [DecidableEq μ] [LinearOrder μ]

omit [DecidableEq κ] in
/-- Frobenius norms of compound matrices are submultiplicative. -/
theorem compound_frobenius_norm_mul_le (k : ℕ) (A : Matrix κ ι ℂ)
    (B : Matrix ι μ ℂ) :
    ‖compound k (A * B)‖ ≤ ‖compound k A‖ * ‖compound k B‖ := by
  rw [compound_mul]
  exact Matrix.frobenius_norm_mul _ _

end FrobeniusCompound

section CompoundEnergy

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- Real Hilbert--Schmidt energy of the `k`th compound matrix. -/
def compoundEnergyReal (k : ℕ) (A : Matrix ι ι ℂ) : ℝ :=
  ‖compound k A‖ ^ 2

/-- The real compound energy is the sum of squared moduli of its minors. -/
theorem compoundEnergyReal_eq_sum_normSq (k : ℕ) (A : Matrix ι ι ℂ) :
    compoundEnergyReal k A =
      ∑ s : powersetCard ι k, ∑ t : powersetCard ι k,
        Complex.normSq (minor k A s t) := by
  rw [compoundEnergyReal, Matrix.frobenius_norm_def,
    ← Real.sqrt_eq_rpow]
  have hsum :
      0 ≤ ∑ s : powersetCard ι k, ∑ t : powersetCard ι k,
        ‖compound k A s t‖ ^ (2 : ℝ) := by
    exact Finset.sum_nonneg fun s _ ↦ Finset.sum_nonneg fun t _ ↦
      Real.rpow_nonneg (norm_nonneg _) _
  rw [Real.sq_sqrt hsum]
  simp_rw [compound_apply, Real.rpow_two, Complex.sq_norm]

/-- The complex-valued compound energy from `AllMinors` is real, and its
real part is the squared Frobenius norm. -/
theorem compoundEnergy_re_eq_compoundEnergyReal (k : ℕ)
    (A : Matrix ι ι ℂ) :
    (compoundEnergy k A).re = compoundEnergyReal k A := by
  rw [compoundEnergyReal_eq_sum_normSq]
  unfold compoundEnergy
  rw [← Complex.reCLM_apply, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Complex.reCLM_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self]
  simp

/-- Equation (9.84) in real form: the Gram energy is the finite sum of the
squared Frobenius norms of all compound matrices. -/
theorem gramEnergy_eq_sum_compoundEnergyReal (A : Matrix ι ι ℂ) :
    gramEnergy A =
      ∑ k ∈ Finset.range (Fintype.card ι + 1), compoundEnergyReal k A := by
  rw [gramEnergy, det_one_add_gram_eq_sum_compoundEnergy_byDegree]
  rw [← Complex.reCLM_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact compoundEnergy_re_eq_compoundEnergyReal k A

end CompoundEnergy

section ExteriorConditioning

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- The deterministic output of the Hodge--Jacobi argument used in the
paper: `E` is nonsingular and every compound of `E` and `E⁻¹` has Frobenius
norm at most `K`.  The condition `1 ≤ K` is the harmless normalization used
when passing from degreewise estimates to one common comparison constant. -/
structure ExteriorConditioning (E : Matrix ι ι ℂ) (K : ℝ) : Prop where
  det_isUnit : IsUnit E.det
  one_le : 1 ≤ K
  forward : ∀ k : ℕ, ‖compound k E‖ ≤ K
  inverse : ∀ k : ℕ, ‖compound k E⁻¹‖ ≤ K

/-- Left multiplication by a conditioned matrix costs at most `K` in every
exterior degree. -/
theorem compound_left_mul_le {E S : Matrix ι ι ℂ} {K : ℝ}
    (hE : ExteriorConditioning E K) (k : ℕ) :
    ‖compound k (E * S)‖ ≤ K * ‖compound k S‖ := by
  calc
    ‖compound k (E * S)‖
        ≤ ‖compound k E‖ * ‖compound k S‖ :=
          compound_frobenius_norm_mul_le k E S
    _ ≤ K * ‖compound k S‖ :=
      mul_le_mul_of_nonneg_right (hE.forward k) (norm_nonneg _)

/-- The inverse compound bounds give the reverse degreewise estimate. -/
theorem compound_le_left_mul {E S : Matrix ι ι ℂ} {K : ℝ}
    (hE : ExteriorConditioning E K) (k : ℕ) :
    ‖compound k S‖ ≤ K * ‖compound k (E * S)‖ := by
  calc
    ‖compound k S‖ = ‖compound k (E⁻¹ * (E * S))‖ := by
      rw [Matrix.nonsing_inv_mul_cancel_left E S hE.det_isUnit]
    _
        ≤ ‖compound k E⁻¹‖ * ‖compound k (E * S)‖ :=
          compound_frobenius_norm_mul_le k E⁻¹ (E * S)
    _ ≤ K * ‖compound k (E * S)‖ :=
      mul_le_mul_of_nonneg_right (hE.inverse k) (norm_nonneg _)

/-- A direct squared-energy version of `compound_left_mul_le`. -/
theorem compoundEnergy_left_mul_le {E S : Matrix ι ι ℂ} {K : ℝ}
    (hE : ExteriorConditioning E K) (k : ℕ) :
    compoundEnergyReal k (E * S) ≤ K ^ 2 * compoundEnergyReal k S := by
  unfold compoundEnergyReal
  rw [← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (le_trans zero_le_one hE.one_le)
    (norm_nonneg _))).2 (compound_left_mul_le hE k)

/-- A direct squared-energy version of `compound_le_left_mul`. -/
theorem compoundEnergy_le_left_mul {E S : Matrix ι ι ℂ} {K : ℝ}
    (hE : ExteriorConditioning E K) (k : ℕ) :
    compoundEnergyReal k S ≤ K ^ 2 * compoundEnergyReal k (E * S) := by
  unfold compoundEnergyReal
  rw [← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (le_trans zero_le_one hE.one_le)
    (norm_nonneg _))).2 (compound_le_left_mul hE k)

/-- Summing the degreewise compound bounds gives the forward Gram-energy
comparison used to remove the left boundary factor. -/
theorem gramEnergy_left_mul_le {E S : Matrix ι ι ℂ} {K : ℝ}
    (hE : ExteriorConditioning E K) :
    gramEnergy (E * S) ≤ K ^ 2 * gramEnergy S := by
  rw [gramEnergy_eq_sum_compoundEnergyReal,
    gramEnergy_eq_sum_compoundEnergyReal]
  calc
    (∑ k ∈ Finset.range (Fintype.card ι + 1),
        compoundEnergyReal k (E * S))
        ≤ ∑ k ∈ Finset.range (Fintype.card ι + 1),
            K ^ 2 * compoundEnergyReal k S := by
          exact Finset.sum_le_sum fun k _ ↦ compoundEnergy_left_mul_le hE k
    _ = K ^ 2 * ∑ k ∈ Finset.range (Fintype.card ι + 1),
        compoundEnergyReal k S := by rw [Finset.mul_sum]

/-- Summing the inverse degreewise bounds gives the reverse Gram-energy
comparison. -/
theorem gramEnergy_le_left_mul {E S : Matrix ι ι ℂ} {K : ℝ}
    (hE : ExteriorConditioning E K) :
    gramEnergy S ≤ K ^ 2 * gramEnergy (E * S) := by
  rw [gramEnergy_eq_sum_compoundEnergyReal,
    gramEnergy_eq_sum_compoundEnergyReal]
  calc
    (∑ k ∈ Finset.range (Fintype.card ι + 1),
        compoundEnergyReal k S)
        ≤ ∑ k ∈ Finset.range (Fintype.card ι + 1),
            K ^ 2 * compoundEnergyReal k (E * S) := by
          exact Finset.sum_le_sum fun k _ ↦ compoundEnergy_le_left_mul hE k
    _ = K ^ 2 * ∑ k ∈ Finset.range (Fintype.card ι + 1),
        compoundEnergyReal k (E * S) := by rw [Finset.mul_sum]

end ExteriorConditioning

section VolumeComparison

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- The energy-level hypotheses isolated from the Hodge--Jacobi and finite
summation step in the paper.  These are stated separately so that the final
square-root argument has no concealed assumptions. -/
structure GramEnergyComparison (A B : Matrix ι ι ℂ) (K : ℝ) : Prop where
  one_le : 1 ≤ K
  forward : gramEnergy A ≤ K ^ 2 * gramEnergy B
  backward : gramEnergy B ≤ K ^ 2 * gramEnergy A

/-- Exterior conditioning supplies both energy inequalities, with no extra
summability hypothesis: this is the exact bridge from the Hodge--Jacobi
output to the Gram determinant comparison. -/
theorem gramEnergyComparison_of_exteriorConditioning
    {E S : Matrix ι ι ℂ} {K : ℝ} (hE : ExteriorConditioning E K) :
    GramEnergyComparison (E * S) S K where
  one_le := hE.one_le
  forward := gramEnergy_left_mul_le hE
  backward := gramEnergy_le_left_mul hE

/-- An upper energy comparison gives the corresponding upper Gram-volume
comparison. -/
theorem gramVolume_le_of_energy_le {A B : Matrix ι ι ℂ} {K : ℝ}
    (hK : 0 ≤ K) (h : gramEnergy A ≤ K ^ 2 * gramEnergy B) :
    gramVolume A ≤ K * gramVolume B := by
  rw [← sq_le_sq₀ (gramVolume_nonneg A)
    (mul_nonneg hK (gramVolume_nonneg B))]
  rw [gramVolume_sq, mul_pow, gramVolume_sq]
  exact h

/-- Bidirectional energy comparison implies bidirectional comparison of the
square-root Gram volumes. -/
theorem gramVolume_comparison {A B : Matrix ι ι ℂ} {K : ℝ}
    (h : GramEnergyComparison A B K) :
    gramVolume A ≤ K * gramVolume B ∧
      gramVolume B ≤ K * gramVolume A := by
  have hK : 0 ≤ K := le_trans zero_le_one h.one_le
  exact ⟨gramVolume_le_of_energy_le hK h.forward,
    gramVolume_le_of_energy_le hK h.backward⟩

/-- The same comparison in the paper's customary `K⁻¹ · Vol(B) ≤ Vol(A)`
form. -/
theorem gramVolume_two_sided {A B : Matrix ι ι ℂ} {K : ℝ}
    (h : GramEnergyComparison A B K) :
    K⁻¹ * gramVolume B ≤ gramVolume A ∧
      gramVolume A ≤ K * gramVolume B := by
  have hvol := gramVolume_comparison h
  constructor
  · have hK : 0 < K := lt_of_lt_of_le zero_lt_one h.one_le
    apply (inv_mul_le_iff₀ hK).2
    simpa [mul_comm] using hvol.2
  · exact hvol.1

/-- Section 9.4.1's deterministic removal of the left boundary matrix:
uniform compound bounds for `E` and its inverse imply a two-sided comparison
of the full Gram volumes. -/
theorem gramVolume_remove_left {E S : Matrix ι ι ℂ} {K : ℝ}
    (hE : ExteriorConditioning E K) :
    K⁻¹ * gramVolume S ≤ gramVolume (E * S) ∧
      gramVolume (E * S) ≤ K * gramVolume S :=
  gramVolume_two_sided (gramEnergyComparison_of_exteriorConditioning hE)

end VolumeComparison

end BernoulliLinearAlgebra
