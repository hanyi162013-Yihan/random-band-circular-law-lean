import CircularLawSections56

/-! # Small boundary-case regression checks for the completed Section 5 API

These examples check the exterior endpoint degrees, the smallest positive taper
width and non-aliasing matrix, and the deliberately hypothesis-free inactive
branches. They are kernel-checked examples, not numerical simulations.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open CircularLawSections56.Section5 CircularLawSections56.Section6
open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights Matrix

-- Exterior degree zero: the complementary degree must be the full dimension.
example (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : IsUnit A.det) :
    ‖(compound 0 A)⁻¹‖ = ‖compound 2 A‖ / ‖A.det‖ :=
  norm_compound_inverse_eq_complement 1 ⟨0, by decide⟩ A hA

-- Exterior top degree: the complementary degree must be zero.
example (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : IsUnit A.det) :
    ‖(compound 2 A)⁻¹‖ = ‖compound 0 A‖ / ‖A.det‖ :=
  norm_compound_inverse_eq_complement 1 ⟨2, by decide⟩ A hA

-- The smallest positive taper width has two transfer coordinates and three slots.
example : taperStateDimension 1 + 1 = 2 := by decide
example : (taperCenter 1 (by decide)).val = 1 := rfl
example : (taperCenter 1 (by decide)) ≠ 0 := taperCenter_ne_zero 1 (by decide)

-- A concrete profile exists; its center is positive and its boundary vanishes.
example : triangleTaperProfile.f 0 = 1 := by norm_num [triangleTaperProfile_value]
example : triangleTaperProfile.f 1 = 0 := by norm_num [triangleTaperProfile_value]
example : triangleTaperProfile.f (-1) = 0 := by norm_num [triangleTaperProfile_value]
example : BoundedVariationOn triangleTaperProfile.f Set.univ :=
  triangleTaperProfile.boundedVariation

-- Sampling at s/(W+1), rather than s/W, keeps both edge weights positive.
example : triangleTaperProfile.weight 1 0 = 1 / 4 := by
  norm_num [PolynomialTaperProfile.weight, PolynomialTaperProfile.mass,
    PolynomialTaperProfile.raw, triangleTaperProfile_value, taperGrid, Fin.sum_univ_succ]
example : triangleTaperProfile.weight 1 1 = 1 / 2 := by
  norm_num [PolynomialTaperProfile.weight, PolynomialTaperProfile.mass,
    PolynomialTaperProfile.raw, triangleTaperProfile_value, taperGrid, Fin.sum_univ_succ]
example : triangleTaperProfile.weight 1 2 = 1 / 4 := by
  norm_num [PolynomialTaperProfile.weight, PolynomialTaperProfile.mass,
    PolynomialTaperProfile.raw, triangleTaperProfile_value, taperGrid, Fin.sum_univ_succ]

-- The exact energy identity at the minimal non-aliasing size N=3, W=1.
example (p : PolynomialTaperProfile) (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν = 1) :
    (∫ ω, physicalEnergy (p.literalMatrix 2 1 (by decide) ω) ∂iidMeasure ν 9) = 1 :=
  taperedMatrix_expected_energy_one p 2 1 (by decide) (by decide) ν hInt hSecond

-- No integrability or measurability of an unused raw observable is required.
example {Ω : ℕ → Type*} (raw : ∀ n, Ω n → ℝ) (scale : ℕ → ℕ) (target : ℝ) :
    literalActiveNormalizedObservable (fun _ => false) raw scale target = fun _ _ => target := by
  funext n ω
  simp only [literalActiveNormalizedObservable, Bool.false_eq_true, ↓reduceIte]

-- Finite-prefix non-fitting matrices are filled explicitly, not silently assumed to fit.
example (b : Fin 3 → ℂ) (ω : Fin 3 → ℂ) :
    filledLiteralIndicatorMatrix 0 1 ⟨1, by decide⟩ b ω = 0 := by
  simp only [filledLiteralIndicatorMatrix]
  norm_num

-- The preferred complex-density endpoint takes an arbitrary fixed shift;
-- no planar almost-everywhere quantifier occurs in its signature.
#check @PublishedSection3Concrete.indicator_complex_logPotential_at_of_bbv
