import CircularLawSection6

open Filter Topology Set Polynomial Real
open MeasureTheory
open scoped BigOperators
open CircularLawSection6 CircularLawSections56.Section6

-- The zero polynomial and zero constant term do not break radial monotonicity.
example : MonotoneOn (polynomialCircleMean 0) (Ioi 0) :=
  polynomialCircleMean_monotoneOn 0

example : MonotoneOn (polynomialCircleMean X) (Ioi 0) :=
  polynomialCircleMean_monotoneOn X

-- A root on the unit circle is allowed; the logarithmic singularity is integrable.
example : polynomialCircleMean (X - C (1 : ℂ)) 1 = 0 := by
  simp [polynomialCircleMean]

-- Empty matrices use the explicitly totalized normalized average.
example (A B : Matrix (Fin 0) (Fin 0) ℂ) :
    Real.log ‖A.det‖ / (0 : ℝ) ≤
      circleAverage (fun w => Real.log ‖(w • B + A).det‖) 0 1 / (0 : ℝ) := by
  simp

-- Constant polynomials retain their actual constant term in Jensen's inequality.
example (a : ℂ) (ha : a ≠ 0) :
    Real.log ‖a‖ ≤ polynomialCircleMean (C a) 1 := by
  simpa using log_norm_eval_zero_le_polynomialCircleMean (C a) (by simpa using ha)

-- The spectral origin and the joining radius of the circular potential are allowed.
example {v : ℕ → ℝ} (hv : Tendsto v atTop (𝓝 1)) :
    Tendsto (fun R => varianceScaledRadialPotential (v R) 0) atTop
      (𝓝 (circularRadialPotential 0)) :=
  varianceScaledRadialPotential_tendsto_one hv 0

example : ContinuousAt circularRadialPotential 1 :=
  continuous_circularRadialPotential.continuousAt

-- Even dimensions use the negative representative at the half-period tie.
example : centeredOffset 4 (2 : ZMod 4) = -2 := by decide

-- Odd dimensions retain both end representatives without assuming profile symmetry.
example : centeredOffset 5 (2 : ZMod 5) = 2 := by decide

example : centeredOffset 5 (3 : ZMod 5) = -2 := by decide

-- At the exact odd-size threshold, the core still has exactly 2 H + 1 offsets.
example : (coreOffsets 5 2).card = 5 := by
  simpa using card_coreOffsets 5 2 (by decide)

-- Beyond the unwrapping condition, the even-size core saturates at N entries.
example : (coreOffsets 4 2).card = 4 := by decide

-- A one-dimensional matrix has one active diagonal even at zero truncation radius.
example : coreOffsets 1 0 = Finset.univ := by
  ext s
  simp only [Finset.mem_univ, iff_true]
  rw [Subsingleton.elim s 0]
  exact zero_mem_coreOffsets 1 0

-- Empty tails are zero; they do not require division by a positive tail mass.
example (N : ℕ) [NeZero N] (q : ZMod N → ℝ) (ω : ZMod N × ZMod N → ℂ) :
    weightedCyclicMatrix N (maskedWeight ∅ q) ω = 0 := by
  ext i j
  simp [weightedCyclicMatrix, maskedWeight]

-- The real two-dimensional standard Gaussian has energy two, not one.
example : (∫ z : ℂ, ‖z‖ ^ 2 ∂ProbabilityTheory.stdGaussian ℂ) = 2 :=
  realStandardComplexGaussian_secondMoment

-- The actual complex atoms are normalized before the matrix construction.
example : (∫ z : ℂ, ‖z‖ ^ 2 ∂circularComplexGaussian) = 1 :=
  circularComplexGaussian_secondMoment

example (a : Circle) :
    circularComplexGaussian.map (fun z : ℂ => (a : ℂ) * z) = circularComplexGaussian :=
  circularComplexGaussian_rotation a

example (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ) :
    ProbabilityTheory.IndepFun (p.coreMatrix N H W) (p.tailMatrix N H W)
      (gaussianProfileLaw N) := p.gaussian_core_tail_independent N H W

example (p : NoncompactProfile) (N : ℕ) [NeZero N] (W : ℝ) :
    (∫ ω, cyclicEnergy N (p.matrix N W ω) ∂gaussianProfileLaw N) = 1 :=
  (p.gaussian_expected_energy N W).2

-- The BV quadrature statement includes a zero-length mesh.
example {f : ℝ → ℝ} (hf : Continuous f) (hBV : BoundedVariationOn f univ)
    (a : ℝ) (n : ℕ) :
    |(0 : ℝ) * (∑ i ∈ Finset.range n, f (a + i * 0)) -
        ∫ x in a..a + n * 0, f x| ≤ 0 := by
  simpa only [zero_mul] using uniformMesh_error_le hf hBV a n (δ := 0) le_rfl

-- A zero cutoff radius has zero limiting core mass, despite its finite diagonal.
example (p : NoncompactProfile) (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (W : ℕ → ℝ) (hW : ∀ n, 0 < W n)
    (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (N n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => p.coreMass (N n) 0 (W n)) atTop (𝓝 0) := by
  simpa using p.coreMass_tendsto_sparse N hN W hW hWlim hsparse (R := 0) le_rfl

-- Radius exhaustion is a separate limit after the fixed-radius matrix-size limit.
example (p : NoncompactProfile) :
    Tendsto (fun R : ℕ => 1 - ∫ x in -(R : ℝ)..(R : ℝ), p.f x) atTop (𝓝 0) :=
  p.limitingTailMass_tendsto_zero

-- Dense comparison has constants uniform over dimensions and bandwidths.
example (p : NoncompactProfile) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ) [NeZero N] (W : ℝ), (N : ℝ) ≤ W →
        ∀ s : ZMod N, c / (N : ℝ) ≤ p.weight N W s ∧ p.weight N W s ≤ C / (N : ℝ) := by
  simpa only [one_mul] using p.dense_weights_comparable (κ := 1) zero_lt_one

-- The literal tail integral includes all mass when the limiting core radius is zero.
example (p : NoncompactProfile) : p.limitingTailMass 0 = 1 := by
  rw [p.limitingTailMass_eq_one_sub le_rfl, NoncompactProfile.limitingCoreMass]
  simp

-- The expected Jensen bound has no remaining small-ball or log-integrability inputs.
example (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      (∫ ω, p.rawCoreLogDet N H W z ω ∂gaussianProfileLaw N) / (N : ℝ) ≤
        (∫ ω, p.rawProfileLogDet N W z ω ∂gaussianProfileLaw N) / (N : ℝ) :=
  p.gaussian_expected_tail_jensen_ae N H W

-- The local L² estimate yields sample integrability from energy, without Gaussianity.
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (N : ℕ) [NeZero N] (A : Ω → Matrix (ZMod N) (ZMod N) ℂ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j))
    (hE : Integrable (fun ω => cyclicEnergy N (A ω)) μ) :
    ∀ᵐ z ∂(volume : Measure ℂ), Integrable (fun ω => Real.log ‖(A ω - z • 1).det‖) μ :=
  ae_cyclic_rawLogDet_integrable μ N A hA hE

-- The actual normalized Gaussian discharges the old bounded-density input.
example : CircularLawSection4.ComplexBallBound circularComplexGaussian (ENNReal.ofReal 2) :=
  circularComplexGaussian_ballBound

-- At the exact full-width threshold the unit core is the literal Section 5 model.
example (p : NoncompactProfile) (W : ℝ) (ω : ZMod 5 × ZMod 5 → ℂ) :
    p.unitCoreMatrix 5 2 W ω = CircularLawSection4.paperIndicatorX 5 3 (2 : Fin 4)
      (fun s => (Real.sqrt (p.coreBandWeight 5 3 (2 : Fin 4) W s) : ℂ))
      (coreBandSample 5 3 (2 : Fin 4) ω) :=
  p.unitCoreMatrix_eq_paperIndicatorX 5 3 (by decide) (2 : Fin 4) (by decide) W ω

-- A proper subset of the original atoms still has the exact smaller IID law.
example : MeasurePreserving (coreBandSample 7 3 (2 : Fin 4))
    (cyclicAtomLaw 7 circularComplexGaussian)
    (CircularLawSection4.paperIndicatorSampleMeasure 7 3 circularComplexGaussian) :=
  coreBandSample_measurePreserving 7 3 (by decide) (2 : Fin 4) circularComplexGaussian

-- Zero cofactor families use the checked all-scales branch, not a positivity premise.
example (z : ℂ) : MemLp (fun η : Fin 1 → ℂ =>
    |Real.log ‖CircularLawSection4.operatorAffine (fun _ : Fin 1 => (1 : ℂ)) η
      (fun _ : Fin 1 => (0 : ℂ →L[ℂ] ℂ)) z 0‖ -
      Real.log (CircularLawSection4.operatorAffineScale (0 : Fin 1)
        (fun _ => (1 : ℂ)) (fun _ => (0 : ℂ →L[ℂ] ℂ)))|)
    2 (CircularLawSection4.iidMeasure circularComplexGaussian 1) :=
  (complex_affine_log_memLp_of_diagonal_all_scales circularComplexGaussian
    circularComplexGaussian_ballBound (by norm_num) (0 : Fin 1) (fun _ => 1)
    (fun _ => (0 : ℂ →L[ℂ] ℂ)) z (q := 1) zero_lt_one le_rfl (by norm_num)
    circularComplexGaussian_sq_integrable circularComplexGaussian_secondMoment.le).1

-- Actual shifted determinants are square-integrable even in dimension one.
example (z : ℂ) : MemLp (weightedRowsLogDet (1 : Matrix (Fin 1) (Fin 1) ℂ) z) 2
    (CircularLawSection4.iidMeasure (CircularLawSection4.iidMeasure circularComplexGaussian 1) 1) :=
  (weightedRowsLogDet_memLp_and_variance circularComplexGaussian circularComplexGaussian_ballBound
    (by norm_num) (1 : Matrix (Fin 1) (Fin 1) ℂ) z (q := 1) zero_lt_one le_rfl
    (by intro i; simp) circularComplexGaussian_sq_integrable
    circularComplexGaussian_secondMoment.le).1
