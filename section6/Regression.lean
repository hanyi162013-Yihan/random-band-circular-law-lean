import CircularLawSection6

open Filter Topology Set Polynomial Real
open MeasureTheory
open scoped BigOperators
open CircularLawSection6 CircularLawSections56.Section6

attribute [local instance] CircularLawSection4.iidMeasure_isProbability

-- The uniform Gaussian theorem now includes dimension one, without a filler.
example (z : ℂ) : MemLp (cyclicRawLogDet 1 (fun _ => 1) 1 z) 2
    (cyclicAtomLaw 1 circularComplexGaussian) :=
  (gaussian_cyclic_memLp_and_variance_all 1 (fun _ => 1) (c := 1)
    zero_lt_one zero_lt_one z (by norm_num)).1

-- A three-dimensional unit core is the actual physical Section 5 matrix.
example (p : NoncompactProfile) (W : ℝ) (z : ℂ) (ω : ZMod 3 × ZMod 3 → ℂ) :
    p.unitCoreLogPotential 3 1 W z ω =
      physicalLogPotential (literalIndicatorMatrix 2 1 (1 : Fin 2)
        (fun s => (Real.sqrt (p.coreBandWeight 3 1 (1 : Fin 2) W s) : ℂ))
        (coreBandSample 3 1 (1 : Fin 2) ω)) z :=
  p.unitCoreLogPotential_eq_literal 1 1 (by decide) (1 : Fin 2) (by decide) W z ω

-- Eigenvector overlap costs agree with actual operator energy already in dimension one.
example (A B : Module.End ℂ ℂ) (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    (∑ i, ∑ j, orthonormalCoupling (hA.eigenvectorBasis rfl) (hB.eigenvectorBasis rfl) i j *
      (hA.eigenvalues rfl i - hB.eigenvalues rfl j) ^ 2) =
      TaoVuReplacement.operatorHilbertSchmidtSq (A - B) :=
  hermitian_eigenvector_coupling_cost A B hA hB

-- The diagonal comparison does not require a positive bandwidth input.
example (p : NoncompactProfile) (N : ℕ) [NeZero N] :
    p.diagonalComparisonConstant / (N : ℝ) ≤ p.weight N 0 0 :=
  p.diagonal_weight_ge N 0

-- A radius-zero normalized core remains covered by the same bound.
example (p : NoncompactProfile) (N : ℕ) [NeZero N] (W : ℝ) :
    p.diagonalComparisonConstant / (N : ℝ) ≤ p.normalizedCoreWeight N 0 W 0 :=
  p.diagonal_normalizedCoreWeight_ge N 0 W

example : scaledDiagonalConstant 2 1 = 1 := by norm_num [scaledDiagonalConstant]

-- Two-dimensional literal Gaussian log determinants already have finite L².
example (p : NoncompactProfile) (W : ℝ) (z : ℂ) :
    MemLp (p.rawProfileLogDet 2 W z) 2 (gaussianProfileLaw 2) :=
  p.rawProfileLogDet_memLp 0 W z

-- Concentration needs no asymptotic assumptions on the bandwidth sequence.
example (p : NoncompactProfile) (d : ℕ → ℕ)
    (hd : Tendsto (fun n => d n + 2) atTop atTop) (W : ℕ → ℝ) (z : ℂ) :
    CircularLawSections56.Section5.TendstoInProbabilityTri (fun n => gaussianProfileLaw (d n + 2))
      (fun n ω => p.rawProfileLogDet (d n + 2) (W n) z ω / (d n + 2 : ℝ) -
        ∫ x, p.rawProfileLogDet (d n + 2) (W n) z x / (d n + 2 : ℝ)
          ∂gaussianProfileLaw (d n + 2)) 0 :=
  p.full_profile_concentration d hd W z

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

-- Column reindexing preserves the actual IID law, including dimension one.
example : MeasurePreserving (cyclicColumnSample 1) (cyclicAtomLaw 1 circularComplexGaussian)
    (CircularLawSection4.iidMeasure (CircularLawSection4.iidMeasure circularComplexGaussian 1) 1) :=
  cyclicColumnSample_measurePreserving 1 circularComplexGaussian

-- The exact determinant identity also includes zero matrix scaling.
example (q : ZMod 3 → ℝ) (z : ℂ) (ω : ZMod 3 × ZMod 3 → ℂ) :
    weightedRowsLogDet (cyclicRowAmplitude 3 q 0) z (cyclicColumnSample 3 ω) =
      cyclicRawLogDet 3 q 0 z ω := weightedRowsLogDet_cyclicColumnSample 3 q 0 z ω

-- No logarithmic rate limit is left as an additional hypothesis.
example : Tendsto (fun n : ℕ => (Real.log (Real.exp 1 * (n : ℝ))) ^ 2 / (n : ℝ))
    atTop (𝓝 0) := tendsto_logEN_sq_div id tendsto_id

-- Totalized zero normalization is preserved by the variance identity.
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) :
    ProbabilityTheory.variance (fun ω => X ω / 0) μ = 0 := by
  rw [variance_div_const]
  simp

-- The cutoff contraction is global, including negative test arguments.
example (x y : ℝ) :
    |Real.log (max x 1) - Real.log (max y 1)| ≤ |x - y| := by
  simpa using log_max_lipschitz zero_lt_one x y

-- The singular-coefficient cost allows zero values without dividing by them.
example (t : ℝ) (ht : 0 ≤ t) (a b : ℂ) :
    (‖a‖ ^ 2 + ‖b‖ ^ 2) * (0 - t) ^ 2 ≤
      ‖(0 : ℂ) * a - (t : ℂ) * b‖ ^ 2 +
        ‖(0 : ℂ) * b - (t : ℂ) * a‖ ^ 2 :=
  complex_two_coefficient_cost 0 t le_rfl ht a b

-- Dimension normalization is exact, not only an asymptotic constant bound.
example (e : ℝ) : Real.sqrt (4 * e) / 4 = Real.sqrt e / 2 := by
  have h4 : Real.sqrt (4 : ℝ) = 2 := by norm_num
  simpa only [h4] using sqrt_mul_div_dimension (e := e) (by norm_num : (0 : ℝ) < 4)

-- Empty raw potentials are totalized, but positive-dimension scaling is not asserted for them.
example (A : Matrix (Fin 0) (Fin 0) ℂ) : matrixRawPotential A = 0 := by
  simp [matrixRawPotential]

-- Positive scaling is exact already for a one-dimensional nonsingular matrix.
example (A : Matrix (Fin 1) (Fin 1) ℂ) (hA : A.det ≠ 0) :
    matrixRawPotential ((2 : ℂ) • A) = Real.log 2 + matrixRawPotential A :=
  matrixRawPotential_smul A hA (by norm_num)

-- A zero energy does not require a separate strictly-positive Cauchy--Schwarz case.
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    MemLp (fun _ : Ω => Real.sqrt 0) 2 μ :=
  memLp_sqrt_of_integrable_nonneg μ (fun _ => 0) (integrable_const _)
    (ae_of_all _ fun _ => le_rfl)

-- In dimension one the radius-zero core is already the whole matrix and the tail error vanishes.
example (p : NoncompactProfile) (W : ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ a : ℝ, 0 < a →
      (∫ ω, |matrixCutoffPotential (p.matrix 1 W ω - z • 1) a -
        matrixCutoffPotential (p.coreMatrix 1 0 W ω - z • 1) a| ∂gaussianProfileLaw 1) ≤ 0 := by
  have hs : coreOffsets 1 0 = Finset.univ := by decide
  filter_upwards [p.gaussian_expected_tail_cutoff_ae 1 0 W] with z hz
  intro a ha
  simpa only [NoncompactProfile.tailMass, hs, Finset.compl_univ, Finset.sum_empty,
    Real.sqrt_zero, zero_div] using (hz a ha).2

-- The actual upper comparison has no supplied singular-value, energy, or integrability premise.
example (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      (∫ ω, p.rawProfileLogDet N W z ω ∂gaussianProfileLaw N) / (N : ℝ) ≤
        (∫ ω, matrixCutoffPotential (p.coreMatrix N H W ω - z • 1) 1 ∂gaussianProfileLaw N) +
          Real.sqrt (p.tailMass N H W) := by
  filter_upwards [p.gaussian_expected_core_full_cutoff_sandwich_ae N H W] with z hz
  simpa only [div_one] using (hz 1 zero_lt_one).2.2

-- Actual radial mean monotonicity includes dimension one and spectral parameter zero.
example (p : NoncompactProfile) (W : ℝ) :
    MonotoneOn (fun r => p.scaledUnitCoreMean 1 0 W r 0) (Ioi 0) :=
  p.scaledUnitCoreMean_monotoneOn 1 0 W 0

-- Cutoff scaling permits a zero comparison scale; nonsingularity is a.e. in the parameter.
example (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      (∫ ω, |matrixCutoffPotential ((0 : ℂ) • p.unitCoreMatrix N H W ω - z • 1) 1 -
        matrixCutoffPotential ((1 : ℂ) • p.unitCoreMatrix N H W ω - z • 1) 1|
        ∂gaussianProfileLaw N) ≤ 1 := by
  filter_upwards [p.gaussian_unitCore_cutoff_scaling_ae N H W 0 1] with z hz
  simpa only [zero_sub, abs_neg, abs_one, div_one, Complex.ofReal_zero,
    Complex.ofReal_one] using (hz 1 zero_lt_one).2.2

-- The first positive half-width has exactly three active offsets.
example : canonicalCoreBand 1 + 2 = 3 := canonicalCoreBand_width (by norm_num)

-- The center is the actual half-width, not a dummy boundary filler.
example : (canonicalCoreCenter 1 (by norm_num)).val = 1 := rfl

-- Positive fixed-scale expectation transport also covers the one-dimensional core.
example (p : NoncompactProfile) (W : ℝ) :
    ∀ᵐ z ∂(volume : Measure ℂ), p.scaledUnitCoreMean 1 0 W 2 z =
      Real.log 2 + ∫ ω, p.unitCoreLogPotential 1 0 W (z / (2 : ℂ)) ω ∂gaussianProfileLaw 1 :=
  p.scaledUnitCoreMean_eq_log_add_ae 1 0 W (by norm_num)

-- The cutoff normalization transport itself does not assume a positive limiting mass.
example (p : NoncompactProfile) (N H : ℕ → ℕ) [∀ n, NeZero (N n)] (W : ℕ → ℝ)
    (hmass : Tendsto (fun n => p.coreMass (N n) (H n) (W n)) atTop (𝓝 0)) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n =>
        |(∫ ω, matrixCutoffPotential (p.coreMatrix (N n) (H n) (W n) ω - z • 1) 1
          ∂gaussianProfileLaw (N n)) -
          ∫ ω, matrixCutoffPotential ((Real.sqrt 0 : ℂ) •
            p.unitCoreMatrix (N n) (H n) (W n) ω - z • 1) 1
            ∂gaussianProfileLaw (N n)|) atTop (𝓝 0) :=
  p.gaussian_core_cutoff_normalization_error N H W hmass zero_lt_one

-- With no changed rows, the common-atom coupling has exactly zero error bound.
example {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (r₁ r₂ : ι → κ → ι) (h₁ : ∀ i, Function.Injective (r₁ i))
    (h₂ : ∀ i, Function.Injective (r₂ i)) (h : ∀ i s, r₁ i s = r₂ i s)
    (b : κ → ℂ) (ω : ι × κ → ℂ) :
    TaoVuReplacement.hilbertSchmidtSq (routedBandMatrix r₁ b ω - routedBandMatrix r₂ b ω) ≤ 0 := by
  simpa only [Finset.sum_empty, mul_zero] using
    routedBand_difference_energy_le r₁ r₂ h₁ h₂ ∅ (fun i _ s => h i s) b ω

-- The finite routing constructor also allows an empty slot set.
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (route : ι → Fin 0 → ι) (b : Fin 0 → ℂ) (ω : ι × Fin 0 → ℂ) :
    routedBandMatrix route b ω = 0 := by
  ext i j
  simp [routedBandMatrix]

-- Negative displacement at the first row really wraps to the last column.
example : cyclicFinSlot 1 (0 : Fin 5) (0 : Fin 3) = 4 := by decide

-- Two length-five blocks have four boundary rows for half-width one.
example : (blockBoundaryRows (fun _ : Fin 2 => 5) 1).card = 4 := by decide

-- A nonzero remainder is absorbed into an actual block, without a terminal filler.
example : ∃ (q : ℕ) (len : Fin q → ℕ), 0 < q ∧ (∑ b, len b) = 10 ∧
    ∀ b, 3 ≤ len b ∧ len b < 6 :=
  exists_periodic_block_lengths (by decide : 0 < 3) (by decide : 3 ≤ 10)

-- Parameter nonvanishing includes empty matrices, whose determinant is one.
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ᵐ _ω ∂μ,
      ((0 : Matrix (Fin 0) (Fin 0) ℂ) - z • 1).det ≠ 0 :=
  ae_shifted_matrix_det_ne_zero μ (fun _ => 0) measurable_const

-- Half-width zero changes no matrix entries under block periodicization.
example {q : ℕ} (len : Fin q → ℕ) [∀ j, NeZero (len j)] [NeZero (∑ j, len j)] :
    (∫ ω, TaoVuReplacement.hilbertSchmidtSq
      (routedBandMatrix (fullBlockRoute len 0) (fun _ => (1 : ℂ)) ω -
        routedBandMatrix (periodicBlockRoute len 0) (fun _ => (1 : ℂ)) ω)
      ∂Measure.pi (fun _ : ((j : Fin q) × Fin (len j)) × Fin 1 => circularComplexGaussian)) ≤ 0 := by
  simpa using (periodicization_expected_energy len (H := 0) (fun j => NeZero.pos (len j))
    (fun _ => 1) (by simp) circularComplexGaussian
    circularComplexGaussian_sq_integrable circularComplexGaussian_secondMoment).2

-- The total block-expectation definition has an explicit inactive zero-dimensional branch.
example (ν : Measure ℂ) (z : ℂ) : cyclicBlockExpectedCutoff 0 0 (fun _ => 1) ν z 1 = 0 := by
  simp [cyclicBlockExpectedCutoff]

-- The exact finite squared-singular CDF controls the bounded matrix test.
example (A : Matrix (Fin 1) (Fin 1) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    |matrixClippedPotential A 1 2 - matrixClippedPotential B 1 2| ≤
      matrixSquaredSingularCdfDistanceOn A B 2 * (Real.log 2 - Real.log 1) :=
  matrixClipped_difference_le_cdf A B zero_lt_one (by norm_num)

-- Exact cutoff scaling includes a threshold change, not just an additive logarithm.
example (A : Matrix (Fin 1) (Fin 1) ℂ) (hA : A.det ≠ 0) :
    matrixCutoffPotential ((2 : ℂ) • A) 1 =
      Real.log 2 + matrixCutoffPotential A (1 / 2) :=
  matrixCutoffPotential_smul A hA (by norm_num) zero_lt_one

-- The scalar logarithmic identity holds even below the truncation threshold.
example : Real.log (max ((2 : ℝ) * 0) 1) =
    Real.log 2 + Real.log (max (0 : ℝ) (1 / 2)) :=
  log_max_positive_scale (by norm_num) zero_lt_one 0

-- Dimension weights normalize for unequal block lengths as well.
example : (∑ b : Fin 2, ((![3, 7] b : ℕ) : ℝ) / 10) = 1 :=
  dimension_weights_sum_one ![3, 7] (by norm_num) (by norm_num [Fin.sum_univ_two])

-- A convex block average inherits the common error without a block-count factor.
example {q : ℕ} (w x : Fin q → ℝ) (hw : ∀ b, 0 ≤ w b) (hsum : ∑ b, w b = 1)
    (target : ℝ) (hx : ∀ b, |x b - target| ≤ (1 : ℝ) / 10) :
    |(∑ b, w b * x b) - target| ≤ (1 : ℝ) / 10 :=
  weighted_block_error_le w x hw hsum target (1 / 10) hx

-- Cyclic displacement agrees with the paper's ZMod indexing, including wraparound.
example : ZMod.finEquiv 5 (cyclicFinSlot 1 (0 : Fin 5) (0 : Fin 3)) =
    ZMod.finEquiv 5 0 - (1 : ZMod 5) + 0 :=
  finEquiv_cyclicFinSlot 1 0 0

-- The flattened sample used for the original full route has the exact IID law.
section
local instance : NeZero (∑ _ : Fin 2, (5 : ℕ)) := ⟨by norm_num [Fin.sum_univ_two]⟩

example (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    MeasurePreserving (fullBlockPaperSample (fun _ : Fin 2 => 5) 1 1 (by decide))
      (Measure.pi (fun _ : ((_b : Fin 2) × Fin 5) × Fin 3 => ν))
      (CircularLawSection4.paperIndicatorSampleMeasure 10 1 ν) :=
  fullBlockPaperSample_measurePreserving (fun _ : Fin 2 => 5) 1 1 (by decide) ν
end

-- The cutoff of two nonsingular scalar blocks is their arithmetic mean.
example (A : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ) (hA : ∀ b, (A b).det ≠ 0) :
    matrixCutoffPotential (Matrix.blockDiagonal' A) 1 =
      (matrixCutoffPotential (A 0) 1 + matrixCutoffPotential (A 1) 1) / 2 := by
  simpa [Fin.sum_univ_two] using matrixCutoffPotential_blockDiagonal A hA zero_lt_one

-- Actual one-dimensional routed Gaussian blocks have integrable cutoffs at every positive threshold.
example : ∀ᵐ z ∂(volume : Measure ℂ), ∀ t : ℝ, 0 < t →
    Integrable (fun ω => matrixCutoffPotential
      (routedBandMatrix (cyclicFinSlot (N := 1) 0) (fun _ => (1 : ℂ)) ω - z • 1) t)
      (Measure.pi (fun _ : Fin 1 × Fin 1 => circularComplexGaussian)) :=
  routedBand_shifted_cutoff_integrable_ae (cyclicFinSlot 0)
    (cyclicFinSlot_injective (by decide)) (fun _ => 1) circularComplexGaussian
    circularComplexGaussian_sq_integrable

-- The actual Gaussian periodicized expectation is the dimension-weighted block expectation.
example {q : ℕ} (len : Fin q → ℕ) [∀ b, NeZero (len b)]
    {H : ℕ} (hfit : ∀ b, 2 * H + 1 ≤ len b) (a : Fin (2 * H + 1) → ℂ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      (∫ ω, matrixCutoffPotential (routedBandMatrix (periodicBlockRoute len H) a ω - z • 1) 1
        ∂Measure.pi (fun _ : ((b : Fin q) × Fin (len b)) × Fin (2 * H + 1) => circularComplexGaussian)) =
        (∑ b, (len b : ℝ) * ∫ η, matrixCutoffPotential
          (routedBandMatrix (cyclicFinSlot H) a η - z • (1 : Matrix (Fin (len b)) (Fin (len b)) ℂ)) 1
            ∂Measure.pi (fun _ : Fin (len b) × Fin (2 * H + 1) => circularComplexGaussian)) /
          (∑ b, len b : ℕ) := by
  filter_upwards [periodicBlockMatrix_expected_cutoff_average_ae len hfit a circularComplexGaussian
    circularComplexGaussian_sq_integrable] with z hz
  exact (hz 1 zero_lt_one).2

-- Scaling by two still gives zero periodicization error for a diagonal band.
example {q : ℕ} (len : Fin q → ℕ) [∀ b, NeZero (len b)] [NeZero (∑ b, len b)] :
    ∀ᵐ z ∂(volume : Measure ℂ),
      (∫ ω, |matrixCutoffPotential
        ((2 : ℂ) • routedBandMatrix (fullBlockRoute len 0) (fun _ => 1) ω - z • 1) 1 -
        matrixCutoffPotential
          ((2 : ℂ) • routedBandMatrix (periodicBlockRoute len 0) (fun _ => 1) ω - z • 1) 1|
        ∂Measure.pi (fun _ : ((b : Fin q) × Fin (len b)) × Fin 1 => circularComplexGaussian)) ≤ 0 := by
  filter_upwards [periodicization_expected_scaled_cutoff_ae len (m₀ := 1) zero_lt_one
    (fun b => NeZero.pos (len b)) (H := 0) (fun b => NeZero.pos (len b))
    (fun _ => 1) (by simp) circularComplexGaussian
    circularComplexGaussian_sq_integrable circularComplexGaussian_secondMoment (r := 2) (by norm_num)]
    with z hz
  simpa using (hz 1 zero_lt_one).2

-- Bounded triangular probability convergence gives the actual expectation limit.
example {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (hX : ∀ n, Measurable (X n))
    (hB : ∀ n, ∀ᵐ ω ∂μ n, |X n ω| ≤ 1)
    (hp : CircularLawSections56.Section5.TendstoInProbabilityTri μ X 0) :
    Tendsto (fun n => ∫ ω, X n ω ∂μ n) atTop (𝓝 0) :=
  tendsto_expectation_of_bounded_probability μ X hX 1 0 hB hp

-- A zero singular value is allowed in the exact cutoff decomposition.
example : Real.log (max (0 : ℝ) 1) =
    ShortRingAnchor.clippedLog 1 2 (0 ^ 2) + ShortRingAnchor.upperLogCorrection 2 0 :=
  cutoffLog_eq_clippedLog_add_upper zero_lt_one (by norm_num) le_rfl

-- The upper-tail error uses only the second moment, not a hard-edge estimate.
example (s : ℝ) (hs : 0 ≤ s) :
    |Real.log (max s 1) - ShortRingAnchor.clippedLog 1 2 (s ^ 2)| ≤ s ^ 2 / 2 :=
  cutoffLog_clipped_abs_error_le_sq_div zero_lt_one (by norm_num) (by norm_num) hs

-- The compact test stays bounded even for negative squared-law arguments.
example (x : ℝ) : |ShortRingAnchor.clippedLog 1 2 x| ≤ max |Real.log 1| |Real.log 2| :=
  clippedLog_abs_le zero_lt_one (by norm_num) x

-- The bounded squared-singular test is an exact difference of matrix cutoffs.
example (A : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixClippedPotential A 1 2 = matrixCutoffPotential A 1 - matrixCutoffPotential A 2 + Real.log 2 :=
  matrixClippedPotential_eq_cutoff_difference A zero_lt_one (by norm_num)

-- A two-dimensional matrix upper error is normalized by both dimension and cutoff.
example (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) :
    |matrixCutoffPotential A 1 - matrixClippedPotential A 1 2| ≤ TaoVuReplacement.hilbertSchmidtSq A / (2 * 2) := by
  simpa using matrixCutoff_clipped_error_le A hA zero_lt_one (by norm_num : (1 : ℝ) ≤ 2)
    (by norm_num)

-- The squared-singular observable is the exact bounded test used in the matrix theorem.
example (A : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixSquaredSingularAverage A (ShortRingAnchor.clippedLog 1 2) = matrixClippedPotential A 1 2 := rfl

-- The actual normalized diagonal Gaussian route has total mean energy equal to its dimension.
example : (∫ ω, TaoVuReplacement.hilbertSchmidtSq (routedBandMatrix (cyclicFinSlot (N := 3) 0) (fun _ => 1) ω)
    ∂Measure.pi (fun _ : Fin 3 × Fin 1 => circularComplexGaussian)) = 3 := by
  simpa using (routedBand_expected_energy (cyclicFinSlot (N := 3) 0)
    (cyclicFinSlot_injective (by decide)) (fun _ => 1) (by simp) circularComplexGaussian
    circularComplexGaussian_sq_integrable circularComplexGaussian_secondMoment).2

-- Uniform second moments turn triangular probability convergence into L1 convergence.
example {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (hX : ∀ n, MemLp (X n) 2 (μ n))
    (hB : ∀ n, (∫ ω, X n ω ^ 2 ∂μ n) ≤ 1)
    (hp : CircularLawSections56.Section5.TendstoInProbabilityTri μ X 0) :
    Tendsto (fun n => ∫ ω, |X n ω| ∂μ n) atTop (𝓝 0) :=
  tendsto_L1_of_ae_uniform_secondMoment_probability μ X hX 1 hB hp

-- The positive logarithmic cutoff square is controlled by normalized matrix energy.
example (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) :
    matrixCutoffPotential A 1 ^ 2 ≤ TaoVuReplacement.hilbertSchmidtSq A / 2 := by
  simpa using matrixCutoffPotential_one_sq_le_energy A hA

-- Lower-cutoff second-moment control is uniform all the way down to zero.
example (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    (matrixCutoffPotential A a - matrixRawPotential A) ^ 2 ≤
      2 * (TaoVuReplacement.hilbertSchmidtSq A / 2) + 2 * matrixRawPotential A ^ 2 := by
  simpa using matrixLowerCutoff_correction_sq_le A hA ha ha1

-- Simultaneous coordinate permutation preserves the actual shifted cutoff.
example (e : Fin 2 ≃ Fin 2) (A : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ)
    (hA : (A - z • 1).det ≠ 0) :
    matrixCutoffPotential (A.submatrix e.symm e.symm - z • 1) 1 =
      matrixCutoffPotential (A - z • 1) 1 :=
  matrixCutoffPotential_shifted_reindex e A z hA zero_lt_one

-- The reference is the actual normalized Gaussian matrix, including dimension one.
example : (∫ ω, TaoVuReplacement.hilbertSchmidtSq (ginibreMatrix 1 ω)
    ∂cyclicAtomLaw 1 circularComplexGaussian) = 1 := by
  simpa only [Nat.cast_one] using (ginibre_expected_energy 1).2

-- The entry/displacement permutation preserves the full IID Gaussian law.
example : MeasurePreserving (ginibreEntryAtoms 3) (cyclicAtomLaw 3 circularComplexGaussian)
    (cyclicAtomLaw 3 circularComplexGaussian) := ginibreEntryAtoms_measurePreserving 3

-- The reference raw log potential is L2 even for every fixed shift in dimension one.
example (z : ℂ) : MemLp (fun ω => matrixRawPotential (ginibreMatrix 1 ω - z • 1)) 2
    (cyclicAtomLaw 1 circularComplexGaussian) := ginibre_raw_memLp 1 z

-- The actual lower error, not a surrogate singular observable, obeys the negative-moment bound.
example (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) {a : ℝ} (ha : 0 < a) :
    |matrixCutoffPotential A a - matrixRawPotential A| ≤ (a ^ (1 : ℝ) / 1) * matrixNegativeMoment A 1 :=
  matrixLowerCutoff_le_negativeMoment A hA ha zero_lt_one

-- A zero triangular observable is tight on every finite Gaussian sample space.
example (N : ℕ → ℕ) [∀ n, NeZero (N n)] :
    BoundedInProbabilityTri (fun n => cyclicAtomLaw (N n) circularComplexGaussian) (fun _ _ => 0) := by
  intro δ hδ
  refine ⟨1, zero_lt_one, Eventually.of_forall fun n => ?_⟩
  simpa only [abs_zero, not_lt_of_ge (zero_le_one : (0 : ℝ) ≤ 1),
    Set.ofPred_false, measureReal_empty] using hδ

-- Complementary core/tail masses share the same fourth-root error bound.
example {v t : ℝ} (hv : 0 ≤ v) (ht : 0 < t) (hsum : v + t = 1) :
    (Real.sqrt t + |Real.sqrt v - 1|) / CircularLawSections56.Section6.fourthRoot t ≤
      2 * CircularLawSections56.Section6.fourthRoot t :=
  normalized_tail_error_le_two_fourthRoot hv ht hsum

-- The actual profile cutoff remains positive and at most one at every radius.
example (p : NoncompactProfile) (R : ℕ) : 0 < p.referenceCoreCutoff R ∧ p.referenceCoreCutoff R ≤ 1 :=
  ⟨p.referenceCoreCutoff_pos R, p.referenceCoreCutoff_le_one R⟩

-- The amplitude identification uses the actual positive sampled core weights.
example (p : NoncompactProfile) (W : ℝ) :
    0 < p.coreBandWeight 3 1 ⟨1, by decide⟩ W ⟨0, by decide⟩ :=
  p.coreBandWeight_pos 3 1 _ W _

-- The replacement matrix has the same actual raw log determinant, even on singular samples.
example (A : Matrix (ZMod 2) (ZMod 2) ℂ) (z : ℂ) :
    CircularLawSections56.Section6.physicalLogPotential (cyclicPhysicalMatrix 1 A) z =
      matrixRawPotential (A - z • 1) := cyclicPhysicalMatrix_logPotential 1 A z

-- Physical reindexing does not change the normalized energy.
example (A : Matrix (ZMod 2) (ZMod 2) ℂ) :
    CircularLawSections56.Section6.physicalEnergy (cyclicPhysicalMatrix 1 A) = cyclicEnergy 2 A :=
  cyclicPhysicalMatrix_energy 1 A

-- One block is already periodic: there is no boundary cost, even for large widths.
private instance : NeZero (∑ _ : Fin 1, (3 : ℕ)) := ⟨by decide⟩

example : fullBlockRoute (fun _ : Fin 1 => 3) 10 = periodicBlockRoute (fun _ : Fin 1 => 3) 10 :=
  oneBlock_routes_eq (fun _ => 3) 10

-- A short matrix is a single block; the allowed source window includes its full dimension.
example : ∃ (q : ℕ) (len : Fin q → ℕ), 0 < q ∧ (∑ j, len j) = 5 ∧
    (∀ j, 3 ≤ len j ∧ len j ≤ 200) ∧ (q = 1 ∨ ∀ j, 100 ≤ len j) := by
  exact exists_one_or_periodic_block_lengths (H := 1) (m₀ := 100) (by decide) (by decide)

-- The block scale is a fixed quadratic polynomial, independent of the global dimension.
example : quadraticBlockScale 2 = 25 := by decide

example (H : ℕ) : (H : ℝ) / quadraticBlockScale H ≤ 1 / ((H : ℝ) + 1) :=
  quadraticBlockScale_ratio_le H

-- Varying-dimension probability limits survive removing a finite prefix.
example : CircularLawSections56.Section5.TendstoInProbabilityTri (fun n => cyclicAtomLaw (n + 2) circularComplexGaussian)
    (fun _ _ => (0 : ℝ)) 0 ↔
    CircularLawSections56.Section5.TendstoInProbabilityTri (fun n => cyclicAtomLaw (n + 1) circularComplexGaussian)
      (fun _ _ => (0 : ℝ)) 0 := by
  simpa only [Nat.add_assoc] using tendstoInProbabilityTri_shift_iff
    (fun n => cyclicAtomLaw (n + 1) circularComplexGaussian) (fun _ _ => (0 : ℝ)) 0 1
