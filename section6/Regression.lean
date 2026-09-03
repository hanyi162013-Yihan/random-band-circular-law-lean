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
 …2953 tokens truncated…ePreserving (fullBlockPaperSample (fun _ : Fin 2 => 5) 1 1 (by decide))
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
