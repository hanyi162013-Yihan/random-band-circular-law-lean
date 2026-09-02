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

-- A one-dimensional matrix has one active diagonal even at zero truncation radius.
example : coreOffsets 1 0 = Finset.univ := by
  ext s
  have : s = 0 := Subsingleton.elim _ _
  simp [this]

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
