import CircularLawSection6.TriangularTightness
import CircularLawSection6.TightVarianceMoments
import CircularLawSection6.GinibreNegativeSources
import CircularLawSection6.IteratedLowerCutoff

/-! # Ginibre logarithmic second moments before the raw-potential limit

An energy bound controls the positive logarithmic part.  Tightness of one
negative singular moment controls the lower correction, so the actual raw
logarithmic potential is tight.  Gaussian concentration and vanishing
variance then give uniformly bounded second moments without a limit for
the deterministic logarithmic center.

For actual Ginibre matrices the negative-moment tightness used here comes
from BBV alone.  The final diagonal and iterated lower-cutoff `L1` statements
therefore do not assume a BC12 raw-log limit, a limiting singular law, or an
eigenvalue correlation formula.  Parameter nonvanishing is needed only for
Lebesgue-almost every spectral shift and is proved by the existing matrix
parameter theorem.
-/

open MeasureTheory ProbabilityTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5
open CircularLawSections56.Section5.PublishedSection3Concrete (BBVComparisonInput)

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

/-- A deterministic logarithmic envelope.  The upper logarithmic part
is controlled by energy, and the lower correction by any positive
negative-moment exponent. -/
theorem abs_matrixRawPotential_le_energy_negativeMoment
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (hA : A.det ≠ 0) {p : ℝ} (hp : 0 < p) :
    |matrixRawPotential A| ≤
      (1 + hilbertSchmidtSq A / (Fintype.card ι : ℝ)) +
        (1 / p) * matrixNegativeMoment A p := by
  have hsq := matrixCutoffPotential_one_sq_le_energy A hA
  have hcut : matrixCutoffPotential A 1 ≤
      1 + hilbertSchmidtSq A / (Fintype.card ι : ℝ) := by
    nlinarith [sq_nonneg (matrixCutoffPotential A 1 - (1 / 2 : ℝ))]
  have hcorr : |matrixCutoffPotential A 1 - matrixRawPotential A| ≤
      (1 / p) * matrixNegativeMoment A p := by
    simpa only [Real.one_rpow] using
      matrixLowerCutoff_le_negativeMoment A hA zero_lt_one hp
  calc
    |matrixRawPotential A| =
        |matrixCutoffPotential A 1 -
          (matrixCutoffPotential A 1 - matrixRawPotential A)| := by
      congr 1
      ring
    _ ≤ |matrixCutoffPotential A 1| +
        |matrixCutoffPotential A 1 - matrixRawPotential A| := abs_sub _ _
    _ = matrixCutoffPotential A 1 +
        |matrixCutoffPotential A 1 - matrixRawPotential A| := by
      rw [abs_of_nonneg (matrixCutoffPotential_one_nonneg A)]
    _ ≤ _ := add_le_add hcut hcorr

/-- Energy bounded in expectation and a tight negative singular moment
make the raw logarithmic potentials tight on varying sample spaces.
There is no convergence premise for the raw potentials or their means. -/
theorem matrixRawPotential_boundedInProbabilityTri_of_energy_negativeMoment
    {Ω ι : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Nonempty (ι n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, Ω n → Matrix (ι n) (ι n) ℂ)
    (hdet : ∀ n, ∀ᵐ ω ∂μ n, (A n ω).det ≠ 0)
    (hE : ∀ n, Integrable (fun ω => hilbertSchmidtSq (A n ω)) (μ n))
    (CE : ℝ)
    (hEb : ∀ n, (∫ ω, hilbertSchmidtSq (A n ω) ∂μ n) /
      (Fintype.card (ι n) : ℝ) ≤ CE)
    {p : ℝ} (hp : 0 < p)
    (hnegative : BoundedInProbabilityTri μ
      (fun n ω => matrixNegativeMoment (A n ω) p)) :
    BoundedInProbabilityTri μ (fun n ω => matrixRawPotential (A n ω)) := by
  let Y : ∀ n, Ω n → ℝ := fun n ω =>
    1 + hilbertSchmidtSq (A n ω) / (Fintype.card (ι n) : ℝ)
  have hYnonneg (n : ℕ) (ω : Ω n) : 0 ≤ Y n ω :=
    add_nonneg zero_le_one
      (div_nonneg (hilbertSchmidtSq_nonneg (A n ω)) (Nat.cast_nonneg _))
  have hYint (n : ℕ) : Integrable (Y n) (μ n) :=
    (integrable_const 1).add ((hE n).div_const _)
  have hYmean (n : ℕ) : (∫ ω, |Y n ω| ∂μ n) ≤ 1 + CE := by
    calc
      (∫ ω, |Y n ω| ∂μ n) = ∫ ω, Y n ω ∂μ n :=
        integral_congr_ae (ae_of_all _ fun ω => abs_of_nonneg (hYnonneg n ω))
      _ = 1 + (∫ ω, hilbertSchmidtSq (A n ω) ∂μ n) /
          (Fintype.card (ι n) : ℝ) := by
        dsimp only [Y]
        rw [integral_add (integrable_const 1) ((hE n).div_const _), integral_div]
        simp
      _ ≤ 1 + CE := add_le_add le_rfl (hEb n)
  have hYtight : BoundedInProbabilityTri μ Y :=
    boundedInProbabilityTri_of_integral_abs_bound μ Y
      (fun n => (hYint n).abs) (1 + CE) hYmean
  have hsum := BoundedInProbabilityTri.add μ hYtight (hnegative.const_mul (1 / p))
  apply hsum.of_ae_abs_le
  intro n
  filter_upwards [hdet n] with ω hω
  exact (abs_matrixRawPotential_le_energy_negativeMoment (A n ω) hω hp).trans
    (le_abs_self _)

/-- Parameter nonvanishing for all sizes simultaneously.  This uses no
random-matrix comparison and no logarithmic limit. -/
theorem ginibre_shifted_det_ne_zero_ae (N : ℕ → ℕ) [∀ n, NeZero (N n)] :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ n,
      ∀ᵐ ω ∂cyclicAtomLaw (N n) circularComplexGaussian,
        (ginibreMatrix (N n) ω - z • 1).det ≠ 0 :=
  ae_all_iff.2 fun n => ae_shifted_matrix_det_ne_zero
    (cyclicAtomLaw (N n) circularComplexGaussian)
    (ginibreMatrix (N n)) (ginibreMatrix_measurable (N n))

/-- The actual Ginibre potential concentrates around its own mean;
the mean is not identified or assumed to converge. -/
theorem ginibre_raw_centered_tendsto (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (z : ℂ) :
    TendstoInProbabilityTri (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
      (fun n ω => matrixRawPotential (ginibreMatrix (N n) ω - z • 1) -
        ∫ x, matrixRawPotential (ginibreMatrix (N n) x - z • 1)
          ∂cyclicAtomLaw (N n) circularComplexGaussian) 0 := by
  simpa only [matrixRawPotential, ginibreMatrix, ZMod.card, cyclicRawLogDet,
    Complex.ofReal_one, one_smul] using
    (gaussian_cyclic_concentration_all N hN (fun n _ => 1 / (N n : ℝ))
      (c := 1) (r := 1) zero_lt_one zero_lt_one z (fun _ => le_rfl)).2

/-- BBV alone supplies the negative-moment input needed for tightness
of the actual raw Ginibre logarithmic potentials. -/
theorem ginibre_raw_tight_of_bbv_ae (hBBV : BBVComparisonInput)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      BoundedInProbabilityTri (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
        (fun n ω => matrixRawPotential (ginibreMatrix (N n) ω - z • 1)) := by
  filter_upwards [ginibre_shifted_det_ne_zero_ae N] with z hz
  exact matrixRawPotential_boundedInProbabilityTri_of_energy_negativeMoment
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
    (fun n ω => ginibreMatrix (N n) ω - z • 1) hz
    (fun n => (ginibre_shifted_expected_energy (N n) z).1) (2 + 2 * ‖z‖ ^ 2)
    (fun n => by simpa only [ZMod.card] using (ginibre_shifted_expected_energy (N n) z).2)
    (by norm_num : (0 : ℝ) < 1 / 128) (ginibre_negative_of_bbv hBBV N hN z)

/-- Uniform second moments of the actual Ginibre raw logarithmic
potentials, obtained before any raw logarithmic-potential limit. -/
theorem ginibre_raw_uniform_secondMoment_of_bbv_ae (hBBV : BBVComparisonInput)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∃ C : ℝ, ∀ n,
      (∫ ω, matrixRawPotential (ginibreMatrix (N n) ω - z • 1) ^ 2
        ∂cyclicAtomLaw (N n) circularComplexGaussian) ≤ C := by
  filter_upwards [ginibre_raw_tight_of_bbv_ae hBBV N hN] with z hz
  exact exists_uniform_secondMoment_of_tight_and_centered
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
    (fun n ω => matrixRawPotential (ginibreMatrix (N n) ω - z • 1))
    (fun n => ginibre_raw_memLp (N n) z) hz
    (ginibre_raw_centered_tendsto N hN z) (ginibre_raw_variance_tendsto N hN z)

/-- Diagonal lower-cutoff removal in `L1`, using BBV but no raw-log
probability limit. -/
theorem ginibreLowerCutoff_L1_of_bbv_ae (hBBV : BBVComparisonInput)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      ∀ a : ℕ → ℝ, (∀ n, 0 < a n) → (∀ n, a n ≤ 1) → Tendsto a atTop (𝓝 0) →
        Tendsto (fun n => ∫ ω,
          |matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) (a n) -
            matrixRawPotential (ginibreMatrix (N n) ω - z • 1)|
          ∂cyclicAtomLaw (N n) circularComplexGaussian) atTop (𝓝 0) := by
  filter_upwards [ginibre_raw_uniform_secondMoment_of_bbv_ae hBBV N hN,
    ginibre_shifted_det_ne_zero_ae N] with z hmoment hdet
  obtain ⟨C, hC⟩ := hmoment
  intro a ha ha1 ha0
  exact matrixLowerCutoff_L1_of_negativeMoment
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
    (fun n ω => ginibreMatrix (N n) ω - z • 1)
    (fun n => (ginibreMatrix_measurable (N n)).sub measurable_const) hdet
    (fun n => (ginibre_shifted_expected_energy (N n) z).1)
    (fun n => ginibre_raw_memLp (N n) z) (2 + 2 * ‖z‖ ^ 2) C
    (fun n => by simpa only [ZMod.card] using (ginibre_shifted_expected_energy (N n) z).2)
    hC (by norm_num : (0 : ℝ) < 1 / 128) (ginibre_negative_of_bbv hBBV N hN z)
    a ha ha1 ha0

/-- Size-before-cutoff `L1` removal.  This is an iterated eventual bound,
not an exchange of limits, and it needs no raw-log limit as input. -/
theorem ginibre_iterated_lowerCutoff_L1_of_bbv_ae (hBBV : BBVComparisonInput)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      ∀ a : ℕ → ℝ, (∀ R, 0 < a R) → (∀ R, a R ≤ 1) → Tendsto a atTop (𝓝 0) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ R in atTop, ∀ᶠ n in atTop,
          (∫ ω, |matrixCutoffPotential (ginibreMatrix (N n) ω - z • 1) (a R) -
            matrixRawPotential (ginibreMatrix (N n) ω - z • 1)|
            ∂cyclicAtomLaw (N n) circularComplexGaussian) < ε := by
  filter_upwards [ginibre_raw_uniform_secondMoment_of_bbv_ae hBBV N hN,
    ginibre_shifted_det_ne_zero_ae N] with z hmoment hdet
  obtain ⟨C, hC⟩ := hmoment
  intro a ha ha1 ha0
  exact matrixLowerCutoff_iterated_L1_of_negativeMoment
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
    (fun n ω => ginibreMatrix (N n) ω - z • 1)
    (fun n => (ginibreMatrix_measurable (N n)).sub measurable_const) hdet
    (fun n => (ginibre_shifted_expected_energy (N n) z).1)
    (fun n => ginibre_raw_memLp (N n) z) (2 + 2 * ‖z‖ ^ 2) C
    (fun n => by simpa only [ZMod.card] using (ginibre_shifted_expected_energy (N n) z).2)
    hC (by norm_num : (0 : ℝ) < 1 / 128) (ginibre_negative_of_bbv hBBV N hN z)
    a ha ha1 ha0

end CircularLawSection6
