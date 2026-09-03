import BernoulliSection10Source.ConnectedHighBand

/-!
# Caller-facing real and planar density circular laws

Every Section 3 model, count, LSV event, rate and high-band anchor is
constructed by the imported proofs. The only literature parameters are
BBV and BC12, and, for real atoms only, geometric Brascamp--Lieb.
-/

open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace BernoulliSection10Source
open BernoulliSection10 Replacement DiskReference TaoVuReplacement
open LivshytsProjectionFormalization

theorem planar_density_circular_law
    (hBBV : BBVComparisonInput) (hBC12 : BC12GinibreInput)
    {μ : Measure ℂ} {L : ℝ} (hμ : BernoulliSection10Complex.IsPlanarDensityAtom μ L)
    (h3 : Integrable (fun x : ℂ => ‖x‖ ^ 3) μ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (f : BoundedContinuousFunction ℂ ℝ) :
    TendstoInMeasure (Measure.infinitePi fun _ : ℕ => μ)
      (fun n ω => realEsdTest
        (BernoulliSection10Complex.densityCyclicMatrix (W n) (s n)
          (BernoulliSection10Complex.physicalRowsFromSequence (W n) (s n) ω)) f)
      atTop (fun _ => ∫ z, f z ∂circularMeasure) :=
  BernoulliSection10Complex.density_circular_law_of_highBand hμ.normalized
    (planar_highBandLogLimit hBBV hBC12 hμ h3) W s hW hWtop f

theorem real_density_circular_law
    (hBBV : BBVComparisonInput) (hBC12 : BC12GinibreInput)
    (hGBL : RealFiniteGeometricBrascampLieb)
    {μ : Measure ℝ} {L : ℝ} (hμ : BernoulliSection10.IsBoundedDensityAtom μ L)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (f : BoundedContinuousFunction ℂ ℝ) :
    TendstoInMeasure (Measure.infinitePi fun _ : ℕ => μ)
      (fun n ω => realEsdTest
        (densityCyclicMatrix (W n) (s n) (physicalRowsFromSequence (W n) (s n) ω)) f)
      atTop (fun _ => ∫ z, f z ∂circularMeasure) :=
  BernoulliSection10.density_circular_law_of_highBand hμ
    (real_highBandLogLimit hBBV hBC12 hGBL hμ h3) W s hW hWtop f

theorem planar_density_ring_log_limit
    (hBBV : BBVComparisonInput) (hBC12 : BC12GinibreInput)
    {μ : Measure ℂ} {L : ℝ} (hμ : BernoulliSection10Complex.IsPlanarDensityAtom μ L)
    (h3 : Integrable (fun x : ℂ => ‖x‖ ^ 3) μ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop) (z : ℂ) :
    ProbabilityLimits.TendstoInProbabilityTri
      (fun n => BernoulliSection10Complex.intervalRowsLaw (W n) (s n + 3) μ)
      (fun n x => BernoulliSection10Complex.densityCyclicLogDet (W n) (s n) z x /
        (((s n + 3) * W n : ℕ) : ℝ)) (ShortRingAnchor.circularLogPotential z) :=
  BernoulliSection10Complex.density_ring_log_limit_of_highBand hμ.normalized
    (planar_highBandLogLimit hBBV hBC12 hμ h3) W s hW hWtop z

theorem real_density_ring_log_limit
    (hBBV : BBVComparisonInput) (hBC12 : BC12GinibreInput)
    (hGBL : RealFiniteGeometricBrascampLieb)
    {μ : Measure ℝ} {L : ℝ} (hμ : BernoulliSection10.IsBoundedDensityAtom μ L)
    (h3 : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop) (z : ℂ) :
    ProbabilityLimits.TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) μ)
      (fun n x => densityCyclicLogDet (W n) (s n) z x /
        (((s n + 3) * W n : ℕ) : ℝ)) (ShortRingAnchor.circularLogPotential z) :=
  BernoulliSection10.density_ring_log_limit_of_highBand hμ
    (real_highBandLogLimit hBBV hBC12 hGBL hμ h3) W s hW hWtop z

end BernoulliSection10Source
