import CircularLawSection6.BBVOnlyProfileEndpoint
import CircularLawSection6.GinibreBBVConsequences

/-! Regression signatures for the source-reduced concrete endpoint.
These examples retain BBV and Section 4 explicitly and provide no separate
Ginibre log, squared-test, or Han input. -/

open MeasureTheory Filter Topology ShortRingAnchor TaoVuReplacement
open CircularLawSections56.Section5
open CircularLawSections56.Section5.PublishedSection3Concrete
  (BBVComparisonInput BC12GinibreInput gaussianSequenceLaw ginibreOnSequence)
open CircularLawSection6 CircularLawSection6.NoncompactProfile

noncomputable section
set_option autoImplicit false
set_option warningAsError true

example (z : ℂ) :
    ∀ᵐ ω ∂gaussianSequenceLaw, (ginibreOnSequence 1 ω - z • 1).det ≠ 0 :=
  ginibreOnSequence_shifted_det_ne_zero 1 (by decide) z

example (hBBV : BBVComparisonInput) : GinibreLogPotentialInput :=
  ginibreLogPotential_of_bbv hBBV

example (hBBV : BBVComparisonInput) : BC12GinibreInput := bc12_of_bbv hBBV

example (hBBV : BBVComparisonInput) (z : ℂ) :
    ConvergesInProbability gaussianSequenceLaw
      (fun n ω => normalizedShiftLogDet (ginibreOnSequence (n + 1) ω) z)
      (circularLogPotential z) :=
  ginibreLogPotential_of_bbv hBBV (fun n => n + 1) (fun n => Nat.succ_pos n)
    (tendsto_add_atTop_nat 1) z

example (hBBV : BBVComparisonInput) (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (z : ℂ) :
    ∃ C : ℝ, ∀ n,
      (∫ ω, matrixRawPotential (ginibreMatrix (N n) ω - z • 1) ^ 2
        ∂cyclicAtomLaw (N n) circularComplexGaussian) ≤ C :=
  ginibre_raw_uniform_secondMoment_of_bbv hBBV N hN z

example (hBBV : BBVComparisonInput) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix n (ginibreMatrix (n + 1) (ω n).2)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) :=
  ginibre_spectral_of_bbv hBBV

example (p : NoncompactProfile) (W : ℕ → ℝ)
    (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hBBV : BBVComparisonInput)
    (h4 : ∀ R : ℕ,
      (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)).ConcreteSection4Input W) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix n (p.matrix (n + 1) (W n) (ω n).1)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) :=
  p.gaussian_profile_circular_law_of_bbv_sources W hW hWlim
    ⟨hBBV, h4⟩
