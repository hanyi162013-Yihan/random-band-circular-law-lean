import CircularLawSection6.ClampedSection5Source
import CircularLawSection6.PublishedGaussianDensity
import CircularLawSections56.Section5.PublishedSection3ConcreteAnchors

/-! # Clamped-core anchors from actual matrices and uniform literature inputs

Only the two finite Section 4 pressure estimates are retained in the core
source record. Section 3's short-ring and calibration-prefix anchors are
constructed by the concrete Section 5 theorem for the existing Gaussian
law and the already constructed clamped core weights. No sampling, model,
or anchor convergence certificate is an input.
-/

open MeasureTheory Filter Topology ShortRingAnchor TaoVuReplacement
open CircularLawSection4
open CircularLawSections56.Section5 CircularLawSections56.Section6
open CircularLawSections56.Section5.PublishedSection3Concrete
  (BBVComparisonInput BC12GinibreInput DensityInput literal_anchors)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.CoreRadiusBounds

variable {p : NoncompactProfile} {R : ℝ}

structure ConcreteSection4Input (B : CoreRadiusBounds p R) (W : ℕ → ℝ) : Prop where
  calibration : ∀ᵐ z ∂(volume : Measure ℂ), ComplexQuantitativeSection4PressureInput
    (clampedCoreSampleLaw R W)
    (literalLongActive (paperSafeShortBranch (fun n => clampedCoreHalfWidth R (W n) n)
      coreSection5Delta coreSection5Gamma))
    (clampedCoreBand R W)
    (fun n => paperBandCellLength (fun k => clampedCoreHalfWidth R (W k) k) coreSection5Delta n -
      (clampedCoreBand R W n + 1))
    (fun n => literalModelCalibrationRaw n (clampedCoreBand R W n)
      (paperBandCellLength (fun k => clampedCoreHalfWidth R (W k) k) coreSection5Delta n)
      (clampedCoreCenter R W n) (B.clampedWeights (W n) n).b z)
    (fun n => literalModelPressure n (clampedCoreBand R W n)
      (paperBandCellLength (fun k => clampedCoreHalfWidth R (W k) k) coreSection5Delta n)
      (B.clampedWeights (W n) n) (clampedCoreCenter R W n) z)
    (fun _ => B.lower / B.upper) 2 z
  finalPressure : ∀ᵐ z ∂(volume : Measure ℂ), ComplexQuantitativeSection4PressureInput
    (clampedCoreSampleLaw R W)
    (literalLongActive (paperSafeShortBranch (fun n => clampedCoreHalfWidth R (W n) n)
      coreSection5Delta coreSection5Gamma))
    (clampedCoreBand R W) (fun n => n + 1 - (clampedCoreBand R W n + 1))
    (fun n => literalModelRawDeterminant n (clampedCoreBand R W n)
      (clampedCoreCenter R W n) (B.clampedWeights (W n) n).b z)
    (fun n => literalModelPressure n (clampedCoreBand R W n) (n + 1)
      (B.clampedWeights (W n) n) (clampedCoreCenter R W n) z)
    (fun _ => B.lower / B.upper) 2 z

theorem ConcreteSection4Input.toSection34 (B : CoreRadiusBounds p R)
    (W : ℕ → ℝ) (hR : 0 < R) (hWlim : Tendsto W atTop atTop)
    (hBBV : BBVComparisonInput) (hBC12 : BC12GinibreInput)
    (h : B.ConcreteSection4Input W) : B.Section34Input W where
  calibration := h.calibration
  finalPressure := h.finalPressure
  anchors := by
    have hwidth (n : ℕ) : clampedCoreBand R W n + 2 =
        2 * clampedCoreHalfWidth R (W n) n + 1 :=
      canonicalCoreBand_width (clampedCoreHalfWidth_pos R (W n) n)
    have hcenter (n : ℕ) : (clampedCoreCenter R W n).val =
        clampedCoreHalfWidth R (W n) n := rfl
    have hfit : ∀ᶠ n in atTop, clampedCoreBand R W n + 2 ≤ n + 1 := by
      filter_upwards [eventually_ge_atTop 2] with n hn
      exact (hwidth n).trans_le (clampedCoreHalfWidth_fits R (W n) hn)
    have hDensity : DensityInput circularComplexGaussian :=
      Or.inl ⟨circularComplexGaussian_publishedDensity⟩
    apply Filter.Eventually.of_forall
    intro z
    exact literal_anchors hBBV hBC12 circularComplexGaussian
      circularComplexGaussian_publishedMoments hDensity
      (clampedCoreBand R W) (fun n => clampedCoreHalfWidth R (W n) n)
      (clampedCoreCenter R W) (fun n => B.clampedWeights (W n) n)
      (div_pos B.lower_pos B.upper_pos) hwidth hcenter
      coreSection5Delta coreSection5Gamma
      (by norm_num [coreSection5Delta])
      (by norm_num [coreSection5Delta, coreSection5Gamma])
      (by norm_num [coreSection5Gamma])
      (clampedCoreHalfWidth_atTop W hWlim hR) hfit z

theorem ConcreteSection4Input.logPotential (B : CoreRadiusBounds p R)
    (W : ℕ → ℝ) (hR : 0 < R) (hWlim : Tendsto W atTop atTop)
    (hBBV : BBVComparisonInput) (hBC12 : BC12GinibreInput)
    (h : B.ConcreteSection4Input W) :
    ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri (clampedCoreSampleLaw R W)
      (fun n ω => physicalLogPotential (literalIndicatorMatrix n (clampedCoreBand R W n)
        (clampedCoreCenter R W n) (B.clampedWeights (W n) n).b ω) z)
      (circularRadialPotential ‖z‖) :=
  Section34Input.logPotential B W hR hWlim
    (ConcreteSection4Input.toSection34 B W hR hWlim hBBV hBC12 h)

end CircularLawSection6.CoreRadiusBounds
