import CircularLawSection6.ClampedCoreProfile
import CircularLawSection6.GaussianAtomTransfer
import CircularLawSections56.Section5.CanonicalSection5Endpoint
import CircularLawSections56.Section5.QuantitativeSection4Inputs
import CircularLawSections56.Section6.Potentials

/-! # Direct application of the existing Section 5 theorem

The only remaining inputs here are the two finite quantitative Section 4
estimates and Section 3's short/calibration anchors. All band geometry,
weights, Gaussian atom estimates, constants and the Section 5 theorem call
are supplied internally. The band is globally defined before subsequences
are selected.
-/

open MeasureTheory Filter Topology ShortRingAnchor TaoVuReplacement
open CircularLawSection4
open CircularLawSections56.Section5 CircularLawSections56.Section6

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

def coreSection5Delta : ℝ := 1 / 32
def coreSection5Gamma : ℝ := 1 / 16

def clampedCoreBand (R : ℝ) (W : ℕ → ℝ) (n : ℕ) : ℕ :=
  canonicalCoreBand (clampedCoreHalfWidth R (W n) n)

def clampedCoreCenter (R : ℝ) (W : ℕ → ℝ) (n : ℕ) : Fin (clampedCoreBand R W n + 1) :=
  canonicalCoreCenter _ (clampedCoreHalfWidth_pos R (W n) n)

def clampedCoreSampleLaw (R : ℝ) (W : ℕ → ℝ) (n : ℕ) :
    Measure (Fin ((n + 1) * (clampedCoreBand R W n + 2)) → ℂ) :=
  iidMeasure circularComplexGaussian _

instance clampedCoreSampleLaw_isProbability (R : ℝ) (W : ℕ → ℝ) (n : ℕ) :
    IsProbabilityMeasure (clampedCoreSampleLaw R W n) :=
  iidMeasure_isProbability circularComplexGaussian _

namespace CoreRadiusBounds

variable {p : NoncompactProfile} {R : ℝ}

structure Section34Input (B : CoreRadiusBounds p R) (W : ℕ → ℝ) : Prop where
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
  anchors : ∀ᵐ z ∂(volume : Measure ℂ), Section3IndicatorAnchorsTri
    (clampedCoreSampleLaw R W)
    (literalShortLogPotential (clampedCoreBand R W) (clampedCoreCenter R W)
      (fun n => (B.clampedWeights (W n) n).b)
      (paperNaturalShortBranch (fun n => clampedCoreHalfWidth R (W n) n) coreSection5Gamma) z)
    (literalActiveNormalizedObservable
      (literalLongActive (paperSafeShortBranch (fun n => clampedCoreHalfWidth R (W n) n)
        coreSection5Delta coreSection5Gamma))
      (fun n => literalModelCalibrationRaw n (clampedCoreBand R W n)
        (paperBandCellLength (fun k => clampedCoreHalfWidth R (W k) k) coreSection5Delta n)
        (clampedCoreCenter R W n) (B.clampedWeights (W n) n).b z)
      (paperBandCellLength (fun n => clampedCoreHalfWidth R (W n) n) coreSection5Delta)
      (circularLogPotential z)) (circularLogPotential z)

theorem Section34Input.logPotential (B : CoreRadiusBounds p R) (W : ℕ → ℝ)
    (hR : 0 < R) (hW : Tendsto W atTop atTop) (hsource : B.Section34Input W) :
    ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri (clampedCoreSampleLaw R W)
      (fun n ω => physicalLogPotential (literalIndicatorMatrix n (clampedCoreBand R W n)
        (clampedCoreCenter R W n) (B.clampedWeights (W n) n).b ω) z)
      (circularRadialPotential ‖z‖) := by
  let H (n : ℕ) := clampedCoreHalfWidth R (W n) n
  have hc : 0 < B.lower / B.upper := div_pos B.lower_pos B.upper_pos
  have hdim (n : ℕ) : clampedCoreBand R W n + 1 = 2 * H n :=
    canonicalCoreCenter_symmetric (clampedCoreHalfWidth_pos R (W n) n)
  have hcenter (n : ℕ) : clampedCoreCenter R W n ≠ 0 := by
    intro h
    exact (Nat.ne_of_gt (clampedCoreHalfWidth_pos R (W n) n)) (congrArg Fin.val h)
  have hfit : ∀ᶠ n in atTop, clampedCoreBand R W n + 2 ≤ n + 1 := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact (canonicalCoreBand_width (clampedCoreHalfWidth_pos R (W n) n)).trans_le
      (clampedCoreHalfWidth_fits R (W n) hn)
  have hprofile (n : ℕ) : |Real.log (B.lower / B.upper)| ≤
      |Real.log (B.lower / B.upper)| * dimensionLogScale (clampedCoreBand R W n) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_dimensionLogScale _) (abs_nonneg (Real.log (B.lower / B.upper)))
  have hcal := hsource.calibration.mono (fun z hz =>
    hz.toCompleted (paperBandCellLength H coreSection5Delta) H |Real.log (B.lower / B.upper)|
      (abs_nonneg _) (fun n _ => clampedCoreHalfWidth_pos R (W n) n)
      (fun n _ => hdim n) (fun n _ => Nat.sub_le _ _) (fun _ _ => hc) (fun n _ => hprofile n))
  have hfinal := hsource.finalPressure.mono (fun z hz =>
    hz.toCompleted (fun n => n + 1) H |Real.log (B.lower / B.upper)|
      (abs_nonneg _) (fun n _ => clampedCoreHalfWidth_pos R (W n) n)
      (fun n _ => hdim n) (fun n _ => Nat.sub_le _ _) (fun _ _ => hc) (fun n _ => hprofile n))
  have hatom := circularComplexGaussian_atomTransferControl
  have h := literal_canonical_profile_endpoint_of_section34
    (clampedCoreBand R W) H (clampedCoreCenter R W) (fun n => B.clampedWeights (W n) n)
    |Real.log (B.lower / B.upper)| (uniformFreshNegativeConstant 2)
    ((Real.log (max 1 (Real.pi * 2)) + 1) / 2)
    (complexLogarithmicSection4Constant |Real.log (B.lower / B.upper)| 2)
    (fun _ => circularComplexGaussian) coreSection5Delta coreSection5Gamma
    (fun _ => hc) (abs_nonneg _) hatom.fresh_constant_nonneg hatom.atom_constant_nonneg
    (by norm_num [coreSection5Delta])
    (by norm_num [coreSection5Delta, coreSection5Gamma])
    (by norm_num [coreSection5Gamma])
    (clampedCoreHalfWidth_atTop W hW hR) hfit hdim hcenter hprofile
    (fun _ => hatom) hcal hfinal hsource.anchors
  exact h.1

end CoreRadiusBounds
end CircularLawSection6
