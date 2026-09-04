import CircularLawSection6.BBVOnlyProfileEndpoint
import CircularLawSections56.Section5.VerifiedComplexSection5Endpoint

/-! # Constructing the Gaussian compact-core pressure inputs

The density, second moment, normalized weights and exact calibration geometry
are already proved for the actual clamped Gaussian cores. The Section 4 finite
seam and pressure estimates can therefore be assembled without any external
pressure premise. The final profile theorem below retains only uniform BBV.
-/

open MeasureTheory Filter Topology TaoVuReplacement ShortRingAnchor
open CircularLawSection4
open CircularLawSections56.Section5 CircularLawSections56.Section6
open CircularLawSections56.Section5.PublishedSection3Concrete (BBVComparisonInput)

noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace CircularLawSection6
namespace CoreRadiusBounds

/-- The constructed complex-density Section 5 theorem at one prescribed
spectral parameter.  This is the pointwise counterpart of the historical
`Section34Input.logPotential` route; it uses the same BBV literature input but
does not pass through an almost-everywhere wrapper. -/
theorem verifiedClampedLogPotential_at {p : NoncompactProfile} {R : ℝ}
    (B : CoreRadiusBounds p R) (W : ℕ → ℝ) (hR : 0 < R)
    (hWlim : Tendsto W atTop atTop) (hBBV : BBVComparisonInput) (z : ℂ) :
    TendstoInProbabilityTri (clampedCoreSampleLaw R W)
      (fun n ω => physicalLogPotential (literalIndicatorMatrix n (clampedCoreBand R W n)
        (clampedCoreCenter R W n) (B.clampedWeights (W n) n).b ω) z)
      (circularRadialPotential ‖z‖) := by
  let H := fun n => clampedCoreHalfWidth R (W n) n
  have hfit : ∀ᶠ n in atTop, clampedCoreBand R W n + 2 ≤ n + 1 := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact (canonicalCoreBand_width (clampedCoreHalfWidth_pos R (W n) n)).trans_le
      (clampedCoreHalfWidth_fits R (W n) hn)
  have hwidth (n : ℕ) : clampedCoreBand R W n + 2 = 2 * H n + 1 := by
    simpa only [clampedCoreBand, H] using
      canonicalCoreBand_width (clampedCoreHalfWidth_pos R (W n) n)
  have hcenter (n : ℕ) : (clampedCoreCenter R W n).val = H n := rfl
  have hMom : AtomMomentAssumption21
      (volume.withDensity circularGaussianDensity) id := by
    rw [circularGaussianDensity_withDensity]
    exact PublishedSection3Concrete.gaussianMoments
  have h := PublishedSection3Concrete.indicator_complex_logPotential_at_of_bbv hBBV
    (clampedCoreBand R W) H (clampedCoreCenter R W)
    (fun n => B.clampedWeights (W n) n) circularGaussianDensity
    coreSection5Delta coreSection5Gamma (div_pos B.lower_pos B.upper_pos)
    (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num [coreSection5Delta])
    (by norm_num [coreSection5Delta, coreSection5Gamma])
    (by norm_num [coreSection5Gamma])
    (clampedCoreHalfWidth_atTop W hWlim hR) hfit hwidth hcenter
    (by simpa only [ENNReal.ofReal_ofNat] using circularGaussianDensity_le_two)
    hMom z
  intro ε hε
  apply (h ε hε).congr'
  exact Eventually.of_forall fun n => by
    simp only [clampedCoreSampleLaw]
    rw [circularGaussianDensity_withDensity]
    apply measureReal_congr
    exact Eventually.of_forall fun _ => by
      simp only [circularLogPotential, circularRadialPotential]

/-- Section 6 compact-core application of the proved Section 4 density estimates.
Both the calibration and full-size pressure contracts are constructed here. -/
theorem verifiedConcreteSection4Input {p : NoncompactProfile} {R : ℝ}
    (B : CoreRadiusBounds p R) (W : ℕ → ℝ) : B.ConcreteSection4Input W := by
  let H := fun n => clampedCoreHalfWidth R (W n) n
  let active := literalLongActive (paperSafeShortBranch H coreSection5Delta coreSection5Gamma)
  have hdim (n : ℕ) : clampedCoreBand R W n + 1 = 2 * H n :=
    canonicalCoreCenter_symmetric (clampedCoreHalfWidth_pos R (W n) n)
  have hcenter (n : ℕ) : clampedCoreCenter R W n ≠ 0 := by
    intro h
    exact (Nat.ne_of_gt (clampedCoreHalfWidth_pos R (W n) n)) (congrArg Fin.val h)
  have hgeom (n : ℕ) (hn : active n = true) :=
    paperTransferReady_geometry H coreSection5Delta n
      (paperSafeShortBranch_active H coreSection5Delta coreSection5Gamma n hn).2
  have hc : 0 < B.lower / B.upper := div_pos B.lower_pos B.upper_pos
  have hsqrt (n : ℕ) :
      Real.sqrt ((B.lower / B.upper) / (clampedCoreBand R W n + 2 : ℝ)) ≤ 1 :=
    normalized_profile_lower_scale_le_one _ (B.clampedWeights (W n) n) hc
  have hf : ∀ᵐ u ∂(volume : Measure ℂ),
      circularGaussianDensity u ≤ ENNReal.ofReal (2 : ℝ) := by
    simpa only [ENNReal.ofReal_ofNat] using circularGaussianDensity_le_two
  have hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2)
      (volume.withDensity circularGaussianDensity) := by
    rw [circularGaussianDensity_withDensity]
    exact circularComplexGaussian_sq_integrable
  have hSecond : (∫ u : ℂ, ‖u‖ ^ 2 ∂volume.withDensity circularGaussianDensity) ≤ 1 := by
    rw [circularGaussianDensity_withDensity]
    exact circularComplexGaussian_secondMoment.le
  constructor
  · apply ae_of_all
    intro z
    unfold clampedCoreSampleLaw
    have h := complex_literalModelCalibration_quantitative active
      (clampedCoreBand R W) (paperBandCellLength H coreSection5Delta)
      (fun n => B.clampedWeights (W n) n) (clampedCoreCenter R W) z
      (fun _ => circularGaussianDensity)
      (fun n hn => (hgeom n hn).2.2.2.2.2)
      (fun n hn => by rw [hdim n]; exact (hgeom n hn).2.2.2.2.1)
      (fun _ _ => hc) (fun n _ => hsqrt n) (fun n _ => hcenter n)
      (by norm_num) (fun _ _ => hf) (fun _ _ => hInt) (fun _ _ => hSecond)
    simp only [active, H, circularGaussianDensity_withDensity] at h
    convert h using 1
    rfl
  · apply ae_of_all
    intro z
    unfold clampedCoreSampleLaw
    have h := complex_literalModelFinal_quantitative active (clampedCoreBand R W)
      (fun n => B.clampedWeights (W n) n) (clampedCoreCenter R W) z
      (fun _ => circularGaussianDensity)
      (fun n hn => by rw [hdim n]; exact (Nat.le_succ _).trans (hgeom n hn).2.1)
      (fun _ _ => hc) (fun n _ => hsqrt n) (fun n _ => hcenter n)
      (by norm_num) (fun _ _ => hf) (fun _ _ => hInt) (fun _ _ => hSecond)
    simp only [active, H, circularGaussianDensity_withDensity] at h
    convert h using 1
    rfl

end CoreRadiusBounds
namespace NoncompactProfile

/-- Section 6 profile circular law for the actual Gaussian matrices, with no
external Gaussian limit or Section 4 pressure estimate. Uniform BBV remains
explicit, along with the profile and bandwidth assumptions. -/
theorem gaussian_profile_circular_law_of_bbv (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hBBV : BBVComparisonInput) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix n (p.matrix (n + 1) (W n) (ω n).1)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) :=
  p.gaussian_profile_circular_law_of_bbv_sources W hW hWlim
    ⟨hBBV, fun R => CoreRadiusBounds.verifiedConcreteSection4Input
      (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)) W⟩

end NoncompactProfile
end CircularLawSection6
