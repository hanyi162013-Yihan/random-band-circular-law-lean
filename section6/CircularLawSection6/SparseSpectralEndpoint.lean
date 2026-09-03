import CircularLawSection6.SparseProfileSourceEndpoint
import CircularLawSection6.ProbabilityFinitePrefix
import CircularLawSection6.ProfileReplacement

/-! # Sparse noncompact profiles: spectral replacement from source inputs

All model transports and finite prefixes are proved. The source bundle
names the local Section 3 comparison, literal Section 5 endpoint, and the
two classical Ginibre probability inputs. It contains no assumption about
the full profile's log potential or spectral distribution.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5 CircularLawSections56.Section6

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

structure SparseGaussianSourceInputs (p : NoncompactProfile) (W : ℕ → ℝ) : Prop where
  coreSection5 : ∀ R : ℕ, p.CanonicalCoreSection5Input (fun n => n) (fun n => W (n + 1)) (R + 1)
  coreSection3 : ∀ R : ℕ, p.CanonicalCoreSection3Input (fun n => n + 2) (fun n => W (n + 1)) (R + 1)
  ginibreRaw : ∀ᵐ z ∂(volume : Measure ℂ),
    TendstoInProbabilityTri (fun n => cyclicAtomLaw (n + 1) circularComplexGaussian)
      (fun n ω => matrixRawPotential (ginibreMatrix (n + 1) ω - z • 1)) (circularRadialPotential ‖z‖)
  ginibreNegative : ∀ᵐ z ∂(volume : Measure ℂ), ∃ q : ℝ, 0 < q ∧
    BC12GinibreNegativeMomentTightnessTri (fun n => n + 1) z q

theorem sparse_profile_probability_of_sources (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (n + 1 : ℕ)) atTop (𝓝 0))
    (hsource : p.SparseGaussianSourceInputs W) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbabilityTri (fun n => gaussianProfileLaw (n + 1))
        (fun n ω => matrixRawPotential (p.matrix (n + 1) (W n) ω - z • 1))
        (circularRadialPotential ‖z‖) := by
  have hGin : ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbabilityTri (fun n => cyclicAtomLaw (n + 2) circularComplexGaussian)
        (fun n ω => matrixRawPotential (ginibreMatrix (n + 2) ω - z • 1)) (circularRadialPotential ‖z‖) := by
    filter_upwards [hsource.ginibreRaw] with z hz
    simpa only [Nat.add_assoc] using (tendstoInProbabilityTri_shift_iff
      (fun n => cyclicAtomLaw (n + 1) circularComplexGaussian)
      (fun n ω => matrixRawPotential (ginibreMatrix (n + 1) ω - z • 1))
      (circularRadialPotential ‖z‖) 1).mpr hz
  have hNeg : ∀ᵐ z ∂(volume : Measure ℂ), ∃ q : ℝ, 0 < q ∧
      BC12GinibreNegativeMomentTightnessTri (fun n => n + 2) z q := by
    filter_upwards [hsource.ginibreNegative] with z hz
    obtain ⟨q, hq, hn⟩ := hz
    refine ⟨q, hq, ?_⟩
    simpa only [BC12GinibreNegativeMomentTightnessTri, Nat.add_assoc] using
      boundedInProbabilityTri_shift (fun n => cyclicAtomLaw (n + 1) circularComplexGaussian)
        (fun n ω => matrixNegativeMoment (ginibreMatrix (n + 1) ω - z • 1) q) hn 1
  have hs : Tendsto (fun n => W (n + 1) / (n + 2 : ℕ)) atTop (𝓝 0) := by
    simpa only [Nat.add_assoc] using hsparse.comp (tendsto_add_atTop_nat 1)
  have htail := p.sparse_profile_probability_of_section3_section5 (fun n => n)
    (tendsto_add_atTop_nat 2) (fun n => W (n + 1)) (fun n => hW (n + 1))
    (hWlim.comp (tendsto_add_atTop_nat 1)) hs hsource.coreSection5 hsource.coreSection3 hGin hNeg
  filter_upwards [htail] with z hz
  apply (tendstoInProbabilityTri_shift_iff (fun n => gaussianProfileLaw (n + 1))
    (fun n ω => matrixRawPotential (p.matrix (n + 1) (W n) ω - z • 1))
    (circularRadialPotential ‖z‖) 1).mp
  simpa only [Nat.add_assoc] using hz

theorem sparse_profile_ginibre_spectral_replacement (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsparse : Tendsto (fun n => W n / (n + 1 : ℕ)) atTop (𝓝 0))
    (hsource : p.SparseGaussianSourceInputs W) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun k ω => esdDifference (cyclicPhysicalMatrix k (p.matrix (k + 1) (W k) (ω k).1))
          (cyclicPhysicalMatrix k (ginibreMatrix (k + 1) (ω k).2)) f) atTop 0 :=
  p.profile_ginibre_replacement_of_log_limits W (fun z => circularRadialPotential ‖z‖)
    (p.sparse_profile_probability_of_sources W hW hWlim hsparse hsource) hsource.ginibreRaw

end CircularLawSection6.NoncompactProfile
