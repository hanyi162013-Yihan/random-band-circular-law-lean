import CircularLawSection6.SparseProfileSourceEndpoint
import CircularLawSection6.SubsequenceProfileReplacement
import CircularLawSections56.Section5.DiskReferenceLaw

/-! # Source-level sparse theorem on any increasing dimension sequence -/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5 CircularLawSections56.Section6

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

def subsequenceCoreSize (φ : ℕ → ℕ) (n : ℕ) : ℕ := φ (n + 1) - 1

theorem subsequenceCoreSize_dimension (φ : ℕ → ℕ) (hφ : StrictMono φ) (n : ℕ) :
    subsequenceCoreSize φ n + 2 = φ (n + 1) + 1 := by
  have h : n + 1 ≤ φ (n + 1) := hφ.id_le (n + 1)
  change φ (n + 1) - 1 + 2 = φ (n + 1) + 1
  omega

namespace NoncompactProfile

private theorem ginibre_raw_bad_dimension {N M : ℕ} [NeZero N] [NeZero M]
    (hNM : N = M) (z : ℂ) (a ε : ℝ) :
    (cyclicAtomLaw N circularComplexGaussian).real
        {ω | ε ≤ |matrixRawPotential (ginibreMatrix N ω - z • 1) - a|} =
      (cyclicAtomLaw M circularComplexGaussian).real
        {ω | ε ≤ |matrixRawPotential (ginibreMatrix M ω - z • 1) - a|} := by
  subst M
  rfl

private theorem ginibre_negative_bad_dimension {N M : ℕ} [NeZero N] [NeZero M]
    (hNM : N = M) (z : ℂ) (q C : ℝ) :
    (cyclicAtomLaw N circularComplexGaussian).real
        {ω | C < |matrixNegativeMoment (ginibreMatrix N ω - z • 1) q|} =
      (cyclicAtomLaw M circularComplexGaussian).real
        {ω | C < |matrixNegativeMoment (ginibreMatrix M ω - z • 1) q|} := by
  subst M
  rfl

private theorem profile_raw_bad_dimension (p : NoncompactProfile)
    {N M : ℕ} [NeZero N] [NeZero M] (hNM : N = M) (W : ℝ) (z : ℂ) (a ε : ℝ) :
    (gaussianProfileLaw N).real
        {ω | ε ≤ |matrixRawPotential (p.matrix N W ω - z • 1) - a|} =
      (gaussianProfileLaw M).real
        {ω | ε ≤ |matrixRawPotential (p.matrix M W ω - z • 1) - a|} := by
  subst M
  rfl

structure GaussianProfileSourceInputs (p : NoncompactProfile) (W : ℕ → ℝ) : Prop where
  coreSection5 : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ R : ℕ,
    p.CanonicalCoreSection5Input (subsequenceCoreSize φ) (fun n => W (φ (n + 1))) (R + 1)
  coreSection3 : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ R : ℕ,
    p.CanonicalCoreSection3Input (fun n => subsequenceCoreSize φ n + 2) (fun n => W (φ (n + 1))) (R + 1)
  ginibreRaw : ∀ᵐ z ∂(volume : Measure ℂ),
    TendstoInProbabilityTri (fun n => cyclicAtomLaw (n + 1) circularComplexGaussian)
      (fun n ω => matrixRawPotential (ginibreMatrix (n + 1) ω - z • 1)) (circularRadialPotential ‖z‖)
  ginibreNegative : ∀ᵐ z ∂(volume : Measure ℂ), ∃ q : ℝ, 0 < q ∧
    BC12GinibreNegativeMomentTightnessTri (fun n => n + 1) z q
  ginibreSpectral : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
    TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
      (fun n ω => realEsdTest (cyclicPhysicalMatrix n (ginibreMatrix (n + 1) (ω n).2)) f)
      atTop (fun _ => ∫ z, f z ∂circularMeasure)

theorem profile_probability_along_sparse_subsequence (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsource : p.GaussianProfileSourceInputs W) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hsparse : Tendsto (fun n => W (φ n) / (φ n + 1 : ℕ)) atTop (𝓝 0)) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbabilityTri (fun n => gaussianProfileLaw (φ n + 1))
        (fun n ω => matrixRawPotential (p.matrix (φ n + 1) (W (φ n)) ω - z • 1))
        (circularRadialPotential ‖z‖) := by
  have hφ' : Tendsto (fun n => φ (n + 1)) atTop atTop :=
    hφ.tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  have hdim : Tendsto (fun n => subsequenceCoreSize φ n + 2) atTop atTop := by
    apply ((tendsto_add_atTop_nat 1).comp hφ').congr'
    exact Eventually.of_forall fun n => (subsequenceCoreSize_dimension φ hφ n).symm
  have hs : Tendsto (fun n => W (φ (n + 1)) / (subsequenceCoreSize φ n + 2 : ℕ)) atTop (𝓝 0) := by
    apply (hsparse.comp (tendsto_add_atTop_nat 1)).congr'
    apply Eventually.of_forall
    intro n
    change W (φ (n + 1)) / ((φ (n + 1) + 1 : ℕ) : ℝ) =
      W (φ (n + 1)) / ((subsequenceCoreSize φ n + 2 : ℕ) : ℝ)
    rw [subsequenceCoreSize_dimension φ hφ n]
  have hg : ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbabilityTri (fun n => cyclicAtomLaw (subsequenceCoreSize φ n + 2) circularComplexGaussian)
        (fun n ω => matrixRawPotential (ginibreMatrix (subsequenceCoreSize φ n + 2) ω - z • 1))
        (circularRadialPotential ‖z‖) := by
    filter_upwards [hsource.ginibreRaw] with z hz
    have h : TendstoInProbabilityTri (fun n => cyclicAtomLaw (φ (n + 1) + 1) circularComplexGaussian)
        (fun n ω => matrixRawPotential (ginibreMatrix (φ (n + 1) + 1) ω - z • 1))
        (circularRadialPotential ‖z‖) := fun ε hε => (hz ε hε).comp hφ'
    intro ε hε
    apply (h ε hε).congr'
    exact Eventually.of_forall fun n => ginibre_raw_bad_dimension
      (subsequenceCoreSize_dimension φ hφ n).symm z (circularRadialPotential ‖z‖) ε
  have hn : ∀ᵐ z ∂(volume : Measure ℂ), ∃ q : ℝ, 0 < q ∧
      BC12GinibreNegativeMomentTightnessTri (fun n => subsequenceCoreSize φ n + 2) z q := by
    filter_upwards [hsource.ginibreNegative] with z hz
    obtain ⟨q, hq, hneg⟩ := hz
    refine ⟨q, hq, ?_⟩
    have h : BC12GinibreNegativeMomentTightnessTri (fun n => φ (n + 1) + 1) z q := by
      intro δ hδ
      obtain ⟨C, hC, hbound⟩ := hneg δ hδ
      exact ⟨C, hC, hφ'.eventually hbound⟩
    intro δ hδ
    obtain ⟨C, hC, hb⟩ := h δ hδ
    refine ⟨C, hC, ?_⟩
    filter_upwards [hb] with n hn
    rw [ginibre_negative_bad_dimension (subsequenceCoreSize_dimension φ hφ n) z q C]
    exact hn
  have hp := p.sparse_profile_probability_of_section3_section5 (subsequenceCoreSize φ) hdim
    (fun n => W (φ (n + 1))) (fun n => hW (φ (n + 1))) (hWlim.comp hφ') hs
    (hsource.coreSection5 φ hφ) (hsource.coreSection3 φ hφ) hg hn
  filter_upwards [hp] with z hz
  apply (tendstoInProbabilityTri_shift_iff (fun n => gaussianProfileLaw (φ n + 1))
    (fun n ω => matrixRawPotential (p.matrix (φ n + 1) (W (φ n)) ω - z • 1))
    (circularRadialPotential ‖z‖) 1).mp
  intro ε hε
  apply (hz ε hε).congr'
  exact Eventually.of_forall fun n => p.profile_raw_bad_dimension
    (subsequenceCoreSize_dimension φ hφ n) (W (φ (n + 1))) z (circularRadialPotential ‖z‖) ε

theorem profile_spectral_limit_along_sparse_subsequence (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsource : p.GaussianProfileSourceInputs W) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hsparse : Tendsto (fun n => W (φ n) / (φ n + 1 : ℕ)) atTop (𝓝 0)) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix (φ n)
          (p.matrix (φ n + 1) (W (φ n)) (ω (φ n)).1)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) := by
  have hrep := p.profile_ginibre_replacement_along_subsequence W φ hφ
    (fun z => circularRadialPotential ‖z‖)
    (p.profile_probability_along_sparse_subsequence W hW hWlim hsource φ hφ hsparse) hsource.ginibreRaw
  intro f hf hc
  have hdiff := (tendstoInMeasure_iff_tri (Measure.infinitePi profileGinibrePairLaw) _ 0).1 (hrep f hf hc)
  have hgin := (tendstoInMeasure_iff_tri (Measure.infinitePi profileGinibrePairLaw) _
    (∫ z, f z ∂circularMeasure)).1 ((hsource.ginibreSpectral f hf hc).comp hφ.tendsto_atTop)
  apply (tendstoInMeasure_iff_tri (Measure.infinitePi profileGinibrePairLaw) _ _).2
  simpa only [esdDifference, Function.comp_apply, sub_add_cancel, zero_add] using
    hdiff.add (fun _ => Measure.infinitePi profileGinibrePairLaw) hgin

end NoncompactProfile
end CircularLawSection6
