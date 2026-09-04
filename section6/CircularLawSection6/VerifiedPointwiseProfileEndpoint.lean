import CircularLawSection6.NoncompactReferenceMeanPointwise
import CircularLawSection6.DenseProfileEndpoint
import CircularLawSection6.GinibreBBVConsequences

/-! # Gaussian full-profile logarithmic potential at every fixed shift

Sparse subsequences use the pointwise compact-core reconstruction; dense
subsequences use the already pointwise Section 3 full-profile theorem.  A
numerical subsequence criterion for the bad-event probabilities joins the two
branches.  The conclusion is for each prescribed `z : ℂ`; it does not assert a
single probability-one event simultaneously for uncountably many shifts.
-/

open MeasureTheory Filter Topology TaoVuReplacement ShortRingAnchor
open CircularLawSections56.Section5 CircularLawSections56.Section6
open CircularLawSections56.Section5.PublishedSection3Concrete (BBVComparisonInput)

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem tendstoInProbabilityTri_of_every_subsequence_has_further
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (a : ℝ)
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      TendstoInProbabilityTri (fun n => μ (φ (ψ n)))
        (fun n => X (φ (ψ n))) a) :
    TendstoInProbabilityTri μ X a := by
  intro ε hε
  apply tendsto_of_every_subsequence_has_further _ 0
  intro φ hφ
  obtain ⟨ψ, hψ, hlim⟩ := h φ hφ
  exact ⟨ψ, hψ, hlim ε hε⟩

theorem tendstoInProbabilityTri_of_sparse_dense_subsequences
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (a : ℝ)
    (ratio : ℕ → ℝ) (hratio : ∀ n, 0 ≤ ratio n)
    (hsparse : ∀ φ : ℕ → ℕ, StrictMono φ →
      Tendsto (fun n => ratio (φ n)) atTop (𝓝 0) →
      TendstoInProbabilityTri (fun n => μ (φ n)) (fun n => X (φ n)) a)
    (hdense : ∀ φ : ℕ → ℕ, StrictMono φ →
      (∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ ratio (φ n)) →
      TendstoInProbabilityTri (fun n => μ (φ n)) (fun n => X (φ n)) a) :
    TendstoInProbabilityTri μ X a := by
  apply tendstoInProbabilityTri_of_every_subsequence_has_further μ X a
  intro φ hφ
  obtain ⟨ψ, hψ, hbranch⟩ :=
    exists_sparse_or_dense_subsequence (fun n => ratio (φ n)) (fun n => hratio (φ n))
  refine ⟨ψ, hψ, ?_⟩
  rcases hbranch with hs | hd
  · exact hsparse (φ ∘ ψ) (hφ.comp hψ) hs
  · exact hdense (φ ∘ ψ) (hφ.comp hψ) hd

namespace NoncompactProfile

private theorem pointwise_profile_raw_bad_dimension (p : NoncompactProfile)
    {N M : ℕ} [NeZero N] [NeZero M] (hNM : N = M) (W : ℝ) (z : ℂ) (a ε : ℝ) :
    (gaussianProfileLaw N).real
        {ω | ε ≤ |matrixRawPotential (p.matrix N W ω - z • 1) - a|} =
      (gaussianProfileLaw M).real
        {ω | ε ≤ |matrixRawPotential (p.matrix M W ω - z • 1) - a|} := by
  subst M
  rfl

theorem profile_probability_along_sparse_subsequence_of_bbv_at (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hBBV : BBVComparisonInput) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hsparse : Tendsto (fun n => W (φ n) / (φ n + 1 : ℕ)) atTop (𝓝 0))
    (z : ℂ) :
    TendstoInProbabilityTri (fun n => gaussianProfileLaw (φ n + 1))
      (fun n ω => matrixRawPotential (p.matrix (φ n + 1) (W (φ n)) ω - z • 1))
      (circularRadialPotential ‖z‖) := by
  have hφ' : Tendsto (fun n => φ (n + 1)) atTop atTop :=
    hφ.tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  have hdim : Tendsto (fun n => subsequenceCoreSize φ n + 2) atTop atTop := by
    apply ((tendsto_add_atTop_nat 1).comp hφ').congr'
    exact Eventually.of_forall fun n => (subsequenceCoreSize_dimension φ hφ n).symm
  have hs : Tendsto
      (fun n => W (φ (n + 1)) / (subsequenceCoreSize φ n + 2 : ℕ))
      atTop (𝓝 0) := by
    apply (hsparse.comp (tendsto_add_atTop_nat 1)).congr'
    apply Eventually.of_forall
    intro n
    rw [subsequenceCoreSize_dimension φ hφ n]
  have hSection5 (R : ℕ) : p.CanonicalCoreSection5InputPointwise
      (subsequenceCoreSize φ) (fun n => W (φ (n + 1))) (R + 1) :=
    CoreRadiusBounds.verifiedToCanonicalPointwise
      (p.coreRadiusBounds (by positivity : (0 : ℝ) ≤ (R : ℝ) + 1)) W
      (by positivity) hW hWlim hBBV φ hφ
  have hp := p.sparse_profile_probability_of_bbv_section5_at hBBV
    (subsequenceCoreSize φ) hdim (fun n => W (φ (n + 1)))
    (fun n => hW (φ (n + 1))) (hWlim.comp hφ') hs hSection5 z
  apply (tendstoInProbabilityTri_shift_iff (fun n => gaussianProfileLaw (φ n + 1))
    (fun n ω => matrixRawPotential (p.matrix (φ n + 1) (W (φ n)) ω - z • 1))
    (circularRadialPotential ‖z‖) 1).mp
  intro ε hε
  apply (hp ε hε).congr'
  exact Eventually.of_forall fun n => p.pointwise_profile_raw_bad_dimension
    (subsequenceCoreSize_dimension φ hφ n) (W (φ (n + 1))) z
    (circularRadialPotential ‖z‖) ε

/-- Preferred Section 6 logarithmic-potential endpoint: for every prescribed
`z : ℂ`, the actual Gaussian full-profile matrices converge in probability.
The only literature input is uniform BBV. -/
theorem gaussian_profile_logPotential_of_bbv (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hBBV : BBVComparisonInput) (z : ℂ) :
    TendstoInProbabilityTri (fun n => gaussianProfileLaw (n + 1))
      (fun n ω => matrixRawPotential (p.matrix (n + 1) (W n) ω - z • 1))
      (circularRadialPotential ‖z‖) := by
  apply tendstoInProbabilityTri_of_sparse_dense_subsequences
    (fun n => gaussianProfileLaw (n + 1))
    (fun n ω => matrixRawPotential (p.matrix (n + 1) (W n) ω - z • 1))
    (circularRadialPotential ‖z‖) (fun n => W n / (n + 1 : ℕ))
    (fun n => div_nonneg (hW n).le (Nat.cast_nonneg _))
  · intro φ hφ hsparse
    exact p.profile_probability_along_sparse_subsequence_of_bbv_at W hW hWlim hBBV
      φ hφ hsparse z
  · intro φ hφ hdense
    obtain ⟨c, hc, hratio⟩ := hdense
    exact DenseProfile.profile_raw_limit hBBV p (fun n => φ n + 1)
      (fun n => W (φ n))
      ((tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop) hc
      (fun n => (le_div_iff₀ (by positivity)).mp (hratio n)) z

/-- Circular-law consequence assembled from the everywhere fixed-shift
logarithmic-potential endpoint.  `ae_of_all` is used only at the Tao--Vu
replacement boundary, because that general theorem asks for an a.e. family. -/
theorem gaussian_profile_circular_law_of_pointwise_bbv (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hBBV : BBVComparisonInput) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest
          (cyclicPhysicalMatrix n (p.matrix (n + 1) (W n) (ω n).1)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) := by
  have hrep := p.profile_ginibre_replacement_of_log_limits W
    (fun z => circularRadialPotential ‖z‖)
    (ae_of_all _ fun z => p.gaussian_profile_logPotential_of_bbv W hW hWlim hBBV z)
    (ae_of_all _ fun z => by
      simpa only [circularRadialPotential, circularLogPotential] using
        ginibre_raw_probability_of_bbv hBBV (fun n => n + 1)
          (tendsto_add_atTop_nat 1) z)
  intro f hf hc
  have hdiff := (tendstoInMeasure_iff_tri (Measure.infinitePi profileGinibrePairLaw) _ 0).1
    (hrep f hf hc)
  have hgin := (tendstoInMeasure_iff_tri (Measure.infinitePi profileGinibrePairLaw) _
    (∫ z, f z ∂circularMeasure)).1 (ginibre_spectral_of_bbv hBBV f hf hc)
  apply (tendstoInMeasure_iff_tri (Measure.infinitePi profileGinibrePairLaw) _ _).2
  simpa only [esdDifference, sub_add_cancel, zero_add] using
    hdiff.add (fun _ => Measure.infinitePi profileGinibrePairLaw) hgin

end NoncompactProfile
end CircularLawSection6
