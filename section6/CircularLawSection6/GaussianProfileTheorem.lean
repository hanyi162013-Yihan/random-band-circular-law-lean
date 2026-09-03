import CircularLawSection6.SubsequenceSourceEndpoint
import CircularLawSection6.DenseGaussianSourceAdapter
import CircularLawSection6.SparseDenseSubsequences

/-! # The noncompact Gaussian profile circular law, conditional on the cited inputs

The model is the actual normalized sample of a positive continuous BV
integrable profile. No assumption is made about the limit of W/N: sparse
and dense further subsequences are constructed and then recombined.

The explicit source hypotheses consist of Section 3's local comparison,
Section 5's literal core endpoint, the classical Ginibre inputs, and Han's
Gaussian high-bandwidth theorem. All Section 6 model, energy, tail,
normalization, expectation, probability and replacement steps are proved.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5 CircularLawSections56.Section6

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

theorem gaussian_profile_circular_law (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsource : p.GaussianProfileSourceInputs W) (hHan : HanGaussianDenseInput) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix n (p.matrix (n + 1) (W n) (ω n).1)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) := by
  intro f hf hc
  apply tendstoInMeasure_of_sparse_dense_subsequences (Measure.infinitePi profileGinibrePairLaw)
    (fun n ω => realEsdTest (cyclicPhysicalMatrix n (p.matrix (n + 1) (W n) (ω n).1)) f)
    (fun _ => ∫ z, f z ∂circularMeasure) (fun n => W n / (n + 1 : ℕ))
    (fun n => div_nonneg (hW n).le (Nat.cast_nonneg _))
  · intro φ hφ hsparse
    exact p.profile_spectral_limit_along_sparse_subsequence W hW hWlim hsource φ hφ hsparse f hf hc
  · intro φ hφ hdense
    exact p.dense_profile_spectral_limit_of_Han W φ hφ hdense hHan f hf hc

end CircularLawSection6.NoncompactProfile
