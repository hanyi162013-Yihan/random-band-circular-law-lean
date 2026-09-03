import CircularLawSection6.PublishedCoreLocalInput
import CircularLawSections56.Section5.PublishedSection3Literature

/-! # Concrete literature sources for every local Gaussian core

The retained singular-law input concerns only actual Ginibre matrices of
dimension `n + 1`. All growing block sequences follow by reindexing this
single sequence, on the same full-measure set of shifts. The other source
is uniform BBV; its applications to the two actual local matrix models are
constructed here, rather than retained as per-model certificates.
-/

open MeasureTheory Filter Topology ShortRingAnchor Arxiv2410V3
open CircularLawSections56.Section5
open CircularLawSections56.Section5.PublishedSection3Concrete (BBVComparisonInput canonicalBBVAt_mono)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

/-- Classical bounded-test singular-law limit for the actual, normalized,
circular complex Ginibre matrices, with one limiting law at each shift. -/
def ClassicalGinibreSquaredTestInput : Prop :=
  ∀ᵐ z ∂(volume : Measure ℂ), ∃ σ : Measure ℝ,
    IsProbabilityMeasure σ ∧ (∀ᵐ s ∂σ, 0 ≤ s) ∧
      Integrable (fun s : ℝ => s ^ 2) σ ∧
      GinibreSquaredTestInput (fun n => ⟨n + 1, Nat.succ_pos n⟩) z σ

theorem ginibreSquaredTestInput_reindex
    {z : ℂ} {σ : Measure ℝ}
    (h : GinibreSquaredTestInput (fun n => ⟨n + 1, Nat.succ_pos n⟩) z σ)
    (M : ℕ → ℕ+) (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop) :
    GinibreSquaredTestInput M z σ := by
  have hpred : Tendsto (fun n => (M n : ℕ) - 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [hM.eventually (eventually_ge_atTop (b + 1))] with n hn
    omega
  have hdim (n : ℕ) : (M n : ℕ) - 1 + 1 = (M n : ℕ) := by
    have := (M n).pos
    omega
  intro φ hφ hb ε hε
  -- Package the dimension-dependent sample space and measure inside one
  -- real-valued function of a positive dimension before transporting it.
  let probability (m : ℕ+) : ℝ :=
    (cyclicAtomLaw (m : ℕ) circularComplexGaussian).real
      {ω | ε ≤ |matrixSquaredSingularAverage (ginibreMatrix (m : ℕ) ω - z • 1) φ -
        ∫ s, φ (s ^ 2) ∂σ|}
  have hcomp : Tendsto
      (fun n => probability ⟨(M n : ℕ) - 1 + 1, Nat.succ_pos _⟩) atTop (𝓝 0) :=
    (h φ hφ hb ε hε).comp hpred
  change Tendsto (fun n => probability (M n)) atTop (𝓝 0)
  apply hcomp.congr'
  apply Eventually.of_forall
  intro n
  exact congrArg probability (Subtype.ext (hdim n))

theorem publishedLocal_spectralParameter_im_pos (M : ℕ+) (u : ℝ) :
    0 < (spectralParameter u (localBulkHeight (1 / 8) M)).im := by
  have hv : 0 < localBulkHeight (1 / 8) (M : ℝ) := by
    unfold localBulkHeight
    positivity
  simpa [spectralParameter] using hv

namespace CoreRadiusBounds

variable {p : NoncompactProfile} {R : ℝ}

theorem publishedLocalInput_of_concrete_literature (B : CoreRadiusBounds p R)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (W : ℕ → ℝ) (hW : ∀ n, 0 < W n)
    (hR : 0 < R) (hWlim : Tendsto W atTop atTop)
    (hBBV : BBVComparisonInput) (hGinibre : ClassicalGinibreSquaredTestInput) :
    B.PublishedLocalInput N W hW := by
  obtain ⟨C, _hCpos, hC⟩ := hBBV
  intro K hH hfit
  have hHlim : Tendsto (fun n => ⌊R * W (n + K)⌋₊) atTop atTop :=
    floor_radius_atTop _ (hWlim.comp (tendsto_add_atTop_nat K)) hR
  have hNlim : Tendsto (fun n => N (n + K)) atTop atTop :=
    tendsto_atTop_mono (fun n => by have := hfit n; omega) hHlim
  filter_upwards [hGinibre] with z hz
  obtain ⟨σ, hσ, hpos, hsecond, hweak⟩ := hz
  refine ⟨σ, hσ, hpos, hsecond,
    ginibreSquaredTestInput_reindex hweak (fun n => ⟨N (n + K), NeZero.pos _⟩) hNlim,
    C, ?_⟩
  intro M hwindow
  have hMlim : Tendsto (fun n => (M n : ℕ)) atTop atTop :=
    tendsto_atTop_mono (fun n => by have := (hwindow n).1; omega) hHlim
  refine ⟨ginibreSquaredTestInput_reindex hweak M hMlim, ?_, ?_⟩
  · intro n u
    have hη := publishedLocal_spectralParameter_im_pos (M n) u
    exact canonicalBBVAt_mono
      (hC (cyclicGinibreJointSample (M n) ⌊R * W (n + K)⌋₊) ℂ
        (cyclicGinibreJointLaw (M n) ⌊R * W (n + K)⌋₊) circularComplexGaussian
        (M n) (M n).pos
        (publishedJointCyclicModel (B.floorLocalWeights N W hW K hH hfit n) (hwindow n).1)
        _ (cyclicVarianceProfile_isBandwidth
          (B.floorLocalWeights N W hW K hH hfit n) (hwindow n).1) z _ hη)
      (B.floorLocalWeights N W hW K hH hfit n).bandwidthParameter_pos hη
      (le_max_left _ _)
  · intro n u
    have hη := publishedLocal_spectralParameter_im_pos (M n) u
    exact canonicalBBVAt_mono
      (hC (cyclicGinibreJointSample (M n) ⌊R * W (n + K)⌋₊) ℂ
        (cyclicGinibreJointLaw (M n) ⌊R * W (n + K)⌋₊) circularComplexGaussian
        (M n) (M n).pos (publishedJointDenseModel (M n) ⌊R * W (n + K)⌋₊)
        _ (denseVarianceProfile_isBandwidth (M n).pos) z _ hη)
      (by positivity) hη (le_max_left _ _)

theorem canonicalCoreSection3Input_of_concrete_literature (B : CoreRadiusBounds p R)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (W : ℕ → ℝ) (hW : ∀ n, 0 < W n)
    (hR : 0 < R) (hWlim : Tendsto W atTop atTop)
    (hBBV : BBVComparisonInput) (hGinibre : ClassicalGinibreSquaredTestInput) :
    p.CanonicalCoreSection3Input N W R :=
  PublishedLocalInput.toCanonical B N W hW hR hWlim
    (B.publishedLocalInput_of_concrete_literature N W hW hR hWlim hBBV hGinibre)

end CoreRadiusBounds
end CircularLawSection6
