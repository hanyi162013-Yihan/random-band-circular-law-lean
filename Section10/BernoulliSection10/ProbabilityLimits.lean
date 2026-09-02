import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Convergence in probability for triangular arrays

Adapted from the user's `CircularLawSections56/Section5/TriangularProbability.lean`
(snapshot 2026-09-02). This module contains only proved general probability
lemmas; its intermediate comparison hypotheses are discharged by Section 10's
concrete model modules before the final public theorem.

The literal Section 10 random matrices have a different finite product
probability space at every matrix size.  `MeasureTheory.TendstoInMeasure` deliberately
uses one fixed sample type, so it is not the right endpoint for those literal objects.

This file supplies the small dependent-type interface needed by the manuscript:

* convergence in probability on varying probability spaces;
* Markov's inequality as an `L¹`-to-probability bridge;
* stability under sums and arbitrary branch selection;
* convergence of deterministic observables; and
* the calibration lemma saying that a deterministic center converges when it is
  `L¹`-close to a random anchor which converges in probability.

No coupling between the probability spaces is introduced.
-/

open Filter MeasureTheory Set Topology

namespace BernoulliSection10.ProbabilityLimits

universe u

variable {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]

/-- Convergence in probability for a triangular array.  The sample type and measure may
depend on the index.  Real-valued probabilities are used because all measures below are
probability measures. -/
def TendstoInProbabilityTri
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (observable : ∀ n, Ω n → ℝ) (target : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto
      (fun n => (μ n).real {ω | ε ≤ |observable n ω - target|})
      atTop (𝓝 0)

/-- Markov's inequality converts a vanishing triangular-array `L¹` error into
convergence in probability. -/
theorem tendstoInProbabilityTri_of_L1
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (observable : ∀ n, Ω n → ℝ) (target : ℝ) (error : ℕ → ℝ)
    (hIntegrable : ∀ n,
      Integrable (fun ω => |observable n ω - target|) (μ n))
    (hIntegral : ∀ n,
      ∫ ω, |observable n ω - target| ∂μ n ≤ error n)
    (hError : Tendsto error atTop (𝓝 0)) :
    TendstoInProbabilityTri μ observable target := by
  intro ε hε
  have hUpper : ∀ n,
      (μ n).real {ω | ε ≤ |observable n ω - target|} ≤ error n / ε := by
    intro n
    have hMarkov := mul_meas_ge_le_integral_of_nonneg
      (μ := μ n) (f := fun ω => |observable n ω - target|)
      (Filter.Eventually.of_forall fun ω => abs_nonneg (observable n ω - target))
      (hIntegrable n) ε
    apply (le_div_iff₀ hε).2
    calc
      (μ n).real {ω | ε ≤ |observable n ω - target|} * ε =
          ε * (μ n).real {ω | ε ≤ |observable n ω - target|} := mul_comm _ _
      _ ≤ ∫ ω, |observable n ω - target| ∂μ n := hMarkov
      _ ≤ error n := hIntegral n
  have hErrorDiv : Tendsto (fun n => error n / ε) atTop (𝓝 0) := by
    simpa using hError.div_const ε
  exact squeeze_zero
    (fun n => measureReal_nonneg)
    hUpper hErrorDiv

/-- Pointwise-identical triangular arrays have the same probability limit. -/
theorem TendstoInProbabilityTri.congr
    {μ : ∀ n, Measure (Ω n)} [∀ n, IsFiniteMeasure (μ n)]
    {X Y : ∀ n, Ω n → ℝ} {x y : ℝ}
    (hX : TendstoInProbabilityTri μ X x)
    (hXY : ∀ n ω, X n ω = Y n ω) (hxy : x = y) :
    TendstoInProbabilityTri μ Y y := by
  subst y
  intro ε hε
  convert hX ε hε using 1
  funext n
  congr 2
  ext ω
  simp only [hXY]

/-- The sum of two triangular arrays converging in probability converges to the sum of
their limits. -/
theorem TendstoInProbabilityTri.add
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    {X Y : ∀ n, Ω n → ℝ} {x y : ℝ}
    (hX : TendstoInProbabilityTri μ X x)
    (hY : TendstoInProbabilityTri μ Y y) :
    TendstoInProbabilityTri μ (fun n ω => X n ω + Y n ω) (x + y) := by
  intro ε hε
  let half : ℝ := ε / 2
  have hhalf : 0 < half := by dsimp [half]; linarith
  let pX : ℕ → ℝ := fun n =>
    (μ n).real {ω | half ≤ |X n ω - x|}
  let pY : ℕ → ℝ := fun n =>
    (μ n).real {ω | half ≤ |Y n ω - y|}
  have hpX : Tendsto pX atTop (𝓝 0) := hX half hhalf
  have hpY : Tendsto pY atTop (𝓝 0) := hY half hhalf
  have hUpper : ∀ n,
      (μ n).real {ω | ε ≤ |(X n ω + Y n ω) - (x + y)|} ≤
        pX n + pY n := by
    intro n
    let badX : Set (Ω n) := {ω | half ≤ |X n ω - x|}
    let badY : Set (Ω n) := {ω | half ≤ |Y n ω - y|}
    have hsubset :
        {ω | ε ≤ |(X n ω + Y n ω) - (x + y)|} ⊆ badX ∪ badY := by
      intro ω hω
      by_contra hbad
      simp only [mem_union, not_or, badX, badY] at hbad
      have htriangle :
          |(X n ω + Y n ω) - (x + y)| ≤
            |X n ω - x| + |Y n ω - y| := by
        rw [show (X n ω + Y n ω) - (x + y) =
          (X n ω - x) + (Y n ω - y) by ring]
        exact abs_add_le _ _
      change ε ≤ |(X n ω + Y n ω) - (x + y)| at hω
      dsimp [half] at hbad
      linarith
    calc
      (μ n).real {ω | ε ≤ |(X n ω + Y n ω) - (x + y)|} ≤
          (μ n).real (badX ∪ badY) := measureReal_mono hsubset
      _ ≤ (μ n).real badX + (μ n).real badY := measureReal_union_le _ _
      _ = pX n + pY n := rfl
  have hSum : Tendsto (fun n => pX n + pY n) atTop (𝓝 0) := by
    simpa only [zero_add] using hpX.add hpY
  exact squeeze_zero
    (fun n => measureReal_nonneg)
    hUpper hSum

/-- An ordinarily convergent deterministic sequence, regarded as a constant random
observable on each probability space, converges in triangular-array probability. -/
theorem tendstoInProbabilityTri_const
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (center : ℕ → ℝ) (target : ℝ)
    (hCenter : Tendsto center atTop (𝓝 target)) :
    TendstoInProbabilityTri μ (fun n _ => center n) target := by
  intro ε hε
  have hEventually : ∀ᶠ n in atTop, |center n - target| < ε := by
    have hdist : Tendsto (fun n => dist (center n) target) atTop (𝓝 0) := by
      simpa using hCenter.dist
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => target) atTop (𝓝 target))
    have hball := (Metric.tendsto_atTop.1 hdist) ε hε
    simpa [Real.dist_eq] using hball
  have hEventuallyZero : ∀ᶠ n in atTop,
      (μ n).real {ω | ε ≤ |center n - target|} = 0 := by
    filter_upwards [hEventually] with n hn
    simp [not_le_of_gt hn]
  have hEq :
      (fun n => (μ n).real {ω | ε ≤ |center n - target|}) =ᶠ[atTop]
        (fun _ => 0) := hEventuallyZero
  exact tendsto_const_nhds.congr' hEq.symm

/-- If a random anchor converges to `target` and its difference from a deterministic
center converges to zero in probability, then the deterministic centers converge in the
ordinary sense.  This is the uniqueness-of-probability-limits step used in mesoscopic
calibration. -/
theorem deterministic_center_tendsto_of_tri_anchor_and_close
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (anchor : ∀ n, Ω n → ℝ) (center : ℕ → ℝ) (target : ℝ)
    (hAnchor : TendstoInProbabilityTri μ anchor target)
    (hClose : TendstoInProbabilityTri μ
      (fun n ω => anchor n ω - center n) 0) :
    Tendsto center atTop (𝓝 target) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  let half : ℝ := ε / 2
  have hhalf : 0 < half := by dsimp [half]; linarith
  let pAnchor : ℕ → ℝ := fun n =>
    (μ n).real {ω | half ≤ |anchor n ω - target|}
  let pClose : ℕ → ℝ := fun n =>
    (μ n).real {ω | half ≤ |(anchor n ω - center n) - 0|}
  have hpAnchor : Tendsto pAnchor atTop (𝓝 0) := hAnchor half hhalf
  have hpClose : Tendsto pClose atTop (𝓝 0) := hClose half hhalf
  have hSmall : ∀ᶠ n in atTop, pAnchor n + pClose n < 1 := by
    have hsum : Tendsto (fun n => pAnchor n + pClose n) atTop (𝓝 0) := by
      simpa only [zero_add] using hpAnchor.add hpClose
    exact hsum.eventually (Iio_mem_nhds zero_lt_one)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hSmall
  refine ⟨N, fun n hnN => ?_⟩
  have hn := hN n hnN
  rw [Real.dist_eq]
  by_contra hnot
  have hlarge : ε ≤ |center n - target| := le_of_not_gt hnot
  let badAnchor : Set (Ω n) := {ω | half ≤ |anchor n ω - target|}
  let badClose : Set (Ω n) :=
    {ω | half ≤ |(anchor n ω - center n) - 0|}
  have hcover : Set.univ ⊆ badAnchor ∪ badClose := by
    intro ω _
    by_contra hbad
    simp only [mem_union, not_or, badAnchor, badClose] at hbad
    have htriangle :
        |center n - target| ≤
          |anchor n ω - target| + |anchor n ω - center n| := by
      calc
        |center n - target| =
            |-(anchor n ω - center n) + (anchor n ω - target)| := by
              exact congrArg abs (by abel)
        _ ≤ |-(anchor n ω - center n)| + |anchor n ω - target| := abs_add_le _ _
        _ = |anchor n ω - target| + |anchor n ω - center n| := by
          rw [abs_neg, add_comm]
    dsimp [half] at hbad
    simp only [sub_zero] at hbad
    linarith
  have hone : (1 : ℝ) ≤ pAnchor n + pClose n := by
    calc
      (1 : ℝ) = (μ n).real Set.univ := by simp [Measure.real]
      _ ≤ (μ n).real (badAnchor ∪ badClose) := measureReal_mono hcover
      _ ≤ (μ n).real badAnchor + (μ n).real badClose := measureReal_union_le _ _
      _ = pAnchor n + pClose n := by rfl
  linarith

/-- The calibration bridge used for (10.35): an `L¹` comparison
with a deterministic center plus the Section 3 convergence-in-probability anchor forces
ordinary convergence of the center. -/
theorem deterministic_center_tendsto_of_tri_anchor_and_L1_close
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (anchor : ∀ n, Ω n → ℝ) (center error : ℕ → ℝ) (target : ℝ)
    (hAnchor : TendstoInProbabilityTri μ anchor target)
    (hIntegrable : ∀ n,
      Integrable (fun ω => |anchor n ω - center n|) (μ n))
    (hIntegral : ∀ n,
      ∫ ω, |anchor n ω - center n| ∂μ n ≤ error n)
    (hError : Tendsto error atTop (𝓝 0)) :
    Tendsto center atTop (𝓝 target) := by
  apply deterministic_center_tendsto_of_tri_anchor_and_close
    μ anchor center target hAnchor
  apply tendstoInProbabilityTri_of_L1 μ
    (fun n ω => anchor n ω - center n) 0 error
  · simpa only [sub_zero] using hIntegrable
  · simpa only [sub_zero] using hIntegral
  · exact hError

/-- Two-step calibration bridge matching the seam-and-concentration adapter shape. The
random anchor is first compared in `L¹` with a random maximal pressure, and that pressure
is then compared in `L¹` with its deterministic mean.  Constructing these two normalized
comparisons from literal matrices is discharged in the concrete Section 10 modules. -/
theorem deterministic_center_tendsto_of_tri_anchor_and_two_L1_seams
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (anchor intermediate : ∀ n, Ω n → ℝ)
    (center seamError fluctuationError : ℕ → ℝ) (target : ℝ)
    (hAnchor : TendstoInProbabilityTri μ anchor target)
    (hSeamIntegrable : ∀ n,
      Integrable (fun ω => |anchor n ω - intermediate n ω|) (μ n))
    (hSeamIntegral : ∀ n,
      ∫ ω, |anchor n ω - intermediate n ω| ∂μ n ≤ seamError n)
    (hFluctuationIntegrable : ∀ n,
      Integrable (fun ω => |intermediate n ω - center n|) (μ n))
    (hFluctuationIntegral : ∀ n,
      ∫ ω, |intermediate n ω - center n| ∂μ n ≤ fluctuationError n)
    (hSeamError : Tendsto seamError atTop (𝓝 0))
    (hFluctuationError : Tendsto fluctuationError atTop (𝓝 0)) :
    Tendsto center atTop (𝓝 target) := by
  have hSeam : TendstoInProbabilityTri μ
      (fun n ω => anchor n ω - intermediate n ω) 0 := by
    apply tendstoInProbabilityTri_of_L1 μ _ 0 seamError
    · simpa only [sub_zero] using hSeamIntegrable
    · simpa only [sub_zero] using hSeamIntegral
    · exact hSeamError
  have hFluctuation : TendstoInProbabilityTri μ
      (fun n ω => intermediate n ω - center n) 0 := by
    apply tendstoInProbabilityTri_of_L1 μ _ 0 fluctuationError
    · simpa only [sub_zero] using hFluctuationIntegrable
    · simpa only [sub_zero] using hFluctuationIntegral
    · exact hFluctuationError
  have hClose : TendstoInProbabilityTri μ
      (fun n ω => anchor n ω - center n) 0 := by
    have hSum := hSeam.add μ hFluctuation
    apply hSum.congr
    · intro n ω
      ring
    · simp
  exact deterministic_center_tendsto_of_tri_anchor_and_close
    μ anchor center target hAnchor hClose

/-- The forward `L¹` bridge: if a triangular random array is `L¹`-close to deterministic
centers and the centers converge, then the random array converges in probability. -/
theorem tendstoInProbabilityTri_of_center_tendsto_and_L1_close
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (observable : ∀ n, Ω n → ℝ) (center error : ℕ → ℝ) (target : ℝ)
    (hCenter : Tendsto center atTop (𝓝 target))
    (hIntegrable : ∀ n,
      Integrable (fun ω => |observable n ω - center n|) (μ n))
    (hIntegral : ∀ n,
      ∫ ω, |observable n ω - center n| ∂μ n ≤ error n)
    (hError : Tendsto error atTop (𝓝 0)) :
    TendstoInProbabilityTri μ observable target := by
  have hClose : TendstoInProbabilityTri μ
      (fun n ω => observable n ω - center n) 0 := by
    apply tendstoInProbabilityTri_of_L1 μ _ 0 error
    · simpa only [sub_zero] using hIntegrable
    · simpa only [sub_zero] using hIntegral
    · exact hError
  have hDeterministic := tendstoInProbabilityTri_const μ center target hCenter
  have hSum := hClose.add μ hDeterministic
  apply hSum.congr
  · intro n ω
    ring
  · simp

/-- The terminal seam and maximal-pressure fluctuation bounds, together with the
deterministic mean-pressure limit, imply the long-branch log-potential limit.
The two `L¹` hypotheses have exactly the shape returned by the fresh-closure and pressure-
concentration APIs after normalization. -/
theorem longBranch_tendstoInProbabilityTri_of_L1_seams
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (logPotential randomPressure : ∀ n, Ω n → ℝ)
    (meanPressure seamError fluctuationError : ℕ → ℝ) (target : ℝ)
    (hSeamIntegrable : ∀ n,
      Integrable (fun ω => |logPotential n ω - randomPressure n ω|) (μ n))
    (hSeamIntegral : ∀ n,
      ∫ ω, |logPotential n ω - randomPressure n ω| ∂μ n ≤ seamError n)
    (hFluctuationIntegrable : ∀ n,
      Integrable (fun ω => |randomPressure n ω - meanPressure n|) (μ n))
    (hFluctuationIntegral : ∀ n,
      ∫ ω, |randomPressure n ω - meanPressure n| ∂μ n ≤ fluctuationError n)
    (hSeamError : Tendsto seamError atTop (𝓝 0))
    (hFluctuationError : Tendsto fluctuationError atTop (𝓝 0))
    (hMeanPressure : Tendsto meanPressure atTop (𝓝 target)) :
    TendstoInProbabilityTri μ logPotential target := by
  have hSeam : TendstoInProbabilityTri μ
      (fun n ω => logPotential n ω - randomPressure n ω) 0 := by
    apply tendstoInProbabilityTri_of_L1 μ _ 0 seamError
    · simpa only [sub_zero] using hSeamIntegrable
    · simpa only [sub_zero] using hSeamIntegral
    · exact hSeamError
  have hFluctuation : TendstoInProbabilityTri μ
      (fun n ω => randomPressure n ω - meanPressure n) 0 := by
    apply tendstoInProbabilityTri_of_L1 μ _ 0 fluctuationError
    · simpa only [sub_zero] using hFluctuationIntegrable
    · simpa only [sub_zero] using hFluctuationIntegral
    · exact hFluctuationError
  have hMean := tendstoInProbabilityTri_const μ meanPressure target hMeanPressure
  have hSum := (hSeam.add μ hFluctuation).add μ hMean
  apply hSum.congr
  · intro n ω
    ring
  · simp

/-- Select the high-band branch or the stitched long branch at each index. -/
def branchSelectedTri
    (shortBranch : ℕ → Bool)
    (shortObservable longObservable : ∀ n, Ω n → ℝ) : ∀ n, Ω n → ℝ :=
  fun n ω => if shortBranch n then shortObservable n ω else longObservable n ω

/-- Arbitrary interleaving preserves a common triangular-array probability limit. -/
theorem tendstoInProbabilityTri_branchSelected
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (shortBranch : ℕ → Bool)
    (shortObservable longObservable : ∀ n, Ω n → ℝ) (target : ℝ)
    (hShort : TendstoInProbabilityTri μ shortObservable target)
    (hLong : TendstoInProbabilityTri μ longObservable target) :
    TendstoInProbabilityTri μ
      (branchSelectedTri shortBranch shortObservable longObservable) target := by
  intro ε hε
  have hMixed := (hShort ε hε).if' (hLong ε hε)
    (p := fun n => shortBranch n = true)
  convert hMixed using 1
  funext n
  cases h : shortBranch n <;> simp [branchSelectedTri, h]

end BernoulliSection10.ProbabilityLimits
