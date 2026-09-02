import BernoulliSection8.RademacherCircularReduction

/-!
# The permitted Section 3 high-band input for real sub-Gaussian atoms

The source is Proposition 3.8, labelled
`prop:subgaussian-block-high-band`, in arXiv:2609.01295v1, `main.tex`
lines 1146--1161, equations (3.18)--(3.19). It is a proved proposition of the permitted Section 3
input, not a Section 10 bounded-density result. This explicit proposition
parameter asserts its log-potential conclusion for the literal normalized
three-neighbour full-block matrix.

`s + 3 ≥ 4` is expressed by `0 < s`; `N = (s + 3)W`. Since `W → ∞`
implies `N → ∞`, a separate dimension-divergence premise is redundant.
Allowing the high-band inequality eventually instead of at every index is
the equivalent asymptotic statement, invariant under finitely many terms.
The mean-zero sub-Gaussian MGF convention is equivalent to a finite
sub-Gaussian norm for these centered laws; no numerical Orlicz constant
enters this source conclusion.

The real logarithm is totalized at zero in Lean. Proposition 3.8 proves a
positive singular-value floor with probability tending to one, so this is
a valid finite-valued version of its logarithmic-potential statement. The
input does not assume almost-sure invertibility at any finite size.
-/

open Filter MeasureTheory Topology
open scoped NNReal

noncomputable section

namespace BernoulliSection8

open BernoulliSection10 ShortRingAnchor BernoulliSection10.DiskReference

/-- The real IID atom hypotheses of the discrete/sub-Gaussian theorem.
There is no absolute-continuity or bounded-density condition. -/
structure IsRealSubgaussianAtom (μ : Measure ℝ) (c : ℝ≥0) : Prop where
  probability : μ Set.univ = 1
  centered : (∫ x : ℝ, x ∂μ) = 0
  second_moment : (∫ x : ℝ, x ^ 2 ∂μ) = 1
  subgaussian : ProbabilityTheory.HasSubgaussianMGF (fun x : ℝ => x) c μ

theorem rademacherLaw_isRealSubgaussianAtom : IsRealSubgaussianAtom rademacherLaw 1 :=
  ⟨measure_univ, rademacherLaw_mean_zero, rademacherLaw_second_moment,
    rademacherLaw_subgaussian⟩

/-- Exactly the Section 3.8 full-block high-band logarithmic-potential
conclusion, specialized to a fixed real IID law. This is an explicit allowed
paper input, not a Lean axiom and not an assumption of a circle law. -/
structure Section3SubgaussianHighBandInput (μ : Measure ℝ) (c : ℝ≥0) : Prop where
  log_limit : IsRealSubgaussianAtom μ c →
    ∀ (W s : ℕ → ℕ), (∀ n, 0 < W n) → (∀ n, 0 < s n) →
      Tendsto W atTop atTop →
      ∀ ω : ℝ, 0 < ω → ω < 1 / 9 →
      (∀ᶠ n in atTop, (((s n + 3) * W n : ℕ) : ℝ) ^ (8 / 9 + ω) ≤ W n) →
      ∀ z : ℂ, TendstoInMeasure (Measure.infinitePi fun _ : ℕ => μ)
        (fun n sample => normalizedShiftLogDet
          (densityCyclicMatrix (W n) (s n)
            (physicalRowsFromSequence (W n) (s n) sample)) z)
        atTop (fun _ => circularLogPotential z)

/-- The true Bernoulli high-band branch, with its concrete atom certificate
fully discharged and only the permitted Proposition 3.8 retained. -/
theorem rademacher_high_band_log_potential
    (hSource : Section3SubgaussianHighBandInput rademacherLaw 1)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hs : ∀ n, 0 < s n)
    (hWtop : Tendsto W atTop atTop)
    (ω : ℝ) (hω : 0 < ω) (hωlt : ω < 1 / 9)
    (hband : ∀ᶠ n in atTop, (((s n + 3) * W n : ℕ) : ℝ) ^ (8 / 9 + ω) ≤ W n)
    (z : ℂ) :
    TendstoInMeasure rademacherSequenceLaw
      (fun n sample => normalizedShiftLogDet (rademacherMatrix (W n) (s n) sample) z)
      atTop (fun _ => circularLogPotential z) :=
  hSource.log_limit rademacherLaw_isRealSubgaussianAtom W s hW hs hWtop ω hω hωlt hband z

/-- A fully assembled caller-facing Bernoulli circular law on the high-band
subregime. This does not assert the remaining `W / log N → ∞` regime. -/
theorem rademacher_high_band_circular_law
    (hSource : Section3SubgaussianHighBandInput rademacherLaw 1)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hs : ∀ n, 0 < s n)
    (hWtop : Tendsto W atTop atTop)
    (ω : ℝ) (hω : 0 < ω) (hωlt : ω < 1 / 9)
    (hband : ∀ᶠ n in atTop, (((s n + 3) * W n : ℕ) : ℝ) ^ (8 / 9 + ω) ≤ W n)
    (f : BoundedContinuousFunction ℂ ℝ) :
    TendstoInMeasure rademacherSequenceLaw
      (fun n sample => TaoVuReplacement.realEsdTest (rademacherMatrix (W n) (s n) sample) f)
      atTop (fun _ => ∫ z, f z ∂circularMeasure) := by
  apply rademacher_circular_law_of_log_potential W s hW hWtop _ f
  exact ae_of_all _ (rademacher_high_band_log_potential hSource W s hW hs hWtop
    ω hω hωlt hband)

end BernoulliSection8
