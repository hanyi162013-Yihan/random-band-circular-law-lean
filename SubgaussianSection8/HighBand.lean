import SubgaussianSection8.SourceInputs
import SubgaussianSection8.CircularReduction

/-! The permitted Proposition 3.8, instantiated at the arbitrary fixed atom. -/
open Filter MeasureTheory Topology
noncomputable section
namespace SubgaussianSection8
open ShortRingAnchor BernoulliSection10 BernoulliSection10.DiskReference TaoVuReplacement

theorem high_band_log_potential
    (A : Atom) (hSource : Section3Input A)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hs : ∀ n, 0 < s n)
    (hWtop : Tendsto W atTop atTop)
    (ω : ℝ) (hω : 0 < ω) (hωlt : ω < 1 / 9)
    (hband : ∀ᶠ n in atTop, (((s n + 3) * W n : ℕ) : ℝ) ^ (8 / 9 + ω) ≤ W n)
    (z : ℂ) :
    TendstoInMeasure (sequenceLaw A)
      (fun n sample => normalizedShiftLogDet (matrix (W n) (s n) sample) z)
      atTop (fun _ => circularLogPotential z) :=
  hSource.log_limit A.section3Atom W s hW hs hWtop ω hω hωlt hband z

theorem high_band_circular_law
    (A : Atom) (hSource : Section3Input A)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hs : ∀ n, 0 < s n)
    (hWtop : Tendsto W atTop atTop)
    (ω : ℝ) (hω : 0 < ω) (hωlt : ω < 1 / 9)
    (hband : ∀ᶠ n in atTop, (((s n + 3) * W n : ℕ) : ℝ) ^ (8 / 9 + ω) ≤ W n)
    (f : BoundedContinuousFunction ℂ ℝ) :
    TendstoInMeasure (sequenceLaw A)
      (fun n sample => realEsdTest (matrix (W n) (s n) sample) f)
      atTop (fun _ => ∫ z, f z ∂circularMeasure) := by
  apply circular_law_of_log_potential A W s hW hWtop _ f
  exact ae_of_all _ (high_band_log_potential A hSource W s hW hs hWtop ω hω hωlt hband)

end SubgaussianSection8
