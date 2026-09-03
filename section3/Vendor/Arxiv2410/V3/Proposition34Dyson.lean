/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Proposition34Dyson.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.FixedZImaginaryBound
import Vendor.Arxiv2410.V3.FreeDysonExistence
import Vendor.Arxiv2410.V3.Proposition34

/-!
# Proposition 3.4 with the free-transform bound discharged internally

These are the deterministic `(3.9) ⇒ (3.10)` bridges for the canonical solution of the
scalar Dyson equation constructed in `FreeDysonExistence.lean`.  They replace the former
external free-Stieltjes bound by the proved estimate `|m_free| < 1`.
-/

namespace Arxiv2410V3

open MeasureTheory

/-- v3 formula (3.10) at one upper-half-plane parameter, with the free bound proved from
v3 (3.2)--(3.4).  The displayed constant is the explicit value `2`. -/
theorem proposition34_formula310_at_point_freeDyson
    {Omega : Type*} {good : Set Omega} {trace : Omega → ℂ}
    {n exponent : ℝ} {z eta : ℂ}
    (heta : 0 < eta.im)
    (hcomparison : ∀ omega ∈ good,
      ‖trace omega - freeDysonStieltjes z eta‖ ≤ Real.rpow n (-exponent))
    (hrate_one : Real.rpow n (-exponent) ≤ 1)
    {omega : Omega} (homega : omega ∈ good) :
    ‖trace omega‖ ≤ 2 := by
  have hfree : ‖freeDysonStieltjes z eta‖ ≤ 1 :=
    (freeDysonStieltjes_norm_lt_one z eta heta).le
  have h := proposition34_formula310_at_point
    hcomparison hfree hrate_one homega
  norm_num at h
  exact h

/-- Uniform deterministic closure from a comparison with the internally constructed free
Dyson transform.  No free-transform hypothesis remains. -/
theorem proposition34_formula310_uniform_event_subset_freeDyson
    {Omega : Type*} {good : Set Omega}
    {trace : Omega → ℂ → ℂ}
    {n : ℕ} {B cPrime delta : ℝ} {z : ℂ}
    (hcomparison : ∀ omega ∈ good, ∀ eta,
      Proposition34EtaDomain n B cPrime eta →
        ‖trace omega eta - freeDysonStieltjes z eta‖ ≤ delta)
    (hdelta : delta ≤ 1) :
    good ⊆ Proposition34UniformTraceGood trace n B cPrime 2 := by
  have hfree : ∀ eta, Proposition34EtaDomain n B cPrime eta →
      ‖freeDysonStieltjes z eta‖ ≤ 1 := by
    intro eta heta
    exact (freeDysonStieltjes_norm_lt_one z eta heta.1).le
  have h := proposition34_formula310_uniform_event_subset
    hcomparison hfree hdelta
  norm_num at h
  exact h

/-- Probability-preserving v3 formula (3.10), now with only a comparison event as input. -/
theorem proposition34_formula310_probability_freeDyson
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {good : Set Omega}
    {trace : Omega → ℂ → ℂ}
    {n : ℕ} {B cPrime delta p : ℝ} {z : ℂ}
    (hprob : ProbabilityAtLeast mu good p)
    (hcomparison : ∀ omega ∈ good, ∀ eta,
      Proposition34EtaDomain n B cPrime eta →
        ‖trace omega eta - freeDysonStieltjes z eta‖ ≤ delta)
    (hdelta : delta ≤ 1) :
    ProbabilityAtLeast mu
      (Proposition34UniformTraceGood trace n B cPrime 2) p := by
  exact hprob.trans (measure_mono
    (proposition34_formula310_uniform_event_subset_freeDyson hcomparison hdelta))

/-- The exact imaginary-part comparison used in the Poisson-kernel proof of v3
Corollary 3.5.  The free term contributes at most `1`. -/
theorem trace_im_le_one_add_of_freeDyson_comparison
    (m : ℂ) {z eta : ℂ} {delta : ℝ}
    (heta : 0 < eta.im)
    (hcomparison : ‖m - freeDysonStieltjes z eta‖ ≤ delta) :
    m.im ≤ 1 + delta := by
  exact im_le_of_norm_sub_le m (freeDysonStieltjes z eta)
    hcomparison (freeDysonStieltjes_im_le_one z eta heta)

end Arxiv2410V3

