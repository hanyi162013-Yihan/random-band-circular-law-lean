import BernoulliSection8.Section3GaussianLaw
import BernoulliSection8.Section3HighBand
import ShortRingAnchor.Proposition38.VerifiedGinibre

/-!
Section 8 now obtains its high-band anchor from the proved Section 3.8
BC12-free endpoint. This file retains only Proposition 3.2, Cook 1.12 and
the two BBV comparisons on the explicit arrays. The Ginibre law, negative
moments and finite formulas are proved, not fields of the public interface.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
noncomputable section
namespace BernoulliSection8.Section3Bridge
open BernoulliSection10 BernoulliSection10.SourceInputs
open BernoulliSection10.ProbabilityLimits ShortRingAnchor Arxiv2410V3

def momentBudget (A : Proposition38.Atom) (C : ℝ) : ℝ :=
  max C (sourceV3MomentBudget A.law circularGaussianPairLaw
    (fun x : ℝ => (x : ℂ)) gaussianAtom)

/-- The accepted upstream theorems of the concrete Section 3 implementation.
Cook 1.12 here is distinct from the Section 8 square-deformation Cook input.
Gaussian moments and all IID/model certificates are constructed, not fields. -/
structure UpstreamInputs (A : Proposition38.Atom) where
  comparisonConstant : ℝ
  proposition32 : ∀ z : ℂ, Proposition38.Proposition32Input (inputLaw A.law) A z
  cook112 : Proposition38.Cook112Input (inputLaw A.law) A
  bbvRing : ∀ (W s : ℕ) (hW : 0 < W) (z eta : ℂ), 0 < eta.im →
    CanonicalBBVAt (Proposition38.fullBlockV3Model hW (ringArray A ((s + 3) * W)))
      z eta (3 * (W : ℝ)) (momentBudget A comparisonConstant)
  bbvGinibre : ∀ (N : ℕ) (hN : 0 < N) (z eta : ℂ), 0 < eta.im →
    CanonicalBBVAt (denseModel A N hN) z eta (N : ℝ) (momentBudget A comparisonConstant)

/-- Match the ring comparison to the exact argument of Proposition 3.8. -/
theorem UpstreamInputs.ringComparison (A : Proposition38.Atom) (known : UpstreamInputs A)
    (W s : ℕ) (hW : 0 < W) (z eta : ℂ) (heta : 0 < eta.im) :
    CanonicalBBVAt (Proposition38.fullBlockV3Model hW (ringArray A ((s + 3) * W)))
      z eta (3 * (W : ℝ))
      (max known.comparisonConstant (sourceV3MomentBudget A.law circularGaussianPairLaw
        (fun x : ℝ => (x : ℂ)) gaussianAtom)) := by
  simpa only [momentBudget] using known.bbvRing W s hW z eta heta

/-- Unfold the dense model and moment budget once, outside the asymptotic assembly. -/
theorem UpstreamInputs.ginibreComparison (A : Proposition38.Atom) (known : UpstreamInputs A)
    (N : ℕ) (hN : 0 < N) (z eta : ℂ) (heta : 0 < eta.im) :
    CanonicalBBVAt
      (denseV3Model hN (denseAtom N) gaussianAtom gaussianAtom_moments (denseAtom_copies A N))
      z eta (N : ℝ)
      (max known.comparisonConstant (sourceV3MomentBudget A.law circularGaussianPairLaw
        (fun x : ℝ => (x : ℂ)) gaussianAtom)) := by
  simpa only [denseModel, momentBudget] using known.bbvGinibre N hN z eta heta

/-- Equality of the whole reference process, usable under singular-value predicates. -/
theorem normalizedDense_process_eq (N : ℕ → ℕ) :
    normalizedDenseMatrixProcess (fun n => denseAtom (N n)) =
      (fun n => circularGinibreMatrix (N n)) := by
  funext n sample
  exact normalizedDense_eq_circularGinibre N n sample

theorem input_log_convergence_iff_sequence (A : Proposition38.Atom)
    (W s : ℕ → ℕ) (z : ℂ) :
    ConvergesInProbability (inputLaw A.law)
      (fun n sample => normalizedShiftLogDet (profileMatrix (physicalProfile (W n) (s n)) sample) z)
      (circularLogPotential z) ↔
    TendstoInMeasure (Measure.infinitePi fun _ : ℕ => A.law)
      (fun n sample => normalizedShiftLogDet
        (densityCyclicMatrix (W n) (s n) (physicalRowsFromSequence (W n) (s n) sample)) z)
      atTop (fun _ => circularLogPotential z) := by
  have hid (W s : ℕ) (x : ℕ → ℝ) :
      normalizedShiftLogDet (densityCyclicMatrix W s (physicalRowsFromSequence W s x)) z =
        densityCyclicLogDet W s z (physicalRowsFromSequence W s x) /
          (((s + 3) * W : ℕ) : ℝ) := by
    unfold normalizedShiftLogDet densityCyclicLogDet
    rw [densityShiftedCyclicMatrix_eq_sub_scalar]
  have ht := tendstoInProbabilityTri_measurePreserving_iff
    (fun _ => (Measure.infinitePi fun _ : ℕ => A.law))
    (fun n => intervalRowsLaw (W n) (s n + 3) A.law)
    (fun n => physicalRowsFromSequence (W n) (s n))
    (fun n => physicalRowsFromSequence_measurePreserving A.law (W n) (s n))
    (fun n x => densityCyclicLogDet (W n) (s n) z x / (((s n + 3) * W n : ℕ) : ℝ))
    (fun n => (measurable_densityCyclicLogDet (W n) (s n) z).div_const _)
    (circularLogPotential z)
  rw [profile_log_converges_iff_physical_rows]
  simpa only [TendstoInProbabilityTri, tendstoInMeasure_iff_measureReal_norm,
    Real.norm_eq_abs, hid] using ht.symm

/-- The actual Section 3 theorem constructs the old internal interface.
Its proof calls `ShortRingAnchor.Proposition38.proposition38_withoutBC12` directly;
the Gaussian reference law is constructed, not supplied by the caller. -/
theorem highBandInput (A : Proposition38.Atom) (known : UpstreamInputs A) :
    Section3SubgaussianHighBandInput A.law A.parameter := by
  refine ⟨?_⟩
  intro _ W s hW hs hWtop omega homega homegaLt hband z
  have hNpos (k : ℕ) : 0 < (s k + 3) * W k := Nat.mul_pos (by omega) (hW k)
  have hN : Tendsto (fun k => (s k + 3) * W k) atTop atTop := by
    apply tendsto_atTop_mono (fun k => ?_) hWtop
    nlinarith [Nat.zero_le (s k), Nat.zero_le (W k)]
  have h := Proposition38.proposition38_withoutBC12
    (μ := inputLaw A.law) (νG := circularGaussianPairLaw) (W := W) (s := s) A hW hs
    (fun k => ringArray A ((s k + 3) * W k))
    (fun k => denseAtom ((s k + 3) * W k)) gaussianAtom gaussianAtom_moments
    (fun k => denseAtom_copies A ((s k + 3) * W k))
    (fun k => normalizedDense_hasGinibreLaw A _ k (hNpos k)) z omega known.comparisonConstant
    ⟨homega, homegaLt⟩ hN hWtop hband (known.proposition32 z) known.cook112
    (fun k eta heta => UpstreamInputs.ringComparison A known (W k) (s k) (hW k) z eta heta)
    (fun k eta heta => UpstreamInputs.ginibreComparison A known
      ((s k + 3) * W k) (hNpos k) z eta heta)
  apply (input_log_convergence_iff_sequence A W s z).1
  simpa only [Proposition38.Conclusion, ConvergesInProbability,
    fullBlockMatrix_eq_physical, ← densityCyclicMatrix_physicalRowsFromInput,
    physicalRowsFromInput] using h

end BernoulliSection8.Section3Bridge

namespace BernoulliSection8

def IsRealSubgaussianAtom.toSection3Atom {μ : Measure ℝ} {c : NNReal}
    (h : IsRealSubgaussianAtom μ c) : ShortRingAnchor.Proposition38.Atom where
  law := μ
  parameter := c
  probability := h.probability
  centered := h.centered
  second_moment := h.second_moment
  subgaussian := h.subgaussian

abbrev RademacherSection3UpstreamInputs :=
  Section3Bridge.UpstreamInputs rademacherLaw_isRealSubgaussianAtom.toSection3Atom

theorem rademacher_section3_input (known : RademacherSection3UpstreamInputs) :
    Section3SubgaussianHighBandInput rademacherLaw 1 :=
  Section3Bridge.highBandInput _ known

end BernoulliSection8
