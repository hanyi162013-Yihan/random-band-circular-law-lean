/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/DiagonalCorrection.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.ResolventPerturbation
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Expected diagonal-pseudovariance correction from an `L¹` perturbation bound

In proof step (4) of arXiv:2410.16457v3, Proposition 3.4, the paper passes from
the samplewise resolvent identity

`|m_z^G(eta) - m_z^{G,o}(eta)| <= ‖Delta‖ / (Im eta)^2`

to the corresponding estimate between expectations.  This file proves that
passage.  Consequently the old trace-level interface
the trace inequality is derived from the strictly lower-level input `E ‖Delta‖ <= K`.

No distributional assertion about the Gaussian diagonal is made here.  The
only remaining probabilistic input is a bound on the first moment of the
actual Hermitization perturbation.
-/

namespace Arxiv2410V3

open Matrix Complex MeasureTheory
open scoped Matrix.Norms.L2Operator

section GenericIntegralPassage

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {mu : Measure Omega}

/-- Bochner integration turns an almost-everywhere norm comparison into a
comparison of the two expectations.  This is the abstract expectation step
used below for v3 proof step (4). -/
theorem norm_integral_sub_integral_le_of_ae_norm_sub_le
    {f g : Omega → E} {envelope : Omega → ℝ}
    (hf : Integrable f mu) (hg : Integrable g mu)
    (henvelope : Integrable envelope mu)
    (hpointwise : ∀ᵐ omega ∂mu, ‖f omega - g omega‖ ≤ envelope omega) :
    ‖(∫ omega, f omega ∂mu) - ∫ omega, g omega ∂mu‖ ≤
      ∫ omega, envelope omega ∂mu := by
  rw [← integral_sub hf hg]
  exact norm_integral_le_of_norm_le henvelope hpointwise

end GenericIntegralPassage

section StieltjesSpecialization

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
  {n : ℕ} [NeZero n]

/-- v3 proof step (4), with an arbitrary integrable envelope for the actual
Hermitization perturbation.  The resolvent estimate is proved pointwise in
`ResolventPerturbation.lean`; only its integration is performed here. -/
theorem norm_expected_stieltjesTrace_sub_le_of_ae_hermitization_envelope
    (X Xo : Omega → Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) {eta : ℂ} (heta : 0 < eta.im)
    {envelope : Omega → ℝ}
    (hX : Integrable (fun omega => stieltjesTrace (X omega) z eta) mu)
    (hXo : Integrable (fun omega => stieltjesTrace (Xo omega) z eta) mu)
    (henvelope : Integrable envelope mu)
    (hperturbation : ∀ᵐ omega ∂mu,
      ‖hermitization (X omega) z - hermitization (Xo omega) z‖ ≤
        envelope omega) :
    ‖(∫ omega, stieltjesTrace (X omega) z eta ∂mu) -
        ∫ omega, stieltjesTrace (Xo omega) z eta ∂mu‖ ≤
      (∫ omega, envelope omega ∂mu) / eta.im ^ 2 := by
  let scaledEnvelope : Omega → ℝ :=
    fun omega => envelope omega / eta.im ^ 2
  have hscaled : Integrable scaledEnvelope mu := by
    exact henvelope.div_const (eta.im ^ 2)
  have htrace : ∀ᵐ omega ∂mu,
      ‖stieltjesTrace (X omega) z eta - stieltjesTrace (Xo omega) z eta‖ ≤
        scaledEnvelope omega := by
    filter_upwards [hperturbation] with omega homega
    exact (norm_stieltjesTrace_sub_le (X omega) (Xo omega) z heta).trans
      (div_le_div_of_nonneg_right homega (sq_nonneg eta.im))
  calc
    ‖(∫ omega, stieltjesTrace (X omega) z eta ∂mu) -
        ∫ omega, stieltjesTrace (Xo omega) z eta ∂mu‖ ≤
        ∫ omega, scaledEnvelope omega ∂mu :=
      norm_integral_sub_integral_le_of_ae_norm_sub_le hX hXo hscaled htrace
    _ = (∫ omega, envelope omega ∂mu) / eta.im ^ 2 := by
      exact integral_div (eta.im ^ 2) envelope

/-- The most direct low-level formulation of the expected correction: a first
moment bound for the actual Hermitization difference implies the expected
Stieltjes-transform bound with the paper's `v⁻²` factor. -/
theorem norm_expected_stieltjesTrace_sub_le_of_integral_hermitization_norm
    (X Xo : Omega → Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) {eta : ℂ} (heta : 0 < eta.im)
    {K : ℝ}
    (hX : Integrable (fun omega => stieltjesTrace (X omega) z eta) mu)
    (hXo : Integrable (fun omega => stieltjesTrace (Xo omega) z eta) mu)
    (hDelta : Integrable (fun omega =>
      ‖hermitization (X omega) z - hermitization (Xo omega) z‖) mu)
    (hDeltaMean : (∫ omega,
      ‖hermitization (X omega) z - hermitization (Xo omega) z‖ ∂mu) ≤ K) :
    ‖(∫ omega, stieltjesTrace (X omega) z eta ∂mu) -
        ∫ omega, stieltjesTrace (Xo omega) z eta ∂mu‖ ≤
      K / eta.im ^ 2 := by
  calc
    ‖(∫ omega, stieltjesTrace (X omega) z eta ∂mu) -
        ∫ omega, stieltjesTrace (Xo omega) z eta ∂mu‖ ≤
        (∫ omega,
          ‖hermitization (X omega) z - hermitization (Xo omega) z‖ ∂mu) /
          eta.im ^ 2 :=
      norm_expected_stieltjesTrace_sub_le_of_ae_hermitization_envelope
        X Xo z heta hX hXo hDelta (Filter.Eventually.of_forall fun _ => le_rfl)
    _ ≤ K / eta.im ^ 2 :=
      div_le_div_of_nonneg_right hDeltaMean (sq_nonneg eta.im)

/-- A transparent low-level certificate for v3 proof step (4).  Unlike the old
trace-level interface, this structure mentions the coupled random matrices
and asks only for integrability and an `L¹` operator-norm estimate on their
Hermitization difference. -/
structure DiagonalPseudovarianceL1Input
    (mu : Measure Omega)
    (X Xo : Omega → Matrix (Fin n) (Fin n) ℂ)
    (z eta : ℂ) (K : ℝ) : Prop where
  trace_integrable : Integrable (fun omega => stieltjesTrace (X omega) z eta) mu
  circular_trace_integrable :
    Integrable (fun omega => stieltjesTrace (Xo omega) z eta) mu
  perturbation_norm_integrable : Integrable (fun omega =>
    ‖hermitization (X omega) z - hermitization (Xo omega) z‖) mu
  perturbation_norm_mean_le : (∫ omega,
    ‖hermitization (X omega) z - hermitization (Xo omega) z‖ ∂mu) ≤ K

/-- Construct the direct trace-level inequality from the new `L¹` perturbation input.
This theorem is the machine-checked replacement for
the sentence "taking expectations in (3.8)" in v3 proof step (4). -/
theorem diagonalPseudovarianceCorrectionHypothesis_of_l1Input
    (X Xo : Omega → Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) {eta : ℂ} (heta : 0 < eta.im) {K : ℝ}
    (input : DiagonalPseudovarianceL1Input mu X Xo z eta K) :
    ‖(∫ omega, stieltjesTrace (X omega) z eta ∂mu) -
        ∫ omega, stieltjesTrace (Xo omega) z eta ∂mu‖ ≤
      K / eta.im ^ 2 := by
  exact norm_expected_stieltjesTrace_sub_le_of_integral_hermitization_norm
    X Xo z heta input.trace_integrable input.circular_trace_integrable
    input.perturbation_norm_integrable input.perturbation_norm_mean_le

/-- The exact scale in v3 formula (3.11): if
`E ‖Delta‖ <= C sqrt(log n) / sqrt(B)`, the expected correction is at most
`C sqrt(log n) / (sqrt(B) v²)`. -/
theorem diagonalPseudovarianceCorrectionHypothesis_v3_of_l1Input
    (X Xo : Omega → Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) {eta : ℂ} (heta : 0 < eta.im)
    {N B C : ℝ}
    (input : DiagonalPseudovarianceL1Input mu X Xo z eta
      (C * Real.sqrt (Real.log N) / Real.sqrt B)) :
    ‖(∫ omega, stieltjesTrace (X omega) z eta ∂mu) -
        ∫ omega, stieltjesTrace (Xo omega) z eta ∂mu‖ ≤
      C * Real.sqrt (Real.log N) / (Real.sqrt B * eta.im ^ 2) := by
  have h := diagonalPseudovarianceCorrectionHypothesis_of_l1Input
    X Xo z heta input
  convert h using 1
  field_simp

end StieltjesSpecialization

end Arxiv2410V3

