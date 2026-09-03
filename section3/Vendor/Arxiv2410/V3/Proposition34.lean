/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Proposition34.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.ProbabilityEvent
import Vendor.Arxiv2410.V3.External.VanHandel
import Vendor.Arxiv2410.V3.Model
import Vendor.Arxiv2410.V3.RandomModel
import Vendor.Arxiv2410.V3.TraceComparison
import Vendor.Arxiv2410.V3.VarianceProfile

/-!
# Conditional reconstruction of v3 Proposition 3.4

The theorems below prove every deterministic inference in formulas (3.11), (3.9), and (3.10).
The heavy analytic statements are explicit structure-valued arguments from `External/`; no
custom axiom or unproved theorem is declared.
-/

namespace Arxiv2410V3

open MeasureTheory

/-- The four named inputs to v3 formula (3.11), bundled without asserting their existence. -/
structure Formula311Inputs
    {Omega : Type*}
    (good : Set Omega) (trace : Omega → ℂ)
    (expectedTrace expectedGaussianTrace expectedCircularGaussianTrace freeTrace : ℂ)
    (n B v C CD : ℝ) : Prop where
  scalarConcentration : ∀ omega ∈ good,
    ‖trace omega - expectedTrace‖ ≤
      CD * Real.sqrt (Real.log n) / (Real.sqrt n * v)
  traceUniversality : External.BVHRemark613UnboundedExtensionHypothesis
    expectedTrace expectedGaussianTrace v (1 / Real.sqrt B) C
  diagonalCorrection :
    ‖expectedGaussianTrace - expectedCircularGaussianTrace‖ ≤
      C * Real.sqrt (Real.log n) / (Real.sqrt B * v ^ 2)
  gaussianFree : External.BBVTheorem28GaussianFreeHypothesis
    expectedCircularGaussianTrace freeTrace B v C

/-- v3 formula (3.11), pointwise on the common good event. -/
theorem proposition34_formula311_from_interfaces
    {Omega : Type*}
    {good : Set Omega} {trace : Omega → ℂ}
    {expectedTrace expectedGaussianTrace expectedCircularGaussianTrace freeTrace : ℂ}
    {n B v C CD : ℝ}
    (inputs : Formula311Inputs good trace expectedTrace expectedGaussianTrace
      expectedCircularGaussianTrace freeTrace n B v C CD)
    {omega : Omega} (homega : omega ∈ good) :
    ‖trace omega - freeTrace‖ ≤ formula311Error n B v C CD := by
  apply formula311_of_four_inputs
    (em := expectedTrace) (emG := expectedGaussianTrace)
    (emGo := expectedCircularGaussianTrace)
  · exact inputs.scalarConcentration omega homega
  · have h := inputs.traceUniversality.estimate
    simpa only [div_eq_mul_inv, one_mul, mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
  · exact inputs.diagonalCorrection
  · exact inputs.gaussianFree.estimate

/-- A precise finite-`n` conditional form of v3 formula (3.9).

Unlike the prose statement, the exponent is outside the sample quantifier and the
`n`-large-enough work is carried by an explicit proved rate certificate.
-/
def Proposition34Formula39Conclusion
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (good : Set Omega)
    (trace : Omega → ℂ) (freeTrace : ℂ) (n : ℝ) : Prop :=
  ∃ exponent : ℝ, 0 < exponent ∧
    ProbabilityAtLeast mu good (1 - n ^ (-10 : ℤ)) ∧
    ∀ omega ∈ good,
      ‖trace omega - freeTrace‖ ≤ Real.rpow n (-exponent)

/-- v3 (3.11) plus the rate certificate imply v3 (3.9), preserving the same event and its
probability lower bound. -/
theorem proposition34_formula39_from_interfaces
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {good : Set Omega} {trace : Omega → ℂ}
    {expectedTrace expectedGaussianTrace expectedCircularGaussianTrace freeTrace : ℂ}
    {n B v C CD : ℝ}
    (inputs : Formula311Inputs good trace expectedTrace expectedGaussianTrace
      expectedCircularGaussianTrace freeTrace n B v C CD)
    (hprob : ProbabilityAtLeast mu good (1 - n ^ (-10 : ℤ)))
    (rate : PolynomialRateCertificate n (formula311Error n B v C CD)) :
    Proposition34Formula39Conclusion mu good trace freeTrace n := by
  refine ⟨rate.exponent, rate.exponent_pos, hprob, ?_⟩
  intro omega homega
  exact formula39_of_formula311 (trace omega) freeTrace
    (proposition34_formula311_from_interfaces inputs homega) rate

/-- v3 Proposition 3.4, formula (3.9), specialized to the paper's actual random-matrix
model and actual normalized Green-function trace.

The model, exact bandwidth identity, bandwidth growth, and eta-scale assumptions are all
present explicitly.  The only remaining inputs are the named comparison estimates, their
common good-event probability, and a checked finite-`n` rate certificate.
-/
theorem proposition34_formula39_for_v3_model
    {n : ℕ} {Omega OmegaXi : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    {B epsilon cPrime : ℝ} {z eta : ℂ}
    (_hbandwidth : IsBandwidth model.profile B)
    (_hgrowth : BandwidthGrowthAssumption n B epsilon)
    (_hetaScale : EtaScaleAssumption n B cPrime eta)
    {good : Set Omega}
    {expectedTrace expectedGaussianTrace expectedCircularGaussianTrace freeTrace : ℂ}
    {C CD : ℝ}
    (inputs : Formula311Inputs good
      (fun omega => stieltjesTrace (model.matrix omega) z eta)
      expectedTrace expectedGaussianTrace expectedCircularGaussianTrace freeTrace
      n B eta.im C CD)
    (hprob : ProbabilityAtLeast mu good (1 - (n : ℝ) ^ (-10 : ℤ)))
    (rate : PolynomialRateCertificate n (formula311Error n B eta.im C CD)) :
    Proposition34Formula39Conclusion mu good
      (fun omega => stieltjesTrace (model.matrix omega) z eta) freeTrace n := by
  exact proposition34_formula39_from_interfaces inputs hprob rate

/-- v3 formula (3.10) at a fixed parameter, fully deduced from (3.9) and the free-transform
bound.  Uniformity in `eta` is a separate net/continuity interface, as it is in the paper. -/
theorem proposition34_formula310_at_point
    {Omega : Type*} {good : Set Omega} {trace : Omega → ℂ} {freeTrace : ℂ}
    {n exponent Cfree : ℝ}
    (hcomparison : ∀ omega ∈ good,
      ‖trace omega - freeTrace‖ ≤ Real.rpow n (-exponent))
    (hfree : ‖freeTrace‖ ≤ Cfree)
    (hrate_one : Real.rpow n (-exponent) ≤ 1)
    {omega : Omega} (homega : omega ∈ good) :
    ‖trace omega‖ ≤ Cfree + 1 := by
  exact trace_bound_of_comparison (trace omega) freeTrace
    (hcomparison omega homega) hfree hrate_one

/-- The exact uniform `eta`-domain appearing in the final clause of v3 Proposition 3.4. -/
def Proposition34EtaDomain (n : ℕ) (B cPrime : ℝ) (eta : ℂ) : Prop :=
  InUpperHalfPlane eta ∧ ‖eta‖ ≤ 5 ∧
    Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n cPrime ≤ eta.im

/-- The common uniform good event needed to pass from v3 (3.10) to Corollary 3.5. -/
def Proposition34UniformTraceGood
    {Omega : Type*} (trace : Omega → ℂ → ℂ)
    (n : ℕ) (B cPrime C1 : ℝ) : Set Omega :=
  {omega | ∀ eta, Proposition34EtaDomain n B cPrime eta → ‖trace omega eta‖ ≤ C1}

/-- The uniform deterministic closure from v3 formula (3.9) to formula (3.10), on one
common event.  Constructing this common event from fixed-`eta` events is carried out by the
explicit finite-net and continuity theorems in `ConcreteEtaNet.lean`.
-/
theorem proposition34_formula310_uniform_event_subset
    {Omega : Type*} {good : Set Omega}
    {trace : Omega → ℂ → ℂ} {freeTrace : ℂ → ℂ}
    {n : ℕ} {B cPrime delta Cfree : ℝ}
    (hcomparison : ∀ omega ∈ good, ∀ eta,
      Proposition34EtaDomain n B cPrime eta →
        ‖trace omega eta - freeTrace eta‖ ≤ delta)
    (hfree : ∀ eta, Proposition34EtaDomain n B cPrime eta →
      ‖freeTrace eta‖ ≤ Cfree)
    (hdelta : delta ≤ 1) :
    good ⊆ Proposition34UniformTraceGood trace n B cPrime (Cfree + 1) := by
  intro omega homega eta heta
  exact trace_bound_of_comparison (trace omega eta) (freeTrace eta)
    (hcomparison omega homega eta heta) (hfree eta heta) hdelta

/-- Probability-preserving version of the preceding v3 `(3.9) => (3.10)` step: set inclusion
alone transfers the lower bound on the common event, with no hidden measurability assumption.
-/
theorem proposition34_formula310_probability
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {good : Set Omega}
    {trace : Omega → ℂ → ℂ} {freeTrace : ℂ → ℂ}
    {n : ℕ} {B cPrime delta Cfree p : ℝ}
    (hprob : ProbabilityAtLeast mu good p)
    (hcomparison : ∀ omega ∈ good, ∀ eta,
      Proposition34EtaDomain n B cPrime eta →
        ‖trace omega eta - freeTrace eta‖ ≤ delta)
    (hfree : ∀ eta, Proposition34EtaDomain n B cPrime eta →
      ‖freeTrace eta‖ ≤ Cfree)
    (hdelta : delta ≤ 1) :
    ProbabilityAtLeast mu
      (Proposition34UniformTraceGood trace n B cPrime (Cfree + 1)) p := by
  exact hprob.trans (measure_mono
    (proposition34_formula310_uniform_event_subset hcomparison hfree hdelta))

end Arxiv2410V3

