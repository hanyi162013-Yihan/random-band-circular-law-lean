import BernoulliSection10Complex.BoundedDensity
import BernoulliSection10.Section3Inputs
import ShortRingAnchor.HermitizationCounting
import ShortRingAnchor.ShortRingModel
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProductMeasure

/-!
# Exact permitted Section 3 inputs, specialized to fixed planar-complex IID atoms

These are propositions supplied as theorem parameters, not axioms. The
variance-profile and scalar-indicator model definitions are literal. In
particular, the scalar anchor field does not assert a full-block result.
The probability space contains an independent circular Ginibre array so
that both applications of Lemma 3.4 use the same comparison array.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped BigOperators

noncomputable section

namespace BernoulliSection10Complex.SourceInputs

open ShortRingAnchor

abbrev InputSpace := (ℕ → ℂ) × (ℕ → ℝ × ℝ)

export BernoulliSection10.SourceInputs (circularGaussianPairLaw)

def inputLaw (μ : Measure ℂ) : Measure InputSpace :=
  (Measure.infinitePi fun _ : ℕ => μ).prod
    (Measure.infinitePi fun _ : ℕ => circularGaussianPairLaw)

instance inputLaw_isProbabilityMeasure (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (inputLaw μ) := by
  unfold inputLaw circularGaussianPairLaw
  infer_instance

export BernoulliSection10.SourceInputs (squareAtomIndex)

def profileMatrix {N : ℕ} (σ : Matrix (Fin N) (Fin N) ℝ) (ω : InputSpace) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (σ i j : ℂ) * ω.1 (squareAtomIndex i j)

def circularGinibreMatrix (N : ℕ) (ω : InputSpace) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ((ω.2 (squareAtomIndex i j)).1 +
    Complex.I * (ω.2 (squareAtomIndex i j)).2) / (Real.sqrt (N : ℝ) : ℂ)

export BernoulliSection10.SourceInputs
  (DoublyStochasticProfile maxEntryVariance effectiveBandwidth scalarCyclicDistance
   squaredEntryMass leastSingularValue hermitianIntervalCount mesoscopicGood scalarIndicatorProfile)

/-- Only the four cited Section 3 statements, with their model hypotheses.
All functions in these statements are the concrete definitions above. -/
structure Section3Inputs (μ : Measure ℂ) (L : ℝ) : Prop where
  leastSingularValue : IsBoundedDensityAtom μ L →
    ∀ (N W : ℕ → ℕ) (σ : ∀ n, Matrix (Fin (N n)) (Fin (N n)) ℝ),
    (∀ n, 0 < N n) → (∀ n, 0 < W n) → Tendsto N atTop atTop →
    (∀ n, DoublyStochasticProfile (σ n)) →
    ∀ χ κ c C Kz R : ℝ,
    0 < χ → 0 < κ → κ < χ / 4 → 0 < c → 0 < C → 0 < Kz → 0 < R →
    (∀ n, maxEntryVariance (σ n) ≤ C / W n) →
    (∀ n i j, scalarCyclicDistance i j ≤ W n → c / W n ≤ σ n i j ^ 2) →
    (∀ᶠ n in atTop, (N n : ℝ) ^ (1 / 2 + χ) ≤ W n) →
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n in atTop, ∀ z : ℂ, ‖z‖ ≤ Kz → ∀ t : ℝ, 0 < t →
      (inputLaw μ) {ω | SourceInputs.leastSingularValue (profileMatrix (σ n) ω - z • 1) ≤
        t * Real.exp (-((N n : ℝ) ^ (3 * κ) * N n / W n)) ∧
        Real.sqrt (squaredEntryMass (profileMatrix (σ n) ω)) ≤ R * Real.sqrt (N n : ℝ)} ≤
      ENNReal.ofReal (D * t + Real.exp (-((N n : ℝ) ^ (1 + κ / 4))))
  mesoscopicCounting : IsBoundedDensityAtom μ L →
    Integrable (fun x : ℂ => ‖x‖ ^ 3) μ →
    ∀ (N : ℕ → ℕ) (σ : ∀ n, Matrix (Fin (N n)) (Fin (N n)) ℝ),
    (∀ n, 0 < N n) → Tendsto N atTop atTop →
    (∀ n, DoublyStochasticProfile (σ n)) →
    ∀ c : ℝ, 0 < c → (∀ᶠ n in atTop, (N n : ℝ) ^ c ≤ effectiveBandwidth (σ n)) →
    ∀ z : ℂ, ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      (inputLaw μ) {ω | ¬mesoscopicGood (profileMatrix (σ n) ω - z • 1)
        (effectiveBandwidth (σ n) ^ (-1 / 8 : ℝ) * (N n : ℝ) ^ τ) C} ≤
        ENNReal.ofReal ((N n : ℝ) ^ (-10 : ℝ))
  localBulk : IsBoundedDensityAtom μ L → Integrable (fun x : ℂ => ‖x‖ ^ 3) μ →
    ∀ (N : ℕ → ℕ) (σ : ∀ n, Matrix (Fin (N n)) (Fin (N n)) ℝ),
    (∀ n, 0 < N n) → Tendsto N atTop atTop →
    (∀ n, DoublyStochasticProfile (σ n)) →
    ∀ c : ℝ, 0 < c → (∀ᶠ n in atTop, (N n : ℝ) ^ c ≤ effectiveBandwidth (σ n)) →
    ∀ z : ℂ, ∀ R : ℝ, 0 ≤ R → ∃ ζ : ℝ, 0 < ζ ∧
      LocalBulkComparisonInput (inputLaw μ)
        (fun n ω (i : Fin (N n)) => shiftedSingularValueFamily (profileMatrix (σ n) ω) z i ^ 2)
        (fun n ω (i : Fin (N n)) => shiftedSingularValueFamily (circularGinibreMatrix (N n) ω) z i ^ 2)
        R (fun n => (N n : ℝ) ^ (-ζ))
  scalarAnchor : IsBoundedDensityAtom μ L → Integrable (fun x : ℂ => ‖x‖ ^ 3) μ →
    ∀ (N W : ℕ → ℕ) (c0 C0 : ℝ) (q : ∀ n, AdmissibleWeights (W n) c0 C0)
      (hfit : ∀ n, 2 * W n + 1 ≤ N n),
    (∀ n, 0 < N n) → Tendsto N atTop atTop → Tendsto W atTop atTop →
    ∀ ω : ℝ, 0 < ω → ω < 1 / 9 →
    (∀ᶠ n in atTop, (N n : ℝ) ^ (8 / 9 + ω) ≤ W n) →
    ∀ z : ℂ, ConvergesInProbability (inputLaw μ)
      (fun n sample => normalizedShiftLogDet
        (profileMatrix (scalarIndicatorProfile (q n) (hfit n)) sample) z)
      (circularLogPotential z)

end BernoulliSection10Complex.SourceInputs
