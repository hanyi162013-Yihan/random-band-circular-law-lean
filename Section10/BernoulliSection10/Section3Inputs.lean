import BernoulliSection10.BoundedDensity
import ShortRingAnchor.HermitizationCounting
import ShortRingAnchor.ShortRingModel
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProductMeasure

/-!
# Exact permitted Section 3 inputs, specialized to fixed real IID atoms

These are propositions supplied as theorem parameters, not axioms. The
variance-profile and scalar-indicator model definitions are literal. In
particular, the scalar anchor field does not assert a full-block result.
The probability space contains an independent circular Ginibre array so
that both applications of Lemma 3.4 use the same comparison array.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped BigOperators

noncomputable section

namespace BernoulliSection10.SourceInputs

open ShortRingAnchor

abbrev InputSpace := (ℕ → ℝ) × (ℕ → ℝ × ℝ)

def circularGaussianPairLaw : Measure (ℝ × ℝ) :=
  (gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))

instance circularGaussianPairLaw_isProbabilityMeasure :
    IsProbabilityMeasure circularGaussianPairLaw := by
  unfold circularGaussianPairLaw
  infer_instance

def inputLaw (μ : Measure ℝ) : Measure InputSpace :=
  (Measure.infinitePi fun _ : ℕ => μ).prod
    (Measure.infinitePi fun _ : ℕ => circularGaussianPairLaw)

instance inputLaw_isProbabilityMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (inputLaw μ) := by
  unfold inputLaw circularGaussianPairLaw
  infer_instance

def squareAtomIndex {N : ℕ} (i j : Fin N) : ℕ :=
  (finProdFinEquiv (i, j)).val

def profileMatrix {N : ℕ} (σ : Matrix (Fin N) (Fin N) ℝ) (ω : InputSpace) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (σ i j * ω.1 (squareAtomIndex i j) : ℝ)

def circularGinibreMatrix (N : ℕ) (ω : InputSpace) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ((ω.2 (squareAtomIndex i j)).1 +
    Complex.I * (ω.2 (squareAtomIndex i j)).2) / (Real.sqrt (N : ℝ) : ℂ)

structure DoublyStochasticProfile {N : ℕ} (σ : Matrix (Fin N) (Fin N) ℝ) : Prop where
  nonnegative : ∀ i j, 0 ≤ σ i j
  row : ∀ i, ∑ j, σ i j ^ 2 = 1
  column : ∀ j, ∑ i, σ i j ^ 2 = 1

def maxEntryVariance {N : ℕ} (σ : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  (((Finset.univ.sup (fun p : Fin N × Fin N =>
    (⟨σ p.1 p.2 ^ 2, sq_nonneg _⟩ : NNReal))) : NNReal) : ℝ)

def effectiveBandwidth {N : ℕ} (σ : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  (maxEntryVariance σ)⁻¹

def scalarCyclicDistance {N : ℕ} (i j : Fin N) : ℕ :=
  min (i.val - j.val + (j.val - i.val)) (N - (i.val - j.val + (j.val - i.val)))

def squaredEntryMass {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

def leastSingularValue {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  matrixSingularValue A (N - 1)

def hermitianIntervalCount {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (a b : ℝ) : ℕ :=
  (Finset.univ.filter (fun i : HermitizationIndex N =>
    a ≤ hermitizationEigenvalue A i ∧ hermitizationEigenvalue A i ≤ b)).card

def mesoscopicGood {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (threshold C : ℝ) : Prop :=
  ∀ a b : ℝ, -5 ≤ a → a ≤ b → b ≤ 5 → threshold ≤ b - a →
    (hermitianIntervalCount A a b : ℝ) ≤ C * N * (b - a)

/-- The scalar indicator profile with the source's admissible weights. -/
def scalarIndicatorProfile {N W : ℕ} {c0 C0 : ℝ}
    (q : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ N) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∑ a : BandOffset W,
    if cyclicColumn hfit i a = j then Real.sqrt (q.q a) else 0

/-- Only the four cited Section 3 statements, with their model hypotheses.
All functions in these statements are the concrete definitions above. -/
structure Section3Inputs (μ : Measure ℝ) (L : ℝ) : Prop where
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
    Integrable (fun x : ℝ => |x| ^ 3) μ →
    ∀ (N : ℕ → ℕ) (σ : ∀ n, Matrix (Fin (N n)) (Fin (N n)) ℝ),
    (∀ n, 0 < N n) → Tendsto N atTop atTop →
    (∀ n, DoublyStochasticProfile (σ n)) →
    ∀ c : ℝ, 0 < c → (∀ᶠ n in atTop, (N n : ℝ) ^ c ≤ effectiveBandwidth (σ n)) →
    ∀ z : ℂ, ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      (inputLaw μ) {ω | ¬mesoscopicGood (profileMatrix (σ n) ω - z • 1)
        (effectiveBandwidth (σ n) ^ (-1 / 8 : ℝ) * (N n : ℝ) ^ τ) C} ≤
        ENNReal.ofReal ((N n : ℝ) ^ (-10 : ℝ))
  localBulk : IsBoundedDensityAtom μ L → Integrable (fun x : ℝ => |x| ^ 3) μ →
    ∀ (N : ℕ → ℕ) (σ : ∀ n, Matrix (Fin (N n)) (Fin (N n)) ℝ),
    (∀ n, 0 < N n) → Tendsto N atTop atTop →
    (∀ n, DoublyStochasticProfile (σ n)) →
    ∀ c : ℝ, 0 < c → (∀ᶠ n in atTop, (N n : ℝ) ^ c ≤ effectiveBandwidth (σ n)) →
    ∀ z : ℂ, ∀ R : ℝ, 0 ≤ R → ∃ ζ : ℝ, 0 < ζ ∧
      LocalBulkComparisonInput (inputLaw μ)
        (fun n ω (i : Fin (N n)) => shiftedSingularValueFamily (profileMatrix (σ n) ω) z i ^ 2)
        (fun n ω (i : Fin (N n)) => shiftedSingularValueFamily (circularGinibreMatrix (N n) ω) z i ^ 2)
        R (fun n => (N n : ℝ) ^ (-ζ))
  scalarAnchor : IsBoundedDensityAtom μ L → Integrable (fun x : ℝ => |x| ^ 3) μ →
    ∀ (N W : ℕ → ℕ) (c0 C0 : ℝ) (q : ∀ n, AdmissibleWeights (W n) c0 C0)
      (hfit : ∀ n, 2 * W n + 1 ≤ N n),
    (∀ n, 0 < N n) → Tendsto N atTop atTop → Tendsto W atTop atTop →
    ∀ ω : ℝ, 0 < ω → ω < 1 / 9 →
    (∀ᶠ n in atTop, (N n : ℝ) ^ (8 / 9 + ω) ≤ W n) →
    ∀ z : ℂ, ConvergesInProbability (inputLaw μ)
      (fun n sample => normalizedShiftLogDet
        (profileMatrix (scalarIndicatorProfile (q n) (hfit n)) sample) z)
      (circularLogPotential z)

end BernoulliSection10.SourceInputs
