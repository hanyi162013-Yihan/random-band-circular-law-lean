import ShortRingAnchor.BC12.GinibreKernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Finite-dimensional Ginibre formula interfaces

The generic analytic route is expressed using these exact formula records.
`VerifiedKernel.lean` and `GaussianMatrixLawBridge.lean` now construct them
from proved Gaussian-entry theorems. The BC12-free proposition endpoints
do not take these records as hypotheses. Nothing in the records
asserts a circular law, a limit, a tail bound, or a BC12 conclusion.

The formulas are the integrated one- and two-point correlation formulas
of BC12 Theorem 3.3, with the Gaussian weight absorbed into the kernel and
eigenvalues divided by `sqrt n`.  The projection formula is the integrated
orthogonality identity for that same finite-rank kernel.  Integrability
clauses make the domains of the integral identities explicit; Lean's total
Bochner integral is not used to pretend a divergent integral is finite.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace ShortRingAnchor.BC12

/-- The variance-normalized complex Ginibre correlation kernel, relative
to planar Lebesgue measure.  Its diagonal is `n * rho_n`. -/
def ginibreKernel (n : ℕ) (w v : ℂ) : ℂ :=
  (((n : ℝ) / Real.pi *
    Real.exp (-((n : ℝ) * (‖w‖ ^ 2 + ‖v‖ ^ 2)) / 2) : ℝ) : ℂ) *
      ∑ k ∈ Finset.range n,
        (((n : ℂ) * w * star v) ^ k) / (Nat.factorial k : ℂ)

/-- Squared kernel on two complex coordinates. -/
def ginibreKernelWeight (n : ℕ) (wv : ℂ × ℂ) : ℝ :=
  ‖ginibreKernel n wv.1 wv.2‖ ^ 2

/-- Normalized eigenvalue linear statistic; eigenvalues need not be
independent and no such assumption is made. -/
def eigenvalueStatistic {Omega : Type*} {n : ℕ}
    (eigenvalue : Omega → Fin n → ℂ) (f : ℂ → ℝ) (sample : Omega) : ℝ :=
  (∑ i, f (eigenvalue sample i)) / (n : ℝ)

/-- Exact integral interface, constructed by `verifiedGinibreProjection`.
This is the symmetric weighted form of
`integral |K_n(w,v)|² dv = n * rho_n(w)`.
It is a finite-dimensional projection identity, not a variance estimate. -/
structure GinibreProjectionIntegralFormula (n : ℕ) : Prop where
  weightedProjection : ∀ g : ℂ → ℝ, Measurable g → (∀ w, 0 ≤ g w) →
    Integrable (fun w => g w * ginibreOnePointDensity n w) →
    Integrable (fun wv : ℂ × ℂ =>
      (g wv.1 + g wv.2) * ginibreKernelWeight n wv) ∧
    (∫ wv : ℂ × ℂ, (g wv.1 + g wv.2) * ginibreKernelWeight n wv) =
      2 * (n : ℝ) * ∫ w, g w * ginibreOnePointDensity n w

/-- Exact correlation interface, constructed for the actual Gaussian law
by `normalizedGinibre_correlations`. There are no asymptotic or inequality fields.
The second formula is the standard difference-square form of the
two-point covariance identity for a projection determinantal process. -/
structure GinibreCorrelationFormulas
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {n : ℕ}
    (eigenvalue : Omega → Fin n → ℂ) : Prop where
  firstMoment : ∀ f : ℂ → ℝ, Measurable f →
    Integrable (fun w => f w * ginibreOnePointDensity n w) →
    Integrable (eigenvalueStatistic eigenvalue f) mu ∧
    (∫ sample, eigenvalueStatistic eigenvalue f sample ∂mu) =
      ∫ w, f w * ginibreOnePointDensity n w
  secondMoment : ∀ f : ℂ → ℝ, Measurable f →
    Integrable (fun w => (f w) ^ 2 * ginibreOnePointDensity n w) →
    Integrable (fun sample =>
      (eigenvalueStatistic eigenvalue f sample -
        ∫ other, eigenvalueStatistic eigenvalue f other ∂mu) ^ 2) mu ∧
    (∫ sample,
      (eigenvalueStatistic eigenvalue f sample -
        ∫ other, eigenvalueStatistic eigenvalue f other ∂mu) ^ 2 ∂mu) =
      (∫ wv : ℂ × ℂ,
        (f wv.1 - f wv.2) ^ 2 * ginibreKernelWeight n wv) / (2 * (n : ℝ) ^ 2)

end ShortRingAnchor.BC12
