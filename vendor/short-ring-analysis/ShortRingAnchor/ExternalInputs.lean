import ShortRingAnchor.BulkProbability
import ShortRingAnchor.GinibreLowerEdge
import ShortRingAnchor.UpperEdgeAssembly

/-!
# Explicit literature interfaces for Proposition 3.6

The declarations in this file are *structures and definitions of
hypotheses*.  They are not axioms and do not assert the cited results.
Keeping them here makes the boundary between checked Lean reasoning and
imported random-matrix mathematics auditable.
-/

open Filter Set
open scoped ENNReal Topology

noncomputable section

namespace ShortRingAnchor

open MeasureTheory

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The specialization of Theorem 3.1 used in Proposition 3.6: outside an
`o(1)` event every singular value is at least `exp(-L_M)`. -/
structure Theorem31LeastSingularValueInput
    {I : Nat -> Type*} [forall n, Fintype (I n)]
    (mu : Measure Omega)
    (singularValue : forall n, Omega -> I n -> Real)
    (L : Nat -> Real) (good : Nat -> Set Omega) : Prop where
  badProbability : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0)
  lower : forall n omega, omega ∈ good n -> forall i,
    Real.exp (-(L n)) <= singularValue n omega i

/-- The specialization of Proposition 3.4 used on `[-a_M,a_M]`: outside
an `o(1)` event there are at most `C_M M a_M` small singular values. -/
structure Proposition34MesoscopicCountingInput
    {I : Nat -> Type*} [forall n, Fintype (I n)]
    (mu : Measure Omega)
    (singularValue : forall n, Omega -> I n -> Real)
    (a C : Nat -> Real) (good : Nat -> Set Omega) : Prop where
  badProbability : Tendsto (fun n => mu (good n)ᶜ) atTop (nhds 0)
  count : forall n omega, omega ∈ good n ->
    ((smallSingularValueIndices (singularValue n omega) (a n)).card : Real) <=
      C n * (Fintype.card (I n) : Real) * a n

/-- Lemma 3.5 at one fixed upper cutoff, exactly formula (3.11).
`rate_n=M^{-zeta}` in the source. -/
def Lemma35LocalBulkComparisonInput
    {I J : Nat -> Type*}
    [forall n, Fintype (I n)] [forall n, Fintype (J n)]
    (mu : Measure Omega)
    (h : forall n, Omega -> I n -> Real)
    (g : forall n, Omega -> J n -> Real)
    (R : Real) (rate : Nat -> Real) : Prop :=
  LocalBulkComparisonInput mu
    (fun n omega i => h n omega i ^ 2)
    (fun n omega j => g n omega j ^ 2) R rate

/-- The remaining BC12 input after the negative-moment interface isolated
in `GinibreLowerEdge.lean`: convergence of the full normalized Ginibre
logarithmic determinant / singular-value logarithmic average. -/
def BC12GinibreFullLogInput
    {J : Nat -> Type*} [forall n, Fintype (J n)]
    (mu : Measure Omega)
    (g : forall n, Omega -> J n -> Real) (limit : Real) : Prop :=
  ConvergesInProbability mu
    (fun n omega => empiricalLog (g n omega)) limit

/-- The elementary moment input used in (3.13).  In the matrix application
the two constants are both `1+|z|^2`, by the Hilbert--Schmidt computation.
This structure asks only for integrability and the displayed uniform mean
bounds. -/
structure UpperSecondMomentInputs
    {I J : Nat -> Type*}
    [forall n, Fintype (I n)] [forall n, Fintype (J n)]
    (mu : Measure Omega)
    (h : forall n, Omega -> I n -> Real)
    (g : forall n, Omega -> J n -> Real)
    (CH CG : Real) : Prop where
  CH_nonneg : 0 <= CH
  CG_nonneg : 0 <= CG
  h_integrable : forall n, Integrable
    (fun omega => empiricalAverage (h n omega) (fun t => t ^ 2)) mu
  g_integrable : forall n, Integrable
    (fun omega => empiricalAverage (g n omega) (fun t => t ^ 2)) mu
  h_mean : forall n,
    ∫ omega, empiricalAverage (h n omega) (fun t => t ^ 2) ∂mu <= CH
  g_mean : forall n,
    ∫ omega, empiricalAverage (g n omega) (fun t => t ^ 2) ∂mu <= CG

/-- The intersection of the Theorem 3.1 and Proposition 3.4 good events
still has failure probability `o(1)`.  This union-bound step is internal. -/
theorem hardEdgeIntersection_badProbability
    {mu : Measure Omega} {goodLSV goodCount : Nat -> Set Omega}
    (hLSV : Tendsto (fun n => mu (goodLSV n)ᶜ) atTop (nhds 0))
    (hCount : Tendsto (fun n => mu (goodCount n)ᶜ) atTop (nhds 0)) :
    Tendsto (fun n => mu ((goodLSV n ∩ goodCount n)ᶜ)) atTop (nhds 0) := by
  have hsum : Tendsto
      (fun n => mu (goodLSV n)ᶜ + mu (goodCount n)ᶜ)
      atTop (nhds 0) := by
    simpa only [add_zero] using hLSV.add hCount
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) ?_
  intro n
  change mu ((goodLSV n ∩ goodCount n)ᶜ) <=
    mu (goodLSV n)ᶜ + mu (goodCount n)ᶜ
  rw [compl_inter]
  exact measure_union_le _ _

end ShortRingAnchor
