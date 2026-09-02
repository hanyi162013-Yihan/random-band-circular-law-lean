import ShortRingAnchor.Approximation
import ShortRingAnchor.BulkProbability
import ShortRingAnchor.GinibreLowerEdge
import ShortRingAnchor.LogDecomposition

/-!
# Assembly of formulas (3.10)--(3.14)

This file contains the deterministic algebra and the final two-stage
probability argument in Proposition 3.6.  It does not assume that the finite
families arise from matrices.  Consequently it can be audited separately
from every random-matrix input.
-/

open Filter Set
open scoped BigOperators ENNReal Topology

noncomputable section

namespace ShortRingAnchor

open MeasureTheory

/-- The lower clipping correction is bounded by the absolute logarithmic
mass below the same cutoff.  This is the bridge from the source's raw
hard-edge estimates (3.10), (3.14) to the exact clipping decomposition.
-/
theorem empiricalLowerLogCorrection_le_normalizedSmallLogMass
    {I : Type*} [Fintype I]
    {singularValue : I -> Real} {a : Real}
    (ha : 0 < a) (ha1 : a <= 1)
    (hs : forall i, 0 < singularValue i) :
    empiricalLowerLogCorrection a singularValue <=
      normalizedSmallLogMass singularValue a := by
  classical
  have hpoint : forall i,
      lowerLogCorrection a (singularValue i) <=
        if singularValue i <= a then |Real.log (singularValue i)| else 0 := by
    intro i
    by_cases hia : singularValue i < a
    · rw [lowerLogCorrection, if_pos hia, if_pos hia.le]
      have hisOne : singularValue i <= 1 := hia.le.trans ha1
      have hlogs : Real.log (singularValue i) <= 0 :=
        Real.log_nonpos (hs i).le hisOne
      have hloga : Real.log a <= 0 := Real.log_nonpos ha.le ha1
      rw [abs_of_nonpos hlogs]
      linarith
    · rw [lowerLogCorrection, if_neg hia]
      split_ifs
      · exact abs_nonneg _
      · exact le_rfl
  unfold empiricalLowerLogCorrection normalizedSmallLogMass empiricalAverage
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    (∑ i, lowerLogCorrection a (singularValue i)) <=
        ∑ i, if singularValue i <= a
          then |Real.log (singularValue i)| else 0 :=
      Finset.sum_le_sum fun i _hi => hpoint i
    _ = ∑ i ∈ smallSingularValueIndices singularValue a,
        |Real.log (singularValue i)| := by
      simpa [smallSingularValueIndices] using
        (Finset.sum_filter (s := (Finset.univ : Finset I))
          (fun i => singularValue i <= a)
          (fun i => |Real.log (singularValue i)|)).symm

/-- Convergence form of the preceding deterministic bridge. -/
theorem empiricalLowerLogCorrection_convergesInProbability_of_smallLogMass
    {Omega : Type*} [MeasurableSpace Omega]
    {I : Nat -> Type*} [forall n, Fintype (I n)]
    [forall n, Nonempty (I n)]
    {mu : Measure Omega}
    {singularValue : forall n, Omega -> I n -> Real}
    {a : Nat -> Real}
    (ha : forall n, 0 < a n) (ha1 : forall n, a n <= 1)
    (hs : forall n omega i, 0 < singularValue n omega i)
    (hmass : ConvergesInProbability mu
      (fun n omega =>
        normalizedSmallLogMass (singularValue n omega) (a n)) 0) :
    ConvergesInProbability mu
      (fun n omega =>
        empiricalLowerLogCorrection (a n) (singularValue n omega)) 0 := by
  apply convergesInProbability_zero_of_norm_le hmass
  intro n omega
  have hcorr : 0 <=
      empiricalLowerLogCorrection (a n) (singularValue n omega) := by
    unfold empiricalLowerLogCorrection empiricalAverage
    exact div_nonneg
      (Finset.sum_nonneg fun i _ =>
        lowerLogCorrection_nonneg (ha n) (hs n omega i))
      (Nat.cast_nonneg _)
  have hmassNonneg := normalizedSmallLogMass_nonneg
    (singularValue n omega) (a n)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hcorr, abs_of_nonneg hmassNonneg]
  exact empiricalLowerLogCorrection_le_normalizedSmallLogMass
    (ha n) (ha1 n) (hs n omega)

/-- The fixed-`R` approximation used before the last sentence of the proof.

It replaces the upper correction of the short-ring family by the upper
correction of the Ginibre family.  After expansion it is

`Ginibre full log + bulk clipped difference - H lower + G lower`.
-/
def fixedUpperApproximation
    {I J : Type*} [Fintype I] [Fintype J]
    (a R : Real) (h : I -> Real) (g : J -> Real) : Real :=
  empiricalLog g +
    (empiricalClippedLog a R (fun i => h i ^ 2) -
      empiricalClippedLog a R (fun j => g j ^ 2)) -
    empiricalLowerLogCorrection a h +
    empiricalLowerLogCorrection a g

/-- Exact low/middle/high algebra underlying the final error decomposition.
-/
theorem empiricalLog_sub_fixedUpperApproximation
    {I J : Type*} [Fintype I] [Fintype J]
    {a R : Real} {h : I -> Real} {g : J -> Real}
    (ha : 0 < a) (haR : a <= R)
    (hh : forall i, 0 < h i) (hg : forall j, 0 < g j) :
    empiricalLog h - fixedUpperApproximation a R h g =
      empiricalUpperLogCorrection R h - empiricalUpperLogCorrection R g := by
  unfold fixedUpperApproximation
  rw [empiricalLog_eq_clipped_sub_lower_add_upper ha haR hh,
    empiricalLog_eq_clipped_sub_lower_add_upper ha haR hg]
  ring

/-- For a family of fixed upper cutoffs, the two upper corrections can be
made uniformly small in probability by choosing a sufficiently large fixed
cutoff.  This is the exact quantifier order `M -> infinity`, then
`R -> infinity` in the source proof. -/
def UpperCorrectionsUniformlyNegligible
    {Omega : Type*} [MeasurableSpace Omega]
    {I J : Nat -> Type*} [forall n, Fintype (I n)]
    [forall n, Fintype (J n)]
    (mu : Measure Omega)
    (h : forall n, Omega -> I n -> Real)
    (g : forall n, Omega -> J n -> Real)
    (R : Nat -> Real) : Prop :=
  forall epsilon : Real, 0 < epsilon ->
    forall delta : ENNReal, 0 < delta ->
      exists r : Nat, ∀ᶠ n in atTop,
        mu {omega | epsilon / 2 <=
            empiricalUpperLogCorrection (R r) (h n omega)} +
          mu {omega | epsilon / 2 <=
            empiricalUpperLogCorrection (R r) (g n omega)} < delta

/-- For every fixed upper cutoff, formulas (3.10), (3.12), (3.14), and the
full Ginibre log-determinant limit make `fixedUpperApproximation` converge to
the circular potential. -/
theorem fixedUpperApproximation_convergesInProbability
    {Omega : Type*} [MeasurableSpace Omega]
    {I J : Nat -> Type*}
    [forall n, Fintype (I n)] [forall n, Fintype (J n)]
    {mu : Measure Omega}
    {h : forall n, Omega -> I n -> Real}
    {g : forall n, Omega -> J n -> Real}
    {a : Nat -> Real} {R : Real} {limit : Real}
    (hGinibreFull : ConvergesInProbability mu
      (fun n omega => empiricalLog (g n omega)) limit)
    (hBulk : ConvergesInProbability mu
      (fun n omega =>
        empiricalClippedLog (a n) R (fun i => h n omega i ^ 2) -
          empiricalClippedLog (a n) R (fun j => g n omega j ^ 2)) 0)
    (hHardLower : ConvergesInProbability mu
      (fun n omega => empiricalLowerLogCorrection (a n) (h n omega)) 0)
    (hGinibreLower : ConvergesInProbability mu
      (fun n omega => empiricalLowerLogCorrection (a n) (g n omega)) 0) :
    ConvergesInProbability mu
      (fun n omega => fixedUpperApproximation (a n) R
        (h n omega) (g n omega)) limit := by
  simpa [fixedUpperApproximation, add_assoc] using
    ((hGinibreFull.add hBulk).sub hHardLower).add hGinibreLower

/-- **Complete internal assembly of (3.10)--(3.14).**

All four convergence premises are exactly the already separated components:
full Ginibre, bulk comparison, short-ring hard edge, and Ginibre hard edge.
The upper-edge premise is supplied internally from (3.13) in
`UpperEdge.lean`.  The conclusion is convergence of the full empirical
logarithmic singular-value average. -/
theorem empiricalLog_convergesInProbability_of_truncations
    {Omega : Type*} [MeasurableSpace Omega]
    {I J : Nat -> Type*}
    [forall n, Fintype (I n)] [forall n, Fintype (J n)]
    {mu : Measure Omega}
    {h : forall n, Omega -> I n -> Real}
    {g : forall n, Omega -> J n -> Real}
    {a R : Nat -> Real} {limit : Real}
    (ha : forall n, 0 < a n)
    (haR : forall r n, a n <= R r)
    (hh : forall n omega i, 0 < h n omega i)
    (hg : forall n omega j, 0 < g n omega j)
    (hGinibreFull : ConvergesInProbability mu
      (fun n omega => empiricalLog (g n omega)) limit)
    (hBulk : forall r, ConvergesInProbability mu
      (fun n omega =>
        empiricalClippedLog (a n) (R r) (fun i => h n omega i ^ 2) -
          empiricalClippedLog (a n) (R r) (fun j => g n omega j ^ 2)) 0)
    (hHardLower : ConvergesInProbability mu
      (fun n omega => empiricalLowerLogCorrection (a n) (h n omega)) 0)
    (hGinibreLower : ConvergesInProbability mu
      (fun n omega => empiricalLowerLogCorrection (a n) (g n omega)) 0)
    (hUpper : UpperCorrectionsUniformlyNegligible mu h g R) :
    ConvergesInProbability mu
      (fun n omega => empiricalLog (h n omega)) limit := by
  let A : Nat -> Nat -> Omega -> Real := fun r n omega =>
    fixedUpperApproximation (a n) (R r) (h n omega) (g n omega)
  apply convergesInProbability_of_arbitrarily_good_approximations
      (A := A)
  · intro r
    exact fixedUpperApproximation_convergesInProbability
      hGinibreFull (hBulk r) hHardLower hGinibreLower
  · intro epsilon hepsilon delta hdelta
    obtain ⟨r, hr⟩ := hUpper epsilon hepsilon delta hdelta
    refine ⟨r, ?_⟩
    filter_upwards [hr] with n hn
    calc
      mu {omega | epsilon <=
          ‖empiricalLog (h n omega) - A r n omega‖}
          <= mu ({omega | epsilon / 2 <=
              empiricalUpperLogCorrection (R r) (h n omega)} ∪
            {omega | epsilon / 2 <=
              empiricalUpperLogCorrection (R r) (g n omega)}) := by
                apply measure_mono
                intro omega homega
                change epsilon <=
                  |empiricalLog (h n omega) - A r n omega| at homega
                rw [empiricalLog_sub_fixedUpperApproximation
                  (ha n) (haR r n) (hh n omega) (hg n omega)] at homega
                simp only [Set.mem_union, Set.mem_ofPred_eq]
                by_cases hH : epsilon / 2 <=
                    empiricalUpperLogCorrection (R r) (h n omega)
                · exact Or.inl hH
                · right
                  by_contra hG
                  have hHlt := lt_of_not_ge hH
                  have hGlt := lt_of_not_ge hG
                  have hHcorr : 0 <=
                      empiricalUpperLogCorrection (R r) (h n omega) := by
                    unfold empiricalUpperLogCorrection empiricalAverage
                    exact div_nonneg
                      (Finset.sum_nonneg fun i _ =>
                        upperLogCorrection_nonneg
                          ((ha n).trans_le (haR r n)) (hh n omega i))
                      (Nat.cast_nonneg _)
                  have hGcorr : 0 <=
                      empiricalUpperLogCorrection (R r) (g n omega) := by
                    unfold empiricalUpperLogCorrection empiricalAverage
                    exact div_nonneg
                      (Finset.sum_nonneg fun j _ =>
                        upperLogCorrection_nonneg
                          ((ha n).trans_le (haR r n)) (hg n omega j))
                      (Nat.cast_nonneg _)
                  have habs :
                      |empiricalUpperLogCorrection (R r) (h n omega) -
                          empiricalUpperLogCorrection (R r) (g n omega)| <=
                        empiricalUpperLogCorrection (R r) (h n omega) +
                          empiricalUpperLogCorrection (R r) (g n omega) := by
                    rw [abs_le]
                    constructor <;> linarith
                  linarith
      _ <= mu {omega | epsilon / 2 <=
            empiricalUpperLogCorrection (R r) (h n omega)} +
          mu {omega | epsilon / 2 <=
            empiricalUpperLogCorrection (R r) (g n omega)} :=
        measure_union_le _ _
      _ < delta := hn

end ShortRingAnchor
