import ShortRingAnchor.ProbabilityModes

/-!
# Removing a fixed truncation after the dimension limit

The last sentence of the proof of Proposition 3.6 takes the matrix dimension
to infinity first and the upper cutoff `R` to infinity afterwards.  This file
formalizes precisely that two-stage probability argument.  It is completely
independent of random-matrix theory.
-/

open Filter Set
open scoped ENNReal Topology

namespace ShortRingAnchor

open MeasureTheory

variable {Omega E : Type*} [MeasurableSpace Omega]

/-- `X` can be approximated in probability, uniformly for all sufficiently
large dimensions, by one member of the family `A r`.

The quantifier order is the one in the source proof: for each error threshold
and tail probability one first chooses a fixed truncation parameter `r`, and
only then lets the dimension tend to infinity. -/
def HasArbitrarilyGoodProbabilityApproximations
    [SeminormedAddCommGroup E]
    (mu : Measure Omega) (X : Nat -> Omega -> E)
    (A : Nat -> Nat -> Omega -> E) : Prop :=
  forall epsilon : Real, 0 < epsilon ->
    forall delta : ENNReal, 0 < delta ->
      exists r : Nat,
        ∀ᶠ n in atTop,
          mu {omega | epsilon <= ‖X n omega - A r n omega‖} < delta

/-- Abstract `M -> infinity`, then `R -> infinity` lemma used in the final
line of Proposition 3.6.

If every fixed truncation `A r` converges in probability to `x`, and a
sufficiently large fixed truncation approximates `X` with arbitrarily small
tail probability, then `X` itself converges in probability to `x`. -/
theorem convergesInProbability_of_arbitrarily_good_approximations
    [SeminormedAddCommGroup E]
    {mu : Measure Omega} {X : Nat -> Omega -> E}
    {A : Nat -> Nat -> Omega -> E} {x : E}
    (hA : forall r, ConvergesInProbability mu (A r) x)
    (hclose : HasArbitrarilyGoodProbabilityApproximations mu X A) :
    ConvergesInProbability mu X x := by
  rw [convergesInProbability_iff_norm]
  intro epsilon hepsilon
  rw [ENNReal.tendsto_nhds_zero]
  intro delta hdelta
  by_cases hdeltaTop : delta = ⊤
  · subst delta
    exact Filter.Eventually.of_forall fun _ => le_top
  have hepsilonHalf : 0 < epsilon / 2 := half_pos hepsilon
  have hdeltaHalf : 0 < delta / 2 := ENNReal.div_pos hdelta.ne' (by norm_num)
  have hdeltaHalfTop : delta / 2 ≠ ⊤ :=
    ENNReal.div_ne_top hdeltaTop (by norm_num)
  obtain ⟨r, hcloseEventually⟩ :=
    hclose (epsilon / 2) hepsilonHalf (delta / 2) hdeltaHalf
  have hAEventually : ∀ᶠ n in atTop,
      mu {omega | epsilon / 2 <= ‖A r n omega - x‖} <= delta / 2 := by
    have ht := (convergesInProbability_iff_norm.mp (hA r))
      (epsilon / 2) hepsilonHalf
    exact (ENNReal.tendsto_nhds_zero.mp ht) (delta / 2) hdeltaHalf
  filter_upwards [hcloseEventually, hAEventually] with n hnClose hnA
  calc
    mu {omega | epsilon <= ‖X n omega - x‖}
        <= mu ({omega | epsilon / 2 <= ‖X n omega - A r n omega‖} ∪
          {omega | epsilon / 2 <= ‖A r n omega - x‖}) := by
            apply measure_mono
            intro omega homega
            change epsilon <= ‖X n omega - x‖ at homega
            simp only [Set.mem_union, Set.mem_ofPred_eq]
            by_cases hXA : epsilon / 2 <= ‖X n omega - A r n omega‖
            · exact Or.inl hXA
            · right
              by_contra hAx
              have hXA' : ‖X n omega - A r n omega‖ < epsilon / 2 :=
                lt_of_not_ge hXA
              have hAx' : ‖A r n omega - x‖ < epsilon / 2 :=
                lt_of_not_ge hAx
              have htriangle : ‖X n omega - x‖ <=
                  ‖X n omega - A r n omega‖ + ‖A r n omega - x‖ := by
                rw [show X n omega - x =
                  (X n omega - A r n omega) + (A r n omega - x) by abel]
                exact norm_add_le _ _
              linarith
    _ <= mu {omega | epsilon / 2 <= ‖X n omega - A r n omega‖} +
        mu {omega | epsilon / 2 <= ‖A r n omega - x‖} := measure_union_le _ _
    _ <= delta := by
      have hsum :
          mu {omega | epsilon / 2 <= ‖X n omega - A r n omega‖} +
              mu {omega | epsilon / 2 <= ‖A r n omega - x‖} <
            delta / 2 + delta / 2 :=
        ENNReal.add_lt_add_of_lt_of_le
          (ne_top_of_le_ne_top hdeltaHalfTop hnA) hnClose hnA
      have hhalves : delta / 2 + delta / 2 = delta := ENNReal.add_halves delta
      exact (hhalves ▸ hsum).le

end ShortRingAnchor
