/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/Section5Formalization/VolumetricNet.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Section5Formalization.MatrixNormal
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.MetricSpace.CoveringNumbers

open MeasureTheory Set Metric
open scoped Function

namespace Section5Formalization

/-! # Quantitative volumetric nets in finite-dimensional real normed spaces -/

/--
A finite `h`-separated subset of the radius-`R` ball has at most
`((2R+h)/h)^dim` points.  This is the standard disjoint-Haar-balls argument
used by the block-net lemma.
-/
theorem card_le_of_norm_le_of_separated
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] (s : Finset E) {R h : Real}
    (hR : 0 <= R) (hh : 0 < h)
    (hs : ∀ c ∈ s, ‖c‖ <= R)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d -> h <= ‖c - d‖) :
    (s.card : Real) <= ((2 * R + h) / h) ^ Module.finrank Real E := by
  borelize E
  let mu : Measure E := Measure.addHaar
  let delta : Real := h / 2
  let rho : Real := R + h / 2
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hrho : 0 < rho := by dsimp [rho]; positivity
  set U := ⋃ c ∈ s, ball (c : E) delta with hU
  have hdisjoint : Set.Pairwise (s : Set E)
      (Disjoint on fun c => ball (c : E) delta) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    simpa [delta, two_mul] using hsep c hc d hd hcd
  have hsubset : U ⊆ ball (0 : E) rho := by
    refine iUnion₂_subset fun c hc => ?_
    apply ball_subset_ball'
    calc
      delta + dist c 0 <= delta + R := by
        rw [dist_zero_right]
        linarith [hs c hc]
      _ = rho := by simp [rho, delta]; ring
  have hmeasure :
      (s.card : ENNReal) * ENNReal.ofReal (delta ^ Module.finrank Real E) *
          mu (ball 0 1) <=
        ENNReal.ofReal (rho ^ Module.finrank Real E) * mu (ball 0 1) := by
    calc
      (s.card : ENNReal) * ENNReal.ofReal (delta ^ Module.finrank Real E) *
            mu (ball 0 1) = mu U := by
        rw [hU, measure_biUnion_finset hdisjoint fun c _ => measurableSet_ball]
        simp only [mu.addHaar_ball_of_pos _ hdelta]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ <= mu (ball (0 : E) rho) := measure_mono hsubset
      _ = ENNReal.ofReal (rho ^ Module.finrank Real E) * mu (ball 0 1) := by
        simp only [mu.addHaar_ball_of_pos _ hrho]
  have hcancel :
      (s.card : ENNReal) * ENNReal.ofReal (delta ^ Module.finrank Real E) <=
        ENNReal.ofReal (rho ^ Module.finrank Real E) :=
    (ENNReal.mul_le_mul_iff_left
      (measure_ball_pos _ _ zero_lt_one).ne'
      measure_ball_lt_top.ne).1 hmeasure
  have hreal :
      (s.card : Real) * delta ^ Module.finrank Real E <=
        rho ^ Module.finrank Real E := by
    have htoReal := ENNReal.toReal_le_of_le_ofReal
      (pow_nonneg hrho.le _) hcancel
    simpa [ENNReal.toReal_mul, hdelta.le] using htoReal
  have hdeltaPow : 0 < delta ^ Module.finrank Real E := pow_pos hdelta _
  calc
    (s.card : Real) <=
        rho ^ Module.finrank Real E / delta ^ Module.finrank Real E :=
      (le_div_iff₀ hdeltaPow).2 hreal
    _ = (rho / delta) ^ Module.finrank Real E := by rw [← div_pow]
    _ = ((2 * R + h) / h) ^ Module.finrank Real E := by
      congr 1
      dsimp [rho, delta]
      field_simp [hh.ne'] <;> ring

/--
Every finite-dimensional closed ball has an internal `h`-net with the
standard volumetric cardinality bound.  This strengthens the qualitative
finite-net theorem used earlier.
-/
theorem exists_volumetric_closedBall_net
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] {R h : Real} (hR : 0 <= R) (hh : 0 < h) :
    ∃ net : Finset E,
      (∀ y ∈ net, ‖y‖ <= R) ∧
      (∀ x : E, ‖x‖ <= R -> ∃ y ∈ net, dist x y <= h) ∧
      (net.card : Real) <= ((2 * R + h) / h) ^ Module.finrank Real E := by
  letI : ProperSpace E := FiniteDimensional.proper Real E
  let epsilon : NNReal := ⟨h, hh.le⟩
  let A : Set E := closedBall 0 R
  obtain ⟨C, hCA, hCfinite, hCcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact
      (ε := epsilon / 2) (by
        apply div_ne_zero
        · intro hepsilon
          have hvalue := congrArg (fun x : NNReal => (x : Real)) hepsilon
          change h = 0 at hvalue
          have : h = 0 := hvalue
          exact hh.ne' this
        · norm_num)
      (isCompact_closedBall (0 : E) R)
  have hpacking_le : Metric.packingNumber epsilon A <=
      Metric.externalCoveringNumber (epsilon / 2) A := by
    have htwo : (2 : NNReal) * (epsilon / 2) = epsilon := by ring
    simpa only [htwo] using
      (Metric.packingNumber_two_mul_le_externalCoveringNumber (epsilon / 2) A)
  have hexternal_le : Metric.externalCoveringNumber (epsilon / 2) A <= C.encard :=
    hCcover.externalCoveringNumber_le_encard
  have hpacking_lt : Metric.packingNumber epsilon A < ⊤ :=
    (hpacking_le.trans hexternal_le).trans_lt
      (Set.encard_lt_top_iff.mpr hCfinite)
  have hpacking_ne : Metric.packingNumber epsilon A ≠ ⊤ := hpacking_lt.ne
  let S : Set E := Metric.maximalSeparatedSet epsilon A
  have hSfinite : S.Finite := by
    apply Set.encard_lt_top_iff.mp
    rw [show S.encard = Metric.packingNumber epsilon A by
      exact Metric.encard_maximalSeparatedSet hpacking_ne]
    exact hpacking_lt
  let net : Finset E := hSfinite.toFinset
  have hnet_mem : ∀ y ∈ net, ‖y‖ <= R := by
    intro y hy
    have hyS : y ∈ S := hSfinite.mem_toFinset.mp hy
    have hyA : y ∈ A := Metric.maximalSeparatedSet_subset hyS
    simpa [A] using hyA
  have hnet_cover : ∀ x : E, ‖x‖ <= R -> ∃ y ∈ net, dist x y <= h := by
    intro x hx
    have hxA : x ∈ A := by simpa [A] using hx
    obtain ⟨y, hyS, hxy⟩ := Metric.isCover_maximalSeparatedSet hpacking_ne hxA
    refine ⟨y, hSfinite.mem_toFinset.mpr hyS, ?_⟩
    exact_mod_cast hxy
  have hnet_sep : ∀ c ∈ net, ∀ d ∈ net, c ≠ d -> h <= ‖c - d‖ := by
    intro c hc d hd hcd
    have hcS : c ∈ S := hSfinite.mem_toFinset.mp hc
    have hdS : d ∈ S := hSfinite.mem_toFinset.mp hd
    have hcd' := Metric.isSeparated_maximalSeparatedSet hcS hdS hcd
    have hdist : h < dist c d := by
      change (epsilon : ENNReal) < edist c d at hcd'
      rw [edist_dist] at hcd'
      have hreal : (epsilon : Real) < dist c d := ENNReal.coe_lt_ofReal.mp hcd'
      change h < dist c d at hreal
      exact hreal
    simpa [dist_eq_norm] using hdist.le
  refine ⟨net, hnet_mem, hnet_cover, ?_⟩
  exact card_le_of_norm_le_of_separated net hR hh hnet_mem hnet_sep

end Section5Formalization

