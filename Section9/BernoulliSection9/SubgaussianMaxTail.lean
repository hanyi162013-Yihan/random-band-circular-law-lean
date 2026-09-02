import BernoulliSection9.ExternalInputs
import Mathlib.MeasureTheory.Measure.Real

/-!
# Maximum-coordinate tails from the internal subgaussian hypothesis

This module derives the `E_max` probability estimate directly from the
subgaussian MGF field of `IidSubgaussianFamily`.  It is not a literature
input and introduces no additional trust-boundary parameter.
-/

open scoped ProbabilityTheory ENNReal NNReal MeasureTheory

noncomputable section

namespace BernoulliSection9

open MeasureTheory ProbabilityTheory Set

/-- Variance one rules out the degenerate zero subgaussian parameter. -/
theorem IidSubgaussianFamily.subgaussianParameter_pos
    {Omega iota : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [Nonempty iota]
    (X : IidSubgaussianFamily Omega mu iota) :
    0 < X.subgaussianParameter := by
  apply pos_iff_ne_zero.mpr
  intro hc
  let i : iota := Classical.choice inferInstance
  have hsub := X.subgaussian i
  rw [hc] at hsub
  have hzero := hsub.ae_eq_zero_of_hasSubgaussianMGF_zero
  have hsq : (fun omega => X.atom i omega ^ 2) =ᵐ[mu]
      (fun _ => (0 : Real)) := by
    filter_upwards [hzero] with omega homega
    simp [homega]
  have hvariance := X.variance_one i
  rw [integral_congr_ae hsq] at hvariance
  simp at hvariance

/-- A two-sided Chernoff bound obtained by applying the one-sided
subgaussian estimate to `X` and `-X`. -/
theorem measureReal_abs_ge_le_of_hasSubgaussianMGF
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {X : Omega -> Real} {c : NNReal}
    (hX : HasSubgaussianMGF X c mu) (M : Real) (hM : 0 <= M) :
    mu.real {omega | M <= abs (X omega)} <=
      2 * Real.exp (-M ^ 2 / (2 * (c : Real))) := by
  have hset : {omega | M <= abs (X omega)} =
      {omega | M <= X omega} ∪ {omega | M <= -X omega} := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [hset]
  calc
    mu.real ({omega | M <= X omega} ∪ {omega | M <= -X omega}) <=
        mu.real {omega | M <= X omega} +
          mu.real {omega | M <= -X omega} :=
      measureReal_union_le _ _
    _ <= Real.exp (-M ^ 2 / (2 * (c : Real))) +
          Real.exp (-M ^ 2 / (2 * (c : Real))) := by
      apply add_le_add
      · exact hX.measure_ge_le hM
      · simpa only [Pi.neg_apply] using hX.neg.measure_ge_le hM
    _ = 2 * Real.exp (-M ^ 2 / (2 * (c : Real))) := by ring

/-- Strict version convenient for complements of coordinatewise bounded
events. -/
theorem measureReal_abs_gt_le_of_hasSubgaussianMGF
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsFiniteMeasure mu]
    {X : Omega -> Real} {c : NNReal}
    (hX : HasSubgaussianMGF X c mu) (M : Real) (hM : 0 <= M) :
    mu.real {omega | M < abs (X omega)} <=
      2 * Real.exp (-M ^ 2 / (2 * (c : Real))) := by
  exact (measureReal_mono (by
    intro omega homega
    change M < abs (X omega) at homega
    change M <= abs (X omega)
    exact le_of_lt homega)).trans
      (measureReal_abs_ge_le_of_hasSubgaussianMGF mu hX M hM)

/-- The event on which every coordinate of an iid family is bounded by
`M`.  Independence is not needed for its probability estimate. -/
def familyCoordinatewiseBoundedEvent
    {Omega iota : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega}
    (X : IidSubgaussianFamily Omega mu iota) (M : Real) : Set Omega :=
  {omega | forall i, abs (X.atom i omega) <= M}

theorem measurableSet_familyCoordinatewiseBoundedEvent
    {Omega iota : Type*} [MeasurableSpace Omega]
    [Fintype iota]
    {mu : Measure Omega}
    (X : IidSubgaussianFamily Omega mu iota) (M : Real) :
    MeasurableSet (familyCoordinatewiseBoundedEvent X M) := by
  rw [show familyCoordinatewiseBoundedEvent X M = ⋂ i,
      {omega | abs (X.atom i omega) <= M} by
    ext omega
    simp [familyCoordinatewiseBoundedEvent]]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (X.measurable_atom i).abs measurable_const

/-- Union bound for the complement of the coordinatewise bounded event.
The cardinality factor is explicit, so later modules can specialize it to
the `7 W^2` packet coordinates. -/
theorem measureReal_compl_familyCoordinatewiseBoundedEvent_le
    {Omega iota : Type*} [MeasurableSpace Omega]
    [Fintype iota]
    (mu : Measure Omega)
    [IsFiniteMeasure mu]
    (X : IidSubgaussianFamily Omega mu iota) (M : Real) (hM : 0 <= M) :
    mu.real (familyCoordinatewiseBoundedEvent X M)ᶜ <=
      (Fintype.card iota : Real) *
        (2 * Real.exp
          (-M ^ 2 / (2 * (X.subgaussianParameter : Real)))) := by
  have hcompl : (familyCoordinatewiseBoundedEvent X M)ᶜ =
      ⋃ i, {omega | M < abs (X.atom i omega)} := by
    ext omega
    simp [familyCoordinatewiseBoundedEvent]
  rw [hcompl]
  calc
    mu.real (⋃ i, {omega | M < abs (X.atom i omega)}) <=
        ∑ i, mu.real {omega | M < abs (X.atom i omega)} :=
      measureReal_iUnion_fintype_le _
    _ <= ∑ _i : iota,
        2 * Real.exp
          (-M ^ 2 / (2 * (X.subgaussianParameter : Real))) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact measureReal_abs_gt_le_of_hasSubgaussianMGF mu
        (X.subgaussian i) M hM
    _ = (Fintype.card iota : Real) *
        (2 * Real.exp
          (-M ^ 2 / (2 * (X.subgaussianParameter : Real)))) := by simp

/-- The canonical finite-family threshold whose union-bound failure is
exactly `exp (-t)`. -/
def familyCoordinateMaxThreshold
    {Omega iota : Type*} [MeasurableSpace Omega]
    [Fintype iota]
    {mu : Measure Omega}
    (X : IidSubgaussianFamily Omega mu iota) (t : Real) : Real :=
  Real.sqrt
    (2 * (X.subgaussianParameter : Real) *
      (t + Real.log (2 * (Fintype.card iota : Real))))

/-- Choosing the preceding threshold turns the exact finite union bound
into a pure exponential.  This is the abstract `E_max` estimate. -/
theorem measureReal_compl_familyCoordinatewiseBoundedEvent_threshold_le
    {Omega iota : Type*} [MeasurableSpace Omega]
    [Fintype iota] [Nonempty iota]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (X : IidSubgaussianFamily Omega mu iota)
    (t : Real) (ht : 0 <= t) :
    mu.real
        (familyCoordinatewiseBoundedEvent X
          (familyCoordinateMaxThreshold X t))ᶜ <=
      Real.exp (-t) := by
  let c : Real := X.subgaussianParameter
  let N : Real := 2 * (Fintype.card iota : Real)
  have hc : 0 < c := by
    exact_mod_cast X.subgaussianParameter_pos
  have hcard : 1 <= Fintype.card iota := Fintype.card_pos_iff.mpr inferInstance
  have hN : 1 <= N := by
    dsimp [N]
    exact_mod_cast (show 1 <= 2 * Fintype.card iota by omega)
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hlog : 0 <= Real.log N := Real.log_nonneg hN
  have hins : 0 <= 2 * c * (t + Real.log N) := by positivity
  have hsqrt :
      familyCoordinateMaxThreshold X t ^ 2 =
        2 * c * (t + Real.log N) := by
    dsimp [familyCoordinateMaxThreshold, c, N]
    exact Real.sq_sqrt hins
  have hbound := measureReal_compl_familyCoordinatewiseBoundedEvent_le
    mu X (familyCoordinateMaxThreshold X t) (Real.sqrt_nonneg _)
  calc
    mu.real
        (familyCoordinatewiseBoundedEvent X
          (familyCoordinateMaxThreshold X t))ᶜ <=
        (Fintype.card iota : Real) *
          (2 * Real.exp
            (-(familyCoordinateMaxThreshold X t) ^ 2 /
              (2 * (X.subgaussianParameter : Real)))) := hbound
    _ = N * Real.exp (-(t + Real.log N)) := by
      rw [hsqrt]
      change (Fintype.card iota : Real) *
          (2 * Real.exp (-(2 * c * (t + Real.log N)) / (2 * c))) = _
      have hcancel :
          -(2 * c * (t + Real.log N)) / (2 * c) =
            -(t + Real.log N) := by
        field_simp
      rw [hcancel]
      dsimp [N]
      ring
    _ = Real.exp (Real.log N) * Real.exp (-(t + Real.log N)) := by
      rw [Real.exp_log hNpos]
    _ = Real.exp (-t) := by
      rw [← Real.exp_add]
      congr 1
      ring

end BernoulliSection9
