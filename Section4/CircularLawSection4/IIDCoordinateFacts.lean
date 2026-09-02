import CircularLawSection4.ProductSmallBall

/-!
# Coordinate marginals of the recursive IID law

This module records the elementary coordinate facts needed when the rows of
the random band model are represented by `iidMeasure`.  Every coordinate has
the original law, coordinate cylinder events therefore have the expected
probability, and a law with no atom at zero produces vectors whose finitely
many coordinates are all nonzero almost surely.
-/

open scoped ENNReal
open MeasureTheory Set

namespace CircularLawSection4

universe u

section CoordinateMarginal

variable {K : Type u} [MeasurableSpace K]

/-- Every coordinate projection of the recursive product law `iidMeasure ν n`
has pushforward law `ν`. -/
theorem iidMeasure_map_coordinate
    (ν : Measure K) [SFinite ν] [IsProbabilityMeasure ν] :
    ∀ {n : ℕ} (i : Fin n),
      Measure.map (fun x : Fin n → K => x i) (iidMeasure ν n) = ν := by
  intro n
  induction n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      intro i
      let _ := iidMeasure_isProbability ν n
      rw [iidMeasure]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Measure.map_map (measurable_pi_apply (Fin.last n)) measurable_joinLast]
        have hcomp :
            (fun x : Fin (n + 1) → K => x (Fin.last n)) ∘ joinLast =
              (Prod.snd : (Fin n → K) × K → K) := by
          funext y
          simp
        rw [hcomp, Measure.map_snd_prod, measure_univ, one_smul]
      · rw [Measure.map_map (measurable_pi_apply j.castSucc) measurable_joinLast]
        have hcomp :
            (fun x : Fin (n + 1) → K => x j.castSucc) ∘ joinLast =
              (fun y : (Fin n → K) × K => y.1 j) := by
          funext y
          simp
        rw [hcomp]
        calc
          Measure.map (fun y : (Fin n → K) × K => y.1 j)
              ((iidMeasure ν n).prod ν) =
              Measure.map (fun x : Fin n → K => x j)
                (Measure.map Prod.fst ((iidMeasure ν n).prod ν)) := by
                  rw [Measure.map_map (measurable_pi_apply j) measurable_fst]
                  congr 1
          _ = Measure.map (fun x : Fin n → K => x j) (iidMeasure ν n) := by
            rw [Measure.map_fst_prod, measure_univ, one_smul]
          _ = ν := ih j

/-- A measurable cylinder event in any coordinate of `iidMeasure ν n` has
the same probability as the corresponding event under `ν`. -/
theorem iidMeasure_coordinate_event
    (ν : Measure K) [SFinite ν] [IsProbabilityMeasure ν]
    {n : ℕ} (i : Fin n) {s : Set K} (hs : MeasurableSet s) :
    iidMeasure ν n {x | x i ∈ s} = ν s := by
  calc
    iidMeasure ν n {x | x i ∈ s} =
        Measure.map (fun x : Fin n → K => x i) (iidMeasure ν n) s := by
      rw [Measure.map_apply (measurable_pi_apply i) hs]
      congr 1
    _ = ν s := by rw [iidMeasure_map_coordinate ν i]

/-- If the one-coordinate law has no atom at zero, then every coordinate of
a finite IID vector is nonzero almost surely. -/
theorem iidMeasure_ae_all_ne_zero
    [Zero K] [MeasurableSingletonClass K]
    (ν : Measure K) [SFinite ν] [IsProbabilityMeasure ν]
    (hν0 : ν ({0} : Set K) = 0) (n : ℕ) :
    ∀ᵐ x ∂iidMeasure ν n, ∀ i, x i ≠ 0 := by
  apply ae_all_iff.mpr
  intro i
  rw [ae_iff]
  have hcoord := iidMeasure_coordinate_event ν i (measurableSet_singleton 0)
  rw [hν0] at hcoord
  simpa only [Set.mem_singleton_iff, ne_eq, not_not] using hcoord

end CoordinateMarginal

section DensityCorollaries

/-- An interval upper bound forces a real coordinate law to have no atom at
zero. -/
theorem measure_singleton_zero_eq_zero_of_realIntervalBound
    {ν : Measure ℝ} {L : ℝ≥0∞} (hν : RealIntervalBound ν L) :
    ν ({0} : Set ℝ) = 0 := by
  have h := hν 0 0 le_rfl
  apply le_antisymm
  · simpa using h
  · exact bot_le

/-- A disk upper bound forces a complex coordinate law to have no atom at
zero. -/
theorem measure_singleton_zero_eq_zero_of_complexBallBound
    {ν : Measure ℂ} {L : ℝ≥0∞} (hν : ComplexBallBound ν L) :
    ν ({0} : Set ℂ) = 0 := by
  have h := hν 0 0 le_rfl
  have hball : Metric.closedBall (0 : ℂ) 0 = ({0} : Set ℂ) := by
    ext z
    simp
  apply le_antisymm
  · simpa [hball] using h
  · exact bot_le

/-- Real interval control gives simultaneous almost-sure nonvanishing of all
coordinates in the recursive IID sample. -/
theorem iidMeasure_ae_all_ne_zero_of_realIntervalBound
    (ν : Measure ℝ) [SFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ≥0∞} (hν : RealIntervalBound ν L) (n : ℕ) :
    ∀ᵐ x ∂iidMeasure ν n, ∀ i, x i ≠ 0 :=
  iidMeasure_ae_all_ne_zero ν
    (measure_singleton_zero_eq_zero_of_realIntervalBound hν) n

/-- Complex disk control gives simultaneous almost-sure nonvanishing of all
coordinates in the recursive IID sample. -/
theorem iidMeasure_ae_all_ne_zero_of_complexBallBound
    (ν : Measure ℂ) [SFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ≥0∞} (hν : ComplexBallBound ν L) (n : ℕ) :
    ∀ᵐ x ∂iidMeasure ν n, ∀ i, x i ≠ 0 :=
  iidMeasure_ae_all_ne_zero ν
    (measure_singleton_zero_eq_zero_of_complexBallBound hν) n

/-- A bounded real Lebesgue density has no zero coordinates in any finite IID
sample, provided the density is normalized to a probability law. -/
theorem iidMeasure_ae_all_ne_zero_real_withDensity
    {f : ℝ → ℝ≥0∞} {L : ℝ≥0∞}
    [IsProbabilityMeasure ((volume : Measure ℝ).withDensity f)]
    (hf : ∀ᵐ x ∂(volume : Measure ℝ), f x ≤ L) (n : ℕ) :
    ∀ᵐ x ∂iidMeasure ((volume : Measure ℝ).withDensity f) n,
      ∀ i, x i ≠ 0 :=
  iidMeasure_ae_all_ne_zero_of_realIntervalBound
    ((volume : Measure ℝ).withDensity f) (realIntervalBound_withDensity hf) n

/-- A bounded planar Lebesgue density has no zero coordinates in any finite
complex IID sample, provided the density is normalized to a probability
law. -/
theorem iidMeasure_ae_all_ne_zero_complex_withDensity
    {f : ℂ → ℝ≥0∞} {L : ℝ≥0∞}
    [IsProbabilityMeasure ((volume : Measure ℂ).withDensity f)]
    (hf : ∀ᵐ z ∂(volume : Measure ℂ), f z ≤ L) (n : ℕ) :
    ∀ᵐ x ∂iidMeasure ((volume : Measure ℂ).withDensity f) n,
      ∀ i, x i ≠ 0 :=
  iidMeasure_ae_all_ne_zero_of_complexBallBound
    ((volume : Measure ℂ).withDensity f) (complexBallBound_withDensity hf) n

end DensityCorollaries

end CircularLawSection4
