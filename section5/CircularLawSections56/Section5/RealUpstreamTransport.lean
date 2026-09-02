import CircularLawSections56.Section5.QuantitativeSection4Inputs
import CircularLawSections56.Section5.RealSampleTransport

/-! # Transport the accepted real Section 3/4 inputs to the complex matrix notation

Complexification preserves the original law, not just the final conclusion.
This reverse adapter lets the upstream finite estimates and Section 3 limits
be supplied on original real arrays. Observable measurability is proved for
the actual determinant and pressure functions below.
-/

open Filter MeasureTheory Topology
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option autoImplicit false

namespace CircularLawSections56.Section5
open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

theorem measurable_literalCalibrationRows (k d m : ℕ) :
    Measurable (literalCalibrationRows k d m) := by
  classical
  unfold literalCalibrationRows
  by_cases hm : m ≤ k + 1
  · simp only [dif_pos hm]
    exact measurable_pi_lambda _ (fun j => (measurable_pi_apply
      (literalCalibrationRowIndex k d m hm j)).comp (paperIndicatorFlatRowsEquiv (k + 1) d).measurable)
  · simp only [dif_neg hm]
    exact measurable_const

theorem measurable_literalModelPressure (k d m : ℕ)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ) (q : ExteriorDegree (d + 1)) :
    Measurable (literalModelPressure k d m profile center z q) :=
  (profile.measurable_paperIndicatorOpenPressure center z q _).comp
    (measurable_literalCalibrationRows k d m)

theorem measurable_literalModelRawDeterminant (k d : ℕ) (center : Fin (d + 1))
    (b : Fin (d + 2) → ℂ) (z : ℂ) :
    Measurable (literalModelRawDeterminant k d center b z) :=
  measurable_log_norm_paperIndicatorXSubZI_det (k + 1) d center b z

theorem measurable_literalModelCalibrationRaw (k d m : ℕ) (center : Fin (d + 1))
    (b : Fin (d + 2) → ℂ) (z : ℂ) :
    Measurable (literalModelCalibrationRaw k d m center b z) := by
  classical
  unfold literalModelCalibrationRaw
  by_cases hm : 0 < m ∧ m ≤ k + 1
  · let : NeZero m := ⟨hm.1.ne'⟩
    simp only [dif_pos hm]
    exact (measurable_log_norm_paperIndicatorXSubZI_det m d center b z).comp
      (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))
  · simp only [dif_neg hm]
    exact measurable_const

theorem measurable_finiteSignedMax_of_measurable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (Y : ι → Ω → ℝ) (hY : ∀ i, Measurable (Y i)) :
    Measurable (fun ω => finiteSignedMax Finset.univ Finset.univ_nonempty (fun i => Y i ω)) := by
  convert Finset.measurable_sup' Finset.univ_nonempty (fun i _ => hY i) using 1
  funext ω
  simp only [finiteSignedMax, Finset.sup'_apply]

theorem QuantitativeSection4PressureInput.of_measurePreserving
    {Ω Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (μ : ∀ n, Measure (Ω n)) (ν : ∀ n, Measure (Ξ n))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (F : ∀ n, Ω n → Ξ n) (hF : ∀ n, MeasurePreserving (F n) (μ n) (ν n))
    (active : ℕ → Bool) (d ell : ℕ → ℕ)
    (raw : ∀ n, Ξ n → ℝ) (Y : ∀ n, ExteriorDegree (d n + 1) → Ξ n → ℝ)
    (c₀ negative fiber : ℕ → ℝ) (z : ℂ)
    (hraw : ∀ n, Measurable (raw n)) (hY : ∀ n r, Measurable (Y n r))
    (h4 : QuantitativeSection4PressureInput μ active d ell
      (fun n ω => raw n (F n ω)) (fun n r ω => Y n r (F n ω)) c₀ negative fiber z) :
    QuantitativeSection4PressureInput ν active d ell raw Y c₀ negative fiber z := by
  have hLp : ∀ n, active n = true → ∀ r, MemLp (Y n r) 2 (ν n) := by
    intro n hn r
    rw [← (hF n).map_eq]
    exact (memLp_map_measure_iff (hY n r).aestronglyMeasurable (hF n).aemeasurable).2
      (h4.pressure_memLp n hn r)
  have hgapMeas (n : ℕ) : Measurable
      (fun ω => |raw n ω - randomFiniteSignedMaxTri Y n ω|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply, randomFiniteSignedMaxTri] using
      ((hraw n).sub (measurable_finiteSignedMax_of_measurable (Y n) (hY n))).norm
  have hgapInt : ∀ n, active n = true → Integrable
      (fun ω => |raw n ω - randomFiniteSignedMaxTri Y n ω|) (ν n) := by
    intro n hn
    rw [← (hF n).map_eq]
    exact (integrable_map_measure (hgapMeas n).aestronglyMeasurable (hF n).aemeasurable).2
      (h4.seam_integrable n hn)
  refine ⟨hgapInt, ?_, hLp, ?_⟩
  · intro n hn
    rw [← integral_comp_measurePreserving_eq (hF n) _ (hgapInt n hn)]
    exact h4.seam_bound n hn
  · intro n hn
    have hmax := (pressure_memLp_and_maxCenteredAbs_of_restriction
      (μ n) (ν n) (F n) (hF n) (Y n) (fun r ω => Y n r (F n ω))
      (hLp n hn) (fun _ => Filter.Eventually.of_forall fun _ => rfl)).2
    rw [← hmax]
    exact h4.pressure_bound n hn

theorem tendstoInProbabilityTri_pushforward_measurePreserving
    {Ω Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (μ : ∀ n, Measure (Ω n)) (ν : ∀ n, Measure (Ξ n))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (F : ∀ n, Ω n → Ξ n) (hF : ∀ n, MeasurePreserving (F n) (μ n) (ν n))
    (X : ∀ n, Ξ n → ℝ) (hX : ∀ n, Measurable (X n)) (a : ℝ)
    (h : TendstoInProbabilityTri μ (fun n ω => X n (F n ω)) a) :
    TendstoInProbabilityTri ν X a := by
  intro ε hε
  have heq (n : ℕ) : (μ n).real {ω | ε ≤ |X n (F n ω) - a|} =
      (ν n).real {ω | ε ≤ |X n ω - a|} := by
    apply congrArg ENNReal.toReal
    have hs : MeasurableSet {ω | ε ≤ |X n ω - a|} := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using
        measurableSet_le measurable_const (((hX n).sub (measurable_const (a := a))).norm)
    exact (hF n).measure_preimage hs.nullMeasurableSet
  simpa only [heq] using h ε hε

end CircularLawSections56.Section5
