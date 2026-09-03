import ShortRingAnchor.UpperEdge
import ShortRingAnchor.GinibreLowerEdge

/-!
# Probability deductions from finite-dimensional moment formulas

These are proved consequences, not external Ginibre inputs.  In the BC12
application the first two correlation functions give finite-dimensional
means and variances; Chebyshev then yields convergence in probability.
An integrable uniform negative-moment bound similarly gives the tightness
premise used in manuscript (3.14).
-/

open Filter Set MeasureTheory
open scoped ENNReal Topology

namespace ShortRingAnchor.BC12

/-- Chebyshev's step in BC12, proved from the existing Markov theorem.
The centre may depend on the dimension. -/
theorem centered_convergesInProbability_of_square_bound
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {X : ℕ → Omega → ℝ} {m rate : ℕ → ℝ}
    (hint : ∀ n, Integrable (fun sample => (X n sample - m n) ^ 2) mu)
    (hbound : ∀ n, ∫ sample, (X n sample - m n) ^ 2 ∂mu ≤ rate n)
    (hrate : Tendsto rate atTop (nhds 0)) :
    ConvergesInProbability mu (fun n sample => X n sample - m n) 0 := by
  have hsquare := convergesInProbability_of_nonneg_integral_bound hint
    (fun n sample => sq_nonneg (X n sample - m n)) hbound hrate
  rw [convergesInProbability_iff_norm] at hsquare ⊢
  intro epsilon hepsilon
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hsquare (epsilon ^ 2) (sq_pos_of_pos hepsilon))
  · intro n
    exact zero_le
  · intro n
    apply measure_mono
    intro sample hsample
    simp only [sub_zero, Real.norm_eq_abs] at hsample ⊢
    change epsilon ≤ |X n sample - m n| at hsample
    change epsilon ^ 2 ≤ |(X n sample - m n) ^ 2|
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (X n sample - m n)]

/-- Deterministic means converging and centred second moments tending to
zero imply convergence in probability.  No random-matrix theorem is used. -/
theorem convergesInProbability_of_mean_and_square_bound
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {X : ℕ → Omega → ℝ} {m rate : ℕ → ℝ} {limit : ℝ}
    (hint : ∀ n, Integrable (fun sample => (X n sample - m n) ^ 2) mu)
    (hbound : ∀ n, ∫ sample, (X n sample - m n) ^ 2 ∂mu ≤ rate n)
    (hrate : Tendsto rate atTop (nhds 0))
    (hmean : Tendsto m atTop (nhds limit)) :
    ConvergesInProbability mu X limit := by
  have hcenter := centered_convergesInProbability_of_square_bound hint hbound hrate
  have hm : ConvergesInProbability mu (fun n (_ : Omega) => m n) limit :=
    tendstoInMeasure_of_tendsto_ae
      (fun _ => aestronglyMeasurable_const) (.of_forall fun _ => hmean)
  simpa only [sub_add_cancel, zero_add] using hcenter.add hm

/-- The `C / M` variance rate needed for finite-rank Ginibre kernels tends
to zero along any dimension sequence tending to infinity. -/
theorem const_div_dimension_tendsto_zero
    {M : ℕ → ℕ} (hM : Tendsto M atTop atTop) (C : ℝ) :
    Tendsto (fun n => C / (M n : ℝ)) atTop (nhds 0) :=
  (tendsto_const_div_atTop_nhds_zero_nat C).comp hM

/-- Uniform nonnegative first moments imply tightness; this supplies the
probability deduction after a singular-value density calculation. -/
theorem boundedInProbability_of_nonneg_integral_bound
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {X : ℕ → Omega → ℝ} {C : ℝ}
    (hint : ∀ n, Integrable (X n) mu)
    (hnonneg : ∀ n sample, 0 ≤ X n sample)
    (hmean : ∀ n, ∫ sample, X n sample ∂mu ≤ C) :
    BoundedInProbability mu X := by
  intro delta hdelta
  have ht : Tendsto (fun k : ℕ => ENNReal.ofReal (C / (k : ℝ))) atTop (nhds 0) := by
    have hreal : Tendsto (fun k : ℕ => C / (k : ℝ)) atTop (nhds (0 : ℝ)) :=
      tendsto_const_div_atTop_nhds_zero_nat C
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
    change Tendsto (fun k : ℕ => ENNReal.ofReal (C / (k : ℝ))) atTop
      (nhds (ENNReal.ofReal 0)) at h
    simpa only [ENNReal.ofReal_zero] using h
  obtain ⟨k, hk, hkpos⟩ :=
    ((ht.eventually (Iio_mem_nhds hdelta)).and (eventually_gt_atTop (0 : ℕ))).exists
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  refine ⟨(k : ℝ), hkreal, .of_forall fun n => ?_⟩
  refine lt_of_le_of_lt (le_trans (measure_mono ?_)
    (measure_ge_le_of_integral_le (hint n) (hnonneg n) (hmean n) hkreal)) hk
  intro sample hsample
  change (k : ℝ) ≤ X n sample
  change (k : ℝ) < ‖X n sample‖ at hsample
  simp only [Real.norm_eq_abs, abs_of_nonneg (hnonneg n sample)] at hsample
  exact hsample.le

/-- Conditional BC12 negative-moment conclusion from a uniform integrable
moment estimate.  This does not claim that the shifted Ginibre density
estimate itself has been proved. -/
theorem negativeMomentTightness_of_uniform_integral_bound
    {Omega : Type*} [MeasurableSpace Omega]
    {I : ℕ → Type*} [∀ n, Fintype (I n)]
    {mu : Measure Omega} (p : ℝ)
    (s : ∀ n, Omega → I n → ℝ) {C : ℝ}
    (hs : ∀ n sample i, 0 ≤ s n sample i)
    (hint : ∀ n, Integrable (fun sample => normalizedNegativeMoment p (s n sample)) mu)
    (hmean : ∀ n, ∫ sample, normalizedNegativeMoment p (s n sample) ∂mu ≤ C) :
    BC12GinibreNegativeMomentTightness mu p s :=
  boundedInProbability_of_nonneg_integral_bound hint
    (fun n sample => normalizedNegativeMoment_nonneg (hs n sample)) hmean

end ShortRingAnchor.BC12
