import CircularLawSection6.CompactCutoffExpectation
import CircularLawSection6.RoutedBandCoupling
import CircularLawSection6.MatrixParameterNonvanishing

/-! # Fixed-cutoff expectation on the actual IID routed matrix law

The matrix energy and almost-sure nonsingularity assumptions in the
compact-cutoff theorem are discharged for the actual IID routed model.
The remaining input is explicitly a bounded squared-singular probability
comparison and its limiting law, not an expectation convergence premise.
-/

open MeasureTheory Filter Topology TaoVuReplacement
open CircularLawSections56.Section5
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem routedBand_expected_energy
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (route : ι → κ → ι) (hroute : ∀ i, Function.Injective (route i))
    (b : κ → ℂ) (hb : ∑ s, ‖b s‖ ^ 2 = 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hMoment : (∫ u : ℂ, ‖u‖ ^ 2 ∂ν) = 1) :
    Integrable (fun ω => hilbertSchmidtSq (routedBandMatrix route b ω))
      (Measure.pi (fun _ : ι × κ => ν)) ∧
      (∫ ω, hilbertSchmidtSq (routedBandMatrix route b ω)
        ∂Measure.pi (fun _ : ι × κ => ν)) = (Fintype.card ι : ℝ) := by
  simpa only [hilbertSchmidtSq, routedBand_row_energy route hroute,
    Finset.card_univ, hb, hMoment, mul_one] using
    routedAtoms_expected_boundary_energy (Finset.univ : Finset ι) b ν hInt

theorem expected_shifted_scaled_energy_le
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → Matrix ι ι ℂ) (hA : Measurable A)
    (hE : Integrable (fun ω => hilbertSchmidtSq (A ω)) μ)
    (hmean : (∫ ω, hilbertSchmidtSq (A ω) ∂μ) = (Fintype.card ι : ℝ)) (c z : ℂ) :
    Integrable (fun ω => hilbertSchmidtSq (c • A ω - z • 1)) μ ∧
      (∫ ω, hilbertSchmidtSq (c • A ω - z • 1) ∂μ) / (Fintype.card ι : ℝ) ≤
        2 * ‖c‖ ^ 2 + 2 * ‖z‖ ^ 2 := by
  have hscale : Integrable (fun ω => hilbertSchmidtSq (c • A ω)) μ := by
    simpa only [hilbertSchmidtSq_smul] using hE.const_mul (‖c‖ ^ 2)
  have hint := integrable_hilbertSchmidtSq_sub μ (fun ω => c • A ω) (fun _ => z • 1)
    (hA.const_smul c) measurable_const hscale (integrable_const _)
  have hI : hilbertSchmidtSq (z • (1 : Matrix ι ι ℂ)) = ‖z‖ ^ 2 * (Fintype.card ι : ℝ) := by
    rw [hilbertSchmidtSq_smul]
    simp [hilbertSchmidtSq, Matrix.one_apply]
  refine ⟨hint, (div_le_iff₀ (Nat.cast_pos.mpr (Fintype.card_pos (α := ι)))).mpr ?_⟩
  calc
    _ ≤ ∫ ω, 2 * hilbertSchmidtSq (c • A ω) + 2 * hilbertSchmidtSq (z • (1 : Matrix ι ι ℂ)) ∂μ :=
      integral_mono hint ((hscale.const_mul 2).add (integrable_const _))
        (fun ω => hilbertSchmidtSq_sub_le _ _)
    _ = _ := by
      rw [integral_add (hscale.const_mul 2) (integrable_const _), integral_const_mul, integral_const, hI]
      simp_rw [hilbertSchmidtSq_smul]
      rw [integral_const_mul, hmean]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      ring

theorem routedBand_expected_cutoff_limit_ae
    {ι κ : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    [∀ n, Nonempty (ι n)] [∀ n, Fintype (κ n)]
    (route : ∀ n, ι n → κ n → ι n) (hroute : ∀ n i, Function.Injective (route n i))
    (b : ∀ n, κ n → ℂ) (hb : ∀ n, ∑ s, ‖b n s‖ ^ 2 = 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hMoment : (∫ u : ℂ, ‖u‖ ^ 2 ∂ν) = 1) (c : ℂ) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ σ : Measure ℝ, IsProbabilityMeasure σ →
      (∀ᵐ s ∂σ, 0 ≤ s) → Integrable (fun s : ℝ => s ^ 2) σ →
      (∀ φ : ℝ → ℝ, Continuous φ → (∃ B : ℝ, ∀ x, |φ x| ≤ B) →
        TendstoInProbabilityTri (fun n => Measure.pi (fun _ : ι n × κ n => ν))
          (fun n ω => matrixSquaredSingularAverage (c • routedBandMatrix (route n) (b n) ω - z • 1) φ)
          (∫ s, φ (s ^ 2) ∂σ)) →
      ∀ a : ℝ, 0 < a →
        Tendsto (fun n => ∫ ω, matrixCutoffPotential
          (c • routedBandMatrix (route n) (b n) ω - z • 1) a
            ∂Measure.pi (fun _ : ι n × κ n => ν))
          atTop (𝓝 (∫ s, Real.log (max s a) ∂σ)) := by
  let μ (n : ℕ) := Measure.pi (fun _ : ι n × κ n => ν)
  have hM (n : ℕ) := routedBandMatrix_measurable (route n) (b n)
  have hdet := ae_all_iff.2 (fun n => ae_shifted_matrix_det_ne_zero (μ n)
    (fun ω => c • routedBandMatrix (route n) (b n) ω) ((hM n).const_smul c))
  have henergy (n : ℕ) := routedBand_expected_energy (route n) (hroute n) (b n) (hb n) ν hInt hMoment
  filter_upwards [hdet] with z hz
  intro σ hσ hσpos hσsecond hweak a ha
  let : IsProbabilityMeasure σ := hσ
  have hshift (n : ℕ) := expected_shifted_scaled_energy_le (μ n)
    (routedBandMatrix (route n) (b n)) (hM n) (henergy n).1 (henergy n).2 c z
  exact matrixCutoff_expectation_of_squared_singular_probability μ
    (fun n ω => c • routedBandMatrix (route n) (b n) ω - z • 1)
    (fun n => ((hM n).const_smul c).sub measurable_const) hz (fun n => (hshift n).1)
    (2 * ‖c‖ ^ 2 + 2 * ‖z‖ ^ 2) (fun n => (hshift n).2) σ hσpos hσsecond hweak ha

end CircularLawSection6
