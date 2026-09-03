import BernoulliSection10Source.LiteratureInputs
import BernoulliSection10.Section3Counting
import ShortRingAnchor.HermitizationCountingFromV3
import ShortRingAnchor.Lemma35FromV3
import ShortRingAnchor.Proposition36

/-!
# Section 10.1 with the actual Section 3 counting and bulk proofs connected

This internal theorem is shared by real and complex atoms. Its LSV and
row-moment inputs are discharged in the two density-specific public adapters.
All counting events, comparison rates, cutoff choices and Gaussian models
are constructed here from the accepted BBV and BC12 hypotheses.
-/

open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section
namespace BernoulliSection10Source
open BernoulliSection10 BernoulliSection10.SourceInputs ShortRingAnchor Arxiv2410V3

set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem fullBlock_log_limit_from_source
    (hBBV : BBVComparisonInput) (hBC12 : BC12GinibreInput)
    {E : Type} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (atom : E → ℂ) (hatom : AtomMomentAssumption21 μ atom)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    {β χ κ τ : ℝ} (hp : HardEdgeAdmissible β χ κ τ) (hβ1 : β ≤ 1)
    (hhigh : ∀ᶠ n in atTop, (((s n + 3) * W n : ℕ) : ℝ) ^ β ≤ W n)
    (z : ℂ)
    (hmom : CenteredMatrixRowSecondMomentInputs (sampleLaw μ)
      (fun n => actualProfileMatrix atom (physicalProfile (W n) (s n))) 1)
    (hmin : ∃ good, Theorem31MinimumSingularValueInput
      (fun n => Nat.mul_pos (by omega) (hW n)) (sampleLaw μ)
      (fun n => actualProfileMatrix atom (physicalProfile (W n) (s n))) z
      (sourceHardEdgeScale (fun n => (s n + 3) * W n) W κ) good) :
    ConvergesInProbability (sampleLaw μ)
      (fun n ω => normalizedShiftLogDet
        (actualProfileMatrix atom (physicalProfile (W n) (s n)) ω) z)
      (circularLogPotential z) := by
  let N := fun n => (s n + 3) * W n
  have hN (n : ℕ) : 0 < N n := Nat.mul_pos (by omega) (hW n)
  letI (n : ℕ) : Nonempty (Fin (N n)) := ⟨⟨0, hN n⟩⟩
  have hNtop : Tendsto N atTop atTop :=
    tendsto_atTop_mono' atTop
      (Eventually.of_forall fun n => Nat.le_mul_of_pos_left (W n) (by omega)) hWtop
  let σ := fun n => physicalProfile (W n) (s n)
  let modelA := fun n => profileV3Model μ atom hatom (σ n)
    (physicalProfile_doublyStochastic (W n) (s n) (hW n))
  let modelG := fun n => gaussianV3Model μ (hN n)
  let BA := fun n => 3 * (W n : ℝ)
  let BG := fun n => (N n : ℝ)
  have hBA (n) : IsBandwidth (modelA n).profile (BA n) :=
    physical_source_bandwidth (W n) (s n) (hW n)
  have hBG (n) : IsBandwidth (modelG n).profile (BG n) :=
    gaussianV3Model_bandwidth μ (hN n)
  have hβ : 0 < β := by have := hp.1; have := hp.2.2.2.1; linarith
  have hscaleA : ∀ᶠ n in atTop, (N n : ℝ) ^ β ≤ BA n := by
    filter_upwards [hhigh] with n hn
    exact hn.trans (by dsimp [BA]; have := Nat.cast_nonneg (α := ℝ) (W n); linarith)
  have hscaleG : ∀ᶠ n in atTop, (N n : ℝ) ^ β ≤ BG n := by
    apply Eventually.of_forall
    intro n
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN n) hβ1
  obtain ⟨C0, _hC0, hbbv⟩ := hBBV
  let mA := (∫ x, ‖atom x‖ ^ 3 ∂μ) + BVH.complexGaussianThirdMomentConstant
  let mG := (∫ x, ‖circularGaussianAtom x‖ ^ 3 ∂circularGaussianPairLaw) +
    BVH.complexGaussianThirdMomentConstant
  let C := max 8 (max C0 (max mA mG))
  have hC : 8 ≤ C := le_max_left _ _
  have hC0C : C0 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hthirdA (n) : BVH.atomThirdMoment (modelA n) +
      BVH.complexGaussianThirdMomentConstant ≤ C :=
    (le_max_left mA mG).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hthirdG (n) : BVH.atomThirdMoment (modelG n) +
      BVH.complexGaussianThirdMomentConstant ≤ C :=
    (le_max_right mA mG).trans ((le_max_right _ _).trans (le_max_right _ _))
  have bbvA (n : ℕ) (η : ℂ) (hη : 0 < η.im) :
      CanonicalBBVAt (modelA n) z η (BA n) C :=
    canonicalBBVAt_mono
      (hbbv (SampleSpace E) E (sampleLaw μ) μ (N n) (hN n) (modelA n)
        (BA n) (hBA n) z η hη) (hBA n).1 hη hC0C
  have bbvG (n : ℕ) (η : ℂ) (hη : 0 < η.im) :
      CanonicalBBVAt (modelG n) z η (BG n) C :=
    canonicalBBVAt_mono
      (hbbv (SampleSpace E) (ℝ × ℝ) (sampleLaw μ) circularGaussianPairLaw
        (N n) (hN n) (modelG n) (BG n) (hBG n) z η hη)
      (hBG n).1 hη hC0C
  obtain ⟨goodCount, hCount⟩ := hermitizationAllCutoffsCountingInput_of_v3_model
    hN hNtop modelA z hC hp.2.2.1 BA hBA hthirdA
    (fun n v hv => bbvA n (spectralParameter 0 v) (by simpa [spectralParameter] using hv))
  have hAll := proposition34AllCutoffsInput_of_hermitization
    (fun n => (modelA n).matrix) z _ _ goodCount hCount
  obtain ⟨good', hCount'⟩ := hAll.specialize_eventually
    (mesoscopicThreshold_le_sourceCutoff_eventually hN hNtop BA hp hscaleA)
  let R := fun r : ℕ => Real.sqrt (Real.exp 1) + (r : ℝ) + 1
  have hR (r : ℕ) : Real.sqrt (Real.exp 1) < R r := by
    dsimp [R]
    have := Nat.cast_nonneg (α := ℝ) r
    linarith
  have hRpos (r : ℕ) : 0 < R r := (Real.sqrt_nonneg _).trans_lt (hR r)
  have hRtop : Tendsto R atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
    exact Eventually.of_forall fun r => by
      dsimp [R]; have := Real.sqrt_nonneg (Real.exp 1); linarith
  have hBulk (r : ℕ) := lemma35LocalBulkComparisonInput_of_v3_models
    hNtop modelA modelG z (hRpos r).le hC hβ BA BG hBA hBG hscaleA hscaleG
    hthirdA hthirdG
    (fun n u => bbvA n _ (by
      simpa [spectralParameter, localBulkHeight] using
        Real.rpow_pos_of_pos (Nat.cast_pos.mpr (hN n)) (-(localBulkEffectiveExponent β / 16))))
    (fun n u => bbvG n _ (by
      simpa [spectralParameter, localBulkHeight] using
        Real.rpow_pos_of_pos (Nat.cast_pos.mpr (hN n)) (-(localBulkEffectiveExponent β / 16))))
  obtain ⟨p, hpp, hneg, hfull⟩ := bc12_on_sampleLaw hBC12 μ N hN hNtop z
  obtain ⟨goodLSV, hLSV⟩ := hmin
  exact proposition36_matrix_form_highProbability
    (fun n => actualProfileMatrix atom (σ n)) (fun n => actualGinibre (N n)) z
    (sourceCutoff N 1 β τ) (fun _ => 2 * 6) (sourceHardEdgeScale N W κ) R
    (fun _ n => (N n : ℝ) ^ (-localBulkRateExponent β)) p (1 + ‖z‖ ^ 2) (1 + ‖z‖ ^ 2)
    (fun n => sourceCutoff_pos (by norm_num) (hN n)) (fun _ => sourceCutoff_le_one)
    (sourceCutoff_tendsto_zero hp hNtop)
    (fun n => sourceHardEdgeScale_nonneg (hN n) (hW n))
    (actualGinibre_nonsingular μ N hN z) goodLSV good'
    (theorem31LeastSingularValueInput_of_minimum hN _ z _ goodLSV hLSV)
    hCount' (sourceHardEdgeError_tendsto_zero hp hNtop hhigh (by norm_num) (by norm_num))
    hBulk
    (fun r => sourceBulkCutoffBookkeeping_tendsto_zero hp hNtop (by norm_num)
      (hRpos r) (localBulkRateExponent_pos hβ))
    hpp hneg hfull hRtop hR
    (upperSecondMomentInputs_of_centered_matrix_entries _ _ z 1 1 hmom
      (actualGinibre_row_moments μ N hN))

end BernoulliSection10Source
