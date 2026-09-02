import CircularLawSections56.Section5.TaperSection3Estimates
import CircularLawSections56.Section5.LiteralSourceMoments
import CircularLawSections56.Section5.Section3ScaleEligibility

/-! # The actual taper short-ring theorem from Section 3 source estimates

The input record contains no short-ring limit. The source's matrix moment
conditions are generated from the atom Assumption 2.1 and the actual sampling
map. The least-singular-value scale uses the inner half-band, while counting
uses the actual taper effective bandwidth. Real samples are covered by composing
their proved complexification map and `real_source_moments_complexify`.
-/

open Filter MeasureTheory Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace CircularLawSections56.Section5
open CircularLawSection4 ShortRingAnchor

theorem exists_taper_section3_parameters
    (γ : ℝ) (hγpos : 0 < γ) (hγ : γ < 1 / 8) :
    ∃ χ κ τ, HardEdgeAdmissible (8 / 9 + section3Margin γ / 2) χ κ τ :=
  exists_hardEdgeAdmissible_of_omega (half_pos (section3Margin_spec γ hγpos hγ).1)

structure Section3TaperAnalyticInputs
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : PolynomialTaperProfile) (M W V : ℕ → ℕ) [∀ n, Nonempty (Fin (M n))]
    (hMpos : ∀ n, 0 < M n)
    (H G : ∀ n, Ω → Matrix (Fin (M n)) (Fin (M n)) ℂ) (z : ℂ)
    (κ τ C a CG : ℝ) (R ζ : ℕ → ℝ) (goodLSV goodCount : ℕ → Set Ω) : Prop where
  dense_nonsingular : ShiftedNonsingularInProbability μ G z
  minimum_singular : Theorem31MinimumSingularValueInput hMpos μ H z
    (sourceHardEdgeScale M V κ) goodLSV
  counting : Proposition34AllCutoffsInput μ (shiftedSingularValueProcess H z)
    (fun n => p.hardEdgeCutoff (M n) (W n) τ) (fun _ => C) goodCount
  local_comparison : ∀ r, Lemma35LocalBulkComparisonInput μ
    (shiftedSingularValueProcess H z) (shiftedSingularValueProcess G z)
    (R r) (sourceBulkRate M ζ r)
  dense_negative_moment : BC12GinibreNegativeMomentTightness μ a (shiftedSingularValueProcess G z)
  dense_log_potential : ConvergesInProbability μ
    (fun n ω => normalizedShiftLogDet (G n ω) z) (circularLogPotential z)
  dense_moments : CenteredMatrixRowSecondMomentInputs μ G CG

def literalTaperProcess
    {Ω : Type*} (p : PolynomialTaperProfile) (k W : ℕ → ℕ) (hWpos : ∀ n, 0 < W n)
    (samples : ∀ n, Ω → Fin ((k n + 1) * (taperStateDimension (W n) + 2)) → ℂ) :
    ∀ n, Ω → Matrix (Fin (k n + 1)) (Fin (k n + 1)) ℂ :=
  fun n ω => p.literalMatrix (k n) (W n) (hWpos n) (samples n ω)

theorem section3_sequence_conclusion_to_physical
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k : ℕ → ℕ) (H : ∀ n, Ω → Matrix (Fin (k n + 1)) (Fin (k n + 1)) ℂ) (z : ℂ)
    (h : Proposition36SequenceConclusion μ (fun n => k n + 1) H z) :
    TendstoInProbabilityTri (fun _ => μ)
      (fun n ω => Section6.physicalLogPotential (H n ω) z) (circularLogPotential z) := by
  apply (Section6.tendstoInMeasure_iff_tri μ _ (circularLogPotential z)).1
  simpa only [Proposition36SequenceConclusion, normalizedShiftLogDet,
    Section6.physicalLogPotential, Nat.cast_add, Nat.cast_one] using h

theorem tapered_short_ring_of_section3_estimates
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : PolynomialTaperProfile) (k W : ℕ → ℕ) (hWpos : ∀ n, 0 < W n)
    (hfit : ∀ n, 2 * W n + 1 ≤ k n + 1)
    (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)]
    (hMom : ∀ n, AtomMomentAssumption21 (ν n) id)
    (samples : ∀ n, Ω → Fin ((k n + 1) * (taperStateDimension (W n) + 2)) → ℂ)
    (hSamples : ∀ n, MeasurePreserving (samples n) μ
      (iidMeasure (ν n) ((k n + 1) * (taperStateDimension (W n) + 2))))
    (G : ∀ n, Ω → Matrix (Fin (k n + 1)) (Fin (k n + 1)) ℂ) (z : ℂ)
    (β χ κ τ K C a CG : ℝ) (R ζ : ℕ → ℝ)
    (hparam : HardEdgeAdmissible β χ κ τ)
    (hM : Tendsto (fun n => k n + 1) atTop atTop)
    (hband : ∀ᶠ n in atTop, (k n + 1 : ℝ) ^ β ≤ (W n / 2 : ℕ))
    (hKdom : p.upperWeightConstant ^ (1 / 8 : ℝ) ≤ K) (hC : 0 ≤ C)
    (hRtop : Tendsto R atTop atTop) (hR : ∀ r, Real.sqrt (Real.exp 1) < R r)
    (hζ : ∀ r, 0 < ζ r) (ha : 0 < a)
    (goodLSV goodCount : ℕ → Set Ω)
    (h3 : Section3TaperAnalyticInputs μ p (fun n => k n + 1) W (fun n => W n / 2)
      (fun n => Nat.succ_pos (k n)) (literalTaperProcess p k W hWpos samples) G z
      κ τ C a CG R ζ goodLSV goodCount) :
    Proposition36SequenceConclusion μ (fun n => k n + 1)
      (literalTaperProcess p k W hWpos samples) z := by
  have hH : CenteredMatrixRowSecondMomentInputs μ (literalTaperProcess p k W hWpos samples) 1 :=
    literal_source_centered_row_moments μ k (PolynomialTaperProfile.dimensions W)
      (PolynomialTaperProfile.centers W hWpos) (p.profiles W hWpos)
      (fun n => p.lowerParameter_pos (W n))
      (fun n => (PolynomialTaperProfile.literalMatrix_band_fits (k n) (W n) (hWpos n)).2 (hfit n))
      ν hMom samples hSamples
  apply section3_short_ring_of_taper_estimates μ p (fun n => k n + 1) W (fun n => W n / 2)
    (literalTaperProcess p k W hWpos samples) G z β χ κ τ K C a 1 CG R ζ
    hparam (fun n => Nat.succ_pos (k n)) hM hWpos (fun n => Nat.div_le_self (W n) 2)
    _ hKdom hC hRtop hR hζ ha h3.dense_nonsingular goodLSV goodCount
    h3.minimum_singular h3.counting h3.local_comparison h3.dense_negative_moment
    h3.dense_log_potential hH h3.dense_moments
  simpa only [Nat.cast_add, Nat.cast_one] using hband

end CircularLawSections56.Section5
