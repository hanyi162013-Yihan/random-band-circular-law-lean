import CircularLawSections56.Section5.TaperShortRingSource
import ShortRingAnchor.BC12.GaussianMatrixLawBridge
import ShortRingAnchor.BC12.GinibreNegativeMoments
import ShortRingAnchor.Proposition38.Assembly

/-!
# Removing Gaussian conclusions from the taper source interface

Only the taper's LSV, count and local comparison are analytic fields.
The reference's law and dense variance profile are model data. Its
nonsingularity, negative moment, full-log limit and row moments are proved.
This does not assert the taper's still-conditional LSV/count/comparison inputs.
-/

open Filter MeasureTheory ProbabilityTheory Topology ShortRingAnchor Arxiv2410V3
noncomputable section
namespace CircularLawSections56.Section5

local instance taperGaussianMatrixMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := borel _
local instance taperGaussianMatrixBorelSpace (n : ℕ) :
    BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩

/-- The three non-Gaussian estimates used by the taper short-ring argument. -/
structure Section3TaperNonGaussianInputs
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : PolynomialTaperProfile) (M W V : ℕ → ℕ) [∀ n, Nonempty (Fin (M n))]
    (hMpos : ∀ n, 0 < M n)
    (H G : ∀ n, Ω → Matrix (Fin (M n)) (Fin (M n)) ℂ) (z : ℂ)
    (κ τ C : ℝ) (R ζ : ℕ → ℝ) (goodLSV goodCount : ℕ → Set Ω) : Prop where
  minimum_singular : Theorem31MinimumSingularValueInput hMpos μ H z
    (sourceHardEdgeScale M V κ) goodLSV
  counting : Proposition34AllCutoffsInput μ (shiftedSingularValueProcess H z)
    (fun n => p.hardEdgeCutoff (M n) (W n) τ) (fun _ => C) goodCount
  local_comparison : ∀ r, Lemma35LocalBulkComparisonInput μ
    (shiftedSingularValueProcess H z) (shiftedSingularValueProcess G z)
    (R r) (sourceBulkRate M ζ r)

/-- Section 3 truncation for taper profiles: all four Gaussian analytic
fields of the older interface are constructed, with exponent `1/128`. -/
theorem Section3TaperNonGaussianInputs.toAnalytic
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : PolynomialTaperProfile) (M W V : ℕ → ℕ) [∀ n, Nonempty (Fin (M n))]
    (hMpos : ∀ n, 0 < M n) (hM : Tendsto M atTop atTop)
    (H : ∀ n, Ω → Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (G : ∀ n, RandomMatrixModelV3 (M n) Ω Ξ μ ν)
    (hGinibre : ∀ n, HasLaw (G n).matrix (BC12.normalizedGinibreLaw (M n)) μ)
    (hGband : ∀ n, IsBandwidth (G n).profile (M n : ℝ))
    (z : ℂ) (κ τ C D : ℝ) (R ζ : ℕ → ℝ) (goodLSV goodCount : ℕ → Set Ω)
    (hD : 8 ≤ D)
    (hthird : ∀ n, BVH.atomThirdMoment (G n) + BVH.complexGaussianThirdMomentConstant ≤ D)
    (bbv : ∀ n v, 0 < v → CanonicalBBVAt (G n) z (spectralParameter 0 v) (M n : ℝ) D)
    (h : Section3TaperNonGaussianInputs μ p M W V hMpos H
      (fun n => (G n).matrix) z κ τ C R ζ goodLSV goodCount) :
    Section3TaperAnalyticInputs μ p M W V hMpos H (fun n => (G n).matrix) z
      κ τ C (1 / 128) 1 R ζ goodLSV goodCount where
  dense_nonsingular := Proposition38.reference_nonsingular_of_formulas hMpos
    (fun n => (G n).matrix)
    (fun n => BC12.normalizedGinibre_correlations (hMpos n) (hGinibre n)) z
  minimum_singular := h.minimum_singular
  counting := h.counting
  local_comparison := h.local_comparison
  dense_negative_moment := BC12.negativeMomentTightness_of_ginibreLaw_and_v3
    hMpos hM G hGinibre hGband z hD hthird bbv
  dense_log_potential := BC12.ginibre_logdet_convergesInProbability_of_ginibreLaw
    hMpos hM (fun n => (G n).matrix) hGinibre z
  dense_moments := Proposition38.centeredRowMoments_of_v3 G

/-- The literal taper short-ring conclusion with no external Gaussian estimate.
The three remaining analytic inputs concern the taper, not its Ginibre reference. -/
theorem tapered_short_ring_of_section3_estimates_withoutBC12
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {νG : Measure Ξ} [IsProbabilityMeasure νG]
    (p : PolynomialTaperProfile) (k W : ℕ → ℕ) (hWpos : ∀ n, 0 < W n)
    (hfit : ∀ n, 2 * W n + 1 ≤ k n + 1)
    (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)]
    (hMom : ∀ n, AtomMomentAssumption21 (ν n) id)
    (samples : ∀ n, Ω → Fin ((k n + 1) * (taperStateDimension (W n) + 2)) → ℂ)
    (hSamples : ∀ n, MeasurePreserving (samples n) μ
      (CircularLawSection4.iidMeasure (ν n) ((k n + 1) * (taperStateDimension (W n) + 2))))
    (G : ∀ n, RandomMatrixModelV3 (k n + 1) Ω Ξ μ νG)
    (hGinibre : ∀ n, HasLaw (G n).matrix (BC12.normalizedGinibreLaw (k n + 1)) μ)
    (hGband : ∀ n, IsBandwidth (G n).profile (k n + 1 : ℕ))
    (z : ℂ) (β χ κ τ K C D : ℝ) (R ζ : ℕ → ℝ)
    (hparam : HardEdgeAdmissible β χ κ τ)
    (hM : Tendsto (fun n => k n + 1) atTop atTop)
    (hband : ∀ᶠ n in atTop, (k n + 1 : ℝ) ^ β ≤ (W n / 2 : ℕ))
    (hKdom : p.upperWeightConstant ^ (1 / 8 : ℝ) ≤ K) (hC : 0 ≤ C)
    (hRtop : Tendsto R atTop atTop) (hR : ∀ r, Real.sqrt (Real.exp 1) < R r)
    (hζ : ∀ r, 0 < ζ r) (hD : 8 ≤ D)
    (hthird : ∀ n, BVH.atomThirdMoment (G n) + BVH.complexGaussianThirdMomentConstant ≤ D)
    (bbv : ∀ n v, 0 < v → CanonicalBBVAt (G n) z (spectralParameter 0 v) (k n + 1 : ℕ) D)
    (goodLSV goodCount : ℕ → Set Ω)
    (h3 : Section3TaperNonGaussianInputs μ p (fun n => k n + 1) W (fun n => W n / 2)
      (fun n => Nat.succ_pos (k n)) (literalTaperProcess p k W hWpos samples)
      (fun n => (G n).matrix) z κ τ C R ζ goodLSV goodCount) :
    Proposition36SequenceConclusion μ (fun n => k n + 1)
      (literalTaperProcess p k W hWpos samples) z := by
  have hfull := h3.toAnalytic p (fun n => k n + 1) W (fun n => W n / 2)
    (fun n => Nat.succ_pos (k n)) hM (literalTaperProcess p k W hWpos samples)
    G hGinibre hGband z κ τ C D R ζ goodLSV goodCount hD hthird bbv
  exact tapered_short_ring_of_section3_estimates μ p k W hWpos hfit ν hMom samples hSamples
    (fun n => (G n).matrix) z β χ κ τ K C (1 / 128) 1 R ζ hparam hM hband hKdom hC
    hRtop hR hζ (by norm_num) goodLSV goodCount hfull

end CircularLawSections56.Section5
