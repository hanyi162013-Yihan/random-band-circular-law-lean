import ShortRingAnchor.Proposition38.LeastValue
import ShortRingAnchor.Proposition38.V3Moments
import ShortRingAnchor.HermitizationCountingFromV3
import ShortRingAnchor.Lemma35Concrete
import ShortRingAnchor.Proposition36
import ShortRingAnchor.BC12.LogdetConvergence

/-!
# Proposition 3.8: complete logarithmic-potential assembly

Equations (3.18)--(3.25). The new external boundary consists precisely of
Proposition 3.2 and Cook 1.12. The pre-existing section3 BBV and BC12
boundary stays explicit: BBV is instantiated for the two actual models;
the BC12 negative-moment conclusion remains a named baseline input, while
the full Ginibre logdet conclusion is derived from its exact finite
correlation/projection formulas. No density of the subgaussian atom is
required. All fixed complex shifts are permitted.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Arxiv2410V3
open scoped Topology BigOperators
namespace ShortRingAnchor.Proposition38

/-- Proposition 3.8, Ginibre reference: the first finite correlation
formula supplies nonsingularity; it is not an additional hypothesis. -/
theorem reference_nonsingular_of_formulas
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k)
    (G : ∀ k, Ω → Matrix (Fin (N k)) (Fin (N k)) ℂ)
    (hcorrelation : ∀ k, BC12.GinibreCorrelationFormulas μ
      (fun sample => BC12.matrixEigenvalues (G k sample))) (z : ℂ) :
    ShiftedNonsingularInProbability μ G z := by
  apply shiftedNonsingularInProbability_of_ae
  intro k
  filter_upwards [BC12.eigenvalues_ne_fixed_ae_of_firstMoment (hN k) (hcorrelation k) z]
    with sample hs
  apply norm_ne_zero_iff.mp
  rw [BC12.norm_shifted_det_eq_prod_of_enumeration (BC12.matrixEigenvalues_spec _) z]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hs i)))

/-- **Proposition 3.8, equation (3.19), on the existing section3 external
boundary.** The actual real-subgaussian full-block matrix is used throughout.

New literature hypotheses: `known32`, `knownCook`. Retained baseline:
`bbvA`, `bbvG`, `hBC12Negative`, and the exact finite Ginibre formulas.
There are no supplied norm, connectivity, spread, LSV, count, CDF,
hard-edge rate, upper-tail, or full-logdet conclusions for the ring.
-/
theorem proposition38
    {Ω ΞG : Type*} [MeasurableSpace Ω] [MeasurableSpace ΞG]
    {μ : Measure Ω} {νG : Measure ΞG} [IsProbabilityMeasure μ] [IsProbabilityMeasure νG]
    (A : Atom) {s W : ℕ → ℕ} (hW : ∀ k, 0 < W k) (hs : ∀ k, 0 < s k)
    (S : ∀ k, AtomArray μ A (Fin ((s k + 3) * W k) × Fin ((s k + 3) * W k)))
    (denseAtom : ∀ k, Ω → Fin ((s k + 3) * W k) → Fin ((s k + 3) * W k) → ℂ)
    (atomG : ΞG → ℂ) (hatomG : AtomMomentAssumption21 νG atomG)
    (hcopiesG : ∀ k, IndependentAtomCopies21 μ νG atomG
      (fun ij : Fin ((s k + 3) * W k) × Fin ((s k + 3) * W k) =>
        fun sample => denseAtom k sample ij.1 ij.2))
    (z : ℂ) (omega comparisonConstant p : ℝ)
    (homega : 0 < omega ∧ omega < 1 / 9)
    (hN : Tendsto (fun k => (s k + 3) * W k) atTop atTop)
    (hWtop : Tendsto W atTop atTop)
    (hband : ∀ᶠ k in atTop,
      (((s k + 3) * W k : ℕ) : ℝ) ^ (8 / 9 + omega) ≤ W k)
    (known32 : Proposition32Input μ A z) (knownCook : Cook112Input μ A)
    (bbvA : ∀ k eta, 0 < eta.im → CanonicalBBVAt
      (fullBlockV3Model (hW k) (S k)) z eta (3 * (W k : ℝ))
      (max comparisonConstant (sourceV3MomentBudget A.law νG (fun x : ℝ => (x : ℂ)) atomG)))
    (bbvG : ∀ k eta, 0 < eta.im → CanonicalBBVAt
      (denseV3Model (Nat.mul_pos (show 0 < s k + 3 by omega) (hW k))
        (denseAtom k) atomG hatomG (hcopiesG k))
      z eta (((s k + 3) * W k : ℕ) : ℝ)
      (max comparisonConstant (sourceV3MomentBudget A.law νG (fun x : ℝ => (x : ℂ)) atomG)))
    (hp : 0 < p)
    (hBC12Negative : BC12GinibreNegativeMomentTightness μ p
      (shiftedSingularValueProcess (normalizedDenseMatrixProcess denseAtom) z))
    (hprojection : ∀ k, BC12.GinibreProjectionIntegralFormula ((s k + 3) * W k))
    (hcorrelation : ∀ k, BC12.GinibreCorrelationFormulas μ
      (fun sample => BC12.matrixEigenvalues (normalizedDenseMatrixProcess denseAtom k sample))) :
    Conclusion μ (fun k => (s k + 3) * W k) (fun k => fullBlockMatrix (S k)) z := by
  let N := fun k => (s k + 3) * W k
  have hNpos (k) : 0 < N k := Nat.mul_pos (by omega) (hW k)
  letI : ∀ k, Nonempty (Fin (N k)) := fun k => Fin.pos_iff_nonempty.mp (hNpos k)
  let modelA := fun k => fullBlockV3Model (hW k) (S k)
  let modelG := fun k => denseV3Model (hNpos k) (denseAtom k) atomG hatomG (hcopiesG k)
  let H := fun k => fullBlockMatrix (S k)
  let G := normalizedDenseMatrixProcess denseAtom
  let beta := (8 / 9 : ℝ) + omega
  let C := max comparisonConstant (sourceV3MomentBudget A.law νG (fun x : ℝ => (x : ℂ)) atomG)
  have hbeta0 : 0 < beta := by dsimp [beta]; linarith [homega.1]
  have hbeta2 : beta ≤ 2 := by dsimp [beta]; linarith [homega.2]
  have hC : 8 ≤ C := (sourceV3MomentBudget_ge_eight (fun x : ℝ => (x : ℂ)) atomG).trans
    (le_max_right comparisonConstant _)
  have hthirdA (k) : BVH.atomThirdMoment (modelA k) + BVH.complexGaussianThirdMomentConstant ≤ C :=
    (sourceV3MomentBudget_ge_left (fun x : ℝ => (x : ℂ)) atomG).trans (le_max_right comparisonConstant _)
  have hthirdG (k) : BVH.atomThirdMoment (modelG k) + BVH.complexGaussianThirdMomentConstant ≤ C :=
    (sourceV3MomentBudget_ge_right (fun x : ℝ => (x : ℂ)) atomG).trans (le_max_right comparisonConstant _)
  obtain ⟨chi, kappa, tau, hparam⟩ := exists_hardEdgeAdmissible_of_omega homega.1
  let a := sourceCutoff N 1 beta tau
  let L := sourceHardEdgeScale N W kappa
  obtain ⟨goodLSV, hLSV⟩ := leastSingularValueInput_of_known A hW hs S z known32 knownCook
    (show 1 / 2 < beta by dsimp [beta]; linarith [homega.1]) hparam.2.1 hN hWtop hband
  obtain ⟨goodCount0, hcount0⟩ := hermitizationAllCutoffsCountingInput_of_v3_model
    hNpos hN modelA z hC hparam.2.2.1 (fun k => 3 * (W k : ℝ))
    (fun k => fullBlockV3Model_isBandwidth (hW k) (S k)) hthirdA
    (fun k v hv => bbvA k (spectralParameter 0 v) (by simpa [spectralParameter] using hv))
  have hcounts : Proposition34AllCutoffsInput μ (shiftedSingularValueProcess H z)
      (fun k => (3 * (W k : ℝ)) ^ (-(1 / 8 : ℝ)) * (N k : ℝ) ^ tau)
      (fun _ => 12) goodCount0 := by
    simpa only [show (2 : ℝ) * 6 = 12 by norm_num] using
      proposition34AllCutoffsInput_of_hermitization H z _ (fun _ => 6) goodCount0 hcount0
  have hBband : ∀ᶠ k in atTop, (N k : ℝ) ^ beta ≤ 3 * (W k : ℝ) := by
    filter_upwards [hband] with k hk
    exact hk.trans (by have := Nat.cast_nonneg (W k) (α := ℝ); linarith)
  obtain ⟨goodCount, hCount⟩ := hcounts.specialize_eventually
    (counting_cutoff_le_eventually hparam hN hBband)
  let R := fun r : ℕ => (r : ℝ) + (Real.sqrt (Real.exp 1) + 1)
  have hR (r) : Real.sqrt (Real.exp 1) < R r := by
    dsimp [R]
    have := Nat.cast_nonneg r (α := ℝ)
    linarith
  have hRpos (r) : 0 < R r := (Real.sqrt_nonneg _).trans_lt (hR r)
  have hRtop : Tendsto R atTop atTop :=
    tendsto_atTop_add_const_right atTop (Real.sqrt (Real.exp 1) + 1) tendsto_natCast_atTop_atTop
  let d := localBulkRateExponent (beta / 2)
  have hd : 0 < d := localBulkRateExponent_pos (by positivity)
  have hbulk (r) : Lemma35LocalBulkComparisonInput μ
      (shiftedSingularValueProcess H z) (shiftedSingularValueProcess G z)
      (R r) (fun k => (N k : ℝ) ^ (-d)) := by
    apply lemma35LocalBulkComparisonInput_of_v3_models hN modelA modelG z
      (hRpos r).le hC (by positivity : 0 < beta / 2)
      (fun k => 3 * (W k : ℝ)) (fun k => (N k : ℝ))
      (fun k => fullBlockV3Model_isBandwidth (hW k) (S k))
      (fun k => denseVarianceProfile_isBandwidth (hNpos k))
    · filter_upwards [hBband] with k hk
      exact (Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hNpos k : (1 : ℝ) ≤ N k) (by linarith : beta / 2 ≤ beta)).trans hk
    · exact Eventually.of_forall (fun k => dense_bandwidth_ge_half_power (hNpos k) hbeta2)
    · exact hthirdA
    · exact hthirdG
    · intro k u
      apply bbvA k
      simpa [spectralParameter, localBulkHeight, N] using
        Real.rpow_pos_of_pos (by exact_mod_cast hNpos k : (0 : ℝ) < N k)
          (-(localBulkEffectiveExponent (beta / 2) / 16))
    · intro k u
      apply bbvG k
      simpa [spectralParameter, localBulkHeight, N] using
        Real.rpow_pos_of_pos (by exact_mod_cast hNpos k : (0 : ℝ) < N k)
          (-(localBulkEffectiveExponent (beta / 2) / 16))
  have hfull := BC12.ginibre_matrix_logdet_convergesInProbability_of_formulas
    hNpos hN G hprojection hcorrelation z
  exact proposition36_matrix_form_highProbability H G z a (fun _ => 12) L R
    (fun _ k => (N k : ℝ) ^ (-d)) p (1 + ‖z‖ ^ 2) (1 + ‖z‖ ^ 2)
    (fun k => sourceCutoff_pos zero_lt_one (hNpos k)) (fun _ => sourceCutoff_le_one)
    (sourceCutoff_tendsto_zero hparam hN)
    (fun k => sourceHardEdgeScale_nonneg (hNpos k) (hW k))
    (reference_nonsingular_of_formulas hNpos G hcorrelation z)
    goodLSV goodCount hLSV hCount
    (sourceHardEdgeError_tendsto_zero hparam hN hband zero_lt_one (by norm_num))
    hbulk (fun r => sourceBulkCutoffBookkeeping_tendsto_zero hparam hN
      zero_lt_one (hRpos r) hd) hp hBC12Negative hfull hRtop hR
    (upperSecondMomentInputs_of_centered_matrix_entries H G z 1 1
      (centeredRowMoments_of_v3 modelA) (centeredRowMoments_of_v3 modelG))

end ShortRingAnchor.Proposition38
