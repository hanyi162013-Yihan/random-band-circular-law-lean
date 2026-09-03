import ShortRingAnchor.BC12.GinibreSmallBall
import ShortRingAnchor.BC12.NegativeMomentCounting
import ShortRingAnchor.HermitizationCountingFromV3
import ShortRingAnchor.DenseV3Model
import ShortRingAnchor.NormalizedGinibre

/-!
# Discharging the BC12 negative-moment input by the short route

BC12 (4.9), as used in manuscript (3.14): a polynomial Gaussian lower edge
and the already formalized v3 Corollary 3.5 imply tightness with the explicit
exponent `p = 1/128`. The only retained random-matrix comparison premise is
`CanonicalBBVAt`; the Gaussian least-value estimate is proved, not assumed.

The `HasLaw` premise specifies that the reference really is normalized
circular Ginibre. Moment conditions alone would not justify that claim.
No independence across dimensions, eigenvalue formula, or expectation
bound on the exceptional event is required.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Arxiv2410V3
open scoped Topology ENNReal
namespace ShortRingAnchor.BC12

local instance (N : ℕ) : MeasurableSpace (Matrix (Fin N) (Fin N) ℂ) := borel _
local instance (N : ℕ) : BorelSpace (Matrix (Fin N) (Fin N) ℂ) := ⟨rfl⟩

/-- BC12 (4.9), source count conversion: divide the multiplicity count by
the dimension. This is the empirical CDF, not an extra analytic assumption. -/
theorem empiricalCdf_le_of_smallSingularValue_count
    {I : Type*} [Fintype I] [Nonempty I] (s : I → ℝ) {C t : ℝ}
    (h : ((smallSingularValueIndices s t).card : ℝ) ≤ C * Fintype.card I * t) :
    empiricalCdf s t ≤ C * t := by
  rw [empiricalCdf]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < Fintype.card I)).2
  simpa only [smallSingularValueIndices, mul_right_comm] using h

/-- BC12 (4.9), complete probability splice with a derived Gaussian lower
edge. The next theorem supplies this lemma's count from the v3 proof. -/
theorem negativeMomentTightness_of_ginibreLaw_and_count
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {N : ℕ → ℕ}
    (hNpos : ∀ k, 0 < N k) (hN : Tendsto N atTop atTop)
    (G : ∀ k, Ω → Matrix (Fin (N k)) (Fin (N k)) ℂ)
    (hG : ∀ k, HasLaw (G k) (normalizedGinibreLaw (N k)) μ) (z : ℂ)
    {C : ℝ} (hC : 0 ≤ C) (countGood : ℕ → Set Ω)
    (hcount : Proposition34AllCutoffsInput μ (shiftedSingularValueProcess G z)
      (fun k => (N k : ℝ) ^ (-(1 / 16 : ℝ))) (fun _ => C) countGood) :
    BC12GinibreNegativeMomentTightness μ (1 / 128) (shiftedSingularValueProcess G z) := by
  letI : ∀ k, Nonempty (Fin (N k)) := fun k => Fin.pos_iff_nonempty.mp (hNpos k)
  let lowerGood := fun k => {sample |
    (N k : ℝ) ^ (-(4 : ℝ)) ≤ GinibreLSV.leastSingularValue (G k sample - z • 1)}
  let good := fun k => countGood k ∩ lowerGood k
  have hlowerBad : Tendsto (fun k => μ (lowerGood k)ᶜ) atTop (nhds 0) := by
    simpa only [lowerGood, compl_setOf, not_le] using
      normalizedGinibre_lower_bad_tendsto_zero hNpos hN G hG z
  have hbad : Tendsto (fun k => μ (good k)ᶜ) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun k => μ (countGood k)ᶜ + μ (lowerGood k)ᶜ) atTop (nhds 0) by
        simpa using hcount.badProbability.add hlowerBad) (fun _ => zero_le)
    intro k
    change μ (countGood k ∩ lowerGood k)ᶜ ≤ _
    rw [compl_inter]
    exact measure_union_le _ _
  apply boundedInProbability_of_bound_on_good hbad
    (K := 1 + C / 127 + C)
  apply Eventually.of_forall
  intro k sample hs
  rw [Real.norm_eq_abs, abs_of_nonneg (normalizedNegativeMoment_nonneg
    (fun i => shiftedSingularValueFamily_nonneg (G k sample) z i))]
  apply normalizedNegativeMoment_one_div_128_le _
    (by exact_mod_cast hNpos k : (1 : ℝ) ≤ N k) hC
  · intro i
    exact shiftedSingularValueFamily_lower_of_last (hNpos k) (G k sample) z _ hs.2 i
  · intro t ht _
    exact empiricalCdf_le_of_smallSingularValue_count _ (hcount.count k sample hs.1 t ht)

/-- Dense specialization of the manuscript cutoff before (3.10): choose
`tau = 1/16` and `B=N` to obtain exactly `N^(-1/16)`. -/
theorem dense_counting_cutoff {N : ℕ} (hN : 0 < N) :
    (N : ℝ) ^ (-(1 / 8 : ℝ)) * (N : ℝ) ^ (1 / 16 : ℝ) =
      (N : ℝ) ^ (-(1 / 16 : ℝ)) := by
  rw [← Real.rpow_add (by exact_mod_cast hN : (0 : ℝ) < N)]
  norm_num

/-- **BC12 (4.9) / manuscript (3.14), with no BC12 negative-moment input.**
The full count event is constructed internally from v3 Corollary 3.5.
The retained literature premise is precisely the displayed `bbv` argument;
all other premises specify the actual dense Gaussian model and its moments. -/
theorem negativeMomentTightness_of_ginibreLaw_and_v3
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {N : ℕ → ℕ} (hNpos : ∀ k, 0 < N k) (hN : Tendsto N atTop atTop)
    (model : ∀ k, RandomMatrixModelV3 (N k) Ω Ξ μ ν)
    (hG : ∀ k, HasLaw (model k).matrix (normalizedGinibreLaw (N k)) μ)
    (hB : ∀ k, IsBandwidth (model k).profile (N k : ℝ))
    (z : ℂ) {C : ℝ} (hC : 8 ≤ C)
    (hthird : ∀ k, BVH.atomThirdMoment (model k) + BVH.complexGaussianThirdMomentConstant ≤ C)
    (bbv : ∀ k v, 0 < v → CanonicalBBVAt (model k) z (spectralParameter 0 v) (N k : ℝ) C) :
    BC12GinibreNegativeMomentTightness μ (1 / 128)
      (shiftedSingularValueProcess (fun k => (model k).matrix) z) := by
  obtain ⟨good, hcount⟩ := hermitizationAllCutoffsCountingInput_of_v3_model
    hNpos hN model z hC (by norm_num : (0 : ℝ) < 1 / 16)
    (fun k => (N k : ℝ)) hB hthird bbv
  have hcounts := proposition34AllCutoffsInput_of_hermitization
    (fun k => (model k).matrix) z _ _ good hcount
  simp_rw [dense_counting_cutoff (hNpos _)] at hcounts
  exact negativeMomentTightness_of_ginibreLaw_and_count hNpos hN
    (fun k => (model k).matrix) hG z (by norm_num : (0 : ℝ) ≤ 2 * 6) good hcounts

/-- Manuscript (3.14), actual dense array adapter. The v3 model and its exact
bandwidth are constructed, not supplied as a new probabilistic interface. -/
theorem negativeMomentTightness_normalizedDenseMatrixProcess
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {N : ℕ → ℕ} (hNpos : ∀ k, 0 < N k) (hN : Tendsto N atTop atTop)
    (entry : ∀ k, Ω → Fin (N k) → Fin (N k) → ℂ)
    (atom : Ξ → ℂ) (hatom : AtomMomentAssumption21 ν atom)
    (hcopies : ∀ k, IndependentAtomCopies21 μ ν atom
      (fun ij : Fin (N k) × Fin (N k) => fun sample => entry k sample ij.1 ij.2))
    (hG : ∀ k, HasLaw (normalizedDenseMatrixProcess entry k) (normalizedGinibreLaw (N k)) μ)
    (z : ℂ) {C : ℝ} (hC : 8 ≤ C)
    (hthird : (∫ x, ‖atom x‖ ^ 3 ∂ν) + BVH.complexGaussianThirdMomentConstant ≤ C)
    (bbv : ∀ k v, 0 < v → CanonicalBBVAt
      (denseV3Model (hNpos k) (entry k) atom hatom (hcopies k)) z
      (spectralParameter 0 v) (N k : ℝ) C) :
    BC12GinibreNegativeMomentTightness μ (1 / 128)
      (shiftedSingularValueProcess (normalizedDenseMatrixProcess entry) z) := by
  exact negativeMomentTightness_of_ginibreLaw_and_v3 hNpos hN
    (fun k => denseV3Model (hNpos k) (entry k) atom hatom (hcopies k)) hG
    (fun k => denseVarianceProfile_isBandwidth (hNpos k)) z hC (fun _ => hthird) bbv

end ShortRingAnchor.BC12
