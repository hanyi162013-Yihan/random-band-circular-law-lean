import ShortRingAnchor.VerticalStieltjesCounting
import ShortRingAnchor.CutoffDominance
import ShortRingAnchor.CyclicV3Model

/-!
# The actual Corollary 3.5 counting input for Proposition 3.6

The cutoff is exactly `B^(-1/8) N^tau`, not an assumed comparable scale.
The identity `B cutoff^8 = N^(8 tau)` makes the v3 error uniformly small
above the cutoff. A finite vertical grid then supplies the all-cutoff event.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal
noncomputable section
namespace ShortRingAnchor
open Arxiv2410V3

/-- The scale immediately before manuscript (3.10), inserted into v3 (3.11). -/
theorem hardEdgeCutoff_eighth_power {N B tau : ℝ} (hN : 0 < N) (hB : 0 < B) :
    B * (B ^ (-(1 / 8 : ℝ)) * N ^ tau) ^ 8 = N ^ (8 * tau) := by
  rw [mul_pow, ← Real.rpow_mul_natCast hB.le, ← Real.rpow_mul_natCast hN.le]
  norm_num only [show -(1 / 8 : ℝ) * (8 : ℕ) = -1 by norm_num]
  rw [Real.rpow_neg_one, ← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul]
  congr 1
  ring

/-- v3 scale bound: the manuscript cutoff is no smaller than `N^(-1/8)`. -/
theorem hardEdgeCutoff_lower {N B tau : ℝ} (hN : 1 ≤ N)
    (hB : 0 < B) (hBN : B ≤ N) (htau : 0 ≤ tau) :
    N ^ (-(1 / 8 : ℝ)) ≤ B ^ (-(1 / 8 : ℝ)) * N ^ tau := by
  have hp := Real.rpow_le_rpow_of_nonpos hB hBN (by norm_num : -(1 / 8 : ℝ) ≤ 0)
  calc
    _ ≤ B ^ (-(1 / 8 : ℝ)) := hp
    _ ≤ B ^ (-(1 / 8 : ℝ)) * N ^ tau :=
      le_mul_of_one_le_right (Real.rpow_nonneg hB.le _) (Real.one_le_rpow hN htau)

/-- v3 (3.11): a single eventual bound works for every height above the hard edge. -/
theorem eventually_formula311Error_hardEdge {C tau : ℝ} (hC : 0 ≤ C) (htau : 0 < tau) :
    ∀ᶠ N : ℕ in atTop, ∀ B v : ℝ, 1 ≤ B → B ≤ (N : ℝ) →
      B ^ (-(1 / 8 : ℝ)) * (N : ℝ) ^ tau ≤ v →
      formula311Error (N : ℝ) B v C 32 ≤ 1 := by
  filter_upwards [eventually_formula311Error_le_explicit_nat_allEta hC
    (by norm_num : (0 : ℝ) ≤ 32) (by positivity : 0 < 8 * tau),
    eventually_ge_atTop 1] with N h hn B v hB hBN hv
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hn
  have hN0 := zero_lt_one.trans_le hN
  have hB0 := zero_lt_one.trans_le hB
  have ha : 0 < B ^ (-(1 / 8 : ℝ)) * (N : ℝ) ^ tau := by positivity
  have hscale : (N : ℝ) ^ (8 * tau) ≤ B * v ^ 8 := by
    rw [← hardEdgeCutoff_eighth_power hN0 hB0]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hv 8) hB0.le
  exact (h B v hB hBN (ha.trans_le hv) hscale).trans
    (Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr (by positivity)))

/-- v3 Corollary 3.5 / manuscript (3.10): construct the actual all-cutoff
Hermitization count. `BBV` is the sole external comparison premise.
The event is explicit, with exceptional initial dimensions discarded. -/
theorem hermitizationAllCutoffsCountingInput_of_v3_model
    {Omega OmegaXi : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {M : ℕ → ℕ} (hMpos : ∀ k, 0 < M k) (hM : Tendsto M atTop atTop)
    (model : ∀ k, RandomMatrixModelV3 (M k) Omega OmegaXi mu nu)
    (z : ℂ) {C tau : ℝ} (hC : 8 ≤ C) (htau : 0 < tau)
    (B : ℕ → ℝ) (hB : ∀ k, IsBandwidth (model k).profile (B k))
    (hthird : ∀ k, BVH.atomThirdMoment (model k) + BVH.complexGaussianThirdMomentConstant ≤ C)
    (bbv : ∀ k v, 0 < v → CanonicalBBVAt (model k) z (spectralParameter 0 v) (B k) C) :
    ∃ good : ℕ → Set Omega, HermitizationAllCutoffsCountingInput mu
      (fun k => (model k).matrix) z
      (fun k => B k ^ (-(1 / 8 : ℝ)) * (M k : ℝ) ^ tau) (fun _ => 6) good := by
  let a := fun k => B k ^ (-(1 / 8 : ℝ)) * (M k : ℝ) ^ tau
  let valid := fun k => 2 ≤ M k ∧
    ∀ v, a k ≤ v → formula311Error (M k : ℝ) (B k) v C 32 ≤ 1
  let good := fun k => {sample | valid k ∧
    sample ∈ verticalStieltjesGridGood (model k).matrix z (a k)}
  have hBpos (k) : 0 < B k := (hB k).1
  have hN1 (k) : (1 : ℝ) ≤ M k := by exact_mod_cast hMpos k
  have hBN (k) : B k ≤ (M k : ℝ) := by
    let _ : NeZero (M k) := ⟨Nat.ne_of_gt (hMpos k)⟩
    simpa using bandwidth_le_card _ (hB k)
  have ha (k) : 0 < a k := by
    dsimp [a]
    exact mul_pos (Real.rpow_pos_of_pos (hBpos k) _)
      (Real.rpow_pos_of_pos (by exact_mod_cast hMpos k) _)
  have hvalid : ∀ᶠ k in atTop, valid k := by
    filter_upwards [hM.eventually (eventually_ge_atTop 2),
      hM.eventually (eventually_formula311Error_hardEdge (C := C) (tau := tau)
        (by linarith) htau)] with k hk he
    refine ⟨hk, fun v hv => he (B k) v ?_ (hBN k) hv⟩
    let _ : NeZero (M k) := ⟨Nat.ne_of_gt (hMpos k)⟩
    exact one_le_bandwidth _ (hB k)
  refine ⟨good, ⟨fun k => (ha k).le, ?_, ?_⟩⟩
  · have hlim : Tendsto (fun k => ENNReal.ofReal (4 * (M k : ℝ) ^ (-(8 : ℝ))))
        atTop (nhds 0) := by
      have h := (tendsto_rpow_atTop_zero_of_neg (by norm_num : -(8 : ℝ) < 0)).comp
        (tendsto_natCast_atTop_atTop.comp hM)
      simpa using ENNReal.tendsto_ofReal (h.const_mul 4)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall (fun _ => zero_le))
    filter_upwards [hvalid] with k hk
    have hgood : good k = verticalStieltjesGridGood (model k).matrix z (a k) := by
      ext sample
      exact and_iff_right hk
    rw [hgood]
    exact verticalStieltjesGridGood_bad_le hk.1 (model k) z (ha k) (hB k) hC (hthird k)
      (fun v hv => bbv k v ((ha k).trans_le hv)) hk.2
  · intro k sample hs r hr
    exact verticalStieltjesGridGood_count hs.1.1 (model k).matrix z
      (hardEdgeCutoff_lower (hN1 k) (hBpos k) (hBN k) htau.le) hs.2 hr

/-- Manuscript (3.1), Corollary 3.5, and (3.10): the cyclic model supplies
the exact bandwidth and the actual shifted Hermitization automatically. -/
theorem hermitizationAllCutoffsCountingInput_cyclic
    {Omega OmegaXi : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {M W : ℕ → ℕ} {c0 C0 : ℝ}
    (weights : ∀ k, AdmissibleWeights (W k) c0 C0)
    (hfit : ∀ k, 2 * W k + 1 ≤ M k) (hMpos : ∀ k, 0 < M k)
    (hM : Tendsto M atTop atTop)
    (entry : ∀ k, Omega → Fin (M k) → BandOffset (W k) → ℂ)
    (atom : OmegaXi → ℂ) (hatom : AtomMomentAssumption21 nu atom)
    (hcopies : ∀ k, IndependentAtomCopies21 mu nu atom
      (fun is : Fin (M k) × BandOffset (W k) => fun sample => entry k sample is.1 is.2))
    (z : ℂ) {C tau : ℝ} (hC : 8 ≤ C) (htau : 0 < tau)
    (hthird : (∫ x, ‖atom x‖ ^ 3 ∂nu) + BVH.complexGaussianThirdMomentConstant ≤ C)
    (bbv : ∀ k v, 0 < v → CanonicalBBVAt
      (cyclicV3Model (weights k) (hfit k) (entry k) atom hatom (hcopies k)) z
      (spectralParameter 0 v) (weights k).bandwidthParameter C) :
    ∃ good : ℕ → Set Omega, HermitizationAllCutoffsCountingInput mu
      (fun k => cyclicShortRingRandomMatrix (weights k) (hfit k) (entry k)) z
      (fun k => manuscriptHardEdgeCutoff (weights k) (M k) tau) (fun _ => 6) good := by
  exact hermitizationAllCutoffsCountingInput_of_v3_model hMpos hM
    (fun k => cyclicV3Model (weights k) (hfit k) (entry k) atom hatom (hcopies k))
    z hC htau (fun k => (weights k).bandwidthParameter)
    (fun k => cyclicVarianceProfile_isBandwidth (weights k) (hfit k)) (fun _ => hthird) bbv

end ShortRingAnchor
