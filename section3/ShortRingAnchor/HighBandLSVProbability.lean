import ShortRingAnchor.HighBandLSVBridge
import ShortRingAnchor.HighBandUniformNumerics
import ShortRingAnchor.HilbertSchmidtCutoffRemoval
import Vendor.PlanarModelTheorem

/-!
# Theorem 3.1: reuse the published bound and remove its HS cutoff

The matrix theorem is called directly from the copied high-band project.
Only its numerical preparation is reindexed. Uniform second moments remove
the HS cutoff by a two-limit Markov argument already proved in this project.
-/

open Filter Set MeasureTheory ProbabilityTheory HighBandLSV
open scoped Topology ENNReal
noncomputable section
namespace ShortRingAnchor

/-- Theorem 3.1: the upstream planar bound at arbitrary positive dimension,
with the four already-proved numerical certificates bundled together. -/
theorem planar_lsv_of_highBandNumericalCertificates
    {N W : ℕ} {c C L kappa R Kz A : ℝ} (m : PlanarBandModel N W c C L)
    (num : HighBandNumericalCertificates N W kappa R Kz A 64)
    (hc : 0 < c) (hL : 0 ≤ L) (hA25 : 25 ≤ A) (hA : Real.pi * L / c ≤ A)
    (z : ℂ) (hz : ‖z‖ ≤ Kz) (t : ℝ) (ht : 0 ≤ t) :
    m.law (leastSingularBadEvent (fun sample => shifted (m.matrix sample) z)
      (HighBandLSV.tau N W kappa t) ∩ hsEvent m.matrix R) ≤
      ENNReal.ofReal (Real.sqrt (Real.pi * L / c) * t) +
        ENNReal.ofReal (Real.exp (-(N : ℝ) ^ (1 + kappa / 4))) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt num.2.1.N_pos)
  exact planar_model_lsv_of_numerics m num.1 num.2.1 num.2.2.1 num.2.2.2
    hc hL hA25 hA (by norm_num) z hz t ht

/-- Theorem 3.1: its proved planar conclusion along the actual dimensions `M k`. -/
theorem eventually_planar_lsv_along_dimensions
    {M W : ℕ → ℕ} {c C L chi kappa R Kz : ℝ}
    (m : ∀ k, PlanarBandModel (M k) (W k) c C L)
    (hM : Tendsto M atTop atTop) (hc : 0 < c) (hL : 0 ≤ L)
    (hchi : 0 < chi) (hchi1 : chi ≤ 1 / 2) (hk : 0 < kappa)
    (hR : 0 ≤ R) (hKz : 0 ≤ Kz)
    (hWp : ∀ᶠ k in atTop, 0 < W k)
    (hband : ∀ᶠ k in atTop, (M k : ℝ) ^ (1 / 2 + chi) ≤ W k)
    (hupper : ∀ᶠ k in atTop, (W k : ℝ) ≤ M k) :
    ∀ᶠ k in atTop, ∀ z : ℂ, ‖z‖ ≤ Kz → ∀ t : ℝ, 0 ≤ t →
      (m k).law (leastSingularBadEvent (fun sample => shifted ((m k).matrix sample) z)
        (HighBandLSV.tau (M k) (W k) kappa t) ∩ hsEvent (m k).matrix R) ≤
        ENNReal.ofReal (Real.sqrt (Real.pi * L / c) * t) +
          ENNReal.ofReal (Real.exp (-(M k : ℝ) ^ (1 + kappa / 4))) := by
  let A := 25 + Real.pi * L / c
  have ha0 : 0 ≤ Real.pi * L / c := by positivity
  have hA : 25 ≤ A := by dsimp [A]; linarith
  filter_upwards [eventually_highBandNumerics_along_dimensions hM hchi hchi1 hk hR hKz
    (show 0 < A by linarith) (by norm_num : (0 : ℝ) < 64) hWp hband hupper] with k hn
  intro z hz t ht
  exact planar_lsv_of_highBandNumericalCertificates (m k) hn hc hL hA
    (by dsimp [A]; linarith) z hz t ht

/-- Theorem 3.1 cutoff: a bound on the empirical second moment implies its HS event. -/
theorem hsCutoff_of_empiricalSecondMoment_le {N : ℕ} (hN : 0 < N)
    (X : Matrix (Fin N) (Fin N) ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hQ : empiricalAverage (shiftedSingularValueFamily X 0) (fun t => t ^ 2) ≤ K) :
    hilbertSchmidt X ≤ Real.sqrt K * Real.sqrt (N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [empiricalSecondMoment_zero_eq_hilbertSchmidt_sq] at hQ
  have hs : hilbertSchmidt X ^ 2 ≤ K * (N : ℝ) := (div_le_iff₀ hn).mp hQ
  have hnonneg : 0 ≤ hilbertSchmidt X := by
    rw [hilbertSchmidt_formula]
    exact Real.sqrt_nonneg _
  apply (sq_le_sq₀ hnonneg (by positivity : 0 ≤ Real.sqrt K * Real.sqrt (N : ℝ))).mp
  simpa only [mul_pow, Real.sq_sqrt hK, Real.sq_sqrt hn.le] using hs

/-- Theorem 3.1 at `t=M^-2`: its explicit probability majorant vanishes. -/
theorem highBandLSV_failure_tendsto_zero {M : ℕ → ℕ} (hM : Tendsto M atTop atTop)
    {kappa : ℝ} (hk : 0 < kappa) (D : ℝ) :
    Tendsto (fun k => ENNReal.ofReal (D * (M k : ℝ) ^ (-(2 : ℝ))) +
      ENNReal.ofReal (Real.exp (-(M k : ℝ) ^ (1 + kappa / 4)))) atTop (nhds 0) := by
  have hm : Tendsto (fun k => (M k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hM
  have hp := (tendsto_rpow_atTop_zero_of_neg (by norm_num : -(2 : ℝ) < 0)).comp hm
  have he := Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp
      ((tendsto_rpow_atTop (by linarith : 0 < 1 + kappa / 4)).comp hm))
  simpa using (ENNReal.tendsto_ofReal (hp.const_mul D)).add (ENNReal.tendsto_ofReal he)

/-- Theorem 3.1 to manuscript (3.10): its truncated estimate plus the proved
row moments construct the least-value interface. The estimate in this
lemma is supplied by the copied theorem in the concrete endpoint below. -/
theorem theorem31MinimumInput_of_truncated_estimate
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
    {M W : ℕ → ℕ} (hMpos : ∀ k, 0 < M k) (hM : Tendsto M atTop atTop)
    (X : ∀ k, Omega → Matrix (Fin (M k)) (Fin (M k)) ℂ)
    (z : ℂ) {kappa D : ℝ} (hk : 0 < kappa)
    (hmom : CenteredMatrixRowSecondMomentInputs mu X 1)
    (hbound : ∀ R : ℝ, 0 ≤ R → ∀ᶠ k in atTop,
      mu {sample | GinibreLSV.leastSingularValue (shifted (X k sample) z) <
        HighBandLSV.tau (M k) (W k) kappa ((M k : ℝ) ^ (-(2 : ℝ))) ∧
        hilbertSchmidt (X k sample) ≤ R * Real.sqrt (M k : ℝ)} ≤
      ENNReal.ofReal (D * (M k : ℝ) ^ (-(2 : ℝ))) +
        ENNReal.ofReal (Real.exp (-(M k : ℝ) ^ (1 + kappa / 4)))) :
    ∃ good, Theorem31MinimumSingularValueInput hMpos mu X z (sourceHardEdgeScale M W kappa) good := by
  let bad := fun k => {sample | GinibreLSV.leastSingularValue (shifted (X k sample) z) <
    HighBandLSV.tau (M k) (W k) kappa ((M k : ℝ) ^ (-(2 : ℝ)))}
  let Q := fun k sample => empiricalAverage (shiftedSingularValueFamily (X k sample) 0)
    (fun t => t ^ 2)
  have hprob : Tendsto (fun k => mu (bad k)) atTop (nhds 0) := by
    apply probability_tendsto_zero_of_truncated_and_mean_bound (Q := Q) (C := 1)
    · intro k
      exact integrable_empiricalSecondMoment_shiftedSingularValueFamily (X k) 0
        (hmom.entry_integrable k) (hmom.entry_sq_integrable k)
    · intro k sample
      rw [show Q k sample = hilbertSchmidt (X k sample) ^ 2 / (M k : ℝ) from
        empiricalSecondMoment_zero_eq_hilbertSchmidt_sq _]
      positivity
    · intro k
      letI : Nonempty (Fin (M k)) := Fin.pos_iff_nonempty.mp (hMpos k)
      have h := integral_empiricalSecondMoment_shiftedSingularValueFamily (X k) 0 1
        (hmom.entry_integrable k) (hmom.entry_sq_integrable k) (hmom.centered k) (hmom.row_secondMoment k)
      simpa only [Q, norm_zero, zero_pow (by omega : 2 ≠ 0), add_zero] using h.le
    · intro K hK
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (highBandLSV_failure_tendsto_zero hM hk D) (Eventually.of_forall (fun _ => zero_le))
      filter_upwards [hbound (Real.sqrt K) (Real.sqrt_nonneg K)] with k hb
      apply le_trans (measure_mono ?_) hb
      intro sample hs
      exact ⟨hs.1, hsCutoff_of_empiricalSecondMoment_le (hMpos k) (X k sample) hK.le hs.2⟩
  refine ⟨fun k => (bad k)ᶜ, ⟨by simpa using hprob, ?_⟩⟩
  intro k sample hs
  change ¬ GinibreLSV.leastSingularValue (shifted (X k sample) z) <
    HighBandLSV.tau (M k) (W k) kappa ((M k : ℝ) ^ (-(2 : ℝ))) at hs
  have hle := le_of_not_gt hs
  change HighBandLSV.tau (M k) (W k) kappa ((M k : ℝ) ^ (-(2 : ℝ))) ≤
    GinibreLSV.leastSingularValue (shifted (X k sample) z) at hle
  rwa [highBand_threshold_eq_source_exp k (hMpos k), ginibreLeastSingularValue_eq_last (hMpos k)] at hle

end ShortRingAnchor
