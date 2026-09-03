import ShortRingAnchor.Proposition38.ExternalInputs
import ShortRingAnchor.Proposition38.Scales

/-!
# Proposition 3.8: the two LSV branches yield one high-probability floor

Equations (3.21)--(3.22). No density is assumed. The number of blocks may
oscillate between the Cook and Proposition 3.2 regimes; a single uniform
vanishing failure budget handles both branches at every sufficiently large
dimension. In particular, no per-dimension almost-sure invertibility is
silently used for discrete atoms.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.L2Operator Topology
namespace ShortRingAnchor.Proposition38

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Proposition 3.8, Cook's norm-event removal: a union bound, retaining
the exact scaling of the actual bottom singular value. -/
theorem least_bad_le_guarded_add_norm {n : ℕ} (hn : 0 < n)
    (X Y : Ω → Matrix (Fin n) (Fin n) ℂ) (c e t K : ℝ)
    (hc : 0 ≤ c) (hY : ∀ sample, Y sample = (c : ℂ) • X sample)
    (hthreshold : c * e ≤ t / Real.sqrt n) :
    μ.real {sample | GinibreLSV.leastSingularValue (X sample) < e} ≤
      μ.real {sample | GinibreLSV.leastSingularValue (Y sample) ≤ t / Real.sqrt n ∧
        ‖Y sample‖ ≤ K * Real.sqrt n} +
      μ.real {sample | K * Real.sqrt n < ‖Y sample‖} := by
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (measureReal_union_le _ _)
  intro sample hs
  by_cases hnorm : ‖Y sample‖ ≤ K * Real.sqrt n
  · left
    refine ⟨?_, hnorm⟩
    rw [hY, leastSingularValue_smul hn, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left hs.le hc).trans hthreshold
  · exact Or.inr (lt_of_not_ge hnorm)

/-- Proposition 3.8, (3.22): both named external estimates, together with
the proved norm and geometry lemmas, imply the required exponential floor.
There is no supplied norm event, connectivity input, or nonsingularity input. -/
theorem leastSingularValueInput_of_known
    (A : Atom) {s W : ℕ → ℕ} (hW : ∀ k, 0 < W k) (hs : ∀ k, 0 < s k)
    (S : ∀ k, AtomArray μ A
      (Fin ((s k + 3) * W k) × Fin ((s k + 3) * W k)))
    (z : ℂ) (known32 : Proposition32Input μ A z) (knownCook : Cook112Input μ A)
    {beta kappa : ℝ} (hbeta : 1 / 2 < beta) (hkappa : 0 < kappa)
    (hN : Tendsto (fun k => (s k + 3) * W k) atTop atTop)
    (hWtop : Tendsto W atTop atTop)
    (hband : ∀ᶠ k in atTop, (((s k + 3) * W k : ℕ) : ℝ) ^ beta ≤ W k) :
    ∃ good : ℕ → Set Ω, Theorem31LeastSingularValueInput μ
      (shiftedSingularValueProcess (fun k => fullBlockMatrix (S k)) z)
      (sourceHardEdgeScale (fun k => (s k + 3) * W k) W kappa) good := by
  let N := fun k => (s k + 3) * W k
  let L := sourceHardEdgeScale N W kappa
  let X := fun k sample => fullBlockMatrix (S k) sample - z • 1
  let good := fun k => {sample | Real.exp (-(L k)) ≤ GinibreLSV.leastSingularValue (X k sample)}
  have hNpos (k) : 0 < N k := Nat.mul_pos (by omega) (hW k)
  have hWN (k) : W k ≤ N k :=
    (Nat.one_mul (W k)).symm.trans_le (Nat.mul_le_mul_right (W k) (by omega))
  obtain ⟨mStar, CJ, hCJ, hjjlo⟩ := known32
  obtain ⟨κ, hκ⟩ := A.exists_cookSpread
  let K := cookNormConstant A mStar z
  have hm : (1 : ℝ) ≤ (mStar + 3 : ℕ) := by exact_mod_cast (show 1 ≤ mStar + 3 by omega)
  have hδ0 : 0 < broadDelta mStar := by unfold broadDelta; positivity
  have hδ1 : broadDelta mStar < 1 := by
    unfold broadDelta
    apply (div_lt_one (by positivity)).mpr
    nlinarith
  have hν0 : 0 < broadNu mStar := by unfold broadNu; positivity
  have hν1 : broadNu mStar < 1 := by
    unfold broadNu
    apply (div_lt_one (by positivity)).mpr
    linarith
  obtain ⟨CC, hCC, hcook⟩ := knownCook κ (broadDelta mStar) (broadNu mStar) K
    hκ hδ0 hδ1 hν0 hν1 (one_le_cookNormConstant A mStar z)
  let budget : ℕ → ℝ := fun k => CJ / Real.sqrt (3 * (W k : ℝ)) +
    CC * ((N k : ℝ) ^ (-(1 / 4 : ℝ)) + 1 / Real.sqrt (N k)) + Real.exp (-(N k : ℝ))
  have hbudget : Tendsto budget atTop (𝓝 0) := by
    have hnreal : Tendsto (fun k => (N k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hN
    have hwreal : Tendsto (fun k => (W k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hWtop
    have hj : Tendsto (fun k => CJ / Real.sqrt (3 * (W k : ℝ))) atTop (𝓝 0) := by
      have ht := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
        (hwreal.const_mul_atTop (by norm_num : (0 : ℝ) < 3)))
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using ht.const_mul CJ
    have ht : Tendsto (fun k => (N k : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_atTop_zero_of_neg (by norm_num)).comp hnreal
    have hr : Tendsto (fun k => 1 / Real.sqrt (N k : ℝ)) atTop (𝓝 0) := by
      simpa only [one_div, Function.comp_def] using
        tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hnreal)
    have he : Tendsto (fun k => Real.exp (-(N k : ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hnreal)
    simpa only [budget, mul_zero, add_zero] using (hj.add ((ht.add hr).const_mul CC)).add he
  have hjfloor := jjlo_exponent_le_sourceHardEdgeScale hkappa hN hW hWN
    (fun _ => rfl : ∀ k, N k = (s k + 3) * W k)
  have hbound : ∀ᶠ k in atTop, μ.real (good k)ᶜ ≤ budget k := by
    filter_upwards [hband, hjfloor, hN.eventually_ge_atTop 3] with k hb hj hn3
    have hmw : s k + 3 ≤ W k :=
      block_count_le_width (by omega) (hW k) rfl hbeta hb
    have hj0 : 0 ≤ CJ / Real.sqrt (3 * (W k : ℝ)) := by positivity
    have hc0 : 0 ≤ CC * ((N k : ℝ) ^ (-(1 / 4 : ℝ)) + 1 / Real.sqrt (N k)) := by positivity
    have he0 : 0 ≤ Real.exp (-(N k : ℝ)) := (Real.exp_pos _).le
    have hgood : (good k)ᶜ = {sample | GinibreLSV.leastSingularValue (X k sample) <
        Real.exp (-(L k))} := by ext sample; simp only [good, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    rw [hgood]
    by_cases hmregime : mStar ≤ s k + 3
    · have hthreshold := exponential_floor_le_jjlo_floor (hW k) hj
      have hle : μ.real {sample | GinibreLSV.leastSingularValue (X k sample) <
          Real.exp (-(L k))} ≤ μ.real {sample |
          GinibreLSV.leastSingularValue (X k sample) ≤
            (3 * (W k : ℝ)) ^ (-(25 * ((s k + 3 : ℕ) : ℝ)))} := by
        apply measureReal_mono _ (measure_ne_top _ _)
        intro sample hsample
        exact hsample.le.trans hthreshold
      have hh := hjjlo (W k) (s k) (hW k) (by have := hs k; omega) hmregime hmw (S k)
      exact (hle.trans hh).trans (by dsimp [budget]; linarith)
    · have hsk : s k ≤ mStar := by omega
      let Y := fun sample => rawFullBlockMatrix (S k) sample -
        ((Real.sqrt (3 * (W k : ℝ)) : ℂ) * z) • 1
      have hY : ∀ sample, Y sample = (Real.sqrt (3 * (W k : ℝ)) : ℂ) • X k sample :=
        fun sample => (rescaled_shift_eq (hW k) (S k) sample z).symm
      have hepoly := exponential_floor_le_polynomial N W kappa k (hNpos k)
      have hthreshold : Real.sqrt (3 * (W k : ℝ)) * Real.exp (-(L k)) ≤
          (N k : ℝ) ^ (-(1 / 4 : ℝ)) / Real.sqrt (N k) :=
        (mul_le_mul_of_nonneg_left hepoly (Real.sqrt_nonneg _)).trans
          (cook_threshold_dominates_polynomial hn3 (hWN k))
      have hsplit := least_bad_le_guarded_add_norm (μ := μ) (hNpos k) (X k) Y
        (Real.sqrt (3 * (W k : ℝ))) (Real.exp (-(L k))) ((N k : ℝ) ^ (-(1 / 4 : ℝ)))
        K (Real.sqrt_nonneg _) hY hthreshold
      have hc := hcook (N k) (hNpos k) (S k) (scalarAdjacent (W k) (s k))
        (fullBlock_broadlyConnected_uniform (W k) (s k) mStar hsk)
        (-(((Real.sqrt (3 * (W k : ℝ)) : ℂ) * z) • 1))
        ((N k : ℝ) ^ (-(1 / 4 : ℝ))) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have hmask (sample) : maskedMatrix id (scalarAdjacent (W k) (s k))
          ((S k).subgaussianSquare.rawMatrix sample) = rawFullBlockMatrix (S k) sample := rfl
      have hc' : μ.real {sample | GinibreLSV.leastSingularValue (Y sample) ≤
            (N k : ℝ) ^ (-(1 / 4 : ℝ)) / Real.sqrt (N k) ∧
          ‖Y sample‖ ≤ K * Real.sqrt (N k)} ≤
            CC * ((N k : ℝ) ^ (-(1 / 4 : ℝ)) + 1 / Real.sqrt (N k)) := by
        simpa only [hmask, Y, sub_eq_add_neg] using hc
      have hnorm := fullBlock_cook_norm_tail (hW k) mStar hsk (S k) z
      exact (hsplit.trans (add_le_add hc' hnorm)).trans (by dsimp [budget]; linarith)
  have hbadR : Tendsto (fun k => μ.real (good k)ᶜ) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) hbound hbudget
  refine ⟨good, ?_, ?_⟩
  · have hh : Tendsto (fun k => ENNReal.ofReal (μ.real (good k)ᶜ)) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hbadR
    apply hh.congr'
    filter_upwards [] with k
    exact ofReal_measureReal (measure_ne_top μ (good k)ᶜ)
  · intro k sample hsample i
    change Real.exp (-(L k)) ≤
      GinibreLSV.leastSingularValue (fullBlockMatrix (S k) sample - z • 1) at hsample
    exact shiftedSingularValueFamily_lower_of_last (hNpos k)
      (fullBlockMatrix (S k) sample) z (Real.exp (-(L k)))
      (by simpa only [leastSingularValue_shift_eq (hNpos k)] using hsample) i

end ShortRingAnchor.Proposition38
