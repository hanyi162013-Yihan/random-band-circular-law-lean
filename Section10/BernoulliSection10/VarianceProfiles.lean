import BernoulliSection10.ScalarBandGeometry
import BernoulliSection10.ScalarReferenceProfile

/-! # Discharging the variance-profile hypotheses for both comparison models -/

open scoped BigOperators

noncomputable section

namespace BernoulliSection10.SourceInputs

open ShortRingAnchor

theorem maxEntryVariance_le_of_entry_le {N : ℕ}
    (σ : Matrix (Fin N) (Fin N) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i j, σ i j ^ 2 ≤ C) : maxEntryVariance σ ≤ C := by
  have hs : ((Finset.univ.sup (fun p : Fin N × Fin N =>
      (⟨σ p.1 p.2 ^ 2, sq_nonneg _⟩ : NNReal))) : NNReal) ≤ (⟨C, hC⟩ : NNReal) := by
    apply Finset.sup_le
    intro p _
    exact h p.1 p.2
  exact hs

theorem entryVariance_le_maxEntryVariance {N : ℕ}
    (σ : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    σ i j ^ 2 ≤ maxEntryVariance σ := by
  exact Finset.le_sup (f := fun p : Fin N × Fin N =>
    (⟨σ p.1 p.2 ^ 2, sq_nonneg _⟩ : NNReal)) (Finset.mem_univ (i, j))

theorem physicalProfile_doublyStochastic (W s : ℕ) (hW : 0 < W) :
    DoublyStochasticProfile (physicalProfile W s) :=
  ⟨physicalProfile_nonnegative W s, physicalProfile_row W s hW,
    physicalProfile_column W s hW⟩

theorem maxEntryVariance_physicalProfile (W s : ℕ) (hW : 0 < W) :
    maxEntryVariance (physicalProfile W s) = (3 * (W : ℝ))⁻¹ := by
  apply le_antisymm
  · exact maxEntryVariance_le_of_entry_le _ (by positivity) (physicalProfile_sq_le W s)
  · let i : Fin ((s + 3) * W) := ⟨0, Nat.mul_pos (by omega) hW⟩
    have h := entryVariance_le_maxEntryVariance (physicalProfile W s) i i
    simpa [physicalProfile, physicalSiteAdjacent, blockNormalization_sq] using h

theorem effectiveBandwidth_physicalProfile (W s : ℕ) (hW : 0 < W) :
    effectiveBandwidth (physicalProfile W s) = 3 * (W : ℝ) := by
  rw [effectiveBandwidth, maxEntryVariance_physicalProfile W s hW, inv_inv]

theorem physicalProfile_lsv_upper (W s : ℕ) (hW : 0 < W) :
    maxEntryVariance (physicalProfile W s) ≤ 1 / (W : ℝ) := by
  rw [maxEntryVariance_physicalProfile W s hW, ← one_div]
  apply one_div_le_one_div_of_le (Nat.cast_pos.mpr hW)
  nlinarith [Nat.cast_nonneg (α := ℝ) W]

theorem physicalProfile_lsv_lower (W s : ℕ) (hW : 0 < W)
    (i j : Fin ((s + 3) * W)) (h : scalarCyclicDistance i j ≤ W) :
    (1 / 3 : ℝ) / W ≤ physicalProfile W s i j ^ 2 := by
  rw [physicalProfile_scalar_band_value W s hW i j h]
  exact le_of_eq (by ring)

theorem maxEntryVariance_uniformIndicator {N W : ℕ}
    (hN : 0 < N) (hfit : 2 * W + 1 ≤ N) :
    maxEntryVariance (scalarIndicatorProfile (uniformIndicatorWeights W) hfit) =
      1 / ((2 * W + 1 : ℕ) : ℝ) := by
  apply le_antisymm
  · exact maxEntryVariance_le_of_entry_le _ (by positivity) (uniformIndicatorProfile_sq_le hfit)
  · let i : Fin N := ⟨0, hN⟩
    have h := entryVariance_le_maxEntryVariance
      (scalarIndicatorProfile (uniformIndicatorWeights W) hfit) i i
    rw [uniformIndicatorProfile_scalar_band hfit i i
      (by simp [scalarCyclicDistance])] at h
    exact h

theorem effectiveBandwidth_uniformIndicator {N W : ℕ}
    (hN : 0 < N) (hfit : 2 * W + 1 ≤ N) :
    effectiveBandwidth (scalarIndicatorProfile (uniformIndicatorWeights W) hfit) =
      ((2 * W + 1 : ℕ) : ℝ) := by
  rw [effectiveBandwidth, maxEntryVariance_uniformIndicator hN hfit, one_div, inv_inv]

theorem uniformIndicator_lsv_upper {N W : ℕ}
    (hN : 0 < N) (hW : 0 < W) (hfit : 2 * W + 1 ≤ N) :
    maxEntryVariance (scalarIndicatorProfile (uniformIndicatorWeights W) hfit) ≤
      1 / (W : ℝ) := by
  rw [maxEntryVariance_uniformIndicator hN hfit]
  apply one_div_le_one_div_of_le (Nat.cast_pos.mpr hW)
  exact_mod_cast (by omega : W ≤ 2 * W + 1)

theorem uniformIndicator_lsv_lower {N W : ℕ}
    (hW : 0 < W) (hfit : 2 * W + 1 ≤ N)
    (i j : Fin N) (h : scalarCyclicDistance i j ≤ W) :
    (1 / 3 : ℝ) / W ≤
      scalarIndicatorProfile (uniformIndicatorWeights W) hfit i j ^ 2 := by
  rw [uniformIndicatorProfile_scalar_band hfit i j h]
  have hcount : (0 : ℝ) < ((2 * W + 1 : ℕ) : ℝ) := by positivity
  apply (div_le_div_iff₀ (Nat.cast_pos.mpr hW) hcount).mpr
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linarith

def scalarReferenceWidth (N : ℕ) : ℕ := (N - 1) / 2

theorem scalarReferenceWidth_fit (N : ℕ) (hN : 0 < N) :
    2 * scalarReferenceWidth N + 1 ≤ N := by
  unfold scalarReferenceWidth
  have := Nat.mod_lt (N - 1) (by decide : 0 < 2)
  omega

theorem width_le_scalarReferenceWidth (W s : ℕ) (hW : 0 < W) :
    W ≤ scalarReferenceWidth ((s + 3) * W) := by
  have hN : 3 * W ≤ (s + 3) * W := Nat.mul_le_mul_right W (by omega)
  unfold scalarReferenceWidth
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  omega

end BernoulliSection10.SourceInputs
