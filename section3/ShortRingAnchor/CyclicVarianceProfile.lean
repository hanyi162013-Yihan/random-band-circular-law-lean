import ShortRingAnchor.CyclicSecondMoment
import Vendor.Arxiv2410.V3.VarianceProfile

/-!
# Manuscript (3.1): the exact cyclic v3 variance profile

The profile is constructed from the actual cyclic placement. Both row and
column normalization are proved, and its exact v3 bandwidth is the already
defined manuscript parameter `(max q)⁻¹`.
-/

open scoped BigOperators
noncomputable section
namespace ShortRingAnchor

/-- Manuscript (3.1): at a fixed offset, cyclic placement permutes the rows. -/
theorem cyclicColumn_row_bijective {M W : ℕ} (hfit : 2 * W + 1 ≤ M)
    (s : BandOffset W) : Function.Bijective (fun i : Fin M => cyclicColumn hfit i s) := by
  apply (Finite.injective_iff_bijective).mp
  intro i j hij
  apply Fin.eq_of_val_eq
  have hm : (i.val + s.val + M - W) ≡ (j.val + s.val + M - W) [MOD M] :=
    congrArg Fin.val hij
  have hi : i.val + s.val + M - W = i.val + (s.val + M - W) := by omega
  have hj : j.val + s.val + M - W = j.val + (s.val + M - W) := by omega
  rw [hi, hj] at hm
  exact Nat.ModEq.eq_of_lt_of_lt
    ((Nat.ModEq.refl (s.val + M - W)).add_right_cancel hm) i.isLt j.isLt

/-- Manuscript (3.1): the finite placement sum has exactly one term at an active entry. -/
theorem cyclicPlacement_sum_at {M W : ℕ} (hfit : 2 * W + 1 ≤ M)
    {E : Type*} [AddCommMonoid E] (a : BandOffset W → E)
    (i : Fin M) (s : BandOffset W) :
    (∑ t, if cyclicColumn hfit i t = cyclicColumn hfit i s then a t else 0) = a s := by
  classical
  simp only [(cyclicColumn_injective hfit i).eq_iff]
  simp

/-- Manuscript (3.1): the actual active matrix entry is `sqrt(q_s) xi_{i,s}`. -/
theorem cyclicShortRingMatrix_at {M W : ℕ} {c0 C0 : ℝ}
    (weights : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ M)
    (entry : Fin M → BandOffset W → ℂ) (i : Fin M) (s : BandOffset W) :
    cyclicShortRingMatrix weights hfit entry i (cyclicColumn hfit i s) =
      (Real.sqrt (weights.q s) : ℂ) * entry i s :=
  cyclicPlacement_sum_at hfit _ i s

/-- Manuscript (3.1): a column outside the active offsets is deterministically zero. -/
theorem cyclicShortRingMatrix_off_band {M W : ℕ} {c0 C0 : ℝ}
    (weights : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ M)
    (entry : Fin M → BandOffset W → ℂ) (i j : Fin M)
    (h : ¬ ∃ s, cyclicColumn hfit i s = j) :
    cyclicShortRingMatrix weights hfit entry i j = 0 := by
  simp [cyclicShortRingMatrix, show ∀ s, cyclicColumn hfit i s ≠ j from fun s hs => h ⟨s, hs⟩]

/-- The nonnegative entry coefficients of the cyclic v3 profile. -/
def cyclicVarianceCoefficient {M W : ℕ} {c0 C0 : ℝ}
    (weights : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ M) (i j : Fin M) : ℝ :=
  ∑ s, if cyclicColumn hfit i s = j then Real.sqrt (weights.q s) else 0

/-- Manuscript (3.1): the cyclic coefficient at an active offset. -/
theorem cyclicVarianceCoefficient_at {M W : ℕ} {c0 C0 : ℝ}
    (weights : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ M)
    (i : Fin M) (s : BandOffset W) :
    cyclicVarianceCoefficient weights hfit i (cyclicColumn hfit i s) = Real.sqrt (weights.q s) :=
  cyclicPlacement_sum_at hfit _ i s

/-- Manuscript (3.1): the coefficient vanishes outside the band. -/
theorem cyclicVarianceCoefficient_off_band {M W : ℕ} {c0 C0 : ℝ}
    (weights : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ M) (i j : Fin M)
    (h : ¬ ∃ s, cyclicColumn hfit i s = j) :
    cyclicVarianceCoefficient weights hfit i j = 0 := by
  simp [cyclicVarianceCoefficient, show ∀ s, cyclicColumn hfit i s ≠ j from fun s hs => h ⟨s, hs⟩]

/-- v3 Definition 1.2: the cyclic coefficient squares are exactly the placed weights. -/
theorem cyclicVarianceCoefficient_sq {M W : ℕ} {c0 C0 : ℝ}
    (weights : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ M) (i j : Fin M) :
    cyclicVarianceCoefficient weights hfit i j ^ 2 =
      ∑ s, if cyclicColumn hfit i s = j then weights.q s else 0 := by
  classical
  by_cases h : ∃ s, cyclicColumn hfit i s = j
  · obtain ⟨s, rfl⟩ := h
    rw [cyclicVarianceCoefficient_at, Real.sq_sqrt (weights.q_nonneg s)]
    exact (cyclicPlacement_sum_at hfit weights.q i s).symm
  · rw [cyclicVarianceCoefficient_off_band weights hfit i j h]
    simp [show ∀ s, cyclicColumn hfit i s ≠ j from fun s hs => h ⟨s, hs⟩]

/-- v3 Definition 1.2: each column has variance sum one, by cyclic permutation. -/
theorem cyclicVarianceCoefficient_col_sq_sum {M W : ℕ} {c0 C0 : ℝ}
    (weights : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ M) (j : Fin M) :
    ∑ i, cyclicVarianceCoefficient weights hfit i j ^ 2 = 1 := by
  classical
  simp_rw [cyclicVarianceCoefficient_sq]
  rw [Finset.sum_comm]
  calc
    _ = ∑ s, weights.q s := by
      apply Finset.sum_congr rfl
      intro s _
      calc
        _ = ∑ k : Fin M, if k = j then weights.q s else 0 :=
          Fintype.sum_bijective (fun i => cyclicColumn hfit i s)
            (cyclicColumn_row_bijective hfit s) _ _ (fun _ => rfl)
        _ = _ := by simp
    _ = 1 := weights.sum_q

/-- The actual cyclic matrix's doubly stochastic variance profile, v3 Definition 1.2. -/
def cyclicVarianceProfile {M W : ℕ} {c0 C0 : ℝ}
    (weights : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ M) :
    Arxiv2410V3.DoublyStochasticVarianceProfile (Fin M) where
  coefficient := cyclicVarianceCoefficient weights hfit
  coefficient_nonneg i j := Finset.sum_nonneg (fun s _ => by split_ifs <;> positivity)
  row_sq_sum i := by
    classical
    simp_rw [cyclicVarianceCoefficient_sq]
    rw [Finset.sum_comm]
    simpa using weights.sum_q
  col_sq_sum := cyclicVarianceCoefficient_col_sq_sum weights hfit

/-- Manuscript (3.1) and v3 bandwidth definition: the exact bandwidth is `(max q)⁻¹`. -/
theorem cyclicVarianceProfile_isBandwidth {M W : ℕ} {c0 C0 : ℝ}
    (weights : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ M) :
    Arxiv2410V3.IsBandwidth (cyclicVarianceProfile weights hfit) weights.bandwidthParameter := by
  classical
  constructor
  · exact weights.bandwidthParameter_pos
  · intro i j
    change cyclicVarianceCoefficient weights hfit i j ^ 2 ≤ weights.bandwidthParameter⁻¹
    by_cases h : ∃ s, cyclicColumn hfit i s = j
    · obtain ⟨s, rfl⟩ := h
      rw [cyclicVarianceCoefficient_at, Real.sq_sqrt (weights.q_nonneg s)]
      simpa [AdmissibleWeights.bandwidthParameter] using weights.le_maxWeight s
    · rw [cyclicVarianceCoefficient_off_band weights hfit i j h]
      simpa only [zero_pow (by omega : 2 ≠ 0)] using
        inv_nonneg.mpr weights.bandwidthParameter_pos.le
  · have hne : (Finset.univ : Finset (BandOffset W)).Nonempty :=
      ⟨firstBandOffset W, Finset.mem_univ _⟩
    obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_sup' hne weights.q
    let i : Fin M := ⟨0, by omega⟩
    refine ⟨i, cyclicColumn hfit i s, ?_⟩
    change cyclicVarianceCoefficient weights hfit i (cyclicColumn hfit i s) ^ 2 = _
    rw [cyclicVarianceCoefficient_at, Real.sq_sqrt (weights.q_nonneg s)]
    simpa [AdmissibleWeights.bandwidthParameter, AdmissibleWeights.maxWeight] using hs.symm

end ShortRingAnchor
