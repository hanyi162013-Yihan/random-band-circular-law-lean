import BernoulliSection10.Section3Inputs
import ShortRingAnchor.CyclicSecondMoment

/-! # A genuine scalar-indicator reference for Proposition 10.1 -/

open scoped BigOperators

noncomputable section

namespace BernoulliSection10.SourceInputs

open ShortRingAnchor

set_option maxHeartbeats 1200000

def uniformIndicatorWeights (W : ℕ) : AdmissibleWeights W 1 1 where
  q _ := 1 / ((2 * W + 1 : ℕ) : ℝ)
  c0_pos := by norm_num
  c0_le_C0 := le_rfl
  sum_q := by
    simp
    exact mul_inv_cancel₀ (by positivity)
  lower _ := le_rfl
  upper _ := le_rfl

theorem cyclicColumn_row_injective {N W : ℕ} (hfit : 2 * W + 1 ≤ N)
    (a : BandOffset W) : Function.Injective (fun i => cyclicColumn hfit i a) := by
  intro i j hij
  apply Fin.ext
  have hm : (i.val + a.val + N - W) ≡ (j.val + a.val + N - W) [MOD N] :=
    congrArg Fin.val hij
  have hi : i.val + a.val + N - W = i.val + (a.val + N - W) := by omega
  have hj : j.val + a.val + N - W = j.val + (a.val + N - W) := by omega
  rw [hi, hj] at hm
  exact Nat.ModEq.eq_of_lt_of_lt
    ((Nat.ModEq.refl (a.val + N - W)).add_right_cancel hm) i.isLt j.isLt

theorem scalarIndicatorProfile_nonnegative {N W : ℕ} {c0 C0 : ℝ}
    (q : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ N) (i j : Fin N) :
    0 ≤ scalarIndicatorProfile q hfit i j := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs <;> positivity

theorem scalarIndicatorProfile_sq {N W : ℕ} {c0 C0 : ℝ}
    (q : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ N) (i j : Fin N) :
    scalarIndicatorProfile q hfit i j ^ 2 =
      ∑ a : BandOffset W, if cyclicColumn hfit i a = j then q.q a else 0 := by
  have hc : (scalarIndicatorProfile q hfit i j : ℂ) =
      cyclicShortRingMatrix q hfit (fun _ _ => 1) i j := by
    simp [scalarIndicatorProfile, cyclicShortRingMatrix]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> rfl
  have h := norm_sq_cyclicShortRingMatrix_apply q hfit (fun _ _ => 1) i j
  rw [← hc] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs, norm_one, one_pow, mul_one] using h

theorem scalarIndicatorProfile_doublyStochastic {N W : ℕ} {c0 C0 : ℝ}
    (q : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ N) :
    DoublyStochasticProfile (scalarIndicatorProfile q hfit) := by
  refine ⟨scalarIndicatorProfile_nonnegative q hfit, ?_, ?_⟩
  · intro i
    simp_rw [scalarIndicatorProfile_sq]
    rw [Finset.sum_comm]
    simpa using q.sum_q
  · intro j
    simp_rw [scalarIndicatorProfile_sq]
    rw [Finset.sum_comm]
    have he (a : BandOffset W) :
        (∑ i : Fin N, if cyclicColumn hfit i a = j then q.q a else 0) = q.q a := by
      let e : Fin N ≃ Fin N := Equiv.ofBijective (fun i => cyclicColumn hfit i a)
        (Finite.injective_iff_bijective.mp (cyclicColumn_row_injective hfit a))
      have hs := e.sum_comp (fun k => if k = j then q.q a else 0)
      simpa [e] using hs
    simp_rw [he]
    exact q.sum_q

theorem exists_cyclicColumn_of_scalar_distance {N W : ℕ}
    (hfit : 2 * W + 1 ≤ N) (i j : Fin N)
    (h : scalarCyclicDistance i j ≤ W) :
    ∃ a : BandOffset W, cyclicColumn hfit i a = j := by
  unfold scalarCyclicDistance at h
  rcases le_total i.val j.val with hij | hji
  · simp only [Nat.sub_eq_zero_of_le hij, zero_add] at h
    rcases min_le_iff.mp h with hnear | hwrap
    · let a : BandOffset W := ⟨W + (j.val - i.val), by omega⟩
      refine ⟨a, Fin.ext ?_⟩
      have he : i.val + a.val + N - W = j.val + N := by dsimp [a]; omega
      change (i.val + a.val + N - W) % N = j.val
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
    · let a : BandOffset W := ⟨W - (N - (j.val - i.val)), by omega⟩
      refine ⟨a, Fin.ext ?_⟩
      have he : i.val + a.val + N - W = j.val := by
        dsimp [a]
        have := j.isLt
        omega
      change (i.val + a.val + N - W) % N = j.val
      rw [he, Nat.mod_eq_of_lt j.isLt]
  · simp only [Nat.sub_eq_zero_of_le hji, add_zero] at h
    rcases min_le_iff.mp h with hnear | hwrap
    · let a : BandOffset W := ⟨W - (i.val - j.val), by omega⟩
      refine ⟨a, Fin.ext ?_⟩
      have he : i.val + a.val + N - W = j.val + N := by dsimp [a]; omega
      change (i.val + a.val + N - W) % N = j.val
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
    · let a : BandOffset W := ⟨W + (N - (i.val - j.val)), by omega⟩
      refine ⟨a, Fin.ext ?_⟩
      have he : i.val + a.val + N - W = j.val + N + N := by
        dsimp [a]
        have := i.isLt
        omega
      change (i.val + a.val + N - W) % N = j.val
      rw [he, Nat.add_mod_right, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

theorem uniformIndicatorProfile_sq_of_active {N W : ℕ}
    (hfit : 2 * W + 1 ≤ N) (i j : Fin N)
    (ha : ∃ a : BandOffset W, cyclicColumn hfit i a = j) :
    scalarIndicatorProfile (uniformIndicatorWeights W) hfit i j ^ 2 =
      1 / ((2 * W + 1 : ℕ) : ℝ) := by
  obtain ⟨a, ha⟩ := ha
  rw [scalarIndicatorProfile_sq, Finset.sum_eq_single a]
  · simp [ha, uniformIndicatorWeights]
  · intro b _ hba
    have hb : cyclicColumn hfit i b ≠ j := fun hb =>
      hba (cyclicColumn_injective hfit i (hb.trans ha.symm))
    simp [hb]
  · simp

theorem uniformIndicatorProfile_sq_le {N W : ℕ}
    (hfit : 2 * W + 1 ≤ N) (i j : Fin N) :
    scalarIndicatorProfile (uniformIndicatorWeights W) hfit i j ^ 2 ≤
      1 / ((2 * W + 1 : ℕ) : ℝ) := by
  by_cases ha : ∃ a : BandOffset W, cyclicColumn hfit i a = j
  · exact (uniformIndicatorProfile_sq_of_active hfit i j ha).le
  · simp only [scalarIndicatorProfile_sq]
    have hnone : ∀ a : BandOffset W, cyclicColumn hfit i a ≠ j := by simpa using ha
    simp [hnone]
    positivity

theorem uniformIndicatorProfile_scalar_band {N W : ℕ}
    (hfit : 2 * W + 1 ≤ N) (i j : Fin N)
    (h : scalarCyclicDistance i j ≤ W) :
    scalarIndicatorProfile (uniformIndicatorWeights W) hfit i j ^ 2 =
      1 / ((2 * W + 1 : ℕ) : ℝ) :=
  uniformIndicatorProfile_sq_of_active hfit i j
    (exists_cyclicColumn_of_scalar_distance hfit i j h)

end BernoulliSection10.SourceInputs
