import CircularLawSection6.PeriodicBlockCutoff

/-! # A one-block periodicization changes no entries

The direct branch must not be charged the coarse boundary estimate, which
need not vanish when the block is the whole matrix. Its two routes agree
exactly, for every half-width and without a nonsingularity condition.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace CircularLawSection6

theorem cyclicFinSlot_finCongr {N M : ℕ} [NeZero N] [NeZero M]
    (h : N = M) (H : ℕ) (i : Fin N) (s : Fin (2 * H + 1)) :
    cyclicFinSlot H (finCongr h i) s = finCongr h (cyclicFinSlot H i s) := by
  subst M
  rfl

theorem oneBlock_routes_eq (len : Fin 1 → ℕ) [∀ b, NeZero (len b)] [NeZero (∑ b, len b)]
    (H : ℕ) : fullBlockRoute len H = periodicBlockRoute len H := by
  have hsum : (∑ b, len b) = len 0 := by simp
  have he (i : Fin (len 0)) :
      finSigmaFinEquiv (⟨0, i⟩ : (b : Fin 1) × Fin (len b)) = finCongr hsum.symm i := by
    apply Fin.ext
    simp
  funext i s
  rcases i with ⟨b, i⟩
  have hb : b = (0 : Fin 1) := Subsingleton.elim _ _
  subst b
  apply finSigmaFinEquiv.injective
  rw [fullBlockRoute, Equiv.apply_symm_apply]
  change cyclicFinSlot H (finSigmaFinEquiv (⟨0, i⟩ : (b : Fin 1) × Fin (len b))) s =
    finSigmaFinEquiv (⟨0, cyclicFinSlot H i s⟩ : (b : Fin 1) × Fin (len b))
  rw [he, he, cyclicFinSlot_finCongr]

theorem oneBlock_matrix_eq (len : Fin 1 → ℕ) [∀ b, NeZero (len b)] [NeZero (∑ b, len b)]
    (H : ℕ) (b : Fin (2 * H + 1) → ℂ)
    (ω : ((j : Fin 1) × Fin (len j)) × Fin (2 * H + 1) → ℂ) :
    routedBandMatrix (fullBlockRoute len H) b ω = routedBandMatrix (periodicBlockRoute len H) b ω := by
  rw [oneBlock_routes_eq]

theorem oneBlock_cutoff_error_zero (len : Fin 1 → ℕ) [∀ b, NeZero (len b)] [NeZero (∑ b, len b)]
    (H : ℕ) (b : Fin (2 * H + 1) → ℂ) (ν : Measure ℂ) (a : ℝ) (z : ℂ) :
    (∫ ω, |matrixCutoffPotential (routedBandMatrix (fullBlockRoute len H) b ω - z • 1) a -
      matrixCutoffPotential (routedBandMatrix (periodicBlockRoute len H) b ω - z • 1) a|
      ∂Measure.pi (fun _ : ((j : Fin 1) × Fin (len j)) × Fin (2 * H + 1) => ν)) = 0 := by
  simp only [oneBlock_matrix_eq, sub_self, abs_zero, integral_zero]

end CircularLawSection6
