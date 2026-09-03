import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.ByContra

/-! # Uniformizing an eventual theorem over arbitrary admissible width sequences -/

open Filter
namespace ShortRingAnchor

/-- Theorem 3.1 reindexing step: an eventual statement valid for every
admissible width sequence is eventually uniform over all admissible widths.
This permits dimensions `M k` with repetitions; no injectivity is assumed. -/
theorem eventually_uniform_of_eventually_every_sequence
    {P Q : ℕ → ℕ → Prop}
    (hdefault : ∀ᶠ n in atTop, P n n)
    (hseq : ∀ W : ℕ → ℕ, (∀ᶠ n in atTop, P n (W n)) →
      ∀ᶠ n in atTop, Q n (W n)) :
    ∀ᶠ n in atTop, ∀ w, P n w → Q n w := by
  classical
  let W := fun n => if h : ∃ w, P n w ∧ ¬Q n w then h.choose else n
  have hp : ∀ᶠ n in atTop, P n (W n) := by
    filter_upwards [hdefault] with n hn
    by_cases h : ∃ w, P n w ∧ ¬Q n w
    · simpa only [W, dif_pos h] using h.choose_spec.1
    · simpa only [W, dif_neg h] using hn
  filter_upwards [hseq W hp] with n hn
  intro w hw
  by_contra hq
  have h : ∃ w, P n w ∧ ¬Q n w := ⟨w, hw, hq⟩
  have hbad := h.choose_spec.2
  apply hbad
  simpa only [W, dif_pos h] using hn

end ShortRingAnchor
