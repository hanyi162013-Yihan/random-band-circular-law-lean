import CircularLawSections56.Section6.ProfileMasses
import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # The literal sampled noncompact profile

The centered representative uses the negative representative at an even-size
tie, exactly as the manuscript's interval `[-floor(N/2), ceil(N/2)-1]` does.
No symmetry of the profile is assumed. Matrix dimensions are positive.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace CircularLawSection6

structure NoncompactProfile where
  f : ℝ → ℝ
  continuous : Continuous f
  integrable : Integrable f
  boundedVariation : BoundedVariationOn f univ
  positive : ∀ x, 0 < f x
  integral_one : ∫ x, f x = 1

def centeredOffset (N : ℕ) (s : ZMod N) : ℤ :=
  if s.val < (N + 1) / 2 then (s.val : ℤ) else (s.val : ℤ) - N

theorem centeredOffset_cast (N : ℕ) [NeZero N] (s : ZMod N) :
    (centeredOffset N s : ZMod N) = s := by
  unfold centeredOffset
  split_ifs <;> simp

theorem centeredOffset_bounds (N : ℕ) [NeZero N] (s : ZMod N) :
    -((N / 2 : ℕ) : ℤ) ≤ centeredOffset N s ∧
      centeredOffset N s < (((N + 1) / 2 : ℕ) : ℤ) := by
  have hs := s.val_lt
  unfold centeredOffset
  split_ifs <;> omega

@[simp] theorem centeredOffset_zero (N : ℕ) [NeZero N] : centeredOffset N 0 = 0 := by
  have hN := NeZero.pos N
  simp [centeredOffset, show 0 < (N + 1) / 2 by omega]

theorem centeredOffset_injective (N : ℕ) [NeZero N] : Function.Injective (centeredOffset N) := by
  intro s t h
  simpa only [centeredOffset_cast] using congrArg (fun z : ℤ => (z : ZMod N)) h

def coreOffsets (N H : ℕ) [NeZero N] : Finset (ZMod N) :=
  Finset.univ.filter (fun s => |centeredOffset N s| ≤ (H : ℤ))

@[simp] theorem mem_coreOffsets (N H : ℕ) [NeZero N] (s : ZMod N) :
    s ∈ coreOffsets N H ↔ |centeredOffset N s| ≤ (H : ℤ) := by
  simp [coreOffsets]

@[simp] theorem zero_mem_coreOffsets (N H : ℕ) [NeZero N] :
    (0 : ZMod N) ∈ coreOffsets N H := by
  simp

theorem coreOffsets_mono (N : ℕ) [NeZero N] {H K : ℕ} (h : H ≤ K) :
    coreOffsets N H ⊆ coreOffsets N K := by
  intro s hs
  exact (mem_coreOffsets N K s).2 ((mem_coreOffsets N H s).1 hs |>.trans (by exact_mod_cast h))

namespace NoncompactProfile

def raw (p : NoncompactProfile) (N : ℕ) (W : ℝ) (s : ZMod N) : ℝ :=
  p.f ((centeredOffset N s : ℝ) / W)

def normalizer (p : NoncompactProfile) (N : ℕ) [NeZero N] (W : ℝ) : ℝ :=
  ∑ s : ZMod N, p.raw N W s

def weight (p : NoncompactProfile) (N : ℕ) [NeZero N] (W : ℝ) (s : ZMod N) : ℝ :=
  p.raw N W s / p.normalizer N W

theorem normalizer_pos (p : NoncompactProfile) (N : ℕ) [NeZero N] (W : ℝ) :
    0 < p.normalizer N W := by
  exact Finset.sum_pos (fun s _ => p.positive _) Finset.univ_nonempty

theorem weight_pos (p : NoncompactProfile) (N : ℕ) [NeZero N] (W : ℝ) (s : ZMod N) :
    0 < p.weight N W s :=
  div_pos (p.positive _) (p.normalizer_pos N W)

theorem sum_weight (p : NoncompactProfile) (N : ℕ) [NeZero N] (W : ℝ) :
    ∑ s : ZMod N, p.weight N W s = 1 := by
  simp only [weight, ← Finset.sum_div]
  exact div_self (p.normalizer_pos N W).ne'

def rawCoreMass (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ) : ℝ :=
  ∑ s ∈ coreOffsets N H, p.raw N W s

def coreMass (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ) : ℝ :=
  ∑ s ∈ coreOffsets N H, p.weight N W s

def tailMass (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ) : ℝ :=
  ∑ s ∈ (coreOffsets N H)ᶜ, p.weight N W s

theorem rawCoreMass_pos (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ) :
    0 < p.rawCoreMass N H W := by
  exact Finset.sum_pos' (fun s _ => (p.positive _).le)
    ⟨0, zero_mem_coreOffsets N H, p.positive _⟩

theorem coreMass_eq_ratio (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ) :
    p.coreMass N H W = p.rawCoreMass N H W / p.normalizer N W := by
  simp only [coreMass, weight, rawCoreMass, Finset.sum_div]

theorem coreMass_pos (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ) :
    0 < p.coreMass N H W := by
  rw [p.coreMass_eq_ratio]
  exact div_pos (p.rawCoreMass_pos N H W) (p.normalizer_pos N W)

theorem coreMass_add_tailMass (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ) :
    p.coreMass N H W + p.tailMass N H W = 1 := by
  rw [coreMass, tailMass, Finset.sum_add_sum_compl, p.sum_weight]

theorem tailMass_nonneg (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ) :
    0 ≤ p.tailMass N H W :=
  Finset.sum_nonneg (fun s _ => (p.weight_pos N W s).le)

theorem coreMass_le_one (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ) :
    p.coreMass N H W ≤ 1 := by
  have := p.coreMass_add_tailMass N H W
  have := p.tailMass_nonneg N H W
  linarith

def normalizedCoreWeight (p : NoncompactProfile) (N H : ℕ) [NeZero N]
    (W : ℝ) (s : ZMod N) : ℝ :=
  p.raw N W s / p.rawCoreMass N H W

theorem normalizedCoreWeight_eq (p : NoncompactProfile) (N H : ℕ) [NeZero N]
    (W : ℝ) (s : ZMod N) :
    p.normalizedCoreWeight N H W s = p.weight N W s / p.coreMass N H W := by
  rw [p.coreMass_eq_ratio]
  exact (div_div_div_cancel_right₀ (p.normalizer_pos N W).ne' _ _).symm

theorem sum_normalizedCoreWeight (p : NoncompactProfile) (N H : ℕ) [NeZero N] (W : ℝ) :
    ∑ s ∈ coreOffsets N H, p.normalizedCoreWeight N H W s = 1 := by
  simp only [normalizedCoreWeight, ← Finset.sum_div]
  exact div_self (p.rawCoreMass_pos N H W).ne'

end NoncompactProfile
end CircularLawSection6
