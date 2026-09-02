import CircularLawSection6.SampledProfile
import Mathlib.Data.Int.Interval

/-! # Centered residue representatives and exact mesh sums

The integer interval is half-open, matching both parities of the matrix
dimension. Compact cores are unwrapped only under an explicit size bound.
-/

open scoped BigOperators

noncomputable section

namespace CircularLawSection6

theorem centeredOffset_image (N : ℕ) [NeZero N] :
    Finset.univ.image (centeredOffset N) =
      Finset.Ico (-((N / 2 : ℕ) : ℤ)) (((N + 1) / 2 : ℕ) : ℤ) := by
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 hz
    exact Finset.mem_Ico.2 (centeredOffset_bounds N s)
  · rw [Finset.card_image_of_injective _ (centeredOffset_injective N),
      Finset.card_univ, ZMod.card, Int.card_Ico]
    omega

theorem sum_centeredOffset (N : ℕ) [NeZero N] (F : ℤ → ℝ) :
    (∑ s : ZMod N, F (centeredOffset N s)) =
      ∑ z ∈ Finset.Ico (-((N / 2 : ℕ) : ℤ)) (((N + 1) / 2 : ℕ) : ℤ), F z := by
  rw [← centeredOffset_image N]
  exact (Finset.sum_image (fun s _ t _ h => centeredOffset_injective N h)).symm

theorem coreOffsets_image (N H : ℕ) [NeZero N] (hsize : 2 * H + 1 ≤ N) :
    (coreOffsets N H).image (centeredOffset N) = Finset.Icc (-(H : ℤ)) (H : ℤ) := by
  ext z
  constructor
  · intro hz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hz
    exact Finset.mem_Icc.2 (abs_le.1 ((mem_coreOffsets N H s).1 hs))
  · intro hz
    have hz' := Finset.mem_Icc.1 hz
    have hzfull : z ∈ Finset.Ico (-((N / 2 : ℕ) : ℤ)) (((N + 1) / 2 : ℕ) : ℤ) := by
      apply Finset.mem_Ico.2
      omega
    rw [← centeredOffset_image N] at hzfull
    obtain ⟨s, _, hs⟩ := Finset.mem_image.1 hzfull
    refine Finset.mem_image.2 ⟨s, ?_, hs⟩
    rw [mem_coreOffsets, hs]
    exact abs_le.2 hz'

theorem card_coreOffsets (N H : ℕ) [NeZero N] (hsize : 2 * H + 1 ≤ N) :
    (coreOffsets N H).card = 2 * H + 1 := by
  have h := congrArg Finset.card (coreOffsets_image N H hsize)
  rw [Finset.card_image_of_injective _ (centeredOffset_injective N), Int.card_Icc] at h
  omega

theorem sum_coreOffsets (N H : ℕ) [NeZero N] (hsize : 2 * H + 1 ≤ N) (F : ℤ → ℝ) :
    (∑ s ∈ coreOffsets N H, F (centeredOffset N s)) =
      ∑ z ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), F z := by
  rw [← coreOffsets_image N H hsize]
  exact (Finset.sum_image (fun s _ t _ h => centeredOffset_injective N h)).symm

theorem NoncompactProfile.normalizer_eq_integerSum
    (p : NoncompactProfile) (N : ℕ) [NeZero N] (W : ℝ) :
    p.normalizer N W =
      ∑ z ∈ Finset.Ico (-((N / 2 : ℕ) : ℤ)) (((N + 1) / 2 : ℕ) : ℤ), p.f (z / W) :=
  sum_centeredOffset N (fun z : ℤ => p.f ((z : ℝ) / W))

theorem NoncompactProfile.rawCoreMass_eq_integerSum
    (p : NoncompactProfile) (N H : ℕ) [NeZero N] (hsize : 2 * H + 1 ≤ N) (W : ℝ) :
    p.rawCoreMass N H W = ∑ z ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), p.f (z / W) :=
  sum_coreOffsets N H hsize (fun z : ℤ => p.f ((z : ℝ) / W))

end CircularLawSection6
