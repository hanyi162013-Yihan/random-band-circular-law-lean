import CircularLawSection6.ProfileComparability
import CircularLawSection6.ProfileMatrices
import CircularLawSections56.Section5.TaperModelVariance
import CircularLawSection4.PiRestrictMarginal

/-! # The compact core is the actual Section 5 finite-band model

The coordinate selection below is injective in the unwrapped regime. Its
pushforward is exactly the existing finite IID law, and the corresponding
matrices agree entry by entry. Neither equality in law nor model identity
is introduced as a hypothesis.
-/

open MeasureTheory CircularLawSection4
open scoped BigOperators

noncomputable section

namespace CircularLawSection6

theorem centeredOffset_intCast_of_bounds (N : ℕ) [NeZero N] (z : ℤ)
    (hz : -((N / 2 : ℕ) : ℤ) ≤ z ∧ z < (((N + 1) / 2 : ℕ) : ℤ)) :
    centeredOffset N (z : ZMod N) = z := by
  have hm : z ∈ Finset.univ.image (centeredOffset N) := by
    rw [centeredOffset_image]
    exact Finset.mem_Ico.2 hz
  obtain ⟨s, _, hs⟩ := Finset.mem_image.1 hm
  have hc : (z : ZMod N) = s := by rw [← hs, centeredOffset_cast]
  rw [hc, hs]

def bandSlotOffset (N d : ℕ) (center : Fin (d + 1)) (s : Fin (d + 2)) : ZMod N :=
  (s.val : ZMod N) - (center.val : ZMod N)

theorem bandSlotOffset_injective (N d : ℕ) [NeZero N]
    (hfit : d + 2 ≤ N) (center : Fin (d + 1)) :
    Function.Injective (bandSlotOffset N d center) := by
  intro s t h
  apply Fin.ext
  exact CharP.natCast_injOn_Iio (ZMod N) N
    (s.isLt.trans_le hfit) (t.isLt.trans_le hfit) (sub_right_inj.1 h)

theorem centeredOffset_bandSlot (N d : ℕ) [NeZero N]
    (hfit : d + 2 ≤ N) (center : Fin (d + 1)) (hsym : d + 1 = 2 * center.val)
    (s : Fin (d + 2)) :
    centeredOffset N (bandSlotOffset N d center s) = (s.val : ℤ) - center.val := by
  have hs := s.isLt
  have hb : -((N / 2 : ℕ) : ℤ) ≤ (s.val : ℤ) - center.val ∧
      (s.val : ℤ) - center.val < (((N + 1) / 2 : ℕ) : ℤ) := by omega
  simpa only [Int.cast_sub, Int.cast_natCast, bandSlotOffset] using
    centeredOffset_intCast_of_bounds N ((s.val : ℤ) - center.val) hb

theorem bandSlotOffset_mem_core (N d : ℕ) [NeZero N]
    (hfit : d + 2 ≤ N) (center : Fin (d + 1)) (hsym : d + 1 = 2 * center.val)
    (s : Fin (d + 2)) : bandSlotOffset N d center s ∈ coreOffsets N center.val := by
  rw [mem_coreOffsets, centeredOffset_bandSlot N d hfit center hsym, abs_le]
  have hs := s.isLt
  constructor <;> omega

theorem bandSlotOffset_image (N d : ℕ) [NeZero N]
    (hfit : d + 2 ≤ N) (center : Fin (d + 1)) (hsym : d + 1 = 2 * center.val) :
    Finset.univ.image (bandSlotOffset N d center) = coreOffsets N center.val := by
  apply Finset.eq_of_subset_of_card_le
  · intro t ht
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 ht
    exact bandSlotOffset_mem_core N d hfit center hsym s
  · rw [Finset.card_image_of_injective _ (bandSlotOffset_injective N d hfit center),
      Finset.card_univ, Fintype.card_fin, card_coreOffsets N center.val (by omega)]
    omega

def coreBandCoordinate (N d : ℕ) [NeZero N] (center : Fin (d + 1))
    (k : Fin (N * (d + 2))) : ZMod N × ZMod N :=
  let v := paperIndicatorIndexEquiv N d k
  (v.1, bandSlotOffset N d center v.2)

theorem coreBandCoordinate_injective (N d : ℕ) [NeZero N]
    (hfit : d + 2 ≤ N) (center : Fin (d + 1)) :
    Function.Injective (coreBandCoordinate N d center) := by
  intro a b h
  apply (paperIndicatorIndexEquiv N d).injective
  apply Prod.ext
  · exact congrArg Prod.fst h
  · exact bandSlotOffset_injective N d hfit center (congrArg Prod.snd h)

def coreBandSample (N d : ℕ) [NeZero N] (center : Fin (d + 1))
    (ω : ZMod N × ZMod N → ℂ) : Fin (N * (d + 2)) → ℂ :=
  fun k => ω (coreBandCoordinate N d center k)

@[simp] theorem coreBandSample_flatIndex (N d : ℕ) [NeZero N]
    (center : Fin (d + 1)) (ω : ZMod N × ZMod N → ℂ) (i : ZMod N) (s : Fin (d + 2)) :
    coreBandSample N d center ω (paperIndicatorFlatIndex N d i s) =
      ω (i, bandSlotOffset N d center s) := by
  simp only [coreBandSample, coreBandCoordinate, paperIndicatorIndexEquiv_flatIndex]

theorem coreBandSample_measurePreserving (N d : ℕ) [NeZero N]
    (hfit : d + 2 ≤ N) (center : Fin (d + 1))
    (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    MeasurePreserving (coreBandSample N d center) (cyclicAtomLaw N ν)
      (paperIndicatorSampleMeasure N d ν) := by
  simpa only [coreBandSample, cyclicAtomLaw, paperIndicatorSampleMeasure, iidMeasure_eq_pi] using
    measurePreserving_pi_restrict_injective (coreBandCoordinate N d center)
      (coreBandCoordinate_injective N d hfit center) ν

namespace NoncompactProfile

def coreBandWeight (p : NoncompactProfile) (N d : ℕ) [NeZero N]
    (center : Fin (d + 1)) (W : ℝ) (s : Fin (d + 2)) : ℝ :=
  p.normalizedCoreWeight N center.val W (bandSlotOffset N d center s)

theorem sum_coreBandWeight (p : NoncompactProfile) (N d : ℕ) [NeZero N]
    (hfit : d + 2 ≤ N) (center : Fin (d + 1)) (hsym : d + 1 = 2 * center.val) (W : ℝ) :
    ∑ s, p.coreBandWeight N d center W s = 1 := by
  have hs := p.sum_normalizedCoreWeight N center.val W
  rw [← bandSlotOffset_image N d hfit center hsym, Finset.sum_image
    (fun s _ t _ h => bandSlotOffset_injective N d hfit center h)] at hs
  exact hs

/-- The exact Section 4/5 weight structure. The bounds are on the actual
sampled profile and the normalization is the actual compact-core mass. -/
def corePaperWeights (p : NoncompactProfile) (N d : ℕ) [NeZero N]
    (hfit : d + 2 ≤ N) (center : Fin (d + 1)) (hsym : d + 1 = 2 * center.val)
    (W : ℝ) {m M : ℝ} (hm : 0 < m)
    (hb : ∀ t ∈ coreOffsets N center.val, m ≤ p.raw N W t ∧ p.raw N W t ≤ M) :
    PaperIndicatorWeights (d + 1) (m / M) (M / m) where
  q := p.coreBandWeight N d center W
  normalized := p.sum_coreBandWeight N d hfit center hsym W
  lower s := by
    have hwidth : 2 * center.val + 1 = d + 2 := by omega
    have h := (p.core_weight_bounds_of_raw_bounds N center.val (by omega) W hm hb
      (bandSlotOffset N d center s) (bandSlotOffset_mem_core N d hfit center hsym s)).1
    simpa only [coreBandWeight, hwidth, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      div_div, mul_comm, add_assoc] using h
  upper s := by
    have hwidth : 2 * center.val + 1 = d + 2 := by omega
    have h := (p.core_weight_bounds_of_raw_bounds N center.val (by omega) W hm hb
      (bandSlotOffset N d center s) (bandSlotOffset_mem_core N d hfit center hsym s)).2
    simpa only [coreBandWeight, hwidth, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      div_div, mul_comm, add_assoc] using h

theorem unitCoreMatrix_eq_paperIndicatorX (p : NoncompactProfile)
    (N d : ℕ) [NeZero N] (hfit : d + 2 ≤ N)
    (center : Fin (d + 1)) (hsym : d + 1 = 2 * center.val) (W : ℝ)
    (ω : ZMod N × ZMod N → ℂ) :
    p.unitCoreMatrix N center.val W ω = paperIndicatorX N d center
      (fun s => (Real.sqrt (p.coreBandWeight N d center W s) : ℂ))
      (coreBandSample N d center ω) := by
  classical
  ext i j
  by_cases hslot : ∃ s : Fin (d + 2), j = i - (center.val : ZMod N) + (s.val : ZMod N)
  · obtain ⟨s, rfl⟩ := hslot
    rw [paperIndicatorX, CircularLawSections56.Section5.paperScalarBandMatrix_entry_slot N d hfit]
    have he : i - (center.val : ZMod N) + (s.val : ZMod N) - i =
        bandSlotOffset N d center s := by unfold bandSlotOffset; abel
    simp only [unitCoreMatrix, weightedCyclicMatrix, he, maskedWeight,
      if_pos (bandSlotOffset_mem_core N d hfit center hsym s), coreBandWeight,
      paperIndicatorXi_apply, coreBandSample_flatIndex]
  · have hn : j - i ∉ coreOffsets N center.val := by
      intro hj
      rw [← bandSlotOffset_image N d hfit center hsym] at hj
      obtain ⟨s, _, hs⟩ := Finset.mem_image.1 hj
      apply hslot
      refine ⟨s, ?_⟩
      unfold bandSlotOffset at hs
      calc
        j = i + (j - i) := by abel
        _ = i + ((s.val : ZMod N) - (center.val : ZMod N)) := congrArg (fun t => i + t) hs.symm
        _ = i - (center.val : ZMod N) + (s.val : ZMod N) := by abel
    have hslots : ∀ s : Fin (d + 2), j ≠ i - (center.val : ZMod N) + (s.val : ZMod N) :=
      fun s hs => hslot ⟨s, hs⟩
    simp only [unitCoreMatrix, weightedCyclicMatrix, maskedWeight, if_neg hn,
      Real.sqrt_zero, Complex.ofReal_zero, zero_mul, paperIndicatorX,
      paperScalarBandMatrix, hslots, if_false, Finset.sum_const_zero]

end NoncompactProfile
end CircularLawSection6
