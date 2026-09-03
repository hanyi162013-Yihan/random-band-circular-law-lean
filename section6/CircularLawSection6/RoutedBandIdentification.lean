import CircularLawSection6.PeriodicizationEnergy
import CircularLawSection4.PaperIndicatorRandomMatrix

/-! # The full periodicization route is the literal finite-band matrix

The consecutive block index is transported to `ZMod N`. Its original
full-wrap route then agrees exactly with the Section 4/5 scalar band
matrix. The flattened row/slot sample is a coordinate bijection, so its
law is the actual finite IID law, not an assumed equality in distribution.
-/

open MeasureTheory CircularLawSection4
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

section FinSlots
open Fin.NatCast

theorem finEquiv_cyclicFinSlot {N : ℕ} [NeZero N] (H : ℕ)
    (i : Fin N) (s : Fin (2 * H + 1)) :
    ZMod.finEquiv N (cyclicFinSlot H i s) =
      ZMod.finEquiv N i - (H : ZMod N) + (s.val : ZMod N) := by
  have hcast (k : ℕ) : ZMod.finEquiv N (k : Fin N) = (k : ZMod N) := by
    cases N with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ N => rfl
  simp only [cyclicFinSlot, map_add, map_sub, hcast]

end FinSlots

variable {q : ℕ} (len : Fin q → ℕ) [NeZero (∑ b, len b)]

def blockZModEquiv : ((b : Fin q) × Fin (len b)) ≃ ZMod (∑ b, len b) :=
  finSigmaFinEquiv.trans (ZMod.finEquiv _).toEquiv

theorem blockZModEquiv_fullBlockRoute (H : ℕ)
    (i : (b : Fin q) × Fin (len b)) (s : Fin (2 * H + 1)) :
    blockZModEquiv len (fullBlockRoute len H i s) =
      blockZModEquiv len i - (H : ZMod (∑ b, len b)) + (s.val : ZMod (∑ b, len b)) := by
  simp only [blockZModEquiv, Equiv.trans_apply, RingEquiv.toEquiv_eq_coe,
    fullBlockRoute, Equiv.apply_symm_apply]
  exact finEquiv_cyclicFinSlot H _ s

def fullBlockPaperCoordinate (d H : ℕ) (hwidth : d + 2 = 2 * H + 1)
    (k : Fin ((∑ b, len b) * (d + 2))) :
    ((b : Fin q) × Fin (len b)) × Fin (2 * H + 1) :=
  ((blockZModEquiv len).symm (paperIndicatorIndexEquiv (∑ b, len b) d k).1,
    finCongr hwidth (paperIndicatorIndexEquiv (∑ b, len b) d k).2)

theorem fullBlockPaperCoordinate_injective (d H : ℕ) (hwidth : d + 2 = 2 * H + 1) :
    Function.Injective (fullBlockPaperCoordinate len d H hwidth) := by
  intro x y h
  apply (paperIndicatorIndexEquiv (∑ b, len b) d).injective
  apply Prod.ext
  · exact (blockZModEquiv len).symm.injective (congrArg Prod.fst h)
  · exact (finCongr hwidth).injective (congrArg Prod.snd h)

def fullBlockPaperSample (d H : ℕ) (hwidth : d + 2 = 2 * H + 1)
    (ω : ((b : Fin q) × Fin (len b)) × Fin (2 * H + 1) → ℂ) :
    Fin ((∑ b, len b) * (d + 2)) → ℂ := fun k => ω (fullBlockPaperCoordinate len d H hwidth k)

theorem fullBlockPaperSample_measurePreserving (d H : ℕ) (hwidth : d + 2 = 2 * H + 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    MeasurePreserving (fullBlockPaperSample len d H hwidth)
      (Measure.pi (fun _ : ((b : Fin q) × Fin (len b)) × Fin (2 * H + 1) => ν))
      (paperIndicatorSampleMeasure (∑ b, len b) d ν) := by
  unfold fullBlockPaperSample paperIndicatorSampleMeasure
  rw [iidMeasure_eq_pi]
  exact measurePreserving_pi_restrict_injective (fullBlockPaperCoordinate len d H hwidth)
    (fullBlockPaperCoordinate_injective len d H hwidth) ν

theorem fullBlockMatrix_eq_paperScalarBandMatrix (d H : ℕ)
    (hwidth : d + 2 = 2 * H + 1) (center : Fin (d + 1)) (hcenter : center.val = H)
    (a : Fin (2 * H + 1) → ℂ)
    (ω : ((b : Fin q) × Fin (len b)) × Fin (2 * H + 1) → ℂ) :
    (routedBandMatrix (fullBlockRoute len H) a ω).submatrix
      (blockZModEquiv len).symm (blockZModEquiv len).symm =
      paperScalarBandMatrix (∑ b, len b) d center
        (fun i k => a (finCongr hwidth k) * ω ((blockZModEquiv len).symm i, finCongr hwidth k)) := by
  ext i j
  simp only [Matrix.submatrix_apply, routedBandMatrix, paperScalarBandMatrix]
  apply Fintype.sum_equiv (finCongr hwidth).symm
  intro s
  have heq : (blockZModEquiv len).symm j =
      fullBlockRoute len H ((blockZModEquiv len).symm i) s ↔
      j = i - (H : ZMod (∑ b, len b)) + (s.val : ZMod (∑ b, len b)) := by
    constructor
    · intro h
      have hc := congrArg (blockZModEquiv len) h
      simpa only [Equiv.apply_symm_apply, blockZModEquiv_fullBlockRoute] using hc
    · intro h
      apply (blockZModEquiv len).injective
      simpa only [Equiv.apply_symm_apply, blockZModEquiv_fullBlockRoute] using h
  have hsval : ((finCongr hwidth).symm s).val = s.val := rfl
  simp only [Equiv.apply_symm_apply, hsval, hcenter, heq]

theorem fullBlockMatrix_eq_paperIndicatorX (d H : ℕ)
    (hwidth : d + 2 = 2 * H + 1) (center : Fin (d + 1)) (hcenter : center.val = H)
    (a : Fin (2 * H + 1) → ℂ)
    (ω : ((b : Fin q) × Fin (len b)) × Fin (2 * H + 1) → ℂ) :
    (routedBandMatrix (fullBlockRoute len H) a ω).submatrix
      (blockZModEquiv len).symm (blockZModEquiv len).symm =
      paperIndicatorX (∑ b, len b) d center (fun k => a (finCongr hwidth k))
        (fullBlockPaperSample len d H hwidth ω) := by
  rw [fullBlockMatrix_eq_paperScalarBandMatrix len d H hwidth center hcenter]
  congr 1
  funext i k
  simp only [paperIndicatorXi, fullBlockPaperSample, fullBlockPaperCoordinate,
    paperIndicatorIndexEquiv_flatIndex]

end CircularLawSection6
