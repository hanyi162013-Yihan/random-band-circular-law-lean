import CircularLawSections56.Section5.PublishedSection3Source
import CircularLawSections56.Section6.LiteralIndicatorModel

/-! # Exact finite identification of the Section 3 and Section 5 cyclic matrices

The two projects use the same signed offsets but different finite coordinate
encodings. These identities expose the concrete reindexing, with no probability
or asymptotic assumptions and no spectral conclusion supplied by the caller.
-/

open MeasureTheory Filter Topology ShortRingAnchor
open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CircularLawSections56.Section5

theorem section3_finEquiv_eq_natCast {N : ℕ} [NeZero N] (i : Fin N) :
    ZMod.finEquiv N i = (i.val : ZMod N) := by
  have hv : (ZMod.finEquiv N i).val = i.val := by
    cases N with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => rfl
  apply ZMod.val_injective
  rw [hv, ZMod.val_natCast_of_lt i.isLt]

theorem section3_cyclicColumn_finEquiv {N W : ℕ} [NeZero N]
    (hfit : 2 * W + 1 ≤ N) (i : Fin N) (s : BandOffset W) :
    ZMod.finEquiv N (cyclicColumn hfit i s) =
      ZMod.finEquiv N i - (W : ZMod N) + (s.val : ZMod N) := by
  rw [section3_finEquiv_eq_natCast, section3_finEquiv_eq_natCast]
  change (((i.val + s.val + N - W) % N : ℕ) : ZMod N) = _
  rw [ZMod.natCast_mod, Nat.cast_sub (by omega : W ≤ i.val + s.val + N),
    Nat.cast_add, Nat.cast_add, ZMod.natCast_self, add_zero]
  ring

def paperSection3Weights {d W : ℕ} {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hwidth : d + 2 = 2 * W + 1) (hc₀ : 0 < c₀) : AdmissibleWeights W c₀ C₀ where
  q s := profile.q ((finCongr hwidth).symm s)
  c0_pos := hc₀
  c0_le_C0 := by
    have h := (profile.lower 0).trans (profile.upper 0)
    exact (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < (d + 1 : ℕ) + 1)).1 h
  sum_q := by
    exact ((finCongr hwidth).symm.sum_comp profile.q).trans profile.normalized
  lower s := by
    have hd : ((d + 1 : ℕ) : ℝ) + 1 = ((2 * W + 1 : ℕ) : ℝ) := by exact_mod_cast hwidth
    simpa only [hd] using profile.lower ((finCongr hwidth).symm s)
  upper s := by
    have hd : ((d + 1 : ℕ) : ℝ) + 1 = ((2 * W + 1 : ℕ) : ℝ) := by exact_mod_cast hwidth
    simpa only [hd] using profile.upper ((finCongr hwidth).symm s)

def paperSection3Atoms (k d W : ℕ) (hwidth : d + 2 = 2 * W + 1)
    (ω : Fin ((k + 1) * (d + 2)) → ℂ) : Fin (k + 1) → BandOffset W → ℂ :=
  fun i s => ω (paperIndicatorFlatIndex (k + 1) d (ZMod.finEquiv (k + 1) i)
    ((finCongr hwidth).symm s))

theorem literalIndicatorMatrix_eq_section3
    (k d W : ℕ) (hwidth : d + 2 = 2 * W + 1)
    (center : Fin (d + 1)) (hcenter : center.val = W)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hfit : 2 * W + 1 ≤ k + 1)
    (ω : Fin ((k + 1) * (d + 2)) → ℂ) :
    Section6.literalIndicatorMatrix k d center profile.b ω =
      cyclicShortRingMatrix (paperSection3Weights profile hwidth hc₀) hfit
        (paperSection3Atoms k d W hwidth ω) := by
  classical
  ext i j
  change (∑ s : Fin (d + 2),
    if ZMod.finEquiv (k + 1) j = ZMod.finEquiv (k + 1) i -
        (center.val : ZMod (k + 1)) + (s.val : ZMod (k + 1))
    then profile.b s * ω (paperIndicatorFlatIndex (k + 1) d (ZMod.finEquiv (k + 1) i) s)
    else 0) = _
  unfold cyclicShortRingMatrix
  apply Fintype.sum_equiv (finCongr hwidth)
  intro s
  have hcol := section3_cyclicColumn_finEquiv hfit i (finCongr hwidth s)
  have he : cyclicColumn hfit i (finCongr hwidth s) = j ↔
      ZMod.finEquiv (k + 1) j = ZMod.finEquiv (k + 1) i -
        (center.val : ZMod (k + 1)) + (s.val : ZMod (k + 1)) := by
    constructor
    · intro hj
      rw [hj] at hcol
      simpa only [hcenter, finCongr_apply_coe] using hcol
    · intro hj
      apply (ZMod.finEquiv (k + 1)).injective
      exact hcol.trans (by simpa only [hcenter, finCongr_apply_coe] using hj.symm)
  simp only [he, paperSection3Weights, paperSection3Atoms,
    Equiv.symm_apply_apply, PaperIndicatorWeights.b]

theorem literalPhysicalLogPotential_eq_section3
    (k d W : ℕ) (hwidth : d + 2 = 2 * W + 1)
    (center : Fin (d + 1)) (hcenter : center.val = W)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hfit : 2 * W + 1 ≤ k + 1)
    (ω : Fin ((k + 1) * (d + 2)) → ℂ) (z : ℂ) :
    Section6.physicalLogPotential (Section6.literalIndicatorMatrix k d center profile.b ω) z =
      normalizedShiftLogDet
        (cyclicShortRingMatrix (paperSection3Weights profile hwidth hc₀) hfit
          (paperSection3Atoms k d W hwidth ω)) z := by
  rw [literalIndicatorMatrix_eq_section3 k d W hwidth center hcenter profile hc₀ hfit]
  simp only [Section6.physicalLogPotential, normalizedShiftLogDet, Nat.cast_add, Nat.cast_one]

end CircularLawSections56.Section5
