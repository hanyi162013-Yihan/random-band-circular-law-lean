import CircularLawSection4.CyclicCompanionPhysicalBlock

/-!
# The manuscript's sparse cyclic last row

This module specializes the abstract cyclic-companion elimination to the
last equation used in the periodic determinant argument.  The raw last row
has a closure coefficient at `(i + 1, m)` and coefficients
`βᵢ⁻¹ aᵢₖ` on the copies `(i,k)`.  The two contributions are deliberately
added rather than made mutually exclusive: when `N = 1`, the closure and
same-block coordinates can coincide.

After the anchor-row scaling by `βᵢ`, the inverses disappear.  The residual
physical matrix is therefore the cyclic band matrix consisting of the
closure diagonal plus the sum of all coefficients whose shifted physical
column is the requested column.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix

variable {R : Type*} [Field R]

/-- The raw sparse last row in the periodic companion system.  It is written
as a sum of two indicator terms so that the `N = 1` overlap is retained. -/
def paperSparseCyclicLastRow
    (N m : ℕ) [NeZero N]
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R) :
    ZMod N → (ZMod N × Fin (m + 1) → R) :=
  fun i col ↦
    (if col = (i + 1, Fin.last m) then 1 else 0) +
      if col.1 = i then (βraw i)⁻¹ * a i col.2 else 0

/-- The ordered anchor-row multiplier belonging to physical row `p`. -/
def paperCyclicOrderedScaling
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (βraw : ZMod N → R) : Fin N → R :=
  fun p ↦ βraw (cyclicAnchorEquationRawSite N m offset p)

/-- The explicit cyclic band matrix left after state-copy elimination and
denominator clearing.  In physical row `p`, put `i` for its raw equation
site.  There is a closure entry `βraw i` in column `p`, and every `a i k`
is placed in the physical column represented by `i + offset + k`. -/
def paperCyclicPhysicalMatrix
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R) :
    Matrix (Fin N) (Fin N) R :=
  fun p j ↦
    let i := cyclicAnchorEquationRawSite N m offset p
    (if j = p then βraw i else 0) +
      ∑ k : Fin (m + 1),
        if ZMod.finEquiv N j = i + offset + (k.val : ZMod N)
        then a i k else 0

private theorem cyclicEarly_eq_raw_iff
    (N : ℕ) [NeZero N] (offset i : ZMod N)
    (j : Fin N) (k : Fin m) :
    cyclicEarlyStateCopyRawSite N offset j k = i ↔
      ZMod.finEquiv N j = i + offset + (k.val : ZMod N) := by
  simp [cyclicEarlyStateCopyRawSite]
  constructor <;> intro h
  · rw [← h]
    abel
  · rw [h]
    abel

private theorem cyclicAnchor_eq_raw_iff
    (N m : ℕ) [NeZero N] (offset i : ZMod N)
    (j : Fin N) :
    cyclicAnchorStateCopyRawSite N m offset j = i ↔
      ZMod.finEquiv N j = i + offset + (m : ZMod N) := by
  simp [cyclicAnchorStateCopyRawSite]
  constructor <;> intro h
  · rw [← h]
    abel
  · rw [h]
    abel

private theorem cyclicAnchor_closure_iff
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (p j : Fin N) :
    (cyclicAnchorStateCopyRawSite N m offset j, Fin.last m) =
        (cyclicAnchorEquationRawSite N m offset p + 1, Fin.last m) ↔
      j = p := by
  simp only [Prod.mk.injEq]
  constructor
  · intro h
    apply (ZMod.finEquiv N).injective
    simp [cyclicAnchorStateCopyRawSite, cyclicAnchorEquationRawSite] at h
    linear_combination h
  · intro h
    subst j
    simp [cyclicAnchorStateCopyRawSite, cyclicAnchorEquationRawSite]
    abel

private theorem cyclicEarly_ne_closure
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (p j : Fin N) (k : Fin m) :
    (cyclicEarlyStateCopyRawSite N offset j k, k.castSucc) ≠
      (cyclicAnchorEquationRawSite N m offset p + 1, Fin.last m) := by
  intro h
  have hk : k.castSucc = Fin.last m := congrArg Prod.snd h
  have hkval : k.val = m := congrArg Fin.val hk
  exact (Nat.ne_of_lt k.isLt) hkval

/-- Entrywise form of the paper-specific substitution: scaling the raw last
equation by its own nonzero `β` cancels every `β⁻¹`, including in the
degenerate `N = 1` case where the closure and a same-block term coincide. -/
theorem scaledPaperCyclicCompanionPhysicalBlock_apply
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (βraw : ZMod N → R) (hβ : ∀ i, βraw i ≠ 0)
    (a : ZMod N → Fin (m + 1) → R)
    (p j : Fin N) :
    stateCopyPhysicalBlock (R := R) N m
        (stateCopyAnchorRowScaling (R := R) N m
            (paperCyclicOrderedScaling N m offset βraw) *
          orderedCyclicCompanionState N m offset
            (paperSparseCyclicLastRow N m βraw a)) p j =
      paperCyclicPhysicalMatrix N m offset βraw a p j := by
  rw [scaledCyclicCompanionPhysicalBlock_apply (R := R) N m]
  rw [cyclicCompanionPhysicalMatrix]
  simp only [paperCyclicOrderedScaling, paperSparseCyclicLastRow,
    paperCyclicPhysicalMatrix]
  let i := cyclicAnchorEquationRawSite N m offset p
  change
    βraw i *
        ((∑ k : Fin m,
            ((if (cyclicEarlyStateCopyRawSite N offset j k, k.castSucc) =
                (i + 1, Fin.last m) then 1 else 0) +
              if cyclicEarlyStateCopyRawSite N offset j k = i then
                (βraw i)⁻¹ * a i k.castSucc else 0)) +
          ((if (cyclicAnchorStateCopyRawSite N m offset j, Fin.last m) =
              (i + 1, Fin.last m) then 1 else 0) +
            if cyclicAnchorStateCopyRawSite N m offset j = i then
              (βraw i)⁻¹ * a i (Fin.last m) else 0)) =
      (if j = p then βraw i else 0) +
        ∑ k : Fin (m + 1),
          if ZMod.finEquiv N j = i + offset + (k.val : ZMod N) then
            a i k else 0
  have hEarlyClosure (k : Fin m) :
      (cyclicEarlyStateCopyRawSite N offset j k, k.castSucc) ≠
        (i + 1, Fin.last m) := by
    dsimp [i]
    exact cyclicEarly_ne_closure N m offset p j k
  simp_rw [if_neg (hEarlyClosure _)]
  have hAnchorClosure :
      ((cyclicAnchorStateCopyRawSite N m offset j, Fin.last m) =
          (i + 1, Fin.last m)) ↔ j = p := by
    dsimp [i]
    exact cyclicAnchor_closure_iff N m offset p j
  simp only [hAnchorClosure]
  simp_rw [cyclicEarly_eq_raw_iff N offset i j]
  simp only [cyclicAnchor_eq_raw_iff N m offset i j]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  simp_rw [mul_add, Finset.mul_sum]
  simp only [zero_add, mul_ite, mul_zero, mul_one]
  simp only [← mul_assoc, mul_inv_cancel₀ (hβ i), one_mul]
  ring

/-- Matrix form: the paper's row scaling removes all raw inverses and leaves
exactly the explicit closure-plus-band physical matrix. -/
theorem scaledPaperCyclicCompanionPhysicalBlock_eq
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (βraw : ZMod N → R) (hβ : ∀ i, βraw i ≠ 0)
    (a : ZMod N → Fin (m + 1) → R) :
    stateCopyPhysicalBlock (R := R) N m
        (stateCopyAnchorRowScaling (R := R) N m
            (paperCyclicOrderedScaling N m offset βraw) *
          orderedCyclicCompanionState N m offset
            (paperSparseCyclicLastRow N m βraw a)) =
      paperCyclicPhysicalMatrix N m offset βraw a := by
  ext p j
  exact scaledPaperCyclicCompanionPhysicalBlock_apply
    (R := R) N m offset βraw hβ a p j

end CircularLawSection4
