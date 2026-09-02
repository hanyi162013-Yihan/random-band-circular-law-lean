import CircularLawSection4.PaperCyclicLastRow

/-!
# The paper's cyclic band matrix in raw and physical coordinates

The residual matrix produced by state-copy elimination is naturally indexed
by the physical labels `Fin N`, whereas the manuscript first writes its rows
and columns using raw cyclic sites in `ZMod N`.  This module gives both
independent relabelings explicitly and records their deterministic determinant
sign.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix

variable {R : Type*} [Field R]

/-- The closure-plus-band matrix before converting raw cyclic sites to the
ordered physical labels.  The two terms are added, so coincident closure and
band positions (for example when `N = 1`) retain both contributions. -/
def paperCyclicRawBandMatrix
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R) :
    Matrix (ZMod N) (ZMod N) R :=
  fun i j ↦
    (if j = i + offset + 1 + (m : ZMod N) then βraw i else 0) +
      ∑ k : Fin (m + 1),
        if j = i + offset + (k.val : ZMod N) then a i k else 0

/-- Row relabeling: raw equation site `i` is sent to the physical label of
its closure site `i + offset + 1 + m`. -/
def paperCyclicBandRowEquiv
    (N m : ℕ) [NeZero N] (offset : ZMod N) : ZMod N ≃ Fin N where
  toFun i := (ZMod.finEquiv N).symm
    (i + offset + 1 + (m : ZMod N))
  invFun p := ZMod.finEquiv N p - offset - 1 - (m : ZMod N)
  left_inv i := by
    simp
    abel
  right_inv p := by
    apply (ZMod.finEquiv N).injective
    simp
    abel

/-- Column relabeling from a raw cyclic physical site to its canonical
`Fin N` representative. -/
def paperCyclicBandColumnEquiv
    (N : ℕ) [NeZero N] : ZMod N ≃ Fin N :=
  (ZMod.finEquiv N).symm

@[simp] theorem paperCyclicBandRowEquiv_symm_apply
    (N m : ℕ) [NeZero N] (offset : ZMod N) (p : Fin N) :
    (paperCyclicBandRowEquiv N m offset).symm p =
      cyclicAnchorEquationRawSite N m offset p :=
  rfl

@[simp] theorem paperCyclicBandColumnEquiv_symm_apply
    (N : ℕ) [NeZero N] (j : Fin N) :
    (paperCyclicBandColumnEquiv N).symm j = ZMod.finEquiv N j :=
  rfl

private theorem paperCyclicRawBand_closure_iff
    (N m : ℕ) [NeZero N] (offset : ZMod N) (p j : Fin N) :
    ZMod.finEquiv N j =
        cyclicAnchorEquationRawSite N m offset p + offset + 1 +
          (m : ZMod N) ↔
      j = p := by
  constructor
  · intro h
    apply (ZMod.finEquiv N).injective
    rw [h]
    simp [cyclicAnchorEquationRawSite]
    abel
  · intro h
    subst j
    simp [cyclicAnchorEquationRawSite]
    abel

/-- The independent raw-row/raw-column relabelings turn the manuscript's raw
cyclic band matrix into exactly `paperCyclicPhysicalMatrix`. -/
theorem paperCyclicRawBandMatrix_reindex
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R) :
    Matrix.reindex (paperCyclicBandRowEquiv N m offset)
        (paperCyclicBandColumnEquiv N)
        (paperCyclicRawBandMatrix N m offset βraw a) =
      paperCyclicPhysicalMatrix N m offset βraw a := by
  ext p j
  change
    paperCyclicRawBandMatrix N m offset βraw a
        ((paperCyclicBandRowEquiv N m offset).symm p)
        ((paperCyclicBandColumnEquiv N).symm j) =
      paperCyclicPhysicalMatrix N m offset βraw a p j
  rw [paperCyclicBandRowEquiv_symm_apply,
    paperCyclicBandColumnEquiv_symm_apply]
  simp only [paperCyclicRawBandMatrix, paperCyclicPhysicalMatrix]
  simp only [show
      (ZMod.finEquiv N j =
          cyclicAnchorEquationRawSite N m offset p + offset + 1 +
            (m : ZMod N)) ↔ j = p by
    exact paperCyclicRawBand_closure_iff N m offset p j]

/-- The deterministic sign caused by the independent row and column
relabelings of the raw cyclic band matrix. -/
def paperCyclicBandReindexSign
    (N m : ℕ) [NeZero N] (offset : ZMod N) : R :=
  (Equiv.Perm.sign
    ((paperCyclicBandColumnEquiv N).trans
      (paperCyclicBandRowEquiv N m offset).symm) : R)

/-- The raw-band reindexing factor is always `+1` or `-1`. -/
theorem paperCyclicBandReindexSign_spec
    (N m : ℕ) [NeZero N] (offset : ZMod N) :
    paperCyclicBandReindexSign (R := R) N m offset = 1 ∨
      paperCyclicBandReindexSign (R := R) N m offset = -1 := by
  rcases Int.units_eq_one_or
      (Equiv.Perm.sign
        ((paperCyclicBandColumnEquiv N).trans
          (paperCyclicBandRowEquiv N m offset).symm)) with h | h
  · left
    simp [paperCyclicBandReindexSign, h]
  · right
    simp [paperCyclicBandReindexSign, h]

/-- Exact determinant comparison between the physical and raw cyclic band
matrices, with the independent reindexings exposed as a deterministic sign. -/
theorem paperCyclicPhysicalMatrix_det
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R) :
    (paperCyclicPhysicalMatrix N m offset βraw a).det =
      paperCyclicBandReindexSign (R := R) N m offset *
        (paperCyclicRawBandMatrix N m offset βraw a).det := by
  rw [← paperCyclicRawBandMatrix_reindex (R := R) N m offset βraw a]
  simpa [paperCyclicBandReindexSign] using
    Matrix.det_reindex
      (paperCyclicBandRowEquiv N m offset)
      (paperCyclicBandColumnEquiv N)
      (paperCyclicRawBandMatrix N m offset βraw a)

/-- Sign-only existential form of `paperCyclicPhysicalMatrix_det`. -/
theorem exists_sign_paperCyclicPhysicalMatrix_det
    (N m : ℕ) [NeZero N] (offset : ZMod N)
    (βraw : ZMod N → R) (a : ZMod N → Fin (m + 1) → R) :
    ∃ σ : R, (σ = 1 ∨ σ = -1) ∧
      (paperCyclicPhysicalMatrix N m offset βraw a).det =
        σ * (paperCyclicRawBandMatrix N m offset βraw a).det := by
  refine ⟨paperCyclicBandReindexSign (R := R) N m offset,
    paperCyclicBandReindexSign_spec (R := R) N m offset, ?_⟩
  exact paperCyclicPhysicalMatrix_det (R := R) N m offset βraw a

end CircularLawSection4
