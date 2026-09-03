/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/RowIndependence.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.RandomModel
import Mathlib.Probability.Independence.InfinitePi

/-!
# Grouping independent entries into independent rows

McDiarmid's inequality is naturally applied to the rows of the random matrix.  The model in
`RandomModel.lean`, however, states the stronger and more primitive assumption that all matrix
entries are mutually independent.  This file proves, rather than assumes, the bridge from entry
independence to row-vector independence.

The generic theorem `iIndepFun_curry_of_iIndepFun_uncurry` is the converse direction needed here
to mathlib's `ProbabilityTheory.iIndepFun_uncurry`: a mutually independent dependent family stays
mutually independent after its coordinates are grouped into blocks.
-/

namespace Arxiv2410V3

open MeasureTheory ProbabilityTheory

section Grouping

variable {ι Ω : Type*} {κ : ι → Type*}
  {𝓧 : (i : ι) → κ i → Type*}
  [MeasurableSpace Ω] [∀ i j, MeasurableSpace (𝓧 i j)]
  {P : Measure Ω}

/-- Grouping a mutually independent dependent family into coordinate blocks preserves mutual
independence.  This is the direction complementary to mathlib's `iIndepFun_uncurry`.

The proof identifies the law of all scalar coordinates with their infinite product, transports
that law through the measurable currying equivalence, and identifies each block marginal with
the corresponding inner product measure. -/
theorem iIndepFun_curry_of_iIndepFun_uncurry
    {X : (i : ι) → (j : κ i) → Ω → 𝓧 i j}
    (hX : ∀ i j, Measurable (X i j))
    (hIndep : iIndepFun (fun (p : (i : ι) × κ i) ω ↦ X p.1 p.2 ω) P) :
    iIndepFun (fun i ω j ↦ X i j ω) P := by
  let _ : IsProbabilityMeasure P := hIndep.isProbabilityMeasure
  have hCoordinateIndep (i : ι) : iIndepFun (X i) P := by
    exact hIndep.precomp (g := fun j ↦ ⟨i, j⟩) (by
      intro j k hjk
      simpa using hjk)
  have hCurry :
      (MeasurableEquiv.piCurry 𝓧) ∘
          (fun ω (p : (i : ι) × κ i) ↦ X p.1 p.2 ω) =
        fun ω i j ↦ X i j ω := by
    ext ω i j
    rfl
  have hRowsMeas : ∀ i, Measurable (fun ω j ↦ X i j ω) :=
    fun i ↦ measurable_pi_lambda _ (hX i)
  let _ (i : ι) (j : κ i) : IsProbabilityMeasure (P.map (X i j)) :=
    Measure.isProbabilityMeasure_map (hX i j).aemeasurable
  let _ (i : ι) : IsProbabilityMeasure (P.map (fun ω j ↦ X i j ω)) :=
    Measure.isProbabilityMeasure_map (hRowsMeas i).aemeasurable
  have hFlatMeas :
      Measurable (fun ω (p : (i : ι) × κ i) ↦ X p.1 p.2 ω) :=
    measurable_pi_lambda _ fun p ↦ hX p.1 p.2
  have hCurryMeas : Measurable (MeasurableEquiv.piCurry 𝓧) :=
    (MeasurableEquiv.piCurry 𝓧).measurable
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map hRowsMeas]
  rw [← hCurry, ← Measure.map_map hCurryMeas hFlatMeas,
    hIndep.map_fun_eq_infinitePi_map (fun p ↦ hX p.1 p.2),
    Measure.infinitePi_map_piCurry (fun i j ↦ P.map (X i j))]
  apply congrArg Measure.infinitePi
  funext i
  exact ((hCoordinateIndep i).map_fun_eq_infinitePi_map (hX i)).symm

end Grouping

section MatrixRows

variable {n : ℕ}
  {Omega OmegaXi : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
  {mu : Measure Omega} {nu : Measure OmegaXi}
  [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]

/-- The row-vector random variables in a v3 random-matrix model are mutually independent.

This is the exact independence input needed before applying a row-wise bounded-differences /
McDiarmid argument.  It is derived solely from `RandomMatrixModelV3.entries_independent` and the
coordinate measurability fields; no additional probabilistic interface is used. -/
theorem RandomMatrixModelV3.rows_independent
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    iIndepFun (fun i omega j ↦ model.matrix omega i j) mu := by
  have hEntriesSigma :
      iIndepFun
        (fun (p : (i : Fin n) × Fin n) omega ↦ model.matrix omega p.1 p.2) mu := by
    simpa using model.entries_independent.precomp
      (Equiv.sigmaEquivProd (Fin n) (Fin n)).injective
  exact iIndepFun_curry_of_iIndepFun_uncurry model.entry_measurable
    hEntriesSigma

/-- Each random row, regarded as a `Fin n → ℂ`-valued function, is measurable. -/
theorem RandomMatrixModelV3.row_measurable
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i : Fin n) :
    Measurable (fun omega j ↦ model.matrix omega i j) :=
  measurable_pi_iff.2 (model.entry_measurable i)

end MatrixRows

end Arxiv2410V3

