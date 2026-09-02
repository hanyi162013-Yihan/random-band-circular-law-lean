import CircularLawSection4.PaperPressureObservable

/-!
# Measurability of the paper pressure observable

The row-linear exterior step and its finite open product are continuous in
all scalar row entries.  The logarithm of the product norm is therefore
measurable (continuity of the logarithm at zero is neither true nor needed).
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

namespace PaperIndicatorWeights

variable {m n : ℕ} {c₀ C₀ : ℝ}

/-- A denominator-cleared exterior row depends continuously on all scalar
atom entries of that row. -/
theorem continuous_paperIndicatorOpenExteriorRow
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1)) :
    Continuous (fun row : PaperIndicatorAtomRow m =>
      profile.paperIndicatorOpenExteriorRow center z q row) := by
  classical
  unfold paperIndicatorOpenExteriorRow
  apply Continuous.sub
  · apply continuous_finsetSum Finset.univ
    intro ell _
    have hatom : Continuous (fun row : PaperIndicatorAtomRow m =>
        paperIndicatorOpenRowAtoms row ell) := by
      cases ell with
      | none =>
          simpa [paperIndicatorOpenRowAtoms] using
            (continuous_apply (Fin.last (m + 1)) :
              Continuous (fun row : PaperIndicatorAtomRow m =>
                row (Fin.last (m + 1))))
      | some j =>
          simpa [paperIndicatorOpenRowAtoms] using
            (continuous_apply j.castSucc :
              Continuous (fun row : PaperIndicatorAtomRow m => row j.castSucc))
    exact (continuous_const.mul hatom).smul continuous_const
  · exact continuous_const

/-- The chronological exterior product is continuous in the complete list
of sampled rows. -/
theorem continuous_paperIndicatorOpenExteriorProduct
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1)) : ∀ n : ℕ,
    Continuous (fun rows : Fin n → PaperIndicatorAtomRow m =>
      profile.paperIndicatorOpenExteriorProduct center z q rows) := by
  intro n
  induction n with
  | zero =>
      exact continuous_const
  | succ n ih =>
      have htail : Continuous
          (fun rows : Fin (n + 1) → PaperIndicatorAtomRow m =>
            fun i : Fin n => rows i.succ) := by
        apply continuous_pi
        intro i
        exact continuous_apply i.succ
      have hhead : Continuous
          (fun rows : Fin (n + 1) → PaperIndicatorAtomRow m =>
            profile.paperIndicatorOpenExteriorRow center z q
              (rows 0)) :=
        (continuous_paperIndicatorOpenExteriorRow profile center z q).comp
          (continuous_apply 0)
      have hrest : Continuous
          (fun rows : Fin (n + 1) → PaperIndicatorAtomRow m =>
            profile.paperIndicatorOpenExteriorProduct center z q
              (fun i : Fin n => rows i.succ)) :=
        ih.comp htail
      have hmul : Continuous
          (fun rows : Fin (n + 1) → PaperIndicatorAtomRow m =>
            profile.paperIndicatorOpenExteriorProduct center z q
                (fun i : Fin n => rows i.succ) *
              profile.paperIndicatorOpenExteriorRow center z q (rows 0)) :=
        hrest.mul hhead
      simpa [paperIndicatorOpenExteriorProduct, List.ofFn_succ',
        chronologicalProduct_append] using hmul

/-- The paper's open pressure `log ||A_[1,n]^(q)||` is measurable on the
literal IID row sample space. -/
theorem measurable_paperIndicatorOpenPressure
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1)) (n : ℕ) :
    Measurable (fun rows : Fin n → PaperIndicatorAtomRow m =>
      profile.paperIndicatorOpenPressure center z q rows) := by
  unfold paperIndicatorOpenPressure
  exact Real.measurable_log.comp
    (continuous_paperIndicatorOpenExteriorProduct
      profile center z q n).norm.measurable

end PaperIndicatorWeights

end CircularLawSection4
