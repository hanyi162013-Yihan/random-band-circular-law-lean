import CircularLawSection6.MatrixCutoffComparison
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Tactic.FunProp

/-! # Measurability of the actual cutoff on the nonsingular event

The proved comparison implies continuity on invertible matrices. Extending
by zero off that open set yields a measurable representative. Consequently
the genuine cutoff is a.e. strongly measurable for every measurable random
matrix whose determinant is nonzero almost surely; no measurable choice
of singular vectors is needed.
-/

open MeasureTheory Filter Topology Set
open TaoVuReplacement

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
theorem continuous_hilbertSchmidtSq :
    Continuous (hilbertSchmidtSq : Matrix ι ι ℂ → ℝ) := by
  unfold hilbertSchmidtSq
  fun_prop

theorem continuousOn_matrixCutoffPotential {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun A : Matrix ι ι ℂ => matrixCutoffPotential A a) {A | A.det ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_iff_continuousAt.mpr
  intro A
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : Tendsto (fun B : {B : Matrix ι ι ℂ // B.det ≠ 0} =>
      Real.sqrt (hilbertSchmidtSq (B.val - A.val)) /
        (a * Real.sqrt (Fintype.card ι : ℝ))) (𝓝 A) (𝓝 0) := by
    have hc : Continuous (fun B : {B : Matrix ι ι ℂ // B.det ≠ 0} =>
        Real.sqrt (hilbertSchmidtSq (B.val - A.val)) /
          (a * Real.sqrt (Fintype.card ι : ℝ))) :=
      (Real.continuous_sqrt.comp (continuous_hilbertSchmidtSq.comp
        (continuous_subtype_val.sub continuous_const))).div_const _
    simpa [hilbertSchmidtSq] using hc.tendsto A
  apply squeeze_zero (fun _ => norm_nonneg _) (fun B => ?_) hb
  simpa only [Real.norm_eq_abs, Set.domRestrict_apply] using
    matrixCutoffPotential_difference_le B.val A.val B.property A.property ha

def goodMatrixCutoffPotential (a : ℝ) (A : Matrix ι ι ℂ) : ℝ :=
  if A.det ≠ 0 then matrixCutoffPotential A a else 0

theorem measurable_goodMatrixCutoffPotential {a : ℝ} (ha : 0 < a) :
    Measurable (goodMatrixCutoffPotential (ι := ι) a) := by
  have hS : MeasurableSet {A : Matrix ι ι ℂ | A.det ≠ 0} :=
    (isClosed_eq Matrix.continuous_det continuous_const).isOpen_compl.measurableSet
  exact (continuousOn_matrixCutoffPotential (ι := ι) ha).measurable_piecewise
    continuousOn_const hS

theorem aestronglyMeasurable_matrixCutoffPotential {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Ω → Matrix ι ι ℂ) (hA : Measurable A)
    (hdet : ∀ᵐ ω ∂μ, (A ω).det ≠ 0) {a : ℝ} (ha : 0 < a) :
    AEStronglyMeasurable (fun ω => matrixCutoffPotential (A ω) a) μ := by
  apply ((measurable_goodMatrixCutoffPotential ha).comp hA).aestronglyMeasurable.congr
  filter_upwards [hdet] with ω hω
  simp [goodMatrixCutoffPotential, hω]

end CircularLawSection6
