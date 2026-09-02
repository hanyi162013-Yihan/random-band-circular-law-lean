import BernoulliLinearAlgebra.BoundaryGram
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# Dense-chart extension by continuity

Section 9.5 first proves the coefficient--volume bounds on the chart where the
upper-left boundary block is nonsingular and then passes to an arbitrary
boundary relation by a small perturbation.  This file isolates that last,
purely deterministic step.

There are three layers below:

* closed two-sided inequalities pass to limits;
* entrywise convergence of finite matrices implies convergence of their
  determinant and Gram determinant;
* a reusable package extends coefficient--volume bounds from any
  sequentially dense chart.

The paper's algebraic construction of perturbations `Θ + εₙ I`, with `εₙ`
chosen away from finitely many zeros, is deliberately an input here through
`SequentiallyDenseAt`.  Thus the analytic limit passage is formalized without
silently assuming a particular perturbation sequence.
-/

open Filter Topology
open scoped Matrix Topology

namespace BernoulliLinearAlgebra

section ClosedInequalities

/-- A two-sided real inequality is preserved under a common limiting process.
The bounds are allowed to vary with the approximation parameter. -/
theorem two_sided_bounds_of_tendsto {X : Type*} {l : Filter X} [l.NeBot]
    {lower middle upper : X → ℝ} {a b c : ℝ}
    (hlower : Tendsto lower l (nhds a))
    (hmiddle : Tendsto middle l (nhds b))
    (hupper : Tendsto upper l (nhds c))
    (hbounds : ∀ᶠ x in l, lower x ≤ middle x ∧ middle x ≤ upper x) :
    a ≤ b ∧ b ≤ c := by
  constructor
  · exact le_of_tendsto_of_tendsto hlower hmiddle (hbounds.mono fun _ hx ↦ hx.1)
  · exact le_of_tendsto_of_tendsto hmiddle hupper (hbounds.mono fun _ hx ↦ hx.2)

/-- Sequence form of `two_sided_bounds_of_tendsto`.  This is the form used
directly for the perturbations in Section 9.5. -/
theorem two_sided_bounds_of_sequence_limit
    {lower middle upper : ℕ → ℝ} {a b c : ℝ}
    (hlower : Tendsto lower atTop (nhds a))
    (hmiddle : Tendsto middle atTop (nhds b))
    (hupper : Tendsto upper atTop (nhds c))
    (hbounds : ∀ n, lower n ≤ middle n ∧ middle n ≤ upper n) :
    a ≤ b ∧ b ≤ c :=
  two_sided_bounds_of_tendsto hlower hmiddle hupper
    (Filter.Eventually.of_forall hbounds)

/-- If three real-valued functions are continuous at a target, a two-sided
inequality along any convergent sequence survives at the target. -/
theorem continuous_two_sided_bounds_at_limit
    {X : Type*} [TopologicalSpace X] {xSeq : ℕ → X} {x : X}
    {lower middle upper : X → ℝ}
    (hx : Tendsto xSeq atTop (nhds x))
    (hlower : ContinuousAt lower x)
    (hmiddle : ContinuousAt middle x)
    (hupper : ContinuousAt upper x)
    (hbounds : ∀ n,
      lower (xSeq n) ≤ middle (xSeq n) ∧
        middle (xSeq n) ≤ upper (xSeq n)) :
    lower x ≤ middle x ∧ middle x ≤ upper x := by
  exact two_sided_bounds_of_sequence_limit
    (by simpa [Function.comp_def] using Filter.Tendsto.comp hlower hx)
    (by simpa [Function.comp_def] using Filter.Tendsto.comp hmiddle hx)
    (by simpa [Function.comp_def] using Filter.Tendsto.comp hupper hx)
    hbounds

/-- Constant bounds are closed under sequential limits. -/
theorem mem_Icc_of_sequence_limit {f : ℕ → ℝ} {x lower upper : ℝ}
    (hf : Tendsto f atTop (nhds x))
    (hbounds : ∀ n, lower ≤ f n ∧ f n ≤ upper) :
    lower ≤ x ∧ x ≤ upper := by
  exact two_sided_bounds_of_sequence_limit tendsto_const_nhds hf
    tendsto_const_nhds hbounds

end ClosedInequalities

section MatrixContinuity

variable {m n : Type*}

/-- Convergence in the product topology on a finite matrix is exactly
entrywise convergence.  The forward implication does not need finiteness, but
the finite hypotheses are kept here to match the determinant applications. -/
theorem tendsto_matrix_iff_entrywise {X : Type*} {l : Filter X}
    {A : X → Matrix m n ℂ} {A₀ : Matrix m n ℂ} :
    Tendsto A l (nhds A₀) ↔
      ∀ i j, Tendsto (fun x ↦ A x i j) l (nhds (A₀ i j)) := by
  constructor
  · intro h i j
    exact (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp h) i)) j
  · intro h
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact h i j

variable [Fintype n] [DecidableEq n]

/-- The determinant is continuous under entrywise matrix convergence. -/
theorem tendsto_det_of_entrywise {X : Type*} {l : Filter X}
    {A : X → Matrix n n ℂ} {A₀ : Matrix n n ℂ}
    (hA : ∀ i j, Tendsto (fun x ↦ A x i j) l (nhds (A₀ i j))) :
    Tendsto (fun x ↦ (A x).det) l (nhds A₀.det) := by
  have hA' : Tendsto A l (nhds A₀) :=
    (tendsto_matrix_iff_entrywise (m := n) (n := n)).mpr hA
  simpa [Function.comp_def] using
    Filter.Tendsto.comp continuous_id.matrix_det.continuousAt hA'

variable [Fintype m]

/-- The complex Gram determinant `det(I + Aᴴ A)`. -/
def complexGramDet (A : Matrix m n ℂ) : ℂ :=
  (1 + Aᴴ * A).det

/-- The real form of the Gram determinant.  For a genuine Gram matrix the
complex determinant is real; taking `re` makes the codomain useful for order
and limit arguments without requiring that positivity fact at every call. -/
def realGramDet (A : Matrix m n ℂ) : ℝ :=
  (complexGramDet A).re

/-- The rectangular Gram volume used in the continuity argument, written as
the square root of the real Gram determinant.  The distinct name avoids a
collision with the square-matrix `gramVolume` in `VolumeComparison`. -/
noncomputable def rectangularGramVolume (A : Matrix m n ℂ) : ℝ :=
  Real.sqrt (realGramDet A)

/-- The complex Gram determinant is a continuous polynomial in the matrix
entries and their conjugates. -/
theorem continuous_complexGramDet :
    Continuous (complexGramDet : Matrix m n ℂ → ℂ) := by
  unfold complexGramDet
  exact (continuous_const.add
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_id)).matrix_det

/-- The real Gram determinant is continuous. -/
theorem continuous_realGramDet :
    Continuous (realGramDet : Matrix m n ℂ → ℝ) := by
  unfold realGramDet
  exact Complex.continuous_re.comp continuous_complexGramDet

/-- The Gram volume is continuous.  This is the exact continuity input for
the volume factor `det(I + AᴴA)¹ᐟ²` in the dense-chart argument. -/
theorem continuous_rectangularGramVolume :
    Continuous (rectangularGramVolume : Matrix m n ℂ → ℝ) := by
  unfold rectangularGramVolume
  exact Real.continuous_sqrt.comp continuous_realGramDet

/-- Entrywise convergence implies convergence of the complex Gram
determinant. -/
theorem tendsto_complexGramDet_of_entrywise {X : Type*} {l : Filter X}
    {A : X → Matrix m n ℂ} {A₀ : Matrix m n ℂ}
    (hA : ∀ i j, Tendsto (fun x ↦ A x i j) l (nhds (A₀ i j))) :
    Tendsto (fun x ↦ complexGramDet (A x)) l (nhds (complexGramDet A₀)) := by
  have hA' : Tendsto A l (nhds A₀) :=
    (tendsto_matrix_iff_entrywise (m := m) (n := n)).mpr hA
  simpa [Function.comp_def] using
    Filter.Tendsto.comp
      (continuous_complexGramDet (m := m) (n := n)).continuousAt hA'

/-- Entrywise convergence implies convergence of the real Gram determinant. -/
theorem tendsto_realGramDet_of_entrywise {X : Type*} {l : Filter X}
    {A : X → Matrix m n ℂ} {A₀ : Matrix m n ℂ}
    (hA : ∀ i j, Tendsto (fun x ↦ A x i j) l (nhds (A₀ i j))) :
    Tendsto (fun x ↦ realGramDet (A x)) l (nhds (realGramDet A₀)) := by
  have hA' : Tendsto A l (nhds A₀) :=
    (tendsto_matrix_iff_entrywise (m := m) (n := n)).mpr hA
  simpa [Function.comp_def] using
    Filter.Tendsto.comp
      (continuous_realGramDet (m := m) (n := n)).continuousAt hA'

/-- Entrywise convergence also implies convergence of the Gram volume. -/
theorem tendsto_rectangularGramVolume_of_entrywise {X : Type*} {l : Filter X}
    {A : X → Matrix m n ℂ} {A₀ : Matrix m n ℂ}
    (hA : ∀ i j, Tendsto (fun x ↦ A x i j) l (nhds (A₀ i j))) :
    Tendsto (fun x ↦ rectangularGramVolume (A x)) l
      (nhds (rectangularGramVolume A₀)) := by
  have hA' : Tendsto A l (nhds A₀) :=
    (tendsto_matrix_iff_entrywise (m := m) (n := n)).mpr hA
  simpa [Function.comp_def] using
    Filter.Tendsto.comp
      (continuous_rectangularGramVolume
        (m := m) (n := n)).continuousAt hA'

end MatrixContinuity

section DenseChart

variable {X : Type*} [TopologicalSpace X]

/-- A point is sequentially approachable from a chart if there is a sequence
of chart points converging to it.  In the paper, this packages the separate
algebraic choice of `εₙ → 0` avoiding the finitely many zeros of the relevant
determinant polynomial. -/
def SequentiallyDenseAt (chart : Set X) (x : X) : Prop :=
  ∃ xSeq : ℕ → X, (∀ n, xSeq n ∈ chart) ∧ Tendsto xSeq atTop (nhds x)

/-- Sequential density of a chart, in the exact form needed for the limit
argument. -/
def SequentiallyDense (chart : Set X) : Prop :=
  ∀ x, SequentiallyDenseAt chart x

/-- Data for a coefficient--volume comparison proved on a chart.  Continuity
is recorded globally because the Section 9.5 coefficient and Gram-volume
functions are finite-dimensional polynomial/continuous expressions. -/
structure ChartVolumeBounds (X : Type*) [TopologicalSpace X] where
  chart : Set X
  coefficient : X → ℝ
  volume : X → ℝ
  lowerConstant : ℝ
  upperConstant : ℝ
  continuous_coefficient : Continuous coefficient
  continuous_volume : Continuous volume
  bounds_on_chart : ∀ x ∈ chart,
    lowerConstant * volume x ≤ coefficient x ∧
      coefficient x ≤ upperConstant * volume x

namespace ChartVolumeBounds

/-- The coefficient--volume bounds extend from the chart to any point that is
the limit of chart points. -/
theorem bounds_at_limit (B : ChartVolumeBounds X) {x : X}
    (hx : SequentiallyDenseAt B.chart x) :
    B.lowerConstant * B.volume x ≤ B.coefficient x ∧
      B.coefficient x ≤ B.upperConstant * B.volume x := by
  rcases hx with ⟨xSeq, hxChart, hxLimit⟩
  apply continuous_two_sided_bounds_at_limit hxLimit
  · exact (continuous_const.mul B.continuous_volume).continuousAt
  · exact B.continuous_coefficient.continuousAt
  · exact (continuous_const.mul B.continuous_volume).continuousAt
  · intro n
    exact B.bounds_on_chart (xSeq n) (hxChart n)

/-- A sequentially dense chart transfers the comparison to every point. -/
theorem bounds_everywhere (B : ChartVolumeBounds X)
    (hdense : SequentiallyDense B.chart) (x : X) :
    B.lowerConstant * B.volume x ≤ B.coefficient x ∧
      B.coefficient x ≤ B.upperConstant * B.volume x :=
  B.bounds_at_limit (hdense x)

/-- Positivity at a limit point follows from a positive lower comparison
constant and positive volume. -/
theorem coefficient_pos_at_limit (B : ChartVolumeBounds X) {x : X}
    (hx : SequentiallyDenseAt B.chart x)
    (hlower : 0 < B.lowerConstant) (hvolume : 0 < B.volume x) :
    0 < B.coefficient x := by
  exact (mul_pos hlower hvolume).trans_le (B.bounds_at_limit hx).1

/-- Bundled conclusion used at the end of Section 9.5: both comparison bounds
and positivity hold at an arbitrary sequential limit point. -/
theorem bounds_and_positivity_at_limit (B : ChartVolumeBounds X) {x : X}
    (hx : SequentiallyDenseAt B.chart x)
    (hlower : 0 < B.lowerConstant) (hvolume : 0 < B.volume x) :
    (B.lowerConstant * B.volume x ≤ B.coefficient x ∧
      B.coefficient x ≤ B.upperConstant * B.volume x) ∧
      0 < B.coefficient x := by
  exact ⟨B.bounds_at_limit hx,
    B.coefficient_pos_at_limit hx hlower hvolume⟩

end ChartVolumeBounds

end DenseChart

end BernoulliLinearAlgebra
