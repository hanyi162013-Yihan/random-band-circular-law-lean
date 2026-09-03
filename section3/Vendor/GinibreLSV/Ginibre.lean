/- Source snapshot: upstream-sources/i-2/work/ginibre-lsv-lean/GinibreLSV/Ginibre.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.GinibreLSV.Conditioning
import Vendor.GinibreLSV.Deterministic
import Vendor.GinibreLSV.GaussianSmallBall
import Vendor.GinibreLSV.Probability
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The square complex Ginibre column model

The ambient probability space is a finite product of standard real Gaussians
on complex Euclidean space.  This is the convenient column-wise form of the
complex Ginibre ensemble for the distance-to-span argument.
-/

open MeasureTheory ProbabilityTheory Set

noncomputable section

namespace GinibreLSV

abbrev ComplexColumn (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- Independent standard Gaussian columns. -/
def complexGinibreColumns (n : ℕ) : Measure (Fin n → ComplexColumn n) :=
  Measure.pi fun _ : Fin n => stdGaussian (ComplexColumn n)

/-- Insert a distinguished column into the family of all remaining columns. -/
def insertColumn {n : ℕ} (j : Fin (n + 1)) (z : ComplexColumn (n + 1))
    (rest : Fin n → ComplexColumn (n + 1)) :
    Fin (n + 1) → ComplexColumn (n + 1) :=
  (MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => ComplexColumn (n + 1)) j).symm (z, rest)

/-- The matrix obtained after exposing one column and freezing the others. -/
def fiberMatrix {n : ℕ} (j : Fin (n + 1))
    (z : ComplexColumn (n + 1)) (rest : Fin n → ComplexColumn (n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  matrixOfColumns (insertColumn j z rest)

@[simp]
theorem insertColumn_self {n : ℕ} (j : Fin (n + 1))
    (z : ComplexColumn (n + 1)) (rest : Fin n → ComplexColumn (n + 1)) :
    insertColumn j z rest j = z := by
  simp [insertColumn, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

@[simp]
theorem insertColumn_succAbove {n : ℕ} (j : Fin (n + 1))
    (z : ComplexColumn (n + 1)) (rest : Fin n → ComplexColumn (n + 1)) (k : Fin n) :
    insertColumn j z rest (j.succAbove k) = rest k := by
  simp [insertColumn, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

@[simp]
theorem fiberMatrix_column_self {n : ℕ} (j : Fin (n + 1))
    (z : ComplexColumn (n + 1)) (rest : Fin n → ComplexColumn (n + 1)) :
    column (fiberMatrix j z rest) j = z := by
  simp [fiberMatrix]

@[simp]
theorem fiberMatrix_column_succAbove {n : ℕ} (j : Fin (n + 1))
    (z : ComplexColumn (n + 1)) (rest : Fin n → ComplexColumn (n + 1)) (k : Fin n) :
    column (fiberMatrix j z rest) (j.succAbove k) = rest k := by
  simp [fiberMatrix]

/-- The frozen span of the `n` columns other than the exposed column. -/
def otherColumnSpan {n : ℕ} (rest : Fin n → ComplexColumn (n + 1)) :
    Submodule ℂ (ComplexColumn (n + 1)) :=
  Submodule.span ℂ (Set.range rest)

theorem fiberMatrix_columnSpanExcept {n : ℕ} (j : Fin (n + 1))
    (z : ComplexColumn (n + 1)) (rest : Fin n → ComplexColumn (n + 1)) :
    columnSpanExcept (fiberMatrix j z rest) j = otherColumnSpan rest := by
  apply congrArg (Submodule.span ℂ)
  ext v
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hk
    subst k
    exact ⟨l, (fiberMatrix_column_succAbove j z rest l).symm⟩
  · rintro ⟨l, rfl⟩
    exact ⟨⟨j.succAbove l, Fin.succAbove_ne j l⟩,
      fiberMatrix_column_succAbove j z rest l⟩

theorem otherColumnSpan_ne_top {n : ℕ}
    (rest : Fin n → ComplexColumn (n + 1)) :
    otherColumnSpan rest ≠ ⊤ := by
  intro htop
  have hle : n + 1 ≤ n := by
    simpa [otherColumnSpan] using
      (finrank_le_of_span_eq_top (R := ℂ) (M := ComplexColumn (n + 1)) htop)
  omega

theorem fiberMatrix_columnDistance {n : ℕ} (j : Fin (n + 1))
    (z : ComplexColumn (n + 1)) (rest : Fin n → ComplexColumn (n + 1)) :
    columnDistance (fiberMatrix j z rest) j =
      ‖(otherColumnSpan rest)ᗮ.starProjection z‖ := by
  simp [columnDistance, fiberMatrix_columnSpanExcept]

/-- Conditional on all other columns, the exposed Gaussian column has a
uniform linear small-ball bound for its distance to their span. -/
theorem fiberMatrix_columnDistance_smallBall {n : ℕ} (j : Fin (n + 1))
    (rest : Fin n → ComplexColumn (n + 1)) (r : ℝ) (hr : 0 ≤ r) :
    stdGaussian (ComplexColumn (n + 1))
        {z | columnDistance (fiberMatrix j z rest) j < r} ≤
      gaussianPeak 1 * ENNReal.ofReal (2 * r) := by
  simpa only [fiberMatrix_columnDistance] using
    stdGaussian_complexSubspace_smallBall
      (otherColumnSpan rest) (otherColumnSpan_ne_top rest) r hr

/-- The event that a column lies within distance `r` of the moving span of
the other columns is open (hence Borel measurable).  It is an arbitrary union,
over coefficient vectors, of strict norm sublevel sets of continuous maps. -/
theorem measurableSet_columnDistance_matrixOfColumns_lt
    {m : ℕ} (j : Fin m) (r : ℝ) :
    MeasurableSet
      {C : Fin m → ComplexColumn m |
        columnDistance (matrixOfColumns C) j < r} := by
  have heq :
      {C : Fin m → ComplexColumn m |
          columnDistance (matrixOfColumns C) j < r} =
        ⋃ a : {k : Fin m // k ≠ j} → ℂ,
          {C | ‖C j - ∑ k, a k • C k‖ < r} := by
    ext C
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    simpa only [column_matrixOfColumns] using
      columnDistance_lt_iff_exists_coeff (matrixOfColumns C) j r
  rw [heq]
  apply IsOpen.measurableSet
  apply isOpen_iUnion
  intro a
  apply isOpen_lt
  · fun_prop
  · fun_prop

/-- The unconditional one-column estimate under the finite product Gaussian
law.  The moving-span event's measurability is kept as an explicit hypothesis;
the probability and conditioning content is completely discharged here. -/
theorem complexGinibre_columnDistance_smallBall_of_measurable
    {n : ℕ} (j : Fin (n + 1)) (r : ℝ) (hr : 0 ≤ r)
    (hMeas : MeasurableSet
      {C : Fin (n + 1) → ComplexColumn (n + 1) |
        columnDistance (matrixOfColumns C) j < r}) :
    complexGinibreColumns (n + 1)
        {C | columnDistance (matrixOfColumns C) j < r} ≤
      gaussianPeak 1 * ENNReal.ofReal (2 * r) := by
  let E := ComplexColumn (n + 1)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) j
  let S : Set (E × (Fin n → E)) :=
    {p | columnDistance (fiberMatrix j p.1 p.2) j < r}
  have hS : MeasurableSet S := by
    have heq : S = e.symm ⁻¹'
        {C : Fin (n + 1) → E | columnDistance (matrixOfColumns C) j < r} := by
      ext p
      simp [S, e, E, fiberMatrix, insertColumn]
    rw [heq]
    exact hMeas.preimage e.symm.measurable
  have hprod :
      (stdGaussian E).prod (Measure.pi fun _ : Fin n => stdGaussian E) S ≤
        gaussianPeak 1 * ENNReal.ofReal (2 * r) := by
    exact prod_measure_le_of_forall_left_fiber
      (stdGaussian E) (Measure.pi fun _ : Fin n => stdGaussian E)
      S hS (gaussianPeak 1 * ENNReal.ofReal (2 * r)) fun rest => by
        simpa [S, E] using fiberMatrix_columnDistance_smallBall j rest r hr
  have hpres := measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => stdGaussian E) j
  have hpre : e ⁻¹' S =
      {C : Fin (n + 1) → E | columnDistance (matrixOfColumns C) j < r} := by
    ext C
    change columnDistance
        (matrixOfColumns (insertColumn j (e C).1 (e C).2)) j < r ↔
      columnDistance (matrixOfColumns C) j < r
    have heC : insertColumn j (e C).1 (e C).2 = C := by
      change e.symm (e C) = C
      exact e.symm_apply_apply C
    rw [heC]
  calc
    complexGinibreColumns (n + 1)
        {C | columnDistance (matrixOfColumns C) j < r} =
        (Measure.pi fun _ : Fin (n + 1) => stdGaussian E) (e ⁻¹' S) := by
      rw [hpre]
      rfl
    _ = ((stdGaussian E).prod
        (Measure.pi fun _ : Fin n => stdGaussian E)) S :=
      hpres.measure_preimage hS.nullMeasurableSet
    _ ≤ gaussianPeak 1 * ENNReal.ofReal (2 * r) := hprod

theorem complexGinibre_columnDistance_smallBall
    {n : ℕ} (j : Fin (n + 1)) (r : ℝ) (hr : 0 ≤ r) :
    complexGinibreColumns (n + 1)
        {C | columnDistance (matrixOfColumns C) j < r} ≤
      gaussianPeak 1 * ENNReal.ofReal (2 * r) :=
  complexGinibre_columnDistance_smallBall_of_measurable j r hr
    (measurableSet_columnDistance_matrixOfColumns_lt j r)

/-- A square complex Ginibre least-singular-value lower-tail estimate, after
the `n` conditional estimates are combined by a union bound. -/
theorem complexGinibre_leastSingularValue_smallBall_of_measurable
    {n : ℕ} (r : ℝ) (hr : 0 ≤ r)
    (hMeas : ∀ j : Fin (n + 1), MeasurableSet
      {C : Fin (n + 1) → ComplexColumn (n + 1) |
        columnDistance (matrixOfColumns C) j < r}) :
    complexGinibreColumns (n + 1)
        {C | leastSingularValue (matrixOfColumns C) < r / (n + 1 : ℝ)} ≤
      (n + 1 : ENNReal) *
        (gaussianPeak 1 * ENNReal.ofReal (2 * r)) := by
  simpa [Nat.succ_eq_add_one] using
    measure_leastSingularValue_lt_le
      (complexGinibreColumns (n + 1)) (Nat.succ_pos n)
      (fun C => matrixOfColumns C) r
      (gaussianPeak 1 * ENNReal.ofReal (2 * r))
      (fun j => complexGinibre_columnDistance_smallBall_of_measurable
        j r hr (hMeas j))

/-- A sorry-free polynomial lower-tail theorem for square complex Ginibre
matrices.  The elementary deterministic reduction used here loses a factor
`n + 1`; sharpening that coordinate step to `sqrt (n + 1)` improves the scale
without changing the conditioning argument. -/
theorem complexGinibre_leastSingularValue_smallBall
    {n : ℕ} (r : ℝ) (hr : 0 ≤ r) :
    complexGinibreColumns (n + 1)
        {C | leastSingularValue (matrixOfColumns C) < r / (n + 1 : ℝ)} ≤
      (n + 1 : ENNReal) *
        (gaussianPeak 1 * ENNReal.ofReal (2 * r)) :=
  complexGinibre_leastSingularValue_smallBall_of_measurable r hr fun j =>
    measurableSet_columnDistance_matrixOfColumns_lt j r

end GinibreLSV

