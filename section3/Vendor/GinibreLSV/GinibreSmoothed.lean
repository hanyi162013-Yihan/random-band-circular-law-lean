/- Source snapshot: upstream-sources/i-2/work/ginibre-lsv-lean/GinibreLSV/GinibreSmoothed.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.GinibreLSV.Ginibre

/-!
# Smoothed least singular value for square complex Ginibre matrices

This file extends the column-exposure proof in `GinibreLSV.Ginibre` to an
arbitrary deterministic matrix shift and an arbitrary positive Gaussian
scale.  The probability bound is uniform in the shift.
-/

open MeasureTheory ProbabilityTheory Set

noncomputable section

namespace GinibreLSV

/-- Columns of a deterministic matrix plus scaled independent Gaussian
columns. -/
def shiftedScaledColumnFamily {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (ρ : ℝ)
    (C : Fin n → ComplexColumn n) : Fin n → ComplexColumn n :=
  fun j => column M j + (ρ : ℂ) • C j

/-- The smoothed matrix `M + ρG`, in the column realization used by the
existing square-Ginibre proof. -/
def shiftedScaledGinibreMatrix {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (ρ : ℝ)
    (C : Fin n → ComplexColumn n) : Matrix (Fin n) (Fin n) ℂ :=
  matrixOfColumns (shiftedScaledColumnFamily M ρ C)

@[simp]
theorem column_shiftedScaledGinibreMatrix {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (ρ : ℝ)
    (C : Fin n → ComplexColumn n) (j : Fin n) :
    column (shiftedScaledGinibreMatrix M ρ C) j =
      column M j + (ρ : ℂ) • C j := by
  simp [shiftedScaledGinibreMatrix, shiftedScaledColumnFamily]

/-- Entrywise matrix form of the column construction. -/
theorem shiftedScaledGinibreMatrix_eq_add_smul {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (ρ : ℝ)
    (C : Fin n → ComplexColumn n) :
    shiftedScaledGinibreMatrix M ρ C =
      M + (ρ : ℂ) • matrixOfColumns C := by
  ext i j
  simp [shiftedScaledGinibreMatrix, shiftedScaledColumnFamily,
    matrixOfColumns, column, Matrix.toLpLin_apply]

/-- Frozen span of all shifted Gaussian columns except the exposed one. -/
def shiftedOtherColumnSpan {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ρ : ℝ)
    (j : Fin (n + 1)) (rest : Fin n → ComplexColumn (n + 1)) :
    Submodule ℂ (ComplexColumn (n + 1)) :=
  Submodule.span ℂ (Set.range fun k =>
    column M (j.succAbove k) + (ρ : ℂ) • rest k)

/-- Smoothed matrix in the fiber where column `j` is fresh and all other
Gaussian columns are frozen. -/
def shiftedScaledFiberMatrix {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ρ : ℝ)
    (j : Fin (n + 1)) (z : ComplexColumn (n + 1))
    (rest : Fin n → ComplexColumn (n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  shiftedScaledGinibreMatrix M ρ (insertColumn j z rest)

@[simp]
theorem shiftedScaledFiberMatrix_column_self {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ρ : ℝ)
    (j : Fin (n + 1)) (z : ComplexColumn (n + 1))
    (rest : Fin n → ComplexColumn (n + 1)) :
    column (shiftedScaledFiberMatrix M ρ j z rest) j =
      column M j + (ρ : ℂ) • z := by
  simp [shiftedScaledFiberMatrix]

@[simp]
theorem shiftedScaledFiberMatrix_column_succAbove {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ρ : ℝ)
    (j : Fin (n + 1)) (z : ComplexColumn (n + 1))
    (rest : Fin n → ComplexColumn (n + 1)) (k : Fin n) :
    column (shiftedScaledFiberMatrix M ρ j z rest) (j.succAbove k) =
      column M (j.succAbove k) + (ρ : ℂ) • rest k := by
  simp [shiftedScaledFiberMatrix]

theorem shiftedScaledFiberMatrix_columnSpanExcept {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ρ : ℝ)
    (j : Fin (n + 1)) (z : ComplexColumn (n + 1))
    (rest : Fin n → ComplexColumn (n + 1)) :
    columnSpanExcept (shiftedScaledFiberMatrix M ρ j z rest) j =
      shiftedOtherColumnSpan M ρ j rest := by
  apply congrArg (Submodule.span ℂ)
  ext v
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hk
    subst k
    exact ⟨l, (shiftedScaledFiberMatrix_column_succAbove
      M ρ j z rest l).symm⟩
  · rintro ⟨l, rfl⟩
    exact ⟨⟨j.succAbove l, Fin.succAbove_ne j l⟩,
      shiftedScaledFiberMatrix_column_succAbove M ρ j z rest l⟩

theorem shiftedOtherColumnSpan_ne_top {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ρ : ℝ)
    (j : Fin (n + 1)) (rest : Fin n → ComplexColumn (n + 1)) :
    shiftedOtherColumnSpan M ρ j rest ≠ ⊤ := by
  intro htop
  have hle : n + 1 ≤ n := by
    simpa [shiftedOtherColumnSpan] using
      (finrank_le_of_span_eq_top (R := ℂ)
        (M := ComplexColumn (n + 1)) htop)
  omega

theorem shiftedScaledFiberMatrix_columnDistance {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ρ : ℝ)
    (j : Fin (n + 1)) (z : ComplexColumn (n + 1))
    (rest : Fin n → ComplexColumn (n + 1)) :
    columnDistance (shiftedScaledFiberMatrix M ρ j z rest) j =
      ‖(shiftedOtherColumnSpan M ρ j rest)ᗮ.starProjection
        (column M j + (ρ : ℂ) • z)‖ := by
  simp [columnDistance, shiftedScaledFiberMatrix_columnSpanExcept]

/-- The one-column smoothed small-ball estimate, uniform in the deterministic
matrix and in all frozen Gaussian columns. -/
theorem shiftedScaledFiberMatrix_columnDistance_smallBall {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ρ : ℝ)
    (j : Fin (n + 1)) (rest : Fin n → ComplexColumn (n + 1))
    (r : ℝ) (hρ : 0 < ρ) (hr : 0 ≤ r) :
    stdGaussian (ComplexColumn (n + 1))
        {z | columnDistance (shiftedScaledFiberMatrix M ρ j z rest) j < r} ≤
      gaussianPeak 1 * ENNReal.ofReal (2 * (r / ρ)) := by
  simpa only [shiftedScaledFiberMatrix_columnDistance] using
    stdGaussian_complexSubspace_shift_scale_smallBall
      (shiftedOtherColumnSpan M ρ j rest)
      (shiftedOtherColumnSpan_ne_top M ρ j rest)
      (column M j) ρ r hρ hr

/-- The moving-span bad-column event remains open after adding an arbitrary
deterministic matrix and scaling the Gaussian columns. -/
theorem measurableSet_columnDistance_shiftedScaledGinibreMatrix_lt
    {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (ρ : ℝ)
    (j : Fin m) (r : ℝ) :
    MeasurableSet
      {C : Fin m → ComplexColumn m |
        columnDistance (shiftedScaledGinibreMatrix M ρ C) j < r} := by
  have heq :
      {C : Fin m → ComplexColumn m |
          columnDistance (shiftedScaledGinibreMatrix M ρ C) j < r} =
        ⋃ a : {k : Fin m // k ≠ j} → ℂ,
          {C | ‖(column M j + (ρ : ℂ) • C j) -
            ∑ k, a k • (column M k + (ρ : ℂ) • C k)‖ < r} := by
    ext C
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    simpa only [column_shiftedScaledGinibreMatrix] using
      columnDistance_lt_iff_exists_coeff
        (shiftedScaledGinibreMatrix M ρ C) j r
  rw [heq]
  apply IsOpen.measurableSet
  apply isOpen_iUnion
  intro a
  apply isOpen_lt
  · fun_prop
  · fun_prop

/-- Unconditional one-column smoothed estimate after conditioning on all
other columns. -/
theorem shiftedScaledGinibre_columnDistance_smallBall
    {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ρ : ℝ) (j : Fin (n + 1)) (r : ℝ) (hρ : 0 < ρ) (hr : 0 ≤ r) :
    complexGinibreColumns (n + 1)
        {C | columnDistance (shiftedScaledGinibreMatrix M ρ C) j < r} ≤
      gaussianPeak 1 * ENNReal.ofReal (2 * (r / ρ)) := by
  let E := ComplexColumn (n + 1)
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => E) j
  let S : Set (E × (Fin n → E)) :=
    {p | columnDistance (shiftedScaledFiberMatrix M ρ j p.1 p.2) j < r}
  have hS : MeasurableSet S := by
    have heq : S = e.symm ⁻¹'
        {C : Fin (n + 1) → E |
          columnDistance (shiftedScaledGinibreMatrix M ρ C) j < r} := by
      ext p
      simp [S, e, E, shiftedScaledFiberMatrix, insertColumn]
    rw [heq]
    exact (measurableSet_columnDistance_shiftedScaledGinibreMatrix_lt
      M ρ j r).preimage e.symm.measurable
  have hprod :
      (stdGaussian E).prod (Measure.pi fun _ : Fin n => stdGaussian E) S ≤
        gaussianPeak 1 * ENNReal.ofReal (2 * (r / ρ)) := by
    exact prod_measure_le_of_forall_left_fiber
      (stdGaussian E) (Measure.pi fun _ : Fin n => stdGaussian E)
      S hS (gaussianPeak 1 * ENNReal.ofReal (2 * (r / ρ))) fun rest => by
        simpa [S, E] using
          shiftedScaledFiberMatrix_columnDistance_smallBall
            M ρ j rest r hρ hr
  have hpres := measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => stdGaussian E) j
  have hpre : e ⁻¹' S =
      {C : Fin (n + 1) → E |
        columnDistance (shiftedScaledGinibreMatrix M ρ C) j < r} := by
    ext C
    change columnDistance
        (shiftedScaledFiberMatrix M ρ j (e C).1 (e C).2) j < r ↔
      columnDistance (shiftedScaledGinibreMatrix M ρ C) j < r
    have heC : insertColumn j (e C).1 (e C).2 = C := by
      change e.symm (e C) = C
      exact e.symm_apply_apply C
    simp only [shiftedScaledFiberMatrix, heC]
  calc
    complexGinibreColumns (n + 1)
        {C | columnDistance (shiftedScaledGinibreMatrix M ρ C) j < r} =
        (Measure.pi fun _ : Fin (n + 1) => stdGaussian E) (e ⁻¹' S) := by
      rw [hpre]
      rfl
    _ = ((stdGaussian E).prod
        (Measure.pi fun _ : Fin n => stdGaussian E)) S :=
      hpres.measure_preimage hS.nullMeasurableSet
    _ ≤ gaussianPeak 1 * ENNReal.ofReal (2 * (r / ρ)) := hprod

/-- Smoothed-analysis least-singular-value bound for a square complex
Ginibre matrix.  It is uniform over the deterministic perturbation `M`. -/
theorem shiftedScaledGinibre_leastSingularValue_smallBall
    {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ρ r : ℝ) (hρ : 0 < ρ) (hr : 0 ≤ r) :
    complexGinibreColumns (n + 1)
        {C | leastSingularValue (shiftedScaledGinibreMatrix M ρ C) <
          r / (n + 1 : ℝ)} ≤
      (n + 1 : ENNReal) *
        (gaussianPeak 1 * ENNReal.ofReal (2 * (r / ρ))) := by
  simpa [Nat.succ_eq_add_one] using
    measure_leastSingularValue_lt_le
      (complexGinibreColumns (n + 1)) (Nat.succ_pos n)
      (fun C => shiftedScaledGinibreMatrix M ρ C) r
      (gaussianPeak 1 * ENNReal.ofReal (2 * (r / ρ)))
      (fun j => shiftedScaledGinibre_columnDistance_smallBall
        M ρ j r hρ hr)

/-- A normalized complex Ginibre matrix has entries
`(X + iY) / sqrt 2`; hence in the raw complex-column realization its scale
is `σ / sqrt 2`. -/
def normalizedShiftedGinibreMatrix {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ)
    (C : Fin n → ComplexColumn n) : Matrix (Fin n) (Fin n) ℂ :=
  shiftedScaledGinibreMatrix M (σ / Real.sqrt 2) C

/-- Normalized complex Ginibre matrix built from raw real-standard Gaussian
columns.  Its entries have complex variance one. -/
def normalizedComplexGinibreMatrix {n : ℕ}
    (C : Fin n → ComplexColumn n) : Matrix (Fin n) (Fin n) ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • matrixOfColumns C

theorem normalizedShiftedGinibreMatrix_eq_add {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ)
    (C : Fin n → ComplexColumn n) :
    normalizedShiftedGinibreMatrix M σ C =
      M + (σ : ℂ) • normalizedComplexGinibreMatrix C := by
  rw [normalizedShiftedGinibreMatrix,
    shiftedScaledGinibreMatrix_eq_add_smul]
  unfold normalizedComplexGinibreMatrix
  rw [smul_smul]
  congr 2
  push_cast
  rw [div_eq_mul_inv]

/-- Smoothed least-singular-value bound for `M + σG`, where `G` is normalized
complex Ginibre (entry variance one). -/
theorem normalizedShiftedGinibre_leastSingularValue_smallBall
    {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (σ r : ℝ) (hσ : 0 < σ) (hr : 0 ≤ r) :
    complexGinibreColumns (n + 1)
        {C | leastSingularValue (normalizedShiftedGinibreMatrix M σ C) <
          r / (n + 1 : ℝ)} ≤
      (n + 1 : ENNReal) *
        (gaussianPeak 1 *
          ENNReal.ofReal (2 * (r / (σ / Real.sqrt 2)))) := by
  exact shiftedScaledGinibre_leastSingularValue_smallBall
    M (σ / Real.sqrt 2) r (div_pos hσ (Real.sqrt_pos.2 (by norm_num))) hr

/-- The same uniform estimate with the least-singular-value threshold written
directly as `ε`. -/
theorem normalizedShiftedGinibre_leastSingularValue_lt_le
    {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 ≤ ε) :
    complexGinibreColumns (n + 1)
        {C | leastSingularValue (normalizedShiftedGinibreMatrix M σ C) < ε} ≤
      (n + 1 : ENNReal) *
        (gaussianPeak 1 * ENNReal.ofReal
          (2 * (((n + 1 : ℕ) : ℝ) * ε / (σ / Real.sqrt 2)))) := by
  have hd : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hcancel : (((n + 1 : ℕ) : ℝ) * ε) / (n + 1 : ℝ) = ε := by
    rw [Nat.cast_add, Nat.cast_one]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn]
  simpa only [hcancel] using
    (normalizedShiftedGinibre_leastSingularValue_smallBall
      M σ (((n + 1 : ℕ) : ℝ) * ε) hσ (mul_nonneg hd.le hε))

/-- Conditioning on an arbitrary random residual matrix.  Since the
one-column estimate is uniform in the deterministic shift, integrating over
any independent residual law leaves the same bound unchanged. -/
theorem prod_normalizedShiftedGinibre_leastSingularValue_lt_le_of_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (M : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 ≤ ε)
    (hMeas : MeasurableSet
      {p : Ω × (Fin (n + 1) → ComplexColumn (n + 1)) |
        leastSingularValue
          (normalizedShiftedGinibreMatrix (M p.1) σ p.2) < ε}) :
    μ.prod (complexGinibreColumns (n + 1))
        {p | leastSingularValue
          (normalizedShiftedGinibreMatrix (M p.1) σ p.2) < ε} ≤
      (n + 1 : ENNReal) *
        (gaussianPeak 1 * ENNReal.ofReal
          (2 * (((n + 1 : ℕ) : ℝ) * ε / (σ / Real.sqrt 2)))) := by
  letI : SFinite (complexGinibreColumns (n + 1)) := by
    unfold complexGinibreColumns
    infer_instance
  exact prod_measure_le_of_forall_fiber
    μ (complexGinibreColumns (n + 1)) _ hMeas _ (fun ω => by
      simpa only [Set.preimage_setOf_eq] using
        normalizedShiftedGinibre_leastSingularValue_lt_le
          (M ω) σ ε hσ hε)

end GinibreLSV

