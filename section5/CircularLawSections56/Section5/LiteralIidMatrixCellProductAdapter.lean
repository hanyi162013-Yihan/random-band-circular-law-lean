import CircularLawSections56.Section5.LiteralIidCellAdapter
import CircularLawSection4.ContinuousEfronStein

/-!
# Literal IID matrix-cell product telescope

This file upgrades one-cell directional logarithmic estimates to bounds for
the expected logarithm of an actual chronological product of iid random
matrices.  In particular, the terminal potential below is

`log ‖C(omega_{q-1}) ... C(omega_0)‖`,

not a separately defined sum of scalar increments.

The basic receiver retains an explicit `hLowerAlgebra` interface, while the
`_autoDirection` wrapper below discharges it: compactness of the finite-
dimensional unit sphere produces a norm-attaining input for each frozen past,
and normalizing its image gives the adapted unit direction.  No measurable
choice is needed because each direction is used only inside its frozen-past
conditional integral.  The fiber and outer integrability assumptions remain
visible; they are exactly the hypotheses used by Fubini and `integral_mono`.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSections56.Section5

open CircularLawSection4

variable {Omega m : Type*} [MeasurableSpace Omega]
  [Fintype m] [DecidableEq m] [Nonempty m]

/-- The genuine chronological product of `q` iid matrix cells. -/
def iidMatrixCellProduct (C : Omega -> Matrix m m Complex) {q : Nat}
    (omega : Fin q -> Omega) : Matrix m m Complex :=
  chronologicalProduct (List.ofFn fun j : Fin q => C (omega j))

/-- Logarithmic operator-norm potential of the genuine matrix product. -/
def iidMatrixCellLogPotential (C : Omega -> Matrix m m Complex) {q : Nat}
    (omega : Fin q -> Omega) : Real :=
  Real.log ‖iidMatrixCellProduct C omega‖

/-- Logarithmic growth of one cell on a Euclidean unit direction. -/
def matrixCellVectorLog (C : Omega -> Matrix m m Complex) (a : Omega)
    (v : EuclideanSpace Complex m) : Real :=
  Real.log ‖(EuclideanSpace.equiv m Complex).symm ((C a).mulVec fun j => v j)‖

omit [MeasurableSpace Omega] [Nonempty m] in
@[simp] theorem iidMatrixCellProduct_zero
    (C : Omega -> Matrix m m Complex) (omega : Fin 0 -> Omega) :
    iidMatrixCellProduct C omega = 1 := by
  simp [iidMatrixCellProduct]

omit [MeasurableSpace Omega] in
@[simp] theorem iidMatrixCellLogPotential_zero
    (C : Omega -> Matrix m m Complex) (omega : Fin 0 -> Omega) :
    iidMatrixCellLogPotential C omega = 0 := by
  simp [iidMatrixCellLogPotential]

omit [MeasurableSpace Omega] [Nonempty m] in
/-- Appending the last iid cell multiplies it on the left, matching the
chronological convention of Section 4. -/
theorem iidMatrixCellProduct_joinLast {q : Nat}
    (C : Omega -> Matrix m m Complex) (past : Fin q -> Omega) (a : Omega) :
    iidMatrixCellProduct C (joinLast (past, a)) =
      C a * iidMatrixCellProduct C past := by
  simp only [iidMatrixCellProduct, List.ofFn_succ', joinLast_castSucc,
    joinLast_last, List.concat_eq_append, chronologicalProduct_append]
  simp

omit [MeasurableSpace Omega] [Nonempty m] in
/-- The corresponding exact successor identity for the actual log
potential. -/
theorem iidMatrixCellLogPotential_joinLast {q : Nat}
    (C : Omega -> Matrix m m Complex) (past : Fin q -> Omega) (a : Omega) :
    iidMatrixCellLogPotential C (joinLast (past, a)) =
      Real.log ‖C a * iidMatrixCellProduct C past‖ := by
  rw [iidMatrixCellLogPotential, iidMatrixCellProduct_joinLast]

omit [MeasurableSpace Omega] [Nonempty m] in
/-- Pointwise upper increment bound from operator-norm submultiplicativity.
Positivity is explicit because Lean's total real logarithm has `log 0 = 0`,
so ordinary logarithmic addition is only valid away from the zero set. -/
theorem iidMatrixCellLogPotential_joinLast_le {q : Nat}
    (C : Omega -> Matrix m m Complex) (past : Fin q -> Omega) (a : Omega)
    (hCell : 0 < ‖C a‖)
    (hPast : 0 < ‖iidMatrixCellProduct C past‖)
    (hFull : 0 < ‖iidMatrixCellProduct C (joinLast (past, a))‖) :
    iidMatrixCellLogPotential C (joinLast (past, a)) <=
      iidMatrixCellLogPotential C past + Real.log ‖C a‖ := by
  have hNorm : ‖C a * iidMatrixCellProduct C past‖ <=
      ‖C a‖ * ‖iidMatrixCellProduct C past‖ :=
    Matrix.l2_opNorm_mul _ _
  have hLog : Real.log ‖C a * iidMatrixCellProduct C past‖ <=
      Real.log (‖C a‖ * ‖iidMatrixCellProduct C past‖) := by
    apply (Real.log_le_log_iff ?_ (mul_pos hCell hPast)).2 hNorm
    simpa only [iidMatrixCellProduct_joinLast] using hFull
  rw [Real.log_mul hCell.ne' hPast.ne'] at hLog
  simpa only [iidMatrixCellLogPotential, iidMatrixCellProduct_joinLast,
    add_comm] using hLog

omit [Nonempty m] in
/-- One frozen-past cell has the desired two-sided conditional expectation
bound.  The lower estimate applies the uniform deterministic-unit-vector
input to the adapted direction.  The upper estimate is proved from matrix
norm submultiplicativity, rather than assumed as an increment bound. -/
theorem iidMatrixCell_conditionalBounds
    (mu : Measure Omega) [SigmaFinite mu] [IsProbabilityMeasure mu]
    (C : Omega -> Matrix m m Complex) (q : Nat) (base error : Real)
    (direction : (n : Nat) -> (Fin n -> Omega) -> EuclideanSpace Complex m)
    (hDirectionUnit : forall n (_hn : n < q) past,
      ‖direction n past‖ = 1)
    (hLowerAlgebra : forall n (_hn : n < q) past a,
      iidMatrixCellLogPotential C past +
          matrixCellVectorLog C a (direction n past) <=
        iidMatrixCellLogPotential C (joinLast (past, a)))
    (hOneLower : forall v : EuclideanSpace Complex m, ‖v‖ = 1 ->
      Integrable (fun a => matrixCellVectorLog C a v) mu /\
        base - error <= ∫ a, matrixCellVectorLog C a v ∂mu)
    (hOneUpper :
      Integrable (fun a => Real.log ‖C a‖) mu /\
        (∫ a, Real.log ‖C a‖ ∂mu) <= base + error)
    (hCellPos : forall a, 0 < ‖C a‖)
    (hProductPos : forall n, n <= q -> forall omega : Fin n -> Omega,
      0 < ‖iidMatrixCellProduct C omega‖)
    (hFiberInt : forall n (_hn : n < q) (past : Fin n -> Omega),
      Integrable (fun a =>
        iidMatrixCellLogPotential C (joinLast (past, a))) mu) :
    forall n (_hn : n < q) (past : Fin n -> Omega),
      iidMatrixCellLogPotential C past + (base - error) <=
          ∫ a, iidMatrixCellLogPotential C (joinLast (past, a)) ∂mu /\
        (∫ a, iidMatrixCellLogPotential C (joinLast (past, a)) ∂mu) <=
          iidMatrixCellLogPotential C past + (base + error) := by
  intro n hn past
  have hDirectional := hOneLower (direction n past) (hDirectionUnit n hn past)
  have hLowerInt : Integrable (fun a =>
      iidMatrixCellLogPotential C past +
        matrixCellVectorLog C a (direction n past)) mu :=
    (integrable_const _).add hDirectional.1
  have hLowerIntegral :
      (∫ a, iidMatrixCellLogPotential C past +
          matrixCellVectorLog C a (direction n past) ∂mu) <=
        ∫ a, iidMatrixCellLogPotential C (joinLast (past, a)) ∂mu :=
    integral_mono hLowerInt (hFiberInt n hn past)
      (fun a => hLowerAlgebra n hn past a)
  have hLower : iidMatrixCellLogPotential C past + (base - error) <=
      ∫ a, iidMatrixCellLogPotential C (joinLast (past, a)) ∂mu := by
    rw [integral_add (integrable_const _) hDirectional.1] at hLowerIntegral
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hLowerIntegral
    linarith [hDirectional.2]

  have hUpperInt : Integrable (fun a =>
      iidMatrixCellLogPotential C past + Real.log ‖C a‖) mu :=
    (integrable_const _).add hOneUpper.1
  have hUpperIntegral :
      (∫ a, iidMatrixCellLogPotential C (joinLast (past, a)) ∂mu) <=
        ∫ a, iidMatrixCellLogPotential C past + Real.log ‖C a‖ ∂mu := by
    apply integral_mono (hFiberInt n hn past) hUpperInt
    intro a
    exact iidMatrixCellLogPotential_joinLast_le C past a (hCellPos a)
      (hProductPos n (Nat.le_of_lt hn) past)
      (hProductPos (n + 1) (Nat.succ_le_iff.2 hn) (joinLast (past, a)))
  have hUpper :
      (∫ a, iidMatrixCellLogPotential C (joinLast (past, a)) ∂mu) <=
        iidMatrixCellLogPotential C past + (base + error) := by
    rw [integral_add (integrable_const _) hOneUpper.1] at hUpperIntegral
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hUpperIntegral
    linarith [hOneUpper.2]
  exact ⟨hLower, hUpper⟩

/-- Minimal conditional-expectation telescope for the genuine iid
chronological matrix product.

`hGlobalInt` supplies integrability of every product potential used by the
successor Fubini identity.  Its pullback through `joinLast` also gives the
outer-section integrability needed to integrate the conditional inequalities;
that consequence is proved below rather than assumed.  This is the smallest
matrix-level receiver for a Section 4 conditional projective estimate: its
potential remains the log norm of the actual product. -/
theorem iidMatrixCellProduct_expectedLog_telescope_of_conditional
    (mu : Measure Omega) [SigmaFinite mu] [IsProbabilityMeasure mu]
    (C : Omega -> Matrix m m Complex) (q : Nat) (base error : Real)
    (hConditional : forall n (_hn : n < q) (past : Fin n -> Omega),
      iidMatrixCellLogPotential C past + (base - error) <=
          ∫ a, iidMatrixCellLogPotential C (joinLast (past, a)) ∂mu /\
        (∫ a, iidMatrixCellLogPotential C (joinLast (past, a)) ∂mu) <=
          iidMatrixCellLogPotential C past + (base + error))
    (hGlobalInt : forall n, n <= q ->
      Integrable (iidMatrixCellLogPotential C) (iidMeasure mu n)) :
    (q : Real) * (base - error) <=
        ∫ omega, iidMatrixCellLogPotential C omega ∂iidMeasure mu q /\
      (∫ omega, iidMatrixCellLogPotential C omega ∂iidMeasure mu q) <=
        (q : Real) * (base + error) := by
  let expected : Nat -> Real := fun n =>
    ∫ omega, iidMatrixCellLogPotential C omega ∂iidMeasure mu n
  have hExpectedZero : expected 0 = 0 := by
    simp only [expected, iidMatrixCellLogPotential_zero, integral_zero]
  have hCell : forall n, n < q ->
      base - error <= expected (n + 1) - expected n /\
        expected (n + 1) - expected n <= base + error := by
    intro n hn
    let _ : IsProbabilityMeasure (iidMeasure mu n) :=
      iidMeasure_isProbability mu n
    let inner : (Fin n -> Omega) -> Real := fun past =>
      ∫ a, iidMatrixCellLogPotential C (joinLast (past, a)) ∂mu
    have hFubini : expected (n + 1) = ∫ past, inner past ∂iidMeasure mu n := by
      simpa only [expected, inner] using
        integral_iidMeasure_succ mu (hGlobalInt (n + 1) (Nat.succ_le_iff.2 hn))
    have hPairInt : Integrable (fun p : (Fin n -> Omega) × Omega =>
        iidMatrixCellLogPotential C (joinLast p)) ((iidMeasure mu n).prod mu) := by
      have hSuccInt := hGlobalInt (n + 1) (Nat.succ_le_iff.2 hn)
      rw [iidMeasure] at hSuccInt
      exact hSuccInt.comp_aemeasurable measurable_joinLast.aemeasurable
    have hInnerOuterInt : Integrable inner (iidMeasure mu n) := by
      simpa only [inner] using hPairInt.integral_prod_left
    have hPastInt := hGlobalInt n (Nat.le_of_lt hn)
    have hLowerFunctionInt : Integrable (fun past : Fin n -> Omega =>
        iidMatrixCellLogPotential C past + (base - error)) (iidMeasure mu n) :=
      hPastInt.add (integrable_const _)
    have hUpperFunctionInt : Integrable (fun past : Fin n -> Omega =>
        iidMatrixCellLogPotential C past + (base + error)) (iidMeasure mu n) :=
      hPastInt.add (integrable_const _)
    have hLowerIntegrated :
        (∫ past, iidMatrixCellLogPotential C past + (base - error)
          ∂iidMeasure mu n) <= ∫ past, inner past ∂iidMeasure mu n := by
      apply integral_mono hLowerFunctionInt hInnerOuterInt
      intro past
      exact (hConditional n hn past).1
    have hUpperIntegrated :
        (∫ past, inner past ∂iidMeasure mu n) <=
          ∫ past, iidMatrixCellLogPotential C past + (base + error)
            ∂iidMeasure mu n := by
      apply integral_mono hInnerOuterInt hUpperFunctionInt
      intro past
      exact (hConditional n hn past).2
    have hLowerStep : expected n + (base - error) <= expected (n + 1) := by
      rw [integral_add hPastInt (integrable_const _)] at hLowerIntegrated
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hLowerIntegrated
      simpa only [expected, hFubini] using hLowerIntegrated
    have hUpperStep : expected (n + 1) <= expected n + (base + error) := by
      rw [integral_add hPastInt (integrable_const _)] at hUpperIntegrated
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hUpperIntegrated
      simpa only [expected, hFubini] using hUpperIntegrated
    constructor <;> linarith
  simpa only [expected] using
    (iidFreshCell_pressure_lift expected base error q hExpectedZero hCell)

/-- Expected-log telescope obtained directly from uniform deterministic-unit-
vector one-cell bounds.  `iidMatrixCell_conditionalBounds` fills the minimal
conditional interface above: Section 4's projective lower closure supplies
`hOneLower`, its operator-norm upper closure supplies `hOneUpper`, and the
adapted normalized maximizing direction supplies `hLowerAlgebra`. -/
theorem iidMatrixCellProduct_expectedLog_telescope
    (mu : Measure Omega) [SigmaFinite mu] [IsProbabilityMeasure mu]
    (C : Omega -> Matrix m m Complex) (q : Nat) (base error : Real)
    (direction : (n : Nat) -> (Fin n -> Omega) -> EuclideanSpace Complex m)
    (hDirectionUnit : forall n (_hn : n < q) past,
      ‖direction n past‖ = 1)
    (hLowerAlgebra : forall n (_hn : n < q) past a,
      iidMatrixCellLogPotential C past +
          matrixCellVectorLog C a (direction n past) <=
        iidMatrixCellLogPotential C (joinLast (past, a)))
    (hOneLower : forall v : EuclideanSpace Complex m, ‖v‖ = 1 ->
      Integrable (fun a => matrixCellVectorLog C a v) mu /\
        base - error <= ∫ a, matrixCellVectorLog C a v ∂mu)
    (hOneUpper :
      Integrable (fun a => Real.log ‖C a‖) mu /\
        (∫ a, Real.log ‖C a‖ ∂mu) <= base + error)
    (hCellPos : forall a, 0 < ‖C a‖)
    (hProductPos : forall n, n <= q -> forall omega : Fin n -> Omega,
      0 < ‖iidMatrixCellProduct C omega‖)
    (hFiberInt : forall n (_hn : n < q) (past : Fin n -> Omega),
      Integrable (fun a =>
        iidMatrixCellLogPotential C (joinLast (past, a))) mu)
    (hGlobalInt : forall n, n <= q ->
      Integrable (iidMatrixCellLogPotential C) (iidMeasure mu n)) :
    (q : Real) * (base - error) <=
        ∫ omega, iidMatrixCellLogPotential C omega ∂iidMeasure mu q /\
      (∫ omega, iidMatrixCellLogPotential C omega ∂iidMeasure mu q) <=
        (q : Real) * (base + error) := by
  apply iidMatrixCellProduct_expectedLog_telescope_of_conditional
    mu C q base error _ hGlobalInt
  exact iidMatrixCell_conditionalBounds mu C q base error direction
    hDirectionUnit hLowerAlgebra hOneLower hOneUpper hCellPos hProductPos hFiberInt

omit [MeasurableSpace Omega] in
/-- A square complex matrix on a finite-dimensional Euclidean space attains
its `L2` operator norm on the unit sphere.  This is the compactness argument
behind the adapted direction used below. -/
theorem exists_unit_mulVec_norm_eq_l2_opNorm
    (P : Matrix m m Complex) :
    ∃ u : EuclideanSpace Complex m,
      ‖u‖ = 1 ∧
        ‖(EuclideanSpace.equiv m Complex).symm (P.mulVec fun j => u j)‖ = ‖P‖ := by
  let T : EuclideanSpace Complex m →L[Complex] EuclideanSpace Complex m :=
    (Matrix.toEuclideanCLM (n := m) (𝕜 := Complex)) P
  let _ : Inhabited m := ⟨Classical.choice (inferInstance : Nonempty m)⟩
  let e : EuclideanSpace Complex m :=
    WithLp.toLp 2 (Pi.single (default : m) (1 : Complex))
  have he : ‖e‖ = 1 := by
    simp [e]
  have hsNonempty : (Metric.sphere (0 : EuclideanSpace Complex m) 1).Nonempty := by
    exact ⟨e, mem_sphere_zero_iff_norm.2 he⟩
  obtain ⟨u, huSphere, huMax⟩ :=
    (isCompact_sphere (0 : EuclideanSpace Complex m) 1).exists_isMaxOn
      hsNonempty T.continuous.norm.continuousOn
  have hu : ‖u‖ = 1 := mem_sphere_zero_iff_norm.1 huSphere
  have hTop : ‖T‖ ≤ ‖T u‖ := by
    apply T.opNorm_le_bound' (norm_nonneg _)
    intro x hx
    let y : EuclideanSpace Complex m := ((‖x‖ : Complex)⁻¹) • x
    have hy : ‖y‖ = 1 := by
      simp only [y, norm_smul, norm_inv, Complex.norm_real, norm_norm]
      exact inv_mul_cancel₀ hx
    have hMax : ‖T y‖ ≤ ‖T u‖ :=
      huMax (mem_sphere_zero_iff_norm.2 hy)
    have hScaled : ‖x‖⁻¹ * ‖T x‖ ≤ ‖T u‖ := by
      simpa only [y, map_smul, norm_smul, norm_inv, Complex.norm_real,
        norm_norm] using hMax
    calc
      ‖T x‖ = ‖x‖ * (‖x‖⁻¹ * ‖T x‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
      _ ≤ ‖x‖ * ‖T u‖ := mul_le_mul_of_nonneg_left hScaled (norm_nonneg x)
      _ = ‖T u‖ * ‖x‖ := mul_comm _ _
  have hBottom : ‖T u‖ ≤ ‖T‖ := by
    simpa only [hu, mul_one] using T.le_opNorm u
  refine ⟨u, hu, ?_⟩
  change ‖T u‖ = ‖P‖
  simpa only [T, Matrix.l2_opNorm_toEuclideanCLM] using
    (le_antisymm hBottom hTop)

omit [MeasurableSpace Omega] in
/-- A fixed norm-attaining input for a finite complex matrix.  No measurable
choice is involved: this will only be evaluated after the past has been
frozen in a conditional integral. -/
def l2OpNormAttainingUnit (P : Matrix m m Complex) :
    EuclideanSpace Complex m :=
  Classical.choose (exists_unit_mulVec_norm_eq_l2_opNorm P)

omit [MeasurableSpace Omega] in
@[simp] theorem norm_l2OpNormAttainingUnit (P : Matrix m m Complex) :
    ‖l2OpNormAttainingUnit P‖ = 1 :=
  (Classical.choose_spec (exists_unit_mulVec_norm_eq_l2_opNorm P)).1

omit [MeasurableSpace Omega] in
theorem norm_mulVec_l2OpNormAttainingUnit (P : Matrix m m Complex) :
    ‖(EuclideanSpace.equiv m Complex).symm
        (P.mulVec fun j => l2OpNormAttainingUnit P j)‖ = ‖P‖ :=
  (Classical.choose_spec (exists_unit_mulVec_norm_eq_l2_opNorm P)).2

omit [MeasurableSpace Omega] in
/-- The adapted direction determined by a frozen past product: apply that
product to a norm-attaining input and divide by the product norm. -/
def iidMatrixCellAdaptedDirection (C : Omega -> Matrix m m Complex)
    (n : Nat) (past : Fin n -> Omega) : EuclideanSpace Complex m :=
  let P := iidMatrixCellProduct C past
  ((‖P‖ : Complex)⁻¹) •
    (Matrix.toEuclideanCLM (n := m) (𝕜 := Complex)) P
      (l2OpNormAttainingUnit P)

omit [MeasurableSpace Omega] in
/-- The automatically chosen adapted direction is a unit vector whenever
the frozen past product is nonzero. -/
theorem norm_iidMatrixCellAdaptedDirection
    (C : Omega -> Matrix m m Complex) (n : Nat) (past : Fin n -> Omega)
    (hPast : 0 < ‖iidMatrixCellProduct C past‖) :
    ‖iidMatrixCellAdaptedDirection C n past‖ = 1 := by
  have hAttain :
      ‖(Matrix.toEuclideanCLM (n := m) (𝕜 := Complex))
          (iidMatrixCellProduct C past)
            (l2OpNormAttainingUnit (iidMatrixCellProduct C past))‖ =
        ‖iidMatrixCellProduct C past‖ := by
    change ‖(EuclideanSpace.equiv m Complex).symm
        ((iidMatrixCellProduct C past).mulVec fun j =>
          l2OpNormAttainingUnit (iidMatrixCellProduct C past) j)‖ =
      ‖iidMatrixCellProduct C past‖
    exact norm_mulVec_l2OpNormAttainingUnit (iidMatrixCellProduct C past)
  simp only [iidMatrixCellAdaptedDirection, norm_smul, norm_inv,
    Complex.norm_real, norm_norm]
  rw [hAttain]
  exact inv_mul_cancel₀ hPast.ne'

omit [MeasurableSpace Omega] in
/-- The norm-attaining adapted direction supplies the formerly explicit
lower-algebra certificate.  Positivity of the cell action is genuinely
needed because Lean's totalized logarithm has `log 0 = 0`. -/
theorem iidMatrixCellAdaptedDirection_lowerAlgebra
    (C : Omega -> Matrix m m Complex) (n : Nat) (past : Fin n -> Omega)
    (a : Omega)
    (hPast : 0 < ‖iidMatrixCellProduct C past‖)
    (hAction : 0 < ‖(EuclideanSpace.equiv m Complex).symm
      ((C a).mulVec fun j => iidMatrixCellAdaptedDirection C n past j)‖)
    (hFull : 0 < ‖iidMatrixCellProduct C (joinLast (past, a))‖) :
    iidMatrixCellLogPotential C past +
        matrixCellVectorLog C a (iidMatrixCellAdaptedDirection C n past) <=
      iidMatrixCellLogPotential C (joinLast (past, a)) := by
  let P := iidMatrixCellProduct C past
  let u := l2OpNormAttainingUnit P
  let T := Matrix.toEuclideanCLM (n := m) (𝕜 := Complex)
  have hu : ‖u‖ = 1 := norm_l2OpNormAttainingUnit P
  have hCompose : T (C a) (T P u) = T (C a * P) u := by
    simpa only [mul_apply_eq_comp] using
      congrArg (fun f => f u) (map_mul T (C a) P).symm
  have hActionEq :
      ‖T (C a) (iidMatrixCellAdaptedDirection C n past)‖ =
        ‖P‖⁻¹ * ‖T (C a * P) u‖ := by
    simp only [iidMatrixCellAdaptedDirection, P, u, T, map_smul, norm_smul,
      norm_inv, Complex.norm_real, norm_norm, hCompose]
  have hProductActionEq :
      ‖P‖ * ‖T (C a) (iidMatrixCellAdaptedDirection C n past)‖ =
        ‖T (C a * P) u‖ := by
    rw [hActionEq, ← mul_assoc, mul_inv_cancel₀ hPast.ne', one_mul]
  have hGrowth :
      ‖P‖ * ‖T (C a) (iidMatrixCellAdaptedDirection C n past)‖ <=
        ‖C a * P‖ := by
    rw [hProductActionEq]
    calc
      ‖T (C a * P) u‖ <= ‖T (C a * P)‖ * ‖u‖ :=
        (T (C a * P)).le_opNorm u
      _ = ‖C a * P‖ := by
        rw [hu, mul_one, Matrix.l2_opNorm_toEuclideanCLM]
  simp only [iidMatrixCellLogPotential, matrixCellVectorLog,
    iidMatrixCellProduct_joinLast]
  change Real.log ‖P‖ +
      Real.log ‖T (C a) (iidMatrixCellAdaptedDirection C n past)‖ <=
    Real.log ‖C a * P‖
  have hPastP : 0 < ‖P‖ := hPast
  have hActionT :
      0 < ‖T (C a) (iidMatrixCellAdaptedDirection C n past)‖ := by
    change 0 < ‖(EuclideanSpace.equiv m Complex).symm
      ((C a).mulVec fun j => iidMatrixCellAdaptedDirection C n past j)‖
    exact hAction
  have hFullCP : 0 < ‖C a * P‖ := by
    simpa only [P, iidMatrixCellProduct_joinLast] using hFull
  rw [← Real.log_mul hPastP.ne' hActionT.ne']
  exact (Real.log_le_log_iff (mul_pos hPastP hActionT) hFullCP).2 hGrowth

/-- Genuine iid matrix-product telescope with the adapted direction and its
lower-algebra inequality constructed automatically from finite-dimensional
norm attainment.  The additional action-positivity hypothesis excludes the
real obstruction created by the totalized value `Real.log 0 = 0`. -/
theorem iidMatrixCellProduct_expectedLog_telescope_autoDirection
    (mu : Measure Omega) [SigmaFinite mu] [IsProbabilityMeasure mu]
    (C : Omega -> Matrix m m Complex) (q : Nat) (base error : Real)
    (hOneLower : forall v : EuclideanSpace Complex m, ‖v‖ = 1 ->
      Integrable (fun a => matrixCellVectorLog C a v) mu /\
        base - error <= ∫ a, matrixCellVectorLog C a v ∂mu)
    (hOneUpper :
      Integrable (fun a => Real.log ‖C a‖) mu /\
        (∫ a, Real.log ‖C a‖ ∂mu) <= base + error)
    (hCellPos : forall a, 0 < ‖C a‖)
    (hProductPos : forall n, n <= q -> forall omega : Fin n -> Omega,
      0 < ‖iidMatrixCellProduct C omega‖)
    (hActionPos : forall a (v : EuclideanSpace Complex m), ‖v‖ = 1 ->
      0 < ‖(EuclideanSpace.equiv m Complex).symm
        ((C a).mulVec fun j => v j)‖)
    (hFiberInt : forall n (_hn : n < q) (past : Fin n -> Omega),
      Integrable (fun a =>
        iidMatrixCellLogPotential C (joinLast (past, a))) mu)
    (hGlobalInt : forall n, n <= q ->
      Integrable (iidMatrixCellLogPotential C) (iidMeasure mu n)) :
    (q : Real) * (base - error) <=
        ∫ omega, iidMatrixCellLogPotential C omega ∂iidMeasure mu q /\
      (∫ omega, iidMatrixCellLogPotential C omega ∂iidMeasure mu q) <=
        (q : Real) * (base + error) := by
  apply iidMatrixCellProduct_expectedLog_telescope mu C q base error
    (iidMatrixCellAdaptedDirection C)
  · intro n hn past
    exact norm_iidMatrixCellAdaptedDirection C n past
      (hProductPos n (Nat.le_of_lt hn) past)
  · intro n hn past a
    have hUnit := norm_iidMatrixCellAdaptedDirection C n past
      (hProductPos n (Nat.le_of_lt hn) past)
    exact iidMatrixCellAdaptedDirection_lowerAlgebra C n past a
      (hProductPos n (Nat.le_of_lt hn) past)
      (hActionPos a (iidMatrixCellAdaptedDirection C n past) hUnit)
      (hProductPos (n + 1) (Nat.succ_le_iff.2 hn) (joinLast (past, a)))
  · exact hOneLower
  · exact hOneUpper
  · exact hCellPos
  · exact hProductPos
  · exact hFiberInt
  · exact hGlobalInt

end CircularLawSections56.Section5
