import CircularLawSections56.Section5.LiteralIidMatrixCellProductAdapter

/-!
# Almost-everywhere IID matrix-cell telescope

The literal random cells used in Section 4 are invertible almost surely, not at every
point of their ambient atom space.  This file gives the corresponding honest receiver
for the genuine IID matrix product.  A single almost-everywhere `IsUnit` hypothesis is
lifted to every finite IID past.  Conditional lower and upper inequalities are then
proved only for almost every past and integrated with `integral_mono_ae`.

Thus the public `_autoDirection_ae` theorem needs no pointwise nonvanishing, no explicit
adapted direction, no lower-algebra certificate, and no all-pasts fiber-integrability
hypothesis.  Global product-potential integrability supplies the needed fiber
integrability almost everywhere through Fubini.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSections56.Section5

open CircularLawSection4

variable {Omega m : Type*} [MeasurableSpace Omega]
  [Fintype m] [DecidableEq m] [Nonempty m]

omit [MeasurableSpace Omega] [Nonempty m] in
/-- A chronological product is a unit when every matrix in the list is a unit. -/
theorem chronologicalProduct_isUnit_of_forall_mem_matrixCell
    (xs : List (Matrix m m Complex))
    (hxs : ∀ A ∈ xs, IsUnit A) :
    IsUnit (chronologicalProduct xs) := by
  induction xs with
  | nil => simp
  | cons A xs ih =>
      rw [chronologicalProduct_cons]
      exact (ih (fun B hB => hxs B (List.mem_cons_of_mem A hB))).mul
        (hxs A (List.mem_cons_self))

omit [Nonempty m] in
/-- Almost-sure invertibility of one cell lifts to the genuine chronological product
under every finite IID law. -/
theorem ae_iidMatrixCellProduct_isUnit
    (mu : Measure Omega) [SigmaFinite mu] [IsProbabilityMeasure mu]
    (C : Omega -> Matrix m m Complex)
    (hCellUnit : ∀ᵐ a ∂mu, IsUnit (C a)) (n : Nat) :
    ∀ᵐ omega ∂iidMeasure mu n, IsUnit (iidMatrixCellProduct C omega) := by
  rw [iidMeasure_eq_pi]
  have hcoords : ∀ᵐ omega ∂Measure.pi (fun _ : Fin n => mu),
      ∀ i : Fin n, IsUnit (C (omega i)) := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin n => mu) i).quasiMeasurePreserving.ae
      hCellUnit
  filter_upwards [hcoords] with omega homega
  unfold iidMatrixCellProduct
  apply chronologicalProduct_isUnit_of_forall_mem_matrixCell
  intro A hA
  simp only [List.mem_ofFn] at hA
  obtain ⟨i, rfl⟩ := hA
  exact homega i

omit [MeasurableSpace Omega] [Nonempty m] in
/-- An invertible matrix acts nontrivially on every Euclidean unit vector. -/
theorem norm_euclidean_mulVec_pos_of_isUnit
    (A : Matrix m m Complex)
    (v : EuclideanSpace Complex m) (hv : ‖v‖ = 1) (hA : IsUnit A) :
    0 < ‖(EuclideanSpace.equiv m Complex).symm
      (A.mulVec fun j => v j)‖ := by
  apply norm_pos_iff.mpr
  intro hzero
  have hmulZero : A.mulVec (fun j => v j) = 0 := by
    apply (EuclideanSpace.equiv m Complex).symm.injective
    simpa using hzero
  have hvFunZero : (fun j => v j) = 0 := by
    apply Matrix.mulVec_injective_of_isUnit hA
    simpa using hmulZero
  have hvZero : v = 0 := by
    ext j
    exact congrFun hvFunZero j
  subst v
  simp at hv

/-- The expected-log telescope only needs its conditional inequalities almost
everywhere in the frozen past. -/
theorem iidMatrixCellProduct_expectedLog_telescope_of_conditional_ae
    (mu : Measure Omega) [SigmaFinite mu] [IsProbabilityMeasure mu]
    (C : Omega -> Matrix m m Complex) (q : Nat) (base error : Real)
    (hConditional : forall n (_hn : n < q),
      ∀ᵐ past ∂iidMeasure mu n,
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
      exact integral_mono_ae hLowerFunctionInt hInnerOuterInt
        ((hConditional n hn).mono fun past hpast => hpast.1)
    have hUpperIntegrated :
        (∫ past, inner past ∂iidMeasure mu n) <=
          ∫ past, iidMatrixCellLogPotential C past + (base + error)
            ∂iidMeasure mu n := by
      exact integral_mono_ae hInnerOuterInt hUpperFunctionInt
        ((hConditional n hn).mono fun past hpast => hpast.2)
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

/-- Almost-everywhere conditional bounds with the norm-attaining adapted direction.
Fiber integrability is derived almost everywhere from the successor global integral. -/
theorem ae_iidMatrixCell_conditionalBounds_autoDirection
    (mu : Measure Omega) [SigmaFinite mu] [IsProbabilityMeasure mu]
    (C : Omega -> Matrix m m Complex) (q : Nat) (base error : Real)
    (hOneLower : forall v : EuclideanSpace Complex m, ‖v‖ = 1 ->
      Integrable (fun a => matrixCellVectorLog C a v) mu /\
        base - error <= ∫ a, matrixCellVectorLog C a v ∂mu)
    (hOneUpper :
      Integrable (fun a => Real.log ‖C a‖) mu /\
        (∫ a, Real.log ‖C a‖ ∂mu) <= base + error)
    (hCellUnit : ∀ᵐ a ∂mu, IsUnit (C a))
    (hGlobalInt : forall n, n <= q ->
      Integrable (iidMatrixCellLogPotential C) (iidMeasure mu n)) :
    forall n (_hn : n < q),
      ∀ᵐ past ∂iidMeasure mu n,
        iidMatrixCellLogPotential C past + (base - error) <=
            ∫ a, iidMatrixCellLogPotential C (joinLast (past, a)) ∂mu /\
          (∫ a, iidMatrixCellLogPotential C (joinLast (past, a)) ∂mu) <=
            iidMatrixCellLogPotential C past + (base + error) := by
  intro n hn
  let _ : IsProbabilityMeasure (iidMeasure mu n) :=
    iidMeasure_isProbability mu n
  have hPastUnit := ae_iidMatrixCellProduct_isUnit mu C hCellUnit n
  have hPairInt : Integrable (fun p : (Fin n -> Omega) × Omega =>
      iidMatrixCellLogPotential C (joinLast p)) ((iidMeasure mu n).prod mu) := by
    have hSuccInt := hGlobalInt (n + 1) (Nat.succ_le_iff.2 hn)
    rw [iidMeasure] at hSuccInt
    exact hSuccInt.comp_aemeasurable measurable_joinLast.aemeasurable
  have hFiberInt : ∀ᵐ past ∂iidMeasure mu n,
      Integrable (fun a =>
        iidMatrixCellLogPotential C (joinLast (past, a))) mu := by
    simpa using hPairInt.prod_right_ae
  filter_upwards [hPastUnit, hFiberInt] with past hpastUnit hpastInt
  have hpastPos : 0 < ‖iidMatrixCellProduct C past‖ :=
    norm_pos_iff.mpr hpastUnit.ne_zero
  have hunitDirection : ‖iidMatrixCellAdaptedDirection C n past‖ = 1 :=
    norm_iidMatrixCellAdaptedDirection C n past hpastPos
  have hDirectional := hOneLower
    (iidMatrixCellAdaptedDirection C n past) hunitDirection
  have hLowerInt : Integrable (fun a =>
      iidMatrixCellLogPotential C past +
        matrixCellVectorLog C a (iidMatrixCellAdaptedDirection C n past)) mu :=
    (integrable_const _).add hDirectional.1
  have hLowerAE : ∀ᵐ a ∂mu,
      iidMatrixCellLogPotential C past +
          matrixCellVectorLog C a (iidMatrixCellAdaptedDirection C n past) <=
        iidMatrixCellLogPotential C (joinLast (past, a)) := by
    filter_upwards [hCellUnit] with a haUnit
    have hfullUnit : IsUnit
        (iidMatrixCellProduct C (joinLast (past, a))) := by
      rw [iidMatrixCellProduct_joinLast]
      exact haUnit.mul hpastUnit
    exact iidMatrixCellAdaptedDirection_lowerAlgebra C n past a hpastPos
      (norm_euclidean_mulVec_pos_of_isUnit (C a)
        (iidMatrixCellAdaptedDirection C n past) hunitDirection haUnit)
      (norm_pos_iff.mpr hfullUnit.ne_zero)
  have hLowerIntegral :
      (∫ a, iidMatrixCellLogPotential C past +
          matrixCellVectorLog C a (iidMatrixCellAdaptedDirection C n past) ∂mu) <=
        ∫ a, iidMatrixCellLogPotential C (joinLast (past, a)) ∂mu :=
    integral_mono_ae hLowerInt hpastInt hLowerAE
  have hLower : iidMatrixCellLogPotential C past + (base - error) <=
      ∫ a, iidMatrixCellLogPotential C (joinLast (past, a)) ∂mu := by
    rw [integral_add (integrable_const _) hDirectional.1] at hLowerIntegral
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hLowerIntegral
    linarith [hDirectional.2]

  have hUpperInt : Integrable (fun a =>
      iidMatrixCellLogPotential C past + Real.log ‖C a‖) mu :=
    (integrable_const _).add hOneUpper.1
  have hUpperAE : ∀ᵐ a ∂mu,
      iidMatrixCellLogPotential C (joinLast (past, a)) <=
        iidMatrixCellLogPotential C past + Real.log ‖C a‖ := by
    filter_upwards [hCellUnit] with a haUnit
    have hfullUnit : IsUnit
        (iidMatrixCellProduct C (joinLast (past, a))) := by
      rw [iidMatrixCellProduct_joinLast]
      exact haUnit.mul hpastUnit
    exact iidMatrixCellLogPotential_joinLast_le C past a
      (norm_pos_iff.mpr haUnit.ne_zero) hpastPos
      (norm_pos_iff.mpr hfullUnit.ne_zero)
  have hUpperIntegral :
      (∫ a, iidMatrixCellLogPotential C (joinLast (past, a)) ∂mu) <=
        ∫ a, iidMatrixCellLogPotential C past + Real.log ‖C a‖ ∂mu :=
    integral_mono_ae hpastInt hUpperInt hUpperAE
  have hUpper :
      (∫ a, iidMatrixCellLogPotential C (joinLast (past, a)) ∂mu) <=
        iidMatrixCellLogPotential C past + (base + error) := by
    rw [integral_add (integrable_const _) hOneUpper.1] at hUpperIntegral
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hUpperIntegral
    linarith [hOneUpper.2]
  exact ⟨hLower, hUpper⟩

/-- AE-friendly genuine IID matrix-product telescope.  This is the form directly
instantiable from the almost-sure invertibility certificates supplied by Section 4. -/
theorem iidMatrixCellProduct_expectedLog_telescope_autoDirection_ae
    (mu : Measure Omega) [SigmaFinite mu] [IsProbabilityMeasure mu]
    (C : Omega -> Matrix m m Complex) (q : Nat) (base error : Real)
    (hOneLower : forall v : EuclideanSpace Complex m, ‖v‖ = 1 ->
      Integrable (fun a => matrixCellVectorLog C a v) mu /\
        base - error <= ∫ a, matrixCellVectorLog C a v ∂mu)
    (hOneUpper :
      Integrable (fun a => Real.log ‖C a‖) mu /\
        (∫ a, Real.log ‖C a‖ ∂mu) <= base + error)
    (hCellUnit : ∀ᵐ a ∂mu, IsUnit (C a))
    (hGlobalInt : forall n, n <= q ->
      Integrable (iidMatrixCellLogPotential C) (iidMeasure mu n)) :
    (q : Real) * (base - error) <=
        ∫ omega, iidMatrixCellLogPotential C omega ∂iidMeasure mu q /\
      (∫ omega, iidMatrixCellLogPotential C omega ∂iidMeasure mu q) <=
        (q : Real) * (base + error) := by
  apply iidMatrixCellProduct_expectedLog_telescope_of_conditional_ae
    mu C q base error _ hGlobalInt
  exact ae_iidMatrixCell_conditionalBounds_autoDirection
    mu C q base error hOneLower hOneUpper hCellUnit hGlobalInt

end CircularLawSections56.Section5
