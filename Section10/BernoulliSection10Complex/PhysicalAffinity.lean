import BernoulliSection10Complex.MultiAffine
import BernoulliSection10Complex.PhysicalModel

set_option maxHeartbeats 800000

/-!
# Concrete physical-row affinity

This module contains the deterministic reverse-product isolation, the
canonical affine normal form obtained by exposing one complete physical row,
and the continuity and measurability facts shared by the Hodge-integrability
and Efron--Stein layers.
-/

open scoped BigOperators Matrix ENNReal NNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open Matrix Set Set.powersetCard
open BernoulliLinearAlgebra

/-! ## Isolating one factor of the reverse product -/

/-- The list whose product is `reverseMatrixProduct M`. -/
def reverseMatrixList {s : ℕ} {q : Type*} [Fintype q] [DecidableEq q]
    (M : Fin s → Matrix q q ℂ) : List (Matrix q q ℂ) :=
  List.ofFn fun j : Fin s ↦ M j.rev

/-- The factors strictly to the left of site `j` in the reverse product. -/
def reverseMatrixPrefix {s : ℕ} {q : Type*} [Fintype q] [DecidableEq q]
    (M : Fin s → Matrix q q ℂ) (j : Fin s) : Matrix q q ℂ :=
  (reverseMatrixList M).take j.rev.1 |>.prod

/-- The factors strictly to the right of site `j` in the reverse product. -/
def reverseMatrixSuffix {s : ℕ} {q : Type*} [Fintype q] [DecidableEq q]
    (M : Fin s → Matrix q q ℂ) (j : Fin s) : Matrix q q ℂ :=
  (reverseMatrixList M).drop (j.rev.1 + 1) |>.prod

/-- Replacing one factor of a reverse product exposes deterministic left and
right multipliers. -/
theorem reverseMatrixProduct_update {s : ℕ} {q : Type*}
    [Fintype q] [DecidableEq q] (M : Fin s → Matrix q q ℂ)
    (j : Fin s) (A : Matrix q q ℂ) :
    reverseMatrixProduct (Function.update M j A) =
      reverseMatrixPrefix M j * A * reverseMatrixSuffix M j := by
  let l : List (Matrix q q ℂ) := reverseMatrixList M
  have hl : reverseMatrixList (Function.update M j A) = l.set j.rev.1 A := by
    apply List.ext_getElem
    · simp [l, reverseMatrixList]
    · intro i hi₁ hi₂
      simp only [reverseMatrixList, List.length_ofFn] at hi₁
      by_cases h : i = j.rev.1
      · subst i
        rw [List.getElem_set]
        simp [reverseMatrixList]
        let k : Fin s := ⟨s - (j.1 + 1), by omega⟩
        change Function.update M j A k.rev = A
        have hk : k = j.rev := by rfl
        rw [hk, Fin.rev_rev]
        simp
      · have hfin : (⟨i, hi₁⟩ : Fin s) ≠ j.rev := by
          intro heq
          exact h (congrArg Fin.val heq)
        have hrev : (⟨i, hi₁⟩ : Fin s).rev ≠ j := by
          intro heq
          apply hfin
          simpa using congrArg Fin.rev heq
        rw [List.getElem_set]
        rw [if_neg (Ne.symm h)]
        simp [l, reverseMatrixList, hrev]
  change (reverseMatrixList (Function.update M j A)).prod = _
  rw [hl, List.prod_set]
  have hlen : j.rev.1 < l.length := by
    simpa [l, reverseMatrixList] using j.rev.2
  rw [if_pos hlen]
  rfl

/-! ## A finite-dimensional affine-coordinate normal form -/

/-- A map on a complex vector space which preserves every two-point affine
interpolation has the canonical `affineValue` coordinate expansion. -/
theorem affineValue_eq_of_map_line
    {p : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : (Fin p → ℂ) → E)
    (hF : ∀ (x y : Fin p → ℂ) (t : ℂ),
      F ((1 - t) • x + t • y) = (1 - t) • F x + t • F y) :
    F = affineValue (F 0)
      (fun i ↦ F (Pi.single i 1) - F 0) := by
  exact map_eq_affineValue_of_line F hF

/-! ## The conditioned operator is a concrete affine map -/

/-- The atom-to-physical-row map respects complex affine interpolation.  The
deterministic `-z` diagonal shift is part of the affine center. -/
theorem physicalRowGroupOfAtoms_line (W : ℕ) (z : ℂ) (a : Fin W)
    (x y : PhysicalRowAtoms W) (t : ℂ) :
    physicalRowGroupOfAtoms W z a ((1 - t) • x + t • y) =
      PhysicalRowGroup.interpolate (t : ℂ)
        (physicalRowGroupOfAtoms W z a x)
        (physicalRowGroupOfAtoms W z a y) := by
  ext c <;>
    simp only [physicalRowGroupOfAtoms, PhysicalRowGroup.interpolate,
      normalizedPhysicalAtom, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one,
      Complex.ofReal_sub]
  · push_cast
    ring
  · split_ifs <;> push_cast <;> ring
  · push_cast
    ring

/-- The interval product with the factor at site `j` replaced by an arbitrary
physical row `g` at within-site row `a`.  The prefix and suffix do not depend
on `g`. -/
def conditionedIntervalClearedProduct (W s : ℕ) (z : ℂ)
    (x : IntervalRows W s) (r : Fin (2 * W + 1)) (j : Fin s) (a : Fin W)
    (g : PhysicalRowGroup (Fin W)) :
    Matrix (powersetCard (Fin W ⊕ Fin W) r.1)
      (powersetCard (Fin W ⊕ Fin W) r.1) ℂ :=
  let M := fun k ↦ intervalClearedStep W z x r k
  let X := (intervalSiteBlocks z x j).replaceRow a g
  reverseMatrixPrefix M j * clearedStepCompound r.1 X.B X.D X.C *
    reverseMatrixSuffix M j

/-- Resampling an outer row coordinate is exactly evaluation of the
conditioned one-row product. -/
theorem intervalClearedProduct_update (W s : ℕ) (z : ℂ)
    (x : IntervalRows W s) (r : Fin (2 * W + 1)) (j : Fin s) (a : Fin W)
    (y : PhysicalRowAtoms W) :
    intervalClearedProduct W s z
        (Function.update x (intervalRowIndex j a) y) r =
      conditionedIntervalClearedProduct W s z x r j a
        (physicalRowGroupOfAtoms W z a y) := by
  let M := fun k ↦ intervalClearedStep W z x r k
  let A :=
    let X := (intervalSiteBlocks z x j).replaceRow a
      (physicalRowGroupOfAtoms W z a y)
    clearedStepCompound r.1 X.B X.D X.C
  have hsteps :
      (fun k ↦ intervalClearedStep W z
        (Function.update x (intervalRowIndex j a) y) r k) =
        Function.update M j A := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp [M, A, intervalClearedStep, intervalSiteBlocks_update_same]
    · simp [M, A, intervalClearedStep, hkj,
        intervalSiteBlocks_update_other z x j k a hkj]
  rw [intervalClearedProduct, hsteps, reverseMatrixProduct_update]
  rfl

/-- Lemma 10.4, specialized to a conditioned interval product. -/
theorem conditionedIntervalClearedProduct_line (W s : ℕ) (z : ℂ)
    (x : IntervalRows W s) (r : Fin (2 * W + 1)) (j : Fin s) (a : Fin W)
    (g₀ g₁ : PhysicalRowGroup (Fin W)) (t : ℂ) :
    conditionedIntervalClearedProduct W s z x r j a
        (PhysicalRowGroup.interpolate t g₀ g₁) =
      (1 - t) • conditionedIntervalClearedProduct W s z x r j a g₀ +
        t • conditionedIntervalClearedProduct W s z x r j a g₁ := by
  have hr : r.1 ≤ Fintype.card (Fin W ⊕ Fin W) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  let M := fun k ↦ intervalClearedStep W z x r k
  let L := reverseMatrixPrefix M j
  let R := reverseMatrixSuffix M j
  have h := independent_mul_clearedStepCompound_mul_isAffineInPhysicalRow
    r.1 hr a L R
  simpa [conditionedIntervalClearedProduct, M, L, R] using
    h (intervalSiteBlocks z x j) g₀ g₁ t

/-- After conditioning all other physical rows, the full exterior product is
the canonical affine map of the `3W` atoms in the resampled row. -/
theorem conditionedIntervalClearedProduct_atoms_line (W s : ℕ) (z : ℂ)
    (x : IntervalRows W s) (r : Fin (2 * W + 1)) (j : Fin s) (a : Fin W)
    (u v : PhysicalRowAtoms W) (t : ℂ) :
    conditionedIntervalClearedProduct W s z x r j a
        (physicalRowGroupOfAtoms W z a ((1 - t) • u + t • v)) =
      (1 - t) • conditionedIntervalClearedProduct W s z x r j a
          (physicalRowGroupOfAtoms W z a u) +
        t • conditionedIntervalClearedProduct W s z x r j a
          (physicalRowGroupOfAtoms W z a v) := by
  rw [physicalRowGroupOfAtoms_line]
  have h := conditionedIntervalClearedProduct_line W s z x r j a
    (physicalRowGroupOfAtoms W z a u) (physicalRowGroupOfAtoms W z a v) (t : ℂ)
  exact h

/-- The explicit deterministic center of the conditioned affine operator. -/
def conditionedAffineCenter (W s : ℕ) (z : ℂ) (x : IntervalRows W s)
    (r : Fin (2 * W + 1)) (j : Fin s) (a : Fin W) :
    Matrix (powersetCard (Fin W ⊕ Fin W) r.1)
      (powersetCard (Fin W ⊕ Fin W) r.1) ℂ :=
  conditionedIntervalClearedProduct W s z x r j a
    (physicalRowGroupOfAtoms W z a 0)

/-- The `i`th explicit coefficient of the conditioned affine operator. -/
def conditionedAffineCoefficient (W s : ℕ) (z : ℂ)
    (x : IntervalRows W s) (r : Fin (2 * W + 1)) (j : Fin s) (a : Fin W)
    (i : Fin (3 * W)) :
    Matrix (powersetCard (Fin W ⊕ Fin W) r.1)
      (powersetCard (Fin W ⊕ Fin W) r.1) ℂ :=
  conditionedIntervalClearedProduct W s z x r j a
      (physicalRowGroupOfAtoms W z a (Pi.single i 1)) -
    conditionedAffineCenter W s z x r j a

/-- Concrete affine normal form for a row-resampled interval product. -/
theorem intervalClearedProduct_update_eq_affineValue
    (W s : ℕ) (z : ℂ) (x : IntervalRows W s)
    (r : Fin (2 * W + 1)) (j : Fin s) (a : Fin W)
    (y : PhysicalRowAtoms W) :
    intervalClearedProduct W s z
        (Function.update x (intervalRowIndex j a) y) r =
      affineValue (conditionedAffineCenter W s z x r j a)
        (conditionedAffineCoefficient W s z x r j a) y := by
  rw [intervalClearedProduct_update]
  let F := fun u : PhysicalRowAtoms W ↦
    conditionedIntervalClearedProduct W s z x r j a
      (physicalRowGroupOfAtoms W z a u)
  have hnormal := affineValue_eq_of_map_line F
    (conditionedIntervalClearedProduct_atoms_line W s z x r j a)
  have hy := congrFun hnormal y
  change conditionedIntervalClearedProduct W s z x r j a
      (physicalRowGroupOfAtoms W z a y) =
    affineValue (conditionedAffineCenter W s z x r j a)
      (fun i ↦ conditionedIntervalClearedProduct W s z x r j a
          (physicalRowGroupOfAtoms W z a (Pi.single i 1)) -
        conditionedAffineCenter W s z x r j a) y
  simpa [F, conditionedAffineCenter] using hy

/-- The full product is affine in every one of its `sW` complete physical
rows.  This coordinate-free form is the direct input to the recursive
`IsMultiAffine` representation used by the Hodge-integrability layer. -/
theorem intervalClearedProduct_update_line
    (W s : ℕ) (z : ℂ) (x : IntervalRows W s)
    (r : Fin (2 * W + 1)) (i : Fin (s * W))
    (u v : PhysicalRowAtoms W) (t : ℂ) :
    intervalClearedProduct W s z
        (Function.update x i ((1 - t) • u + t • v)) r =
      (1 - t) • intervalClearedProduct W s z
          (Function.update x i u) r +
        t • intervalClearedProduct W s z
          (Function.update x i v) r := by
  let e : Fin s × Fin W ≃ Fin (s * W) := finProdFinEquiv
  let ja : Fin s × Fin W := e.symm i
  let j : Fin s := ja.1
  let a : Fin W := ja.2
  have hi : intervalRowIndex j a = i := by
    simpa [intervalRowIndex, e, ja, j, a] using e.apply_symm_apply i
  rw [← hi]
  simp only [intervalClearedProduct_update]
  exact conditionedIntervalClearedProduct_atoms_line W s z x r j a u v t

/-! ## Concrete measurability -/

/-- The cleared one-step exterior matrix is continuous whenever its three
physical blocks are continuous. -/
theorem continuous_clearedStepCompound_of_continuous
    {X : Type*} [TopologicalSpace X] {W : Type*}
    [Fintype W] [LinearOrder W]
    (k : ℕ) {B D C : X → Matrix W W ℂ}
    (hB : Continuous B) (hD : Continuous D) (hC : Continuous C) :
    Continuous (fun x ↦ clearedStepCompound k (B x) (D x) (C x)) := by
  letI sumLinearOrder : LinearOrder (W ⊕ W) :=
    LinearOrder.lift' (fun x : W ⊕ W ↦ (toLex x : W ⊕ₗ W))
      (fun _ _ h ↦ toLex.injective h)
  have hL : Continuous (fun x ↦ stepL (B x)) := by
    exact hB.matrix_fromBlocks continuous_const continuous_const continuous_const
  have hK : Continuous (fun x ↦ stepK (D x) (C x)) := by
    exact hD.matrix_fromBlocks hC continuous_const continuous_const
  have hInv : Continuous (fun x ↦
      clearedInverseCompound k (stepL (B x))) :=
    continuous_clearedInverseCompound_of_continuous
      (X := X) (ι := W ⊕ W) k hL
  have hComp : Continuous (fun x ↦ compound k (stepK (D x) (C x))) :=
    continuous_compound_of_continuous (X := X) (ι := W ⊕ W) k hK
  exact (hInv.matrix_mul hComp).const_smul ((-1 : ℂ) ^ k)

theorem continuous_normalizedPhysicalAtom (W : ℕ) (b : Fin 3) (c : Fin W) :
    Continuous (fun x : PhysicalRowAtoms W ↦ normalizedPhysicalAtom x b c) := by
  unfold normalizedPhysicalAtom
  fun_prop

theorem continuous_intervalSiteB (W s : ℕ) (z : ℂ) (j : Fin s) :
    Continuous (fun x : IntervalRows W s ↦ (intervalSiteBlocks z x j).B) := by
  apply continuous_matrix
  intro a c
  simp only [intervalSiteBlocks, intervalPhysicalRow, physicalRowGroupOfAtoms]
  exact (continuous_normalizedPhysicalAtom W 0 c).comp
    (continuous_apply (intervalRowIndex j a))

theorem continuous_intervalSiteD (W s : ℕ) (z : ℂ) (j : Fin s) :
    Continuous (fun x : IntervalRows W s ↦ (intervalSiteBlocks z x j).D) := by
  apply continuous_matrix
  intro a c
  simp only [intervalSiteBlocks, intervalPhysicalRow, physicalRowGroupOfAtoms]
  exact ((continuous_normalizedPhysicalAtom W 1 c).comp
    (continuous_apply (intervalRowIndex j a))).sub continuous_const

theorem continuous_intervalSiteC (W s : ℕ) (z : ℂ) (j : Fin s) :
    Continuous (fun x : IntervalRows W s ↦ (intervalSiteBlocks z x j).C) := by
  apply continuous_matrix
  intro a c
  simp only [intervalSiteBlocks, intervalPhysicalRow, physicalRowGroupOfAtoms]
  exact (continuous_normalizedPhysicalAtom W 2 c).comp
    (continuous_apply (intervalRowIndex j a))

theorem continuous_intervalClearedStep (W s : ℕ) (z : ℂ)
    (r : Fin (2 * W + 1)) (j : Fin s) :
    Continuous (fun x : IntervalRows W s ↦ intervalClearedStep W z x r j) := by
  exact continuous_clearedStepCompound_of_continuous r.1
    (continuous_intervalSiteB W s z j)
    (continuous_intervalSiteD W s z j)
    (continuous_intervalSiteC W s z j)

/-- A finite noncommutative reverse product of continuous matrix functions is
continuous. -/
theorem continuous_reverseMatrixProduct
    {X : Type*} [TopologicalSpace X] {s : ℕ} {q : Type*}
    [Fintype q] [DecidableEq q]
    {M : X → Fin s → Matrix q q ℂ}
    (hM : ∀ j, Continuous (fun x ↦ M x j)) :
    Continuous (fun x ↦ reverseMatrixProduct (M x)) := by
  let fs : List (X → Matrix q q ℂ) :=
    List.ofFn fun j : Fin s ↦ fun x ↦ M x j.rev
  have hfs : ∀ f ∈ fs, Continuous f := by
    intro f hf
    simp only [fs, List.mem_ofFn] at hf
    obtain ⟨j, rfl⟩ := hf
    exact hM j.rev
  have aux : ∀ (l : List (X → Matrix q q ℂ)),
      (∀ f ∈ l, Continuous f) →
        Continuous (fun x ↦ (l.map fun f ↦ f x).prod) := by
    intro l hl
    induction l with
    | nil =>
        simpa using
          (continuous_const : Continuous (fun _ : X ↦ (1 : Matrix q q ℂ)))
    | cons f l ih =>
        have hf : Continuous f := hl f (by simp)
        have hl' : ∀ g ∈ l, Continuous g := by
          intro g hg
          exact hl g (by simp [hg])
        simpa using hf.matrix_mul (ih hl')
  have hprod : Continuous (fun x ↦ (fs.map fun f ↦ f x).prod) :=
    aux fs hfs
  change Continuous (fun x ↦
    (List.ofFn fun j : Fin s ↦ M x j.rev).prod)
  simpa [fs, List.map_ofFn, Function.comp_def] using hprod

theorem continuous_intervalClearedProduct (W s : ℕ) (z : ℂ)
    (r : Fin (2 * W + 1)) :
    Continuous (intervalClearedProduct W s z · r) := by
  apply continuous_reverseMatrixProduct
  exact fun j ↦ continuous_intervalClearedStep W s z r j

/-- The logarithmic norm is Borel measurable even on the (null in the paper)
zero locus, where Lean's total `Real.log` takes its conventional value. -/
theorem measurable_intervalDegreeLog (W s : ℕ) (z : ℂ)
    (r : Fin (2 * W + 1)) :
    Measurable (intervalDegreeLog W s z r) := by
  exact Real.measurable_log.comp
    ((continuous_norm.comp (continuous_intervalClearedProduct W s z r)).measurable)


end BernoulliSection10Complex
