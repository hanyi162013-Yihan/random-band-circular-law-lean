import BernoulliSection10.AffineLog
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Finite row-multiaffine coefficient tensors

This file formalizes Corollary 10.3.  A list `ps` records the (possibly
different) number of atoms in each row group.  Its coefficient tensor is a
recursive finite `L²` direct sum: at a group of size `p`, coordinate `0` is
the constant coefficient and coordinate `s.succ` is the coefficient of the
`s`th atom.  Thus its norm is literally the Euclidean coefficient norm used
in the paper.
-/

open scoped ENNReal NNReal Topology BigOperators
open Set MeasureTheory

noncomputable section

namespace BernoulliSection10

universe u

/-- A dependent finite tuple of real row groups. -/
def MultiAffineRows : List ℕ → Type
  | [] => PUnit
  | p :: ps => (Fin p → ℝ) × MultiAffineRows ps

@[instance_reducible] instance multiAffineRowsTopologicalSpace :
    (ps : List ℕ) → TopologicalSpace (MultiAffineRows ps)
  | [] => inferInstanceAs (TopologicalSpace PUnit)
  | p :: ps =>
      letI : TopologicalSpace (MultiAffineRows ps) :=
        multiAffineRowsTopologicalSpace ps
      inferInstanceAs
        (TopologicalSpace ((Fin p → ℝ) × MultiAffineRows ps))

/-- The recursive Euclidean coefficient tensor.  In each group, coordinate
`0` is the constant term and `Fin.succ s` is the coefficient of atom `s`. -/
def MultiAffineTensor (E : Type u) : List ℕ → Type u
  | [] => E
  | p :: ps => PiLp 2 (fun _ : Fin (p + 1) => MultiAffineTensor E ps)

section TensorInstances

variable {E : Type*}

instance multiAffineTensorNormedAddCommGroup [NormedAddCommGroup E]
    (ps : List ℕ) : NormedAddCommGroup (MultiAffineTensor E ps) := by
  induction ps with
  | nil => exact inferInstanceAs (NormedAddCommGroup E)
  | cons p ps ih =>
      letI : NormedAddCommGroup (MultiAffineTensor E ps) := ih
      exact inferInstanceAs
        (NormedAddCommGroup
          (PiLp 2 (fun _ : Fin (p + 1) => MultiAffineTensor E ps)))

instance multiAffineTensorNormedSpace [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ps : List ℕ) : NormedSpace ℝ (MultiAffineTensor E ps) := by
  induction ps with
  | nil => exact inferInstanceAs (NormedSpace ℝ E)
  | cons p ps ih =>
      letI : NormedSpace ℝ (MultiAffineTensor E ps) := ih
      exact inferInstanceAs
        (NormedSpace ℝ
          (PiLp 2 (fun _ : Fin (p + 1) => MultiAffineTensor E ps)))

end TensorInstances

@[instance_reducible] instance multiAffineRowsMeasurableSpace :
    (ps : List ℕ) → MeasurableSpace (MultiAffineRows ps)
  | [] => inferInstanceAs (MeasurableSpace PUnit)
  | p :: ps =>
      letI : MeasurableSpace (MultiAffineRows ps) :=
        multiAffineRowsMeasurableSpace ps
      inferInstanceAs
        (MeasurableSpace ((Fin p → ℝ) × MultiAffineRows ps))

@[simp] theorem multiAffineRowsMeasurableSpace_cons (p : ℕ) (ps : List ℕ) :
    multiAffineRowsMeasurableSpace (p :: ps) =
      @Prod.instMeasurableSpace (Fin p → ℝ) (MultiAffineRows ps)
        MeasurableSpace.pi (multiAffineRowsMeasurableSpace ps) := rfl

instance multiAffineRowsBorelSpace :
    (ps : List ℕ) → BorelSpace (MultiAffineRows ps)
  | [] => inferInstanceAs (BorelSpace PUnit)
  | p :: ps =>
      letI : BorelSpace (MultiAffineRows ps) :=
        multiAffineRowsBorelSpace ps
      inferInstanceAs
        (BorelSpace ((Fin p → ℝ) × MultiAffineRows ps))

/-- A component in the first tensor direction.  Naming this coercion keeps
the recursive type family transparent to elaboration. -/
def multiAffineTensorHead {E : Type u} {p : ℕ} {ps : List ℕ}
    (c : MultiAffineTensor E (p :: ps)) (a : Fin (p + 1)) :
    MultiAffineTensor E ps :=
  (show PiLp 2 (fun _ : Fin (p + 1) => MultiAffineTensor E ps) from c) a

@[simp] theorem multiAffineTensorHead_zero {E : Type u}
    [NormedAddCommGroup E] {p : ℕ} {ps : List ℕ} (a : Fin (p + 1)) :
    multiAffineTensorHead
      (0 : MultiAffineTensor E (p :: ps)) a = 0 := by
  change
    (0 : PiLp 2 (fun _ : Fin (p + 1) => MultiAffineTensor E ps)) a = 0
  simp

/-- The independent product law of all row groups. -/
def multiAffineRowLaw (μ : Measure ℝ) : (ps : List ℕ) → Measure (MultiAffineRows ps)
  | [] => Measure.dirac PUnit.unit
  | p :: ps => (Measure.pi fun _ : Fin p => μ).prod (multiAffineRowLaw μ ps)

instance multiAffineRowLawIsProbabilityMeasure (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (ps : List ℕ) :
    IsProbabilityMeasure (multiAffineRowLaw μ ps) := by
  induction ps with
  | nil =>
      simp only [multiAffineRowLaw]
      exact MeasureTheory.Measure.dirac.isProbabilityMeasure
  | cons p ps ih =>
      letI : IsProbabilityMeasure (multiAffineRowLaw μ ps) := ih
      letI : ∀ _ : Fin p, IsProbabilityMeasure μ := fun _ ↦ inferInstance
      letI : IsProbabilityMeasure (Measure.pi fun _ : Fin p => μ) :=
        MeasureTheory.Measure.pi.instIsProbabilityMeasure (fun _ : Fin p => μ)
      simp only [multiAffineRowLaw]
      exact MeasureTheory.Measure.prod.instIsProbabilityMeasure _ _

/-- Evaluate a coefficient tensor group by group. -/
def multiAffineEval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    {ps : List ℕ} → MultiAffineTensor E ps → MultiAffineRows ps → E
  | [], c, _ => c
  | p :: ps, c, x =>
      multiAffineEval
        (affineValue (multiAffineTensorHead c 0)
          (fun s : Fin p ↦ multiAffineTensorHead c s.succ) x.1) x.2

@[simp] theorem multiAffineEval_nil {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : MultiAffineTensor E []) (x : MultiAffineRows []) :
    multiAffineEval c x = c := rfl

@[simp] theorem multiAffineEval_cons {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℕ} {ps : List ℕ} (c : MultiAffineTensor E (p :: ps))
    (x : MultiAffineRows (p :: ps)) :
    multiAffineEval c x =
      multiAffineEval
        (affineValue (multiAffineTensorHead c 0)
          (fun s : Fin p ↦ multiAffineTensorHead c s.succ) x.1) x.2 := rfl

/-- Joint continuity in the coefficient tensor and all row variables. -/
theorem continuous_multiAffineEval_uncurry {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ps : List ℕ) :
    Continuous fun z : MultiAffineTensor E ps × MultiAffineRows ps ↦
      multiAffineEval z.1 z.2 := by
  induction ps with
  | nil =>
      change Continuous (fun z : E × PUnit => z.1)
      exact continuous_fst
  | cons p ps ih =>
      have hhead (a : Fin (p + 1)) :
          Continuous fun c : MultiAffineTensor E (p :: ps) ↦
            multiAffineTensorHead c a := by
        change Continuous fun c :
          PiLp 2 (fun _ : Fin (p + 1) => MultiAffineTensor E ps) ↦ c a
        exact PiLp.continuous_apply 2
          (fun _ : Fin (p + 1) => MultiAffineTensor E ps) a
      have hcoeff :
          Continuous fun z :
              MultiAffineTensor E (p :: ps) × MultiAffineRows (p :: ps) ↦
            affineValue (multiAffineTensorHead z.1 0)
              (fun s : Fin p ↦ multiAffineTensorHead z.1 s.succ) z.2.1 := by
        change Continuous fun z :
            MultiAffineTensor E (p :: ps) × MultiAffineRows (p :: ps) ↦
          multiAffineTensorHead z.1 0 +
            ∑ s : Fin p, z.2.1 s • multiAffineTensorHead z.1 s.succ
        fun_prop
      exact ih.comp (hcoeff.prodMk (continuous_snd.comp continuous_snd))

theorem continuous_multiAffineEval {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ps : List ℕ} (c : MultiAffineTensor E ps) :
    Continuous (multiAffineEval c) := by
  exact (continuous_multiAffineEval_uncurry (E := E) ps).comp
    (continuous_const.prodMk continuous_id)

theorem measurable_norm_multiAffineEval {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ps : List ℕ} (c : MultiAffineTensor E ps) :
    Measurable fun x ↦ ‖multiAffineEval c x‖ :=
  (continuous_multiAffineEval c).norm.measurable

/-! ## Canonical tensor of a separately affine function -/

/-- Recursive separate affinity.  The first clause varies the whole current
row group along a real affine line while fixing all remaining rows; the
second clause repeats the same requirement in the tail. -/
def IsMultiAffine {E : Type*} [AddCommGroup E] [Module ℝ E] :
    {ps : List ℕ} → (MultiAffineRows ps → E) → Prop
  | [], _ => True
  | p :: ps, F =>
      (∀ (tail : MultiAffineRows ps) (x y : Fin p → ℝ) (t : ℝ),
        F ((1 - t) • x + t • y, tail) =
          (1 - t) • F (x, tail) + t • F (y, tail)) ∧
      (∀ x : Fin p → ℝ, IsMultiAffine (fun tail ↦ F (x, tail)))

/-- Affine-line preservation gives the canonical coordinate expansion. -/
theorem map_eq_affineValue_of_line
    {p : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : (Fin p → ℝ) → E)
    (hF : ∀ (x y : Fin p → ℝ) (t : ℝ),
      F ((1 - t) • x + t • y) = (1 - t) • F x + t • F y) :
    F = affineValue (F 0)
      (fun i ↦ F (Pi.single i 1) - F 0) := by
  let D : (Fin p → ℝ) → E := fun x ↦ F x - F 0
  have hD_zero : D 0 = 0 := by simp [D]
  have hD_smul (t : ℝ) (x : Fin p → ℝ) : D (t • x) = t • D x := by
    have h := hF 0 x t
    simp only [smul_zero, zero_add] at h
    dsimp [D]
    rw [h]
    module
  have hD_affine (x y : Fin p → ℝ) (t : ℝ) :
      D ((1 - t) • x + t • y) = (1 - t) • D x + t • D y := by
    dsimp [D]
    rw [hF]
    module
  have hD_add (x y : Fin p → ℝ) : D (x + y) = D x + D y := by
    have harg : ((1 - (1 / 2 : ℝ)) • ((2 : ℝ) • x) +
        (1 / 2 : ℝ) • ((2 : ℝ) • y)) = x + y := by
      module
    rw [← harg, hD_affine, hD_smul, hD_smul]
    norm_num [smul_smul]
  let d : (Fin p → ℝ) →ₗ[ℝ] E := {
    toFun := D
    map_add' := hD_add
    map_smul' := hD_smul
  }
  funext x
  have hx_basis : x = ∑ i, x i • (Pi.single i 1 : Fin p → ℝ) := by
    ext i
    classical
    simp [Pi.single_apply]
  calc
    F x = F 0 + D x := by simp [D]
    _ = F 0 + d x := rfl
    _ = F 0 + d (∑ i, x i • (Pi.single i 1 : Fin p → ℝ)) := by rw [← hx_basis]
    _ = F 0 + ∑ i, x i • (F (Pi.single i 1) - F 0) := by
      simp [d, D, map_sum]
    _ = affineValue (F 0) (fun i ↦ F (Pi.single i 1) - F 0) x := rfl

/-- The canonical recursive coefficient tensor, constructed solely from
values at zero and the coordinate vectors. -/
def multiAffineTensorOfFunction {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    {ps : List ℕ} → (MultiAffineRows ps → E) → MultiAffineTensor E ps
  | [], F => F PUnit.unit
  | p :: ps, F =>
      (show PiLp 2 (fun _ : Fin (p + 1) => MultiAffineTensor E ps) from
        WithLp.toLp 2 fun a ↦ Fin.cases
          (multiAffineTensorOfFunction (fun tail ↦ F (0, tail)))
          (fun s ↦ multiAffineTensorOfFunction
            (fun tail ↦ F (Pi.single s 1, tail) - F (0, tail))) a)

@[simp] theorem multiAffineTensorHead_tensorOfFunction_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℕ} {ps : List ℕ} (F : MultiAffineRows (p :: ps) → E) :
    multiAffineTensorHead (multiAffineTensorOfFunction F) 0 =
      multiAffineTensorOfFunction (fun tail ↦ F (0, tail)) := by
  simp [multiAffineTensorHead, multiAffineTensorOfFunction, WithLp.ofLp_toLp]

@[simp] theorem multiAffineTensorHead_tensorOfFunction_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℕ} {ps : List ℕ} (F : MultiAffineRows (p :: ps) → E)
    (s : Fin p) :
    multiAffineTensorHead (multiAffineTensorOfFunction F) s.succ =
      multiAffineTensorOfFunction
        (fun tail ↦ F (Pi.single s 1, tail) - F (0, tail)) := by
  simp [multiAffineTensorHead, multiAffineTensorOfFunction, WithLp.ofLp_toLp]

@[simp] theorem multiAffineTensorHead_add
    {E : Type*} [NormedAddCommGroup E]
    {p : ℕ} {ps : List ℕ} (c d : MultiAffineTensor E (p :: ps))
    (a : Fin (p + 1)) :
    multiAffineTensorHead (c + d) a =
      multiAffineTensorHead c a + multiAffineTensorHead d a := by
  change
    ((show PiLp 2 (fun _ : Fin (p + 1) => MultiAffineTensor E ps) from c) +
      (show PiLp 2 (fun _ : Fin (p + 1) => MultiAffineTensor E ps) from d)).ofLp a = _
  exact congrFun (WithLp.ofLp_add 2 c d) a

@[simp] theorem multiAffineTensorHead_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℕ} {ps : List ℕ} (a : ℝ)
    (c : MultiAffineTensor E (p :: ps)) (i : Fin (p + 1)) :
    multiAffineTensorHead (a • c) i = a • multiAffineTensorHead c i := by
  change
    (a • (show PiLp 2 (fun _ : Fin (p + 1) => MultiAffineTensor E ps) from c)).ofLp i = _
  exact congrFun (WithLp.ofLp_smul 2 a c) i

theorem multiAffineTensorOfFunction_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ps : List ℕ) (F G : MultiAffineRows ps → E) :
    multiAffineTensorOfFunction (fun x ↦ F x + G x) =
      multiAffineTensorOfFunction F + multiAffineTensorOfFunction G := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      change
        (show PiLp 2 (fun _ : Fin (p + 1) => MultiAffineTensor E ps) from
          multiAffineTensorOfFunction (fun x ↦ F x + G x)) =
        (show PiLp 2 (fun _ : Fin (p + 1) => MultiAffineTensor E ps) from
          multiAffineTensorOfFunction F + multiAffineTensorOfFunction G)
      apply PiLp.ext
      intro a
      refine Fin.cases ?_ (fun s ↦ ?_) a
      · change
          multiAffineTensorHead
              (multiAffineTensorOfFunction (fun x ↦ F x + G x)) 0 =
            multiAffineTensorHead
              (multiAffineTensorOfFunction F + multiAffineTensorOfFunction G) 0
        simpa using ih (fun tail ↦ F (0, tail)) (fun tail ↦ G (0, tail))
      · change
          multiAffineTensorHead
              (multiAffineTensorOfFunction (fun x ↦ F x + G x)) s.succ =
            multiAffineTensorHead
              (multiAffineTensorOfFunction F + multiAffineTensorOfFunction G) s.succ
        rw [multiAffineTensorHead_tensorOfFunction_succ,
          multiAffineTensorHead_add,
          multiAffineTensorHead_tensorOfFunction_succ,
          multiAffineTensorHead_tensorOfFunction_succ,
          ← ih
            (fun tail ↦ F (Pi.single s 1, tail) - F (0, tail))
            (fun tail ↦ G (Pi.single s 1, tail) - G (0, tail))]
        congr 1
        funext tail
        module

theorem multiAffineTensorOfFunction_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ps : List ℕ) (a : ℝ) (F : MultiAffineRows ps → E) :
    multiAffineTensorOfFunction (fun x ↦ a • F x) =
      a • multiAffineTensorOfFunction F := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      change
        (show PiLp 2 (fun _ : Fin (p + 1) => MultiAffineTensor E ps) from
          multiAffineTensorOfFunction (fun x ↦ a • F x)) =
        (show PiLp 2 (fun _ : Fin (p + 1) => MultiAffineTensor E ps) from
          a • multiAffineTensorOfFunction F)
      apply PiLp.ext
      intro i
      refine Fin.cases ?_ (fun s ↦ ?_) i
      · change
          multiAffineTensorHead
              (multiAffineTensorOfFunction (fun x ↦ a • F x)) 0 =
            multiAffineTensorHead
              (a • multiAffineTensorOfFunction F) 0
        simpa using ih (fun tail ↦ F (0, tail))
      · change
          multiAffineTensorHead
              (multiAffineTensorOfFunction (fun x ↦ a • F x)) s.succ =
            multiAffineTensorHead
              (a • multiAffineTensorOfFunction F) s.succ
        rw [multiAffineTensorHead_tensorOfFunction_succ,
          multiAffineTensorHead_smul,
          multiAffineTensorHead_tensorOfFunction_succ,
          ← ih (fun tail ↦
            F (Pi.single s 1, tail) - F (0, tail))]
        congr 1
        funext tail
        module

theorem multiAffineTensorOfFunction_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type*} (ps : List ℕ) (s : Finset I)
    (F : I → MultiAffineRows ps → E) :
    multiAffineTensorOfFunction (fun x ↦ ∑ i ∈ s, F i x) =
      ∑ i ∈ s, multiAffineTensorOfFunction (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using multiAffineTensorOfFunction_smul ps (0 : ℝ)
        (fun _ : MultiAffineRows ps ↦ (0 : E))
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [multiAffineTensorOfFunction_add, ih]

/-- The canonical construction as a real linear map. -/
def multiAffineTensorOfFunctionLinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ps : List ℕ) : (MultiAffineRows ps → E) →ₗ[ℝ] MultiAffineTensor E ps where
  toFun := multiAffineTensorOfFunction
  map_add' := multiAffineTensorOfFunction_add ps
  map_smul' := multiAffineTensorOfFunction_smul ps

/-- The `L²` direct-sum norm identifies the affine `rho` scale of the
first row exactly with the unevaluated coefficient-tensor norm. -/
theorem affineRho_head_eq_tensor_norm {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℕ} {ps : List ℕ} (c : MultiAffineTensor E (p :: ps)) :
    affineRho (multiAffineTensorHead c 0)
      (fun s : Fin p ↦ multiAffineTensorHead c s.succ) = ‖c‖ := by
  have hsquare :
      affineRho (multiAffineTensorHead c 0)
        (fun s : Fin p ↦ multiAffineTensorHead c s.succ) ^ 2 = ‖c‖ ^ 2 := by
    rw [affineRho_sq]
    change
      ‖(show PiLp 2 (fun _ : Fin (p + 1) => MultiAffineTensor E ps) from c) 0‖ ^ 2 +
          ∑ s : Fin p,
            ‖(show PiLp 2 (fun _ : Fin (p + 1) => MultiAffineTensor E ps) from c)
                s.succ‖ ^ 2 =
        ‖(show PiLp 2 (fun _ : Fin (p + 1) => MultiAffineTensor E ps) from c)‖ ^ 2
    rw [PiLp.norm_sq_eq_of_L2]
    rw [Fin.sum_univ_succ]
  nlinarith [affineRho_nonneg (multiAffineTensorHead c 0)
    (fun s : Fin p ↦ multiAffineTensorHead c s.succ), norm_nonneg c]

/-- Evaluation of just the first row group, leaving a coefficient tensor in
the remaining groups. -/
def multiAffineHeadEval {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℕ} {ps : List ℕ} (c : MultiAffineTensor E (p :: ps))
    (x : Fin p → ℝ) : MultiAffineTensor E ps :=
  affineValue (multiAffineTensorHead c 0)
    (fun s : Fin p ↦ multiAffineTensorHead c s.succ) x

@[simp] theorem multiAffineHeadEval_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℕ} {ps : List ℕ} (x : Fin p → ℝ) :
    multiAffineHeadEval (0 : MultiAffineTensor E (p :: ps)) x = 0 := by
  simp [multiAffineHeadEval, affineValue]

theorem multiAffineEval_cons_eq_headEval {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℕ} {ps : List ℕ} (c : MultiAffineTensor E (p :: ps))
    (x : MultiAffineRows (p :: ps)) :
    multiAffineEval c x = multiAffineEval (multiAffineHeadEval c x.1) x.2 := rfl

@[simp] theorem multiAffineEval_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ps : List ℕ} (x : MultiAffineRows ps) :
    multiAffineEval (0 : MultiAffineTensor E ps) x = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      rw [multiAffineEval_cons_eq_headEval, multiAffineHeadEval_zero]
      exact ih x.2

/-- Evaluating the head of the canonical coefficient tensor gives the
canonical coefficient tensor of the corresponding partial function. -/
theorem multiAffineHeadEval_tensorOfFunction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℕ} {ps : List ℕ} (F : MultiAffineRows (p :: ps) → E)
    (hF : IsMultiAffine F) (x : Fin p → ℝ) :
    multiAffineHeadEval (multiAffineTensorOfFunction F) x =
      multiAffineTensorOfFunction (fun tail ↦ F (x, tail)) := by
  change
    multiAffineTensorOfFunction (fun tail ↦ F (0, tail)) +
        ∑ s : Fin p, x s • multiAffineTensorOfFunction
          (fun tail ↦ F (Pi.single s 1, tail) - F (0, tail)) =
      multiAffineTensorOfFunction (fun tail ↦ F (x, tail))
  simp_rw [← multiAffineTensorOfFunction_smul ps]
  rw [← multiAffineTensorOfFunction_sum ps,
    ← multiAffineTensorOfFunction_add ps]
  congr 1
  funext tail
  symm
  simpa [affineValue] using congrFun
    (map_eq_affineValue_of_line (fun u : Fin p → ℝ ↦ F (u, tail))
      (hF.1 tail)) x

/-- Canonical representation theorem: separate affinity is enough to
construct all coefficients internally.  No representation certificate is
required from callers. -/
theorem IsMultiAffine.eval_tensorOfFunction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ps : List ℕ} {F : MultiAffineRows ps → E} (hF : IsMultiAffine F) :
    multiAffineEval (multiAffineTensorOfFunction F) = F := by
  induction ps with
  | nil =>
      funext x
      cases x
      rfl
  | cons p ps ih =>
      funext x
      rw [multiAffineEval_cons_eq_headEval,
        multiAffineHeadEval_tensorOfFunction F hF x.1]
      exact congrFun (ih (hF.2 x.1)) x.2

/-- A concrete nonzero value of a separately affine function makes its
internally constructed coefficient tensor nonzero. -/
theorem IsMultiAffine.tensorOfFunction_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ps : List ℕ} {F : MultiAffineRows ps → E} (hF : IsMultiAffine F)
    (x₀ : MultiAffineRows ps) (hx₀ : F x₀ ≠ 0) :
    multiAffineTensorOfFunction F ≠ 0 := by
  intro hc
  apply hx₀
  rw [← congrFun hF.eval_tensorOfFunction x₀, hc]
  exact multiAffineEval_zero x₀

/-- A nonzero recursive tensor gives a nonzero affine coefficient vector in
its first row direction. -/
theorem head_affine_ne_zero_of_tensor_ne_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℕ} {ps : List ℕ} {c : MultiAffineTensor E (p :: ps)}
    (hc : c ≠ 0) :
    multiAffineTensorHead c 0 ≠ 0 ∨
      (fun s : Fin p ↦ multiAffineTensorHead c s.succ) ≠ 0 := by
  by_contra h
  push Not at h
  apply hc
  change
    (show PiLp 2 (fun _ : Fin (p + 1) => MultiAffineTensor E ps) from c) = 0
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun s ↦ ?_) i
  · simpa [multiAffineTensorHead] using h.1
  · have hs := congrFun h.2 s
    simpa [multiAffineTensorHead] using hs

/-- Vector-valued one-row `L²` estimate.  It is exactly Lemma 10.2 with
the recursive coefficient tensor as its normed target and with the `rho`
certificate eliminated by `affineRho_head_eq_tensor_norm`. -/
theorem multiAffineHead_log_lintegral_sq_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℕ} (hp : 0 < p) {ps : List ℕ}
    (c : MultiAffineTensor E (p :: ps)) :
    ∫⁻ x, ENNReal.ofReal
        (|Real.log ‖multiAffineHeadEval c x‖ - Real.log ‖c‖| ^ 2)
        ∂(Measure.pi fun _ : Fin p => μ) ≤
      ENNReal.ofReal
        (lemma10_2Constant L * Real.log (Real.exp 1 * (p : ℝ)) ^ 2) := by
  by_cases hc : c = 0
  · subst c
    simp only [multiAffineHeadEval_zero, norm_zero, Real.log_zero, sub_self,
      abs_zero]
    norm_num
  · have hG := head_affine_ne_zero_of_tensor_ne_zero hc
    cases p with
    | zero => simp at hp
    | succ n =>
        simpa [multiAffineHeadEval, affineRho_head_eq_tensor_norm,
          Nat.succ_eq_add_one] using
          (lemma_10_2_rho_lintegral_le hμ
            (multiAffineTensorHead c 0)
            (fun s : Fin (n + 1) ↦ multiAffineTensorHead c s.succ) hG)

/-- The centered one-row logarithm belongs to `L²`; this is the reusable
general vector-valued probability interface behind Corollary 10.3. -/
theorem multiAffineHead_log_memLp_two
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℕ} (hp : 0 < p) {ps : List ℕ}
    (c : MultiAffineTensor E (p :: ps)) :
    MemLp
      (fun x : Fin p → ℝ ↦
        Real.log ‖multiAffineHeadEval c x‖ - Real.log ‖c‖)
      2 (Measure.pi fun _ : Fin p => μ) := by
  letI := hμ.toIsProbabilityMeasure
  let f : (Fin p → ℝ) → ℝ := fun x ↦
    Real.log ‖multiAffineHeadEval c x‖ - Real.log ‖c‖
  have hf : Measurable f := by
    dsimp [f, multiAffineHeadEval]
    exact (Real.measurable_log.comp
      (measurable_affineValue
        (multiAffineTensorHead c 0)
        (fun s : Fin p ↦ multiAffineTensorHead c s.succ))).sub_const _
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
  have hlin :
      ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂(Measure.pi fun _ : Fin p => μ) ≤
        ENNReal.ofReal
          (lemma10_2Constant L * Real.log (Real.exp 1 * (p : ℝ)) ^ 2) := by
    simpa [f, sq_abs] using multiAffineHead_log_lintegral_sq_le hμ hp c
  have hfinite :
      ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂(Measure.pi fun _ : Fin p => μ) < ∞ :=
    lt_of_le_of_lt hlin (by simp)
  refine ⟨hf.pow_const 2 |>.aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (ae_of_all _ fun x ↦ sq_nonneg (f x))).2 hfinite

/-- Cauchy--Schwarz on a probability space, in the exact form used to pass
from the one-row `L²` bound to the first-moment telescoping bound. -/
theorem integral_abs_le_sqrt_integral_sq
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {f : α → ℝ} (hf : MemLp f 2 ν) :
    ∫ x, |f x| ∂ν ≤ Real.sqrt (∫ x, f x ^ 2 ∂ν) := by
  have hf' : MemLp f (ENNReal.ofReal 2) ν := by simpa using hf
  have hone : MemLp (fun _ : α ↦ (1 : ℝ)) (ENNReal.ofReal 2) ν :=
    memLp_const (1 : ℝ)
  have hcs := integral_mul_norm_le_Lp_mul_Lq
    (μ := ν) Real.HolderConjugate.two_two hf' hone
  simpa [Real.norm_eq_abs, Real.sqrt_eq_rpow] using hcs

/-- First-moment one-row estimate. -/
theorem multiAffineHead_log_integral_abs_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℕ} (hp : 0 < p) {ps : List ℕ}
    (c : MultiAffineTensor E (p :: ps)) :
    ∫ x,
        |Real.log ‖multiAffineHeadEval c x‖ - Real.log ‖c‖|
        ∂(Measure.pi fun _ : Fin p => μ) ≤
      Real.sqrt (lemma10_2Constant L) *
        Real.log (Real.exp 1 * (p : ℝ)) := by
  letI := hμ.toIsProbabilityMeasure
  let ν : Measure (Fin p → ℝ) := Measure.pi fun _ : Fin p => μ
  let f : (Fin p → ℝ) → ℝ := fun x ↦
    Real.log ‖multiAffineHeadEval c x‖ - Real.log ‖c‖
  have hfmeas : Measurable f := by
    dsimp [f, multiAffineHeadEval]
    exact (Real.measurable_log.comp
      (measurable_affineValue
        (multiAffineTensorHead c 0)
        (fun s : Fin p ↦ multiAffineTensorHead c s.succ))).sub_const _
  have hf : MemLp f 2 ν := by
    simpa [f, ν] using multiAffineHead_log_memLp_two hμ hp c
  have hlin := multiAffineHead_log_lintegral_sq_le hμ hp c
  have hC : 0 ≤ lemma10_2Constant L := by
    unfold lemma10_2Constant affineLogConstant
    positivity
  have hell : 0 ≤ Real.log (Real.exp 1 * (p : ℝ)) := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
    linarith [Real.log_nonneg hp1]
  have hsq :
      ∫ x, f x ^ 2 ∂ν ≤
        lemma10_2Constant L * Real.log (Real.exp 1 * (p : ℝ)) ^ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun x ↦ sq_nonneg (f x))
      (hfmeas.pow_const 2).aestronglyMeasurable]
    apply ENNReal.toReal_le_of_le_ofReal
    · positivity
    · simpa [f, ν, sq_abs] using hlin
  calc
    (∫ x, |f x| ∂ν) ≤ Real.sqrt (∫ x, f x ^ 2 ∂ν) :=
      integral_abs_le_sqrt_integral_sq hf
    _ ≤ Real.sqrt
        (lemma10_2Constant L * Real.log (Real.exp 1 * (p : ℝ)) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (lemma10_2Constant L) *
        Real.log (Real.exp 1 * (p : ℝ)) := by
      rw [Real.sqrt_mul hC, Real.sqrt_sq_eq_abs, abs_of_nonneg hell]

/-- `ℝ≥0∞` form of the one-row first-moment estimate.  This is convenient
for Tonelli iteration because it does not require establishing product-space
integrability in advance. -/
theorem multiAffineHead_log_lintegral_abs_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℕ} (hp : 0 < p) {ps : List ℕ}
    (c : MultiAffineTensor E (p :: ps)) :
    ∫⁻ x, ENNReal.ofReal
        |Real.log ‖multiAffineHeadEval c x‖ - Real.log ‖c‖|
        ∂(Measure.pi fun _ : Fin p => μ) ≤
      ENNReal.ofReal
        (Real.sqrt (lemma10_2Constant L) *
          Real.log (Real.exp 1 * (p : ℝ))) := by
  letI := hμ.toIsProbabilityMeasure
  let ν : Measure (Fin p → ℝ) := Measure.pi fun _ : Fin p => μ
  let f : (Fin p → ℝ) → ℝ := fun x ↦
    Real.log ‖multiAffineHeadEval c x‖ - Real.log ‖c‖
  have hf : MemLp f 2 ν := by
    simpa [f, ν] using multiAffineHead_log_memLp_two hμ hp c
  have hfint : Integrable f ν := hf.integrable one_le_two
  have habsint : Integrable (fun x ↦ |f x|) ν := hfint.abs
  have hnonneg : ∀ᵐ x ∂ν, 0 ≤ |f x| :=
    ae_of_all _ fun x ↦ abs_nonneg (f x)
  rw [← ofReal_integral_eq_lintegral_ofReal habsint hnonneg]
  exact ENNReal.ofReal_le_ofReal (by
    simpa [f, ν] using multiAffineHead_log_integral_abs_le hμ hp c)

/-- The exact sum of the one-row costs appearing in the telescoping proof of
Corollary 10.3. -/
def multiAffineLogCost (L : ℝ) : List ℕ → ℝ≥0∞
  | [] => 0
  | p :: ps => multiAffineLogCost L ps +
      ENNReal.ofReal
        (Real.sqrt (lemma10_2Constant L) *
          Real.log (Real.exp 1 * (p : ℝ)))

theorem multiAffineLogCost_ne_top (L : ℝ) (ps : List ℕ) :
    multiAffineLogCost L ps ≠ ∞ := by
  induction ps with
  | nil => simp [multiAffineLogCost]
  | cons p ps ih =>
      change multiAffineLogCost L ps + ENNReal.ofReal
        (Real.sqrt (lemma10_2Constant L) *
          Real.log (Real.exp 1 * (p : ℝ))) ≠ ∞
      exact ENNReal.add_ne_top.2 ⟨ih, ENNReal.ofReal_ne_top⟩

/-- Recursive first-moment telescoping estimate for a row-multiaffine
coefficient tensor.  Every intermediate tensor is constructed by evaluation;
no nonvanishing or representation certificate is supplied by the caller. -/
theorem multiAffineEval_log_lintegral_abs_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ps : List ℕ} (hpos : ∀ p ∈ ps, 0 < p)
    (c : MultiAffineTensor E ps) :
    ∫⁻ x, ENNReal.ofReal
        |Real.log ‖multiAffineEval c x‖ - Real.log ‖c‖|
        ∂(multiAffineRowLaw μ ps) ≤
      multiAffineLogCost L ps := by
  letI := hμ.toIsProbabilityMeasure
  induction ps with
  | nil =>
      have hf : (fun x : MultiAffineRows [] ↦
          ENNReal.ofReal
            |Real.log ‖multiAffineEval c x‖ - Real.log ‖c‖|) = 0 := by
        funext x
        change ENNReal.ofReal |Real.log ‖c‖ - Real.log ‖c‖| = 0
        rw [sub_self, abs_zero, ENNReal.ofReal_zero]
      rw [hf]
      change (∫⁻ _ : MultiAffineRows [], (0 : ℝ≥0∞)
        ∂multiAffineRowLaw μ []) ≤ 0
      exact le_of_eq lintegral_zero
  | cons p ps ih =>
      have hp : 0 < p := hpos p (by simp)
      have htail : ∀ q ∈ ps, 0 < q := by
        intro q hq
        exact hpos q (by simp [hq])
      let νp : Measure (Fin p → ℝ) := Measure.pi fun _ : Fin p => μ
      let νtail : Measure (MultiAffineRows ps) := multiAffineRowLaw μ ps
      let headDiff : (Fin p → ℝ) → ℝ := fun x ↦
        Real.log ‖multiAffineHeadEval c x‖ - Real.log ‖c‖
      let tailDiff : (Fin p → ℝ) → MultiAffineRows ps → ℝ := fun x y ↦
        Real.log ‖multiAffineEval (multiAffineHeadEval c x) y‖ -
          Real.log ‖multiAffineHeadEval c x‖
      have hheadCont : Continuous (multiAffineHeadEval c) := by
        change Continuous fun x : Fin p → ℝ ↦
          multiAffineTensorHead c 0 +
            ∑ s : Fin p, x s • multiAffineTensorHead c s.succ
        fun_prop
      have hevalCont : Continuous fun z :
          (Fin p → ℝ) × MultiAffineRows ps ↦
          multiAffineEval (multiAffineHeadEval c z.1) z.2 := by
        exact (continuous_multiAffineEval_uncurry ps).comp
          ((hheadCont.comp continuous_fst).prodMk continuous_snd)
      have htotalMeas : Measurable fun z :
          (Fin p → ℝ) × MultiAffineRows ps ↦
          ENNReal.ofReal
            |Real.log ‖multiAffineEval c z‖ - Real.log ‖c‖| := by
        change Measurable fun z : (Fin p → ℝ) × MultiAffineRows ps ↦
          ENNReal.ofReal
            |Real.log
                ‖multiAffineEval (multiAffineHeadEval c z.1) z.2‖ -
              Real.log ‖c‖|
        simpa [Real.norm_eq_abs] using
          ((Real.measurable_log.comp hevalCont.norm.measurable).sub_const _).norm.ennreal_ofReal
      change
        (∫⁻ z : (Fin p → ℝ) × MultiAffineRows ps,
          ENNReal.ofReal
            |Real.log ‖multiAffineEval c z‖ - Real.log ‖c‖|
          ∂νp.prod νtail) ≤ multiAffineLogCost L (p :: ps)
      rw [MeasureTheory.lintegral_prod _ htotalMeas.aemeasurable]
      have hinner (x : Fin p → ℝ) :
          (∫⁻ y, ENNReal.ofReal
              |Real.log ‖multiAffineEval c (x, y)‖ - Real.log ‖c‖|
              ∂νtail) ≤
            multiAffineLogCost L ps + ENNReal.ofReal |headDiff x| := by
        have htailMeas : Measurable fun y : MultiAffineRows ps ↦
            ENNReal.ofReal |tailDiff x y| := by
          simpa [tailDiff, Real.norm_eq_abs] using
            ((Real.measurable_log.comp
              (measurable_norm_multiAffineEval
                (multiAffineHeadEval c x))).sub_const _).norm.ennreal_ofReal
        calc
          (∫⁻ y, ENNReal.ofReal
              |Real.log ‖multiAffineEval c (x, y)‖ - Real.log ‖c‖|
              ∂νtail) ≤
              ∫⁻ y, ENNReal.ofReal |tailDiff x y| +
                ENNReal.ofReal |headDiff x| ∂νtail := by
            apply lintegral_mono
            intro y
            change
              ENNReal.ofReal
                  |Real.log ‖multiAffineEval (multiAffineHeadEval c x) y‖ -
                    Real.log ‖c‖| ≤
                ENNReal.ofReal |tailDiff x y| +
                  ENNReal.ofReal |headDiff x|
            have hdecomp :
                Real.log ‖multiAffineEval (multiAffineHeadEval c x) y‖ -
                    Real.log ‖c‖ = tailDiff x y + headDiff x := by
              simp only [tailDiff, headDiff]
              ring
            rw [hdecomp]
            apply le_trans (ENNReal.ofReal_le_ofReal
              (show
                |tailDiff x y + headDiff x| ≤
                  |tailDiff x y| + |headDiff x| by
                exact abs_add_le _ _))
            rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
          _ = (∫⁻ y, ENNReal.ofReal |tailDiff x y| ∂νtail) +
              ENNReal.ofReal |headDiff x| := by
            rw [lintegral_add_left htailMeas]
            simp [νtail]
          _ ≤ multiAffineLogCost L ps + ENNReal.ofReal |headDiff x| := by
            exact add_le_add_left (by
              simpa [tailDiff, νtail] using
                ih htail (multiAffineHeadEval c x)) _
      calc
        (∫⁻ x, ∫⁻ y,
            ENNReal.ofReal
              |Real.log ‖multiAffineEval c (x, y)‖ - Real.log ‖c‖|
              ∂νtail ∂νp) ≤
            ∫⁻ x, multiAffineLogCost L ps +
              ENNReal.ofReal |headDiff x| ∂νp :=
          lintegral_mono hinner
        _ = multiAffineLogCost L ps +
            ∫⁻ x, ENNReal.ofReal |headDiff x| ∂νp := by
          rw [lintegral_add_left measurable_const]
          simp [νp]
        _ ≤ multiAffineLogCost L ps +
            ENNReal.ofReal
              (Real.sqrt (lemma10_2Constant L) *
                Real.log (Real.exp 1 * (p : ℝ))) := by
          exact add_le_add_right (by
            simpa [headDiff, νp] using
              multiAffineHead_log_lintegral_abs_le hμ hp c) _
        _ = multiAffineLogCost L (p :: ps) := rfl

/-! ## Almost-sure nonvanishing -/

/-- A nonzero coefficient tensor remains nonzero after evaluating one
positive-size row group, almost surely. -/
theorem multiAffineHeadEval_ne_zero_ae_of_ne_zero
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℕ} (hp : 0 < p) {ps : List ℕ}
    {c : MultiAffineTensor E (p :: ps)} (hc : c ≠ 0) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin p => μ), multiAffineHeadEval c x ≠ 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  exact lemma_10_2_affineValue_ne_zero_ae hμ
    (multiAffineTensorHead c 0)
    (fun s : Fin (n + 1) ↦ multiAffineTensorHead c s.succ)
    (head_affine_ne_zero_of_tensor_ne_zero hc)

/-- Iterating the one-row nonvanishing theorem gives almost-sure
nonvanishing of a nonzero recursive tensor. -/
theorem multiAffineEval_ne_zero_ae_of_ne_zero
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ps : List ℕ} (hpos : ∀ p ∈ ps, 0 < p)
    {c : MultiAffineTensor E ps} (hc : c ≠ 0) :
    ∀ᵐ x ∂multiAffineRowLaw μ ps, multiAffineEval c x ≠ 0 := by
  letI : IsProbabilityMeasure μ := hμ.toIsProbabilityMeasure
  induction ps with
  | nil =>
      exact ae_of_all _ fun x ↦ by
        change c ≠ 0
        exact hc
  | cons p ps ih =>
      have hp : 0 < p := hpos p (by simp)
      have htail : ∀ q ∈ ps, 0 < q := by
        intro q hq
        exact hpos q (by simp [hq])
      have hhead :
          ∀ᵐ x ∂(Measure.pi fun _ : Fin p => μ),
            multiAffineHeadEval c x ≠ 0 :=
        multiAffineHeadEval_ne_zero_ae_of_ne_zero hμ hp hc
      have hset : MeasurableSet
          {z : (Fin p → ℝ) × MultiAffineRows ps |
            multiAffineEval c z ≠ 0} := by
        have hnorm : MeasurableSet
            {z : (Fin p → ℝ) × MultiAffineRows ps |
              ‖multiAffineEval c z‖ ≠ 0} := by
          change MeasurableSet
            ((fun z ↦ ‖multiAffineEval c z‖) ⁻¹' ({0} : Set ℝ)ᶜ)
          exact (measurableSet_singleton (0 : ℝ)).compl.preimage
            (continuous_multiAffineEval c).norm.measurable
        simpa only [norm_ne_zero_iff] using hnorm
      have hprod :
          ∀ᵐ z : (Fin p → ℝ) × MultiAffineRows ps
              ∂(Measure.pi fun _ : Fin p => μ).prod
              (multiAffineRowLaw μ ps),
            multiAffineEval c z ≠ 0 := by
        rw [MeasureTheory.Measure.ae_prod_iff_ae_ae hset]
        filter_upwards [hhead] with x hx
        change
          ∀ᵐ y ∂multiAffineRowLaw μ ps,
            multiAffineEval (multiAffineHeadEval c x) y ≠ 0
        exact ih htail hx
      change
        ∀ᵐ z : (Fin p → ℝ) × MultiAffineRows ps
            ∂(Measure.pi fun _ : Fin p => μ).prod
              (multiAffineRowLaw μ ps),
          multiAffineEval c z ≠ 0
      exact hprod

/-- Caller-facing nonvanishing statement for a separately affine function.
The coefficient tensor and its nonzero proof are constructed internally from
one concrete witness. -/
theorem IsMultiAffine.ne_zero_ae
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ps : List ℕ} {F : MultiAffineRows ps → E} (hF : IsMultiAffine F)
    (hpos : ∀ p ∈ ps, 0 < p)
    (x₀ : MultiAffineRows ps) (hx₀ : F x₀ ≠ 0) :
    ∀ᵐ x ∂multiAffineRowLaw μ ps, F x ≠ 0 := by
  have hne := multiAffineEval_ne_zero_ae_of_ne_zero hμ hpos
    (hF.tensorOfFunction_ne_zero x₀ hx₀)
  simpa only [hF.eval_tensorOfFunction] using hne

/-- Caller-facing Corollary 10.3.  The coefficient tensor is constructed from
separate affinity, and the almost-sure nonvanishing proof uses only the
paper's assumption that the polynomial/function is nonzero. -/
theorem corollary_10_3
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ps : List ℕ} {F : MultiAffineRows ps → E} (hF : IsMultiAffine F)
    (hpos : ∀ p ∈ ps, 0 < p) (hFne : F ≠ 0) :
    (∫⁻ x, ENNReal.ofReal
        |Real.log ‖F x‖ - Real.log ‖multiAffineTensorOfFunction F‖|
        ∂(multiAffineRowLaw μ ps) ≤ multiAffineLogCost L ps) ∧
      ∀ᵐ x ∂multiAffineRowLaw μ ps, F x ≠ 0 := by
  have hbound := multiAffineEval_log_lintegral_abs_le hμ hpos
    (multiAffineTensorOfFunction F)
  have hx : ∃ x, F x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hFne
    funext x
    exact h x
  obtain ⟨x₀, hx₀⟩ := hx
  exact ⟨by simpa only [hF.eval_tensorOfFunction] using hbound,
    hF.ne_zero_ae hμ hpos x₀ hx₀⟩

end BernoulliSection10
