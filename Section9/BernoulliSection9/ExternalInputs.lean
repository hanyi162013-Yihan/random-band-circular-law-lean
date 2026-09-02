import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Explicit external probability inputs

This module states the two literature inputs used by the local small-ball
proof. It declares no axioms. Instead, the final theorems receive values
of `CookDeformedSquareInput` and `NguyenBottomSingularInput`; their fields are
the cited estimates, stated for the concrete iid matrix model below.

The matrix singular values are the singular values of the associated complex
linear map on Euclidean space.  They are zero-indexed, as in mathlib.
-/

open scoped Matrix.Norms.L2Operator ProbabilityTheory BigOperators ENNReal NNReal MeasureTheory

noncomputable section

namespace BernoulliSection9

open MeasureTheory ProbabilityTheory

/-- The `j`-th singular value of a complex square matrix, in decreasing order
and with zero-based indexing. -/
def matrixSingularValue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (j : ℕ) : ℝ :=
  A.toEuclideanLin.singularValues j

/-- The bottom singular value of an `n × n` matrix.  The zero-dimensional
convention is `0`. -/
def matrixSMin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  if n = 0 then 0 else matrixSingularValue A (n - 1)

/-- An iid centered, variance-one, real subgaussian square.  The atom is
allowed to live on an arbitrary probability space. -/
structure IidSubgaussianSquare
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (n : ℕ) where
  atom : Fin n × Fin n → Ω → ℝ
  measurable_atom : ∀ p, Measurable (atom p)
  independent : iIndepFun atom μ
  identically_distributed : ∀ p q, IdentDistrib (atom p) (atom q) μ μ
  centered : ∀ p, ∫ ω, atom p ω ∂μ = 0
  variance_one : ∀ p, ∫ ω, (atom p ω) ^ 2 ∂μ = 1
  subgaussianParameter : ℝ≥0
  subgaussian : ∀ p, HasSubgaussianMGF (atom p) subgaussianParameter μ

/-- The same iid atom model on an arbitrary finite (or infinite) label type.
The seven packet blocks use this form; the two Cook squares are obtained by
injective restriction below. -/
structure IidSubgaussianFamily
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (ι : Type*) where
  atom : ι → Ω → ℝ
  measurable_atom : ∀ i, Measurable (atom i)
  independent : iIndepFun atom μ
  identically_distributed : ∀ i j, IdentDistrib (atom i) (atom j) μ μ
  centered : ∀ i, ∫ ω, atom i ω ∂μ = 0
  variance_one : ∀ i, ∫ ω, (atom i ω) ^ 2 ∂μ = 1
  subgaussianParameter : ℝ≥0
  subgaussian : ∀ i, HasSubgaussianMGF (atom i) subgaussianParameter μ

/-- Injective reindexing preserves every iid-family hypothesis. -/
def IidSubgaussianFamily.reindex
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ι κ : Type*} (S : IidSubgaussianFamily Ω μ ι) (label : κ ↪ ι) :
    IidSubgaussianFamily Ω μ κ where
  atom i := S.atom (label i)
  measurable_atom i := S.measurable_atom (label i)
  independent := S.independent.precomp label.injective
  identically_distributed i j := S.identically_distributed (label i) (label j)
  centered i := S.centered (label i)
  variance_one i := S.variance_one (label i)
  subgaussianParameter := S.subgaussianParameter
  subgaussian i := S.subgaussian (label i)

/-- Restrict an iid family along an injective labeling of a square.  This is
how the two disjoint complete packet squares are supplied to Cook; iid-ness
is proved here and is not a caller-provided certificate. -/
def IidSubgaussianFamily.squareRestriction
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ι : Type*} {n : ℕ}
    (S : IidSubgaussianFamily Ω μ ι) (label : (Fin n × Fin n) ↪ ι) :
    IidSubgaussianSquare Ω μ n where
  atom p := S.atom (label p)
  measurable_atom p := S.measurable_atom (label p)
  independent := S.independent.precomp label.injective
  identically_distributed p q := S.identically_distributed (label p) (label q)
  centered p := S.centered (label p)
  variance_one p := S.variance_one (label p)
  subgaussianParameter := S.subgaussianParameter
  subgaussian p := S.subgaussian (label p)

/-- Reindex a rectangularly labeled iid family by two coordinate
equivalences.  When the row and column types have the same cardinality this
produces the concrete `Fin n × Fin n` model expected by Cook. -/
def IidSubgaussianFamily.squareOfRowColEquiv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ρ κ : Type*} {n : ℕ}
    (S : IidSubgaussianFamily Ω μ (ρ × κ))
    (rowEquiv : Fin n ≃ ρ) (colEquiv : Fin n ≃ κ) :
    IidSubgaussianSquare Ω μ n :=
  S.squareRestriction
    { toFun := fun p ↦ (rowEquiv p.1, colEquiv p.2)
      inj' := fun p q hpq ↦ Prod.ext
        (rowEquiv.injective (congrArg Prod.fst hpq))
        (colEquiv.injective (congrArg Prod.snd hpq)) }

/-- The raw iid matrix associated with `IidSubgaussianSquare`. -/
def IidSubgaussianSquare.rawMatrix
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : IidSubgaussianSquare Ω μ n) (ω : Ω) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ (S.atom (i, j) ω : ℂ)

/-- Cook's deterministic variance profile, uniformly bounded above and away
from zero. -/
structure CookProfile (n : ℕ) where
  weight : Matrix (Fin n) (Fin n) ℝ
  lowerWeight : ℝ
  upperWeight : ℝ
  lowerWeight_pos : 0 < lowerWeight
  bounds : ∀ i j, lowerWeight ≤ weight i j ∧ weight i j ≤ upperWeight

/-- The profiled iid square `Z = (a_ij ξ_ij)`. -/
def profiledMatrix
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : IidSubgaussianSquare Ω μ n) (a : CookProfile n) (ω : Ω) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ ((a.weight i j * S.atom (i, j) ω : ℝ) : ℂ)

/-- The numerical right side in Cook's estimate (9.11). -/
def cookFailureBound (C c : ℝ) (n : ℕ) : ℝ :=
  C * Real.sqrt (Real.log n / n) + Real.exp (-c * n)

/-- The bad event for the deformed-square estimate. -/
def cookBadEvent
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (S : IidSubgaussianSquare Ω μ n) (a : CookProfile n)
    (D : Ω → Matrix (Fin n) (Fin n) ℂ) (β : ℝ) : Set Ω :=
  {ω | matrixSMin (profiledMatrix S a ω + D ω) ≤ (n : ℝ) ^ (-β)}

/--
Cook's deformed-square least-singular-value estimate, including the version
conditional on an independent sigma-field.  `unconditional` is (9.11) for a
constant deformation.  `conditional` states the same bound for the
conditional probability, represented by the conditional expectation of the
bad-event indicator.

Each input fixes a subgaussian bound and a positive profile interval containing
the unit profile used by the terminal packet.  The estimate is required only
for atoms and profiles within these bounds.  Thus `beta`, `cookC`, and `cookc`
may depend on all three fixed parameters, as well as on their argument `L`.
-/
structure CookDeformedSquareInput where
  subgaussianBound : ℝ≥0
  subgaussianBound_one_le : 1 ≤ subgaussianBound
  lowerWeight : ℝ
  upperWeight : ℝ
  lowerWeight_pos : 0 < lowerWeight
  lowerWeight_le_one : lowerWeight ≤ 1
  one_le_upperWeight : 1 ≤ upperWeight
  beta : ℝ → ℝ
  cookC : ℝ → ℝ
  cookc : ℝ → ℝ
  beta_pos : ∀ L, 0 < beta L
  C_nonneg : ∀ L, 0 ≤ cookC L
  c_pos : ∀ L, 0 < cookc L
  unconditional :
    ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] {n : ℕ}
      (S : IidSubgaussianSquare Ω μ n) (a : CookProfile n)
      (L : ℝ) (D : Matrix (Fin n) (Fin n) ℂ),
      S.subgaussianParameter ≤ subgaussianBound →
      (∀ i j, lowerWeight ≤ a.weight i j ∧ a.weight i j ≤ upperWeight) →
      2 ≤ n → 0 ≤ L → ‖D‖ ≤ (n : ℝ) ^ L →
      μ.real (cookBadEvent S a (fun _ ↦ D) (beta L)) ≤
        cookFailureBound (cookC L) (cookc L) n
  conditional :
    ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] {n : ℕ}
      (S : IidSubgaussianSquare Ω μ n) (a : CookProfile n)
      (L : ℝ) (fresh m : MeasurableSpace Ω)
      (hfresh : fresh ≤ mΩ) (hm : m ≤ mΩ)
      (D : Ω → Matrix (Fin n) (Fin n) ℂ),
      @IidSubgaussianSquare.subgaussianParameter Ω mΩ μ n S ≤ subgaussianBound →
      (∀ i j, lowerWeight ≤ a.weight i j ∧ a.weight i j ≤ upperWeight) →
      2 ≤ n → 0 ≤ L →
      (∀ p, @Measurable Ω ℝ fresh _
        (@IidSubgaussianSquare.atom Ω mΩ μ n S p)) →
      (∀ i j, @StronglyMeasurable Ω ℂ _ m (fun ω ↦ D ω i j)) →
      Indep fresh m μ →
      (∀ᵐ ω ∂μ, ‖D ω‖ ≤ (n : ℝ) ^ L) →
      @MeasurableSet Ω mΩ (@cookBadEvent Ω mΩ μ n S a D (beta L)) ∧
        ∀ᵐ ω ∂μ,
          @MeasureTheory.condExp Ω ℝ m (m₀ := mΩ) _ _ μ
              ((@cookBadEvent Ω mΩ μ n S a D (beta L)).indicator
                (fun _ ↦ (1 : ℝ))) ω ≤
            cookFailureBound (cookC L) (cookc L) n

/-- The right side of Nguyen's fixed-index estimate (9.2). -/
def nguyenFixedIndexBound (C c ε : ℝ) (n k : ℕ) : ℝ :=
  C ^ k * ε ^ (k ^ 2) + Real.exp (-c * n)

/-- The right side of Nguyen's overcrowding estimate (9.1). -/
def nguyenOvercrowdingBound (C c ϑ ε : ℝ) (n k : ℕ) : ℝ :=
  Real.rpow (C * ε) ((1 - ϑ) * (k : ℝ) ^ 2) + Real.exp (-c * n)

/--
Nguyen's fixed-index and overcrowding estimates for the bottom singular
values of an iid square.  The singular value at index `n-k` is the paper's
`s_{n-k+1}`.  All constants belong to the fixed subgaussian range specified
by `subgaussianBound`; each application supplies the corresponding bound on
the atom's subgaussian parameter.
-/
structure NguyenBottomSingularInput where
  subgaussianBound : ℝ≥0
  theta : ℝ
  gamma0 : ℝ
  nguyenc : ℝ
  nguyenC : ℝ
  k0 : ℕ
  theta_mem : theta ∈ Set.Ioo 0 1
  gamma0_pos : 0 < gamma0
  c_pos : 0 < nguyenc
  C_pos : 0 < nguyenC
  fixedIndex :
    ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] {n : ℕ}
      (S : IidSubgaussianSquare Ω μ n) (k : ℕ) (ε : ℝ),
      S.subgaussianParameter ≤ subgaussianBound →
      1 ≤ k → k ≤ k0 → 0 ≤ ε → k ≤ n →
      μ.real {ω | matrixSingularValue (S.rawMatrix ω) (n - k) ≤
          ε / Real.sqrt n} ≤
        nguyenFixedIndexBound nguyenC nguyenc ε n k
  overcrowding :
    ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] {n : ℕ}
      (S : IidSubgaussianSquare Ω μ n) (k : ℕ) (ε : ℝ),
      S.subgaussianParameter ≤ subgaussianBound →
      k0 < k → (k : ℝ) < gamma0 * n → 0 ≤ ε → k ≤ n →
      μ.real {ω | matrixSingularValue (S.rawMatrix ω) (n - k) ≤
          (k : ℝ) * ε / Real.sqrt n} ≤
        nguyenOvercrowdingBound nguyenC nguyenc theta ε n k

end BernoulliSection9
