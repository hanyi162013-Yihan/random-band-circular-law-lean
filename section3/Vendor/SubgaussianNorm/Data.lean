import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian

/-! Model-only excerpt from the published Section 9 ExternalInputs module.
No Cook or Nguyen estimate/interface is included. Used for the norm event
in Proposition 3.8, proof between equations (3.21) and (3.22). -/

open scoped Matrix.Norms.L2Operator ProbabilityTheory BigOperators ENNReal NNReal MeasureTheory
noncomputable section
namespace SubgaussianNorm
open MeasureTheory ProbabilityTheory

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


end SubgaussianNorm

