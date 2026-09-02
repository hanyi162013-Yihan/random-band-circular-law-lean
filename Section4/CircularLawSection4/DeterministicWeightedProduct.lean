import CircularLawSection4.OrderedExteriorPhase

/-!
# Deterministic weighted products

This file isolates the generic product argument needed by the ordered
exterior/Boolean-support bridge.  A weighted matrix is allowed arbitrary
complex phases, but its support in each column is required to be the graph of
a deterministic partial map and every supported entry has norm one.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

section WeightedPartialMap

variable {α β : Type*} [Fintype α] [DecidableEq α]

/-- A family of complex matrices has exactly the column support of a family of
deterministic partial maps. -/
def HasDeterministicSupport
    (K : β → Matrix α α ℂ) (f : β → α → Option α) : Prop :=
  ∀ x B A, K x B A ≠ 0 ↔ f x A = some B

/-- Every supported weight in a matrix family is a complex phase. -/
def HasUnitSupportedWeights (K : β → Matrix α α ℂ) : Prop :=
  ∀ x B A, K x B A ≠ 0 → ‖K x B A‖ = 1

/-- Multiplying matrices whose columns are weighted deterministic partial maps
does not create interference: the norm of the resulting entry is exactly the
Boolean `0`/`1` entry of the composed partial map. -/
theorem chronologicalProduct_map_norm_eq_partialMapMatrix
    (K : β → Matrix α α ℂ) (f : β → α → Option α)
    (hSupport : HasDeterministicSupport K f)
    (hUnit : HasUnitSupportedWeights K)
    (xs : List β) (B A : α) :
    ‖chronologicalProduct (xs.map K) B A‖ =
      ‖partialMapMatrix (partialMapRun (xs.map f)) B A‖ := by
  induction xs generalizing B A with
  | nil =>
      simp [partialMapRun, partialMapMatrix, Matrix.one_apply, eq_comm]
  | cons x xs ih =>
      classical
      cases hx : f x A with
      | none =>
          have hzero : ∀ C : α, K x C A = 0 := by
            intro C
            by_contra hne
            have : f x A = some C := (hSupport x C A).mp hne
            simp [hx] at this
          simp [Matrix.mul_apply, partialMapRun, hx, hzero,
            partialMapMatrix]
      | some C =>
          have hKC : K x C A ≠ 0 :=
            (hSupport x C A).mpr hx
          have hzero : ∀ D : α, D ≠ C → K x D A = 0 := by
            intro D hDC
            by_contra hne
            have hEq : f x A = some D := (hSupport x D A).mp hne
            rw [hx] at hEq
            exact hDC (Option.some.inj hEq).symm
          rw [List.map_cons, chronologicalProduct_cons, Matrix.mul_apply,
            Finset.sum_eq_single C]
          · rw [norm_mul, hUnit x C A hKC, mul_one, ih]
            simp [partialMapMatrix, partialMapRun, hx]
          · intro D _ hDC
            rw [hzero D hDC]
            simp
          · simp

end WeightedPartialMap

section CertificateFromStepData

/-- Stepwise deterministic support and unit phase data imply the word-level
norm equality required by `singletonWordCertificate_of_word_norm_eq`. -/
theorem wordOperator_norm_eq_booleanSupportK_of_step_data
    {d : ℕ}
    (K : (q : ExteriorDegree d) → ResetLabel d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (hSupport : ∀ (q : ExteriorDegree d) (ell : ResetLabel d)
        (B A : ExteriorIndex d q),
      K q ell B A ≠ 0 ↔
        exteriorSupportStep (q := q) (supportLabel ell) A = some B)
    (hUnit : ∀ (q : ExteriorDegree d) (ell : ResetLabel d)
        (B A : ExteriorIndex d q),
      K q ell B A ≠ 0 → ‖K q ell B A‖ = 1)
    (omega : Fin d → ResetLabel d) (q : ExteriorDegree d)
    (B A : ExteriorIndex d q) :
    ‖wordOperator (K q) omega B A‖ =
      ‖wordOperator (booleanSupportK q) omega B A‖ := by
  rw [wordOperator_booleanSupportK]
  unfold wordOperator
  rw [← partialMapRun_exteriorSupport
    (q := q) (List.ofFn fun t => supportLabel (omega t))]
  simpa [List.map_ofFn, Function.comp_def] using
    chronologicalProduct_map_norm_eq_partialMapMatrix
      (K := K q)
      (f := fun ell => exteriorSupportStep (q := q) (supportLabel ell))
      (hSupport := hSupport q)
      (hUnit := hUnit q)
      (xs := List.ofFn omega) B A

/-- Transport any Boolean singleton-word certificate to a weighted family
using only one-step support equality and unit-norm weights. -/
noncomputable def singletonWordCertificate_of_step_data
    {d : ℕ}
    {K : (q : ExteriorDegree d) → ResetLabel d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ}
    {omega : Fin d → ResetLabel d} {r : ExteriorDegree d}
    {I J : ExteriorIndex d r}
    (h0 : SingletonWordCertificate booleanSupportK omega r I J)
    (hSupport : ∀ (q : ExteriorDegree d) (ell : ResetLabel d)
        (B A : ExteriorIndex d q),
      K q ell B A ≠ 0 ↔
        exteriorSupportStep (q := q) (supportLabel ell) A = some B)
    (hUnit : ∀ (q : ExteriorDegree d) (ell : ResetLabel d)
        (B A : ExteriorIndex d q),
      K q ell B A ≠ 0 → ‖K q ell B A‖ = 1) :
    SingletonWordCertificate K omega r I J :=
  singletonWordCertificate_of_word_norm_eq h0
    (wordOperator_norm_eq_booleanSupportK_of_step_data K hSupport hUnit omega)

end CertificateFromStepData

end CircularLawSection4
