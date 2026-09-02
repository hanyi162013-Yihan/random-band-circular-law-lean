import CircularLawSection4.Periodic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Reset words and isolation of a full monomial

This file formalizes the conditional trace-extraction part of
`lem:isolated-monomial`.  A reset-word certificate contains the required
operator equalities; the theorems below then check that all exterior degrees
except the selected one cancel exactly in the alternating trace.  Constructing
this matrix certificate from the Boolean support model in `ResetWord.lean` is
an explicit boundary of the present project.

The coefficient model is deliberately explicit: a full monomial chooses one
row variable in every one of the `d = 2W` fresh rows.  Its coefficient is the
corresponding chronological product of the deterministic row operators.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

/-- `none` is the shift label `star`; `some j` is reset at site `j`. -/
abbrev ResetLabel (d : ℕ) := Option (Fin d)

/-- Exterior degree, including both `0` and `d`. -/
abbrev ExteriorDegree (d : ℕ) := Fin (d + 1)

/-- Coordinate index for exterior degree `q`. -/
abbrev ExteriorIndex (d : ℕ) (q : ExteriorDegree d) :=
  powersetCard (Fin d) q.val

/-- Product of the deterministic row operators selected by a word. -/
def wordOperator {d : ℕ} {q : ExteriorDegree d}
    (K : ResetLabel d → Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (ω : Fin d → ResetLabel d) :
    Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ :=
  chronologicalProduct (List.ofFn fun t => K (ω t))

/-- The coefficient of the full row-multiaffine monomial selected by `ω` in
the alternating exterior trace. -/
def fullMonomialCoefficient {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (K : (q : ExteriorDegree d) → ResetLabel d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (ω : Fin d → ResetLabel d) : ℂ :=
  ∑ q : ExteriorDegree d,
    (-1 : ℂ) ^ q.val * Matrix.trace (B q * wordOperator (K q) ω)

/-- Checkable output of the singleton-domain particle construction.

At degree `r`, the word is a rank-one matrix unit sending `e_J` to `e_I`;
at every other exterior degree the same word is zero.  The phase is allowed
because ordered exterior bases introduce signs. -/
structure SingletonWordCertificate {d : ℕ}
    (K : (q : ExteriorDegree d) → ResetLabel d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (ω : Fin d → ResetLabel d) (r : ExteriorDegree d)
    (I J : ExteriorIndex d r) where
  phase : ℂ
  phase_norm : ‖phase‖ = 1
  selected_degree :
    wordOperator (K r) ω = phase • Matrix.single I J 1
  other_degrees : ∀ q : ExteriorDegree d, q ≠ r →
    wordOperator (K q) ω = 0

/-- A singleton word isolates exactly one matrix entry of `B`; no other
exterior degree contributes to this full monomial. -/
theorem fullMonomialCoefficient_eq_of_singleton {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (K : (q : ExteriorDegree d) → ResetLabel d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (ω : Fin d → ResetLabel d) (r : ExteriorDegree d)
    (I J : ExteriorIndex d r)
    (h : SingletonWordCertificate K ω r I J) :
    fullMonomialCoefficient B K ω =
      (-1 : ℂ) ^ r.val * h.phase * B r J I := by
  unfold fullMonomialCoefficient
  rw [Finset.sum_eq_single r]
  · rw [h.selected_degree]
    simp [Matrix.trace_mul_single]
    ring
  · intro q _ hqr
    rw [h.other_degrees q hqr]
    simp
  · intro hr
    exact False.elim (hr (Finset.mem_univ r))

/-- Consequently the modulus of the isolated coefficient is precisely the
modulus of the selected entry. -/
theorem norm_fullMonomialCoefficient_eq_of_singleton {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (K : (q : ExteriorDegree d) → ResetLabel d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (ω : Fin d → ResetLabel d) (r : ExteriorDegree d)
    (I J : ExteriorIndex d r)
    (h : SingletonWordCertificate K ω r I J) :
    ‖fullMonomialCoefficient B K ω‖ = ‖B r J I‖ := by
  rw [fullMonomialCoefficient_eq_of_singleton B K ω r I J h]
  simp [h.phase_norm]

/-- Abstractly include the deterministic band weights attached to the
selected row atoms.  After a bridge to the manuscript's determinant
polynomial, this is the expression expected for the full-degree coefficient;
that bridge and the claim that the `z` shift only changes lower degree terms
are not proved in this file. -/
def weightedFullMonomialCoefficient {d : ℕ}
    (weight : ResetLabel d → ℂ)
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (K : (q : ExteriorDegree d) → ResetLabel d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (ω : Fin d → ResetLabel d) : ℂ :=
  (∏ t : Fin d, weight (ω t)) * fullMonomialCoefficient B K ω

/-- Exact weighted version of the isolated-coefficient formula. -/
theorem norm_weightedFullMonomialCoefficient_eq_of_singleton {d : ℕ}
    (weight : ResetLabel d → ℂ)
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (K : (q : ExteriorDegree d) → ResetLabel d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (ω : Fin d → ResetLabel d) (r : ExteriorDegree d)
    (I J : ExteriorIndex d r)
    (h : SingletonWordCertificate K ω r I J) :
    ‖weightedFullMonomialCoefficient weight B K ω‖ =
      (∏ t : Fin d, ‖weight (ω t)‖) * ‖B r J I‖ := by
  unfold weightedFullMonomialCoefficient
  rw [norm_mul, norm_fullMonomialCoefficient_eq_of_singleton B K ω r I J h]
  rw [norm_prod]

/-- Conditional quantitative lower bound from a singleton operator
certificate, pointwise weight lower bounds, and a selected-entry lower bound:
one obtains `bmin^d * entryLower`. -/
theorem isolated_full_monomial_lower_bound {d : ℕ}
    (weight : ResetLabel d → ℂ)
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (K : (q : ExteriorDegree d) → ResetLabel d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (ω : Fin d → ResetLabel d) (r : ExteriorDegree d)
    (I J : ExteriorIndex d r)
    (h : SingletonWordCertificate K ω r I J)
    (bmin entryLower : ℝ) (hbmin : 0 ≤ bmin)
    (hweight : ∀ t : Fin d, bmin ≤ ‖weight (ω t)‖)
    (hentry : entryLower ≤ ‖B r J I‖) (hentry_nonneg : 0 ≤ entryLower) :
    bmin ^ d * entryLower ≤
      ‖weightedFullMonomialCoefficient weight B K ω‖ := by
  rw [norm_weightedFullMonomialCoefficient_eq_of_singleton
    weight B K ω r I J h]
  have hw : bmin ^ d ≤ ∏ t : Fin d, ‖weight (ω t)‖ := by
    have hw' : (∏ _t : Fin d, bmin) ≤
        ∏ t : Fin d, ‖weight (ω t)‖ :=
      Finset.prod_le_prod (fun _ _ => hbmin) (fun t _ => hweight t)
    simpa using hw'
  exact mul_le_mul hw hentry hentry_nonneg
    (Finset.prod_nonneg fun t _ => norm_nonneg _)

end CircularLawSection4
