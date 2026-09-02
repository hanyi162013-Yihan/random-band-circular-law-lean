import CircularLawSection4.MultiaffineTranslation
import CircularLawSection4.OrderedIsolatedMaxEntry

/-!
# Fresh-row multiaffine polynomials

This file closes the deterministic bridge between affine matrix rows and the
full fresh monomial isolated by a reset word.  A chronological product of
matrices `base t + x t • linear t` is represented by an explicit recursive
`MultiAffine` polynomial after testing with `trace (B * ·)`.  Its top
coefficient is the same trace with every affine factor replaced by its linear
part.  Summing over exterior degrees with alternating signs then identifies
the top coefficient with `weightedFullMonomialCoefficient`.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

namespace MultiAffine

/-- The identically zero polynomial in any number of variables. -/
def zeroPolynomial {R : Type*} [Zero R] : (n : ℕ) → MultiAffine R n
  | 0 => .const 0
  | n + 1 => .affine (zeroPolynomial n) (zeroPolynomial n)

@[simp] theorem eval_zeroPolynomial {R : Type*} [Semiring R] {n : ℕ}
    (x : Fin n → R) : eval (zeroPolynomial n) x = 0 := by
  induction n with
  | zero => simp [zeroPolynomial]
  | succ n ih => simp [zeroPolynomial, ih]

@[simp] theorem topCoeff_zeroPolynomial {R : Type*} [Semiring R] (n : ℕ) :
    topCoeff (zeroPolynomial (R := R) n) = 0 := by
  induction n with
  | zero => simp [zeroPolynomial]
  | succ n ih => simp [zeroPolynomial, ih]

/-- Sum a list of recursively represented multiaffine polynomials without
requiring a global additive instance on the syntax type. -/
def sumList {R : Type*} [Add R] [Zero R] {n : ℕ} :
    List (MultiAffine R n) → MultiAffine R n
  | [] => zeroPolynomial n
  | p :: ps => add p (sumList ps)

@[simp] theorem eval_sumList {R : Type*} [Semiring R] {n : ℕ}
    (ps : List (MultiAffine R n)) (x : Fin n → R) :
    eval (sumList ps) x = (ps.map fun p => eval p x).sum := by
  induction ps with
  | nil => simp [sumList]
  | cons p ps ih => simp [sumList, ih]

@[simp] theorem topCoeff_sumList {R : Type*} [Semiring R] {n : ℕ}
    (ps : List (MultiAffine R n)) :
    topCoeff (sumList ps) = (ps.map topCoeff).sum := by
  induction ps with
  | nil => simp [sumList]
  | cons p ps ih => simp [sumList, ih]

end MultiAffine

section OneTrace

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Recursive polynomial for a trace-tested chronological product of affine
matrix factors.  The recursion peels off the last chronological factor, so
the frozen testing matrix becomes `B * base last` or `B * linear last`. -/
def affineTracePolynomial : {n : ℕ} →
    Matrix m m ℂ → (Fin n → Matrix m m ℂ) →
      (Fin n → Matrix m m ℂ) → MultiAffine ℂ n
  | 0, B, _, _ => .const (Matrix.trace B)
  | n + 1, B, base, linear =>
      .affine
        (affineTracePolynomial (B * base (Fin.last n))
          (fun t => base t.castSucc) (fun t => linear t.castSucc))
        (affineTracePolynomial (B * linear (Fin.last n))
          (fun t => base t.castSucc) (fun t => linear t.castSucc))

/-- Evaluating the recursive polynomial gives the trace of the original
chronological affine matrix product. -/
theorem eval_affineTracePolynomial : ∀ {n : ℕ}
    (B : Matrix m m ℂ) (base linear : Fin n → Matrix m m ℂ)
    (x : Fin n → ℂ),
    MultiAffine.eval (affineTracePolynomial B base linear) x =
      Matrix.trace (B * chronologicalProduct
        (List.ofFn fun t => base t + x t • linear t))
  | 0, B, base, linear, x => by
      simp [affineTracePolynomial]
  | n + 1, B, base, linear, x => by
      rw [affineTracePolynomial, MultiAffine.eval_affine]
      rw [eval_affineTracePolynomial, eval_affineTracePolynomial]
      rw [List.ofFn_succ', List.concat_eq_append,
        chronologicalProduct_append]
      simp only [chronologicalProduct, MultiAffine.dropLast]
      simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- The full square-free coefficient is obtained by replacing every affine
factor by its linear part. -/
theorem topCoeff_affineTracePolynomial : ∀ {n : ℕ}
    (B : Matrix m m ℂ) (base linear : Fin n → Matrix m m ℂ),
    MultiAffine.topCoeff (affineTracePolynomial B base linear) =
      Matrix.trace (B * chronologicalProduct (List.ofFn linear))
  | 0, B, base, linear => by
      simp [affineTracePolynomial]
  | n + 1, B, base, linear => by
      rw [affineTracePolynomial, MultiAffine.topCoeff_affine]
      rw [topCoeff_affineTracePolynomial]
      rw [List.ofFn_succ', List.concat_eq_append,
        chronologicalProduct_append]
      simp [chronologicalProduct, Matrix.mul_assoc]

/-- Scalar weights factor completely out of a chronological matrix product. -/
theorem chronologicalProduct_weighted_ofFn : ∀ {n : ℕ}
    (weight : Fin n → ℂ) (K : Fin n → Matrix m m ℂ),
    chronologicalProduct (List.ofFn fun t => weight t • K t) =
      (∏ t, weight t) • chronologicalProduct (List.ofFn K)
  | 0, weight, K => by simp
  | n + 1, weight, K => by
      simp only [List.ofFn_succ', List.concat_eq_append]
      rw [chronologicalProduct_append, chronologicalProduct_append]
      rw [chronologicalProduct_weighted_ofFn]
      rw [Fin.prod_univ_castSucc]
      simp [chronologicalProduct]
      rw [smul_smul]

end OneTrace

section AlternatingTrace

/-- Alternating sum, over all exterior degrees, of the affine trace
polynomials associated with the frozen matrices `B q`. -/
def alternatingAffineTracePolynomial {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (base linear : (q : ExteriorDegree d) → Fin d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ) :
    MultiAffine ℂ d :=
  MultiAffine.sumList <| List.ofFn fun q : ExteriorDegree d =>
    MultiAffine.scale ((-1 : ℂ) ^ q.val)
      (affineTracePolynomial (B q) (base q) (linear q))

/-- Evaluation of the alternating polynomial is the alternating exterior
trace of the chronological affine products. -/
theorem eval_alternatingAffineTracePolynomial {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (base linear : (q : ExteriorDegree d) → Fin d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (x : Fin d → ℂ) :
    MultiAffine.eval (alternatingAffineTracePolynomial B base linear) x =
      ∑ q : ExteriorDegree d, (-1 : ℂ) ^ q.val *
        Matrix.trace (B q * chronologicalProduct
          (List.ofFn fun t => base q t + x t • linear q t)) := by
  rw [alternatingAffineTracePolynomial, MultiAffine.eval_sumList]
  simp only [List.map_ofFn]
  rw [List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro q _
  simp [eval_affineTracePolynomial]

/-- The top coefficient of the alternating polynomial is the alternating
trace with every row replaced by its linear coefficient matrix. -/
theorem topCoeff_alternatingAffineTracePolynomial {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (base linear : (q : ExteriorDegree d) → Fin d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ) :
    MultiAffine.topCoeff (alternatingAffineTracePolynomial B base linear) =
      ∑ q : ExteriorDegree d, (-1 : ℂ) ^ q.val *
        Matrix.trace (B q * chronologicalProduct (List.ofFn (linear q))) := by
  rw [alternatingAffineTracePolynomial, MultiAffine.topCoeff_sumList]
  simp only [List.map_ofFn]
  rw [List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro q _
  simp [topCoeff_affineTracePolynomial]

end AlternatingTrace

section WeightedFreshPolynomial

/-- The paper-shaped fresh polynomial: at row `t`, the selected linear atom
is the ordered operator `K q (ω t)` multiplied by its deterministic band
weight.  The base term may contain all frozen variables and deterministic
spectral shifts. -/
def weightedAlternatingFreshPolynomial {d : ℕ}
    (weight : ResetLabel d → ℂ)
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (base : (q : ExteriorDegree d) → Fin d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (K : (q : ExteriorDegree d) → ResetLabel d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (ω : Fin d → ResetLabel d) : MultiAffine ℂ d :=
  alternatingAffineTracePolynomial B base
    (fun q t => weight (ω t) • K q (ω t))

/-- Evaluation formula for the weighted fresh polynomial. -/
theorem eval_weightedAlternatingFreshPolynomial {d : ℕ}
    (weight : ResetLabel d → ℂ)
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (base : (q : ExteriorDegree d) → Fin d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (K : (q : ExteriorDegree d) → ResetLabel d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (ω : Fin d → ResetLabel d) (x : Fin d → ℂ) :
    MultiAffine.eval
        (weightedAlternatingFreshPolynomial weight B base K ω) x =
      ∑ q : ExteriorDegree d, (-1 : ℂ) ^ q.val *
        Matrix.trace (B q * chronologicalProduct
          (List.ofFn fun t =>
            base q t + x t • (weight (ω t) • K q (ω t)))) := by
  exact eval_alternatingAffineTracePolynomial B base
    (fun q t => weight (ω t) • K q (ω t)) x

/-- The full square-free coefficient of the genuine fresh polynomial is
exactly the weighted reset-word coefficient already used by the isolation
theorems.  In particular, every frozen base term disappears from the top
coefficient. -/
theorem topCoeff_weightedAlternatingFreshPolynomial {d : ℕ}
    (weight : ResetLabel d → ℂ)
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (base : (q : ExteriorDegree d) → Fin d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (K : (q : ExteriorDegree d) → ResetLabel d →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (ω : Fin d → ResetLabel d) :
    MultiAffine.topCoeff
        (weightedAlternatingFreshPolynomial weight B base K ω) =
      weightedFullMonomialCoefficient weight B K ω := by
  rw [weightedAlternatingFreshPolynomial,
    topCoeff_alternatingAffineTracePolynomial]
  rw [weightedFullMonomialCoefficient, fullMonomialCoefficient]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [chronologicalProduct_weighted_ofFn]
  simp only [wordOperator, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

end WeightedFreshPolynomial

section OrderedFreshPolynomial

/-- Specialization to the actual ordered star/reset exterior coefficients
and the arbitrary-endpoint singleton word. -/
def orderedFreshPolynomial {d : ℕ}
    (weight : ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (base : (q : ExteriorDegree (d + 1)) → Fin (d + 1) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (r : ExteriorDegree (d + 1))
    (I J : ExteriorIndex (d + 1) r) : MultiAffine ℂ (d + 1) :=
  weightedAlternatingFreshPolynomial weight B base (orderedCoefficient d)
    (arbitrarySupportWord I J)

/-- Exact identification of the ordered fresh polynomial's top coefficient
with the previously isolated weighted word coefficient. -/
@[simp] theorem topCoeff_orderedFreshPolynomial {d : ℕ}
    (weight : ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (base : (q : ExteriorDegree (d + 1)) → Fin (d + 1) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (r : ExteriorDegree (d + 1))
    (I J : ExteriorIndex (d + 1) r) :
    MultiAffine.topCoeff (orderedFreshPolynomial weight B base r I J) =
      weightedFullMonomialCoefficient weight B (orderedCoefficient d)
        (arbitrarySupportWord I J) := by
  exact topCoeff_weightedAlternatingFreshPolynomial weight B base
    (orderedCoefficient d) (arbitrarySupportWord I J)

/-- Hence the top coefficient has exactly the modulus predicted by the
ordered singleton certificate: the product of the selected band weights
times the chosen frozen exterior entry. -/
theorem norm_topCoeff_orderedFreshPolynomial {d : ℕ}
    (weight : ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (base : (q : ExteriorDegree (d + 1)) → Fin (d + 1) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (r : ExteriorDegree (d + 1))
    (I J : ExteriorIndex (d + 1) r) :
    ‖MultiAffine.topCoeff (orderedFreshPolynomial weight B base r I J)‖ =
      (∏ t : Fin (d + 1),
        ‖weight (arbitrarySupportWord I J t)‖) * ‖B r J I‖ := by
  rw [topCoeff_orderedFreshPolynomial]
  exact norm_weightedFullMonomialCoefficient_eq_of_singleton
    weight B (orderedCoefficient d) (arbitrarySupportWord I J) r I J
      (orderedCoefficient_arbitrarySingletonCertificate r I J)

/-- The maximizing operator-norm isolation theorem now lands directly on
the top coefficient of an explicit fresh multiaffine polynomial. -/
theorem exists_orderedFreshPolynomial_topCoeff_maxL2OpNorm_lower_bound
    {d : ℕ} (weight : ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (base : (q : ExteriorDegree (d + 1)) → Fin (d + 1) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (bmin : ℝ) (hbmin : 0 ≤ bmin)
    (hweight : ∀ ell : ResetLabel (d + 1), bmin ≤ ‖weight ell‖) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        bmin ^ (d + 1) *
            (exteriorFamilyMaxL2OpNorm B /
              (Fintype.card (ExteriorFamilyEntry (d + 1)) : ℝ)) ≤
          ‖MultiAffine.topCoeff
            (orderedFreshPolynomial weight B base r I J)‖ := by
  obtain ⟨r, I, J, h⟩ :=
    exists_isolated_orderedCoefficient_maxL2OpNorm_lower_bound
      weight B bmin hbmin hweight
  exact ⟨r, I, J, by simpa using h⟩

end OrderedFreshPolynomial

end CircularLawSection4
