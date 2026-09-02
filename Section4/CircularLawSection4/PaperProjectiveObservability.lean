import CircularLawSection4.ProjectiveCoordinates
import CircularLawSection4.PaperIndicatorFreshRows
import CircularLawSection4.FreshClosure

/-!
# Projective observability for the paper fresh block

This module turns one output coordinate of `B Q v` into an explicit
multiaffine polynomial in one selected atom from every fresh row.  A
singleton reset word isolates its full coefficient, while a finite
coordinate selection compares that coefficient with the Euclidean operator
norm of `B`.  The analytic logarithmic estimates are added below the
deterministic bridge.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

/-- Every valid exterior degree has at least one coordinate subset. -/
theorem exteriorIndex_nonempty (D : ℕ) (q : ExteriorDegree D) :
    Nonempty (ExteriorIndex D q) := by
  have hq : q.val ≤ D := Nat.le_of_lt_succ q.isLt
  obtain ⟨s, hs⟩ :
      ((Finset.univ : Finset (Fin D)).powersetCard q.val).Nonempty :=
    Finset.powersetCard_nonempty.2 (by simpa using hq)
  exact ⟨⟨s, (Finset.mem_powersetCard.1 hs).2⟩⟩

/-- A family supported at one exterior degree. -/
def singleExteriorFamily {D : ℕ} (q : ExteriorDegree D)
    (A : Matrix (ExteriorIndex D q) (ExteriorIndex D q) ℂ) :
    (q' : ExteriorDegree D) →
      Matrix (ExteriorIndex D q') (ExteriorIndex D q') ℂ :=
  fun q' => if h : q' = q then h.symm ▸ A else 0

@[simp] theorem singleExteriorFamily_same {D : ℕ}
    (q : ExteriorDegree D)
    (A : Matrix (ExteriorIndex D q) (ExteriorIndex D q) ℂ) :
    singleExteriorFamily q A q = A := by
  simp [singleExteriorFamily]

theorem singleExteriorFamily_eq_zero {D : ℕ}
    (q q' : ExteriorDegree D) (h : q' ≠ q)
    (A : Matrix (ExteriorIndex D q) (ExteriorIndex D q) ℂ) :
    singleExteriorFamily q A q' = 0 := by
  simp [singleExteriorFamily, h]

/-- The trace test whose value on `Q` is the `o`-th coordinate of
`B * Q` applied to `v`. -/
def projectiveTestingMatrix {m : Type*} [Fintype m]
    (B : Matrix m m ℂ) (v : EuclideanSpace ℂ m) (o : m) :
    Matrix m m ℂ := fun j i => v j * B o i

theorem trace_projectiveTestingMatrix_mul {m : Type*}
    [Fintype m] [DecidableEq m]
    (B Q : Matrix m m ℂ) (v : EuclideanSpace ℂ m) (o : m) :
    Matrix.trace (projectiveTestingMatrix B v o * Q) =
      (B * Q).mulVec (fun j => v j) o := by
  classical
  change (∑ j : m, ∑ i : m, v j * B o i * Q i j) =
    ∑ j : m, (∑ i : m, B o i * Q i j) * v j
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

namespace PaperIndicatorWeights

variable {d : ℕ} {c₀ C₀ : ℝ}

/-- The projective scalar polynomial obtained by retaining one exterior
degree and testing its fresh product against one output coordinate of
`B Q v`. -/
def paperProjectiveFreshPolynomial
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (o I J : ExteriorIndex (d + 1) q) : MultiAffine ℂ (d + 1) :=
  profile.paperIndicatorFreshPolynomial center z atoms
    (singleExteriorFamily q (projectiveTestingMatrix B v o)) q I J

/-- Evaluation of the projective polynomial is a signed coordinate of the
actual fresh product `B Q v`. -/
theorem eval_paperProjectiveFreshPolynomial
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (o I J : ExteriorIndex (d + 1) q) :
    MultiAffine.eval
        (profile.paperProjectiveFreshPolynomial center z atoms q B v o I J)
        (fun t => atoms t (arbitrarySupportWord I J t)) =
      (-1 : ℂ) ^ q.val *
        (B * chronologicalProduct
          (List.ofFn fun t => profile.freshExteriorRow center z atoms q t)).mulVec
            (fun j => v j) o := by
  classical
  rw [paperProjectiveFreshPolynomial,
    profile.eval_paperIndicatorFreshPolynomial]
  rw [Finset.sum_eq_single q]
  · rw [singleExteriorFamily_same,
      trace_projectiveTestingMatrix_mul]
  · intro q' _ hq'
    rw [singleExteriorFamily_eq_zero q q' hq']
    simp
  · intro hq
    exact False.elim (hq (Finset.mem_univ q))

/-- The observed scalar is pointwise dominated by the Euclidean norm of
the full projective vector.  This is the deterministic comparison needed
to transfer a scalar logarithmic small-ball estimate to `‖B Q v‖`. -/
theorem norm_eval_paperProjectiveFreshPolynomial_at_actualAtoms_le
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (o I J : ExteriorIndex (d + 1) q) :
    ‖MultiAffine.eval
        (profile.paperProjectiveFreshPolynomial center z atoms q B v o I J)
        (fun t => atoms t (arbitrarySupportWord I J t))‖ ≤
      ‖Matrix.toEuclideanCLM
        (n := ExteriorIndex (d + 1) q) (𝕜 := ℂ)
        (B * chronologicalProduct
          (List.ofFn fun t => profile.freshExteriorRow center z atoms q t)) v‖ := by
  rw [profile.eval_paperProjectiveFreshPolynomial]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact PiLp.norm_apply_le
    (Matrix.toEuclideanCLM
      (n := ExteriorIndex (d + 1) q) (𝕜 := ℂ)
      (B * chronologicalProduct
        (List.ofFn fun t => profile.freshExteriorRow center z atoms q t)) v) o

/-- Exact modulus of the projective polynomial's full coefficient. -/
theorem norm_topCoeff_paperProjectiveFreshPolynomial
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (o I J : ExteriorIndex (d + 1) q) :
    ‖MultiAffine.topCoeff
        (profile.paperProjectiveFreshPolynomial center z atoms q B v o I J)‖ =
      (∏ t : Fin (d + 1),
        ‖profile.orderedResetWeight (arbitrarySupportWord I J t)‖) *
          ‖B o I * v J‖ := by
  rw [paperProjectiveFreshPolynomial,
    profile.topCoeff_paperIndicatorFreshPolynomial]
  rw [norm_weightedFullMonomialCoefficient_eq_of_singleton
    profile.orderedResetWeight
    (singleExteriorFamily q (projectiveTestingMatrix B v o))
    (orderedCoefficient d) (arbitrarySupportWord I J) q I J
    (orderedCoefficient_arbitrarySingletonCertificate q I J)]
  simp [projectiveTestingMatrix, mul_comm]

/-- A unit input vector and a nonzero exterior operator admit a projective
fresh polynomial whose full coefficient is quantitatively comparable with
the Euclidean operator norm of `B`.  The deliberately elementary
coordinate extraction costs three powers of the exterior-coordinate
cardinality. -/
theorem exists_paperProjectiveFreshPolynomial_topCoeff_lower
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (hv : ‖v‖ = 1) :
    ∃ o I J : ExteriorIndex (d + 1) q,
      (Real.sqrt (c₀ / (d + 2 : ℝ))) ^ (d + 1) *
          (‖B‖ / (Fintype.card (ExteriorIndex (d + 1) q) : ℝ) ^ 3) ≤
        ‖MultiAffine.topCoeff
          (profile.paperProjectiveFreshPolynomial
            center z atoms q B v o I J)‖ := by
  letI : Nonempty (ExteriorIndex (d + 1) q) :=
    exteriorIndex_nonempty (d + 1) q
  obtain ⟨o, I, J, hcoordinate⟩ :=
    exists_matrixEntry_mul_unitCoordinate_ge_opNorm_div_card_cube B v hv
  refine ⟨o, I, J, ?_⟩
  rw [profile.norm_topCoeff_paperProjectiveFreshPolynomial]
  have hbmin : 0 ≤ Real.sqrt (c₀ / (d + 2 : ℝ)) := Real.sqrt_nonneg _
  have hweights :
      (Real.sqrt (c₀ / (d + 2 : ℝ))) ^ (d + 1) ≤
        ∏ t : Fin (d + 1),
          ‖profile.orderedResetWeight (arbitrarySupportWord I J t)‖ := by
    have hprod :
        (∏ _t : Fin (d + 1), Real.sqrt (c₀ / (d + 2 : ℝ))) ≤
          ∏ t : Fin (d + 1),
            ‖profile.orderedResetWeight (arbitrarySupportWord I J t)‖ := by
      apply Finset.prod_le_prod
      · intro _t _ht
        exact hbmin
      · intro t _ht
        exact profile.sqrt_lower_le_norm_orderedResetWeight _
    simpa using hprod
  exact mul_le_mul hweights hcoordinate (by positivity)
    (Finset.prod_nonneg fun t _ => norm_nonneg _)

/-- Positivity of the selected projective coefficient under the paper's
strict profile lower bound and a nonzero exterior operator. -/
theorem exists_paperProjectiveFreshPolynomial_topCoeff_pos
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < ‖B‖)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (hv : ‖v‖ = 1) :
    ∃ o I J : ExteriorIndex (d + 1) q,
      0 < ‖MultiAffine.topCoeff
        (profile.paperProjectiveFreshPolynomial
          center z atoms q B v o I J)‖ := by
  letI : Nonempty (ExteriorIndex (d + 1) q) :=
    exteriorIndex_nonempty (d + 1) q
  obtain ⟨o, I, J, hcoefficient⟩ :=
    profile.exists_paperProjectiveFreshPolynomial_topCoeff_lower
      center z atoms q B v hv
  refine ⟨o, I, J, ?_⟩
  have hden : 0 < (d + 2 : ℝ) := by positivity
  have hbmin : 0 < Real.sqrt (c₀ / (d + 2 : ℝ)) :=
    Real.sqrt_pos.2 (div_pos hc₀ hden)
  have hcard :
      0 < (Fintype.card (ExteriorIndex (d + 1) q) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hlower :
      0 < (Real.sqrt (c₀ / (d + 2 : ℝ))) ^ (d + 1) *
        (‖B‖ / (Fintype.card (ExteriorIndex (d + 1) q) : ℝ) ^ 3) :=
    mul_pos (pow_pos hbmin _) (div_pos hB (pow_pos hcard _))
  exact hlower.trans_le hcoefficient

end PaperIndicatorWeights

end CircularLawSection4
