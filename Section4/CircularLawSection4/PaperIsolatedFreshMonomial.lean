import CircularLawSection4.FreshClosure
import CircularLawSection4.PaperIndicatorFreshSample

/-!
# The paper's isolated full monomial in the actual fresh block

This file packages the deterministic constructions of
`PaperIndicatorFreshRows` and `PaperIndicatorFreshSample` in the notation of
the manuscript's isolated-monomial lemma.  The scalar `paperIndicatorFreshZ`
is the actual alternating exterior trace

`Z_B = ∑ q, (-1)^q trace (B q * Q q)`

for one full fresh block.  The selected multiaffine polynomial evaluates to
this scalar and has a full square-free coefficient bounded below by an
explicit multiple of the maximum Euclidean operator norm of `B`.

The exact coefficient loss is recorded both multiplicatively and
logarithmically.  It consists of the product of the `d` selected indicator
weights and the finite coordinate-extraction loss.  Thus no unspecified
constant is hidden in the Lean statement.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

namespace PaperIndicatorWeights

/-- The manuscript's `Z_B` for one genuine denominator-cleared fresh block.

Here `Q q` is the chronological product of the `q`th exterior fresh rows.
The diagonal spectral translation `-z` is already included in
`freshExteriorRow`. -/
def paperIndicatorFreshZ {d : ℕ} {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ) : ℂ :=
  ∑ q : ExteriorDegree (d + 1), (-1 : ℂ) ^ q.val *
    Matrix.trace (B q * chronologicalProduct
      (List.ofFn fun t : Fin (d + 1) ↦
        profile.freshExteriorRow center z atoms q t))

/-- Evaluation at the selected atoms is exactly the paper's actual `Z_B`.
This is the value-level bridge from the explicit multiaffine polynomial to
the chronological fresh exterior products. -/
theorem eval_paperIndicatorFreshPolynomial_eq_freshZ
    {d : ℕ} {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (r : ExteriorDegree (d + 1))
    (I J : ExteriorIndex (d + 1) r) :
    MultiAffine.eval
        (profile.paperIndicatorFreshPolynomial center z atoms B r I J)
        (fun t ↦ atoms t (arbitrarySupportWord I J t)) =
      profile.paperIndicatorFreshZ center z atoms B := by
  exact profile.eval_paperIndicatorFreshPolynomial center z atoms B r I J

/-- The frozen row used to define the selected-variable polynomial depends
only on atoms away from the reserved label `word t`.  This is the explicit
freezing invariance needed when the product law is split into selected and
unselected fresh coordinates. -/
theorem paperIndicatorFreshBase_congr_off_word
    {d : ℕ} {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms atoms' : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (word : Fin (d + 1) → ResetLabel (d + 1))
    (hoff : ∀ t ell, ell ≠ word t → atoms t ell = atoms' t ell)
    (q : ExteriorDegree (d + 1)) (t : Fin (d + 1)) :
    profile.paperIndicatorFreshBase center z atoms word q t =
      profile.paperIndicatorFreshBase center z atoms' word q t := by
  classical
  unfold paperIndicatorFreshBase
  congr 1
  apply Finset.sum_congr rfl
  intro ell hell
  rw [hoff t ell (Finset.mem_erase.mp hell).1]

/-- Two ambient atom configurations which agree off the one reserved label
in each row define exactly the same actual paper fresh polynomial. -/
theorem paperIndicatorFreshPolynomial_congr_off_selected
    {d : ℕ} {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms atoms' : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (r : ExteriorDegree (d + 1))
    (I J : ExteriorIndex (d + 1) r)
    (hoff : ∀ t ell, ell ≠ arbitrarySupportWord I J t →
      atoms t ell = atoms' t ell) :
    profile.paperIndicatorFreshPolynomial center z atoms B r I J =
      profile.paperIndicatorFreshPolynomial center z atoms' B r I J := by
  classical
  unfold paperIndicatorFreshPolynomial
  apply congrArg (fun base =>
    orderedFreshPolynomial profile.orderedResetWeight B base r I J)
  funext q t
  exact profile.paperIndicatorFreshBase_congr_off_word center z atoms atoms'
    (arbitrarySupportWord I J) hoff q t

/-- The deterministic spectral parameter only changes lower multiaffine
degrees.  In particular, the full square-free coefficient is independent of
`z`.  This is the precise coefficient-level form of the manuscript's
"the `-z` translation only changes lower-degree monomials" sentence. -/
theorem topCoeff_paperIndicatorFreshPolynomial_spectralShift
    {d : ℕ} {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z z' : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (r : ExteriorDegree (d + 1))
    (I J : ExteriorIndex (d + 1) r) :
    MultiAffine.topCoeff
        (profile.paperIndicatorFreshPolynomial center z atoms B r I J) =
      MultiAffine.topCoeff
        (profile.paperIndicatorFreshPolynomial center z' atoms B r I J) := by
  simp

/-- Exact multiplicative loss in the paper-specific isolated coefficient.

For the manuscript specialization `d + 1 = 2W`, this is
`(sqrt (c₀ / (2W + 1)))^(2W)` divided by the number of exterior-family
matrix entries. -/
def paperIsolatedCoefficientFactor (d : ℕ) (c₀ : ℝ) : ℝ :=
  (Real.sqrt (c₀ / (d + 2 : ℝ))) ^ (d + 1) /
    (Fintype.card (ExteriorFamilyEntry (d + 1)) : ℝ)

/-- The exact logarithmic loss corresponding to
`paperIsolatedCoefficientFactor`. -/
def paperIsolatedCoefficientLoss (d : ℕ) (c₀ : ℝ) : ℝ :=
  -Real.log (paperIsolatedCoefficientFactor d c₀)

theorem paperIsolatedCoefficientFactor_pos {d : ℕ} {c₀ : ℝ}
    (hc₀ : 0 < c₀) : 0 < paperIsolatedCoefficientFactor d c₀ := by
  unfold paperIsolatedCoefficientFactor
  have hden : 0 < (d + 2 : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt (c₀ / (d + 2 : ℝ)) :=
    Real.sqrt_pos.2 (div_pos hc₀ hden)
  have hcard : 0 < (Fintype.card (ExteriorFamilyEntry (d + 1)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  exact div_pos (pow_pos hsqrt _) hcard

/-- Under the natural paper normalization on the smallest row amplitude,
the multiplicative isolated-coefficient factor is at most one. -/
theorem paperIsolatedCoefficientFactor_le_one
    {d : ℕ} {c₀ : ℝ}
    (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1) :
    paperIsolatedCoefficientFactor d c₀ ≤ 1 := by
  have hpow :
      (Real.sqrt (c₀ / (d + 2 : ℝ))) ^ (d + 1) ≤ 1 :=
    pow_le_one₀ (Real.sqrt_nonneg _) hsqrt
  have hcard : 0 < (Fintype.card (ExteriorFamilyEntry (d + 1)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hone_card :
      (1 : ℝ) ≤ (Fintype.card (ExteriorFamilyEntry (d + 1)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [paperIsolatedCoefficientFactor, div_le_one hcard]
  exact hpow.trans hone_card

/-- The exact logarithmic loss is nonnegative under the same normalization.
This is the form required by the fresh-closure assembly theorem. -/
theorem paperIsolatedCoefficientLoss_nonneg
    {d : ℕ} {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1) :
    0 ≤ paperIsolatedCoefficientLoss d c₀ := by
  rw [paperIsolatedCoefficientLoss]
  exact neg_nonneg.mpr <| Real.log_nonpos
    (paperIsolatedCoefficientFactor_pos hc₀).le
    (paperIsolatedCoefficientFactor_le_one hsqrt)

/-- Exponentiating the negative exact loss recovers the multiplicative
coefficient factor. -/
@[simp] theorem exp_neg_paperIsolatedCoefficientLoss
    {d : ℕ} {c₀ : ℝ} (hc₀ : 0 < c₀) :
    Real.exp (-paperIsolatedCoefficientLoss d c₀) =
      paperIsolatedCoefficientFactor d c₀ := by
  rw [paperIsolatedCoefficientLoss, neg_neg]
  exact Real.exp_log (paperIsolatedCoefficientFactor_pos hc₀)

/-- Expanded formula for the logarithmic loss.  It displays separately the
weight-product loss and the finite coordinate-extraction loss. -/
theorem paperIsolatedCoefficientLoss_eq
    {d : ℕ} {c₀ : ℝ} (hc₀ : 0 < c₀) :
    paperIsolatedCoefficientLoss d c₀ =
      Real.log (Fintype.card (ExteriorFamilyEntry (d + 1)) : ℝ) -
        (d + 1 : ℝ) * Real.log (Real.sqrt (c₀ / (d + 2 : ℝ))) := by
  have hden : 0 < (d + 2 : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt (c₀ / (d + 2 : ℝ)) :=
    Real.sqrt_pos.2 (div_pos hc₀ hden)
  have hcard : 0 < (Fintype.card (ExteriorFamilyEntry (d + 1)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [paperIsolatedCoefficientLoss, paperIsolatedCoefficientFactor,
    Real.log_div (pow_ne_zero _ hsqrt.ne') hcard.ne', Real.log_pow]
  push_cast
  ring

/-- Paper-specific end-to-end isolated-full-monomial theorem.

The polynomial evaluates to the actual alternating fresh trace `Z_B`, and
its full square-free coefficient is at least the exact profile/cardinality
factor times `M_B = max_q ‖B q‖`.  The exterior degree and the two basis
coordinates selecting the monomial are chosen internally. -/
theorem exists_paperIndicatorFreshZ_isolatedFullMonomial
    {d : ℕ} {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        MultiAffine.eval
            (profile.paperIndicatorFreshPolynomial center z atoms B r I J)
            (fun t ↦ atoms t (arbitrarySupportWord I J t)) =
          profile.paperIndicatorFreshZ center z atoms B ∧
        paperIsolatedCoefficientFactor d c₀ *
            exteriorFamilyMaxL2OpNorm B ≤
          ‖MultiAffine.topCoeff
            (profile.paperIndicatorFreshPolynomial center z atoms B r I J)‖ := by
  obtain ⟨r, I, J, hcoefficient⟩ :=
    profile.exists_paperIndicatorFreshPolynomial_topCoeff_maxL2OpNorm_lower_bound
      center z atoms B
  refine ⟨r, I, J,
    profile.eval_paperIndicatorFreshPolynomial_eq_freshZ
      center z atoms B r I J, ?_⟩
  calc
    paperIsolatedCoefficientFactor d c₀ * exteriorFamilyMaxL2OpNorm B =
        (Real.sqrt (c₀ / (d + 2 : ℝ))) ^ (d + 1) *
          (exteriorFamilyMaxL2OpNorm B /
            (Fintype.card (ExteriorFamilyEntry (d + 1)) : ℝ)) := by
      rw [paperIsolatedCoefficientFactor]
      ring
    _ ≤ ‖MultiAffine.topCoeff
          (profile.paperIndicatorFreshPolynomial center z atoms B r I J)‖ :=
      hcoefficient

/-- Exponential-loss form of the isolated-full-monomial theorem, matching
the presentation `M_B * exp (-loss)` in the manuscript. -/
theorem exists_paperIndicatorFreshZ_isolatedFullMonomial_exp
    {d : ℕ} {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        MultiAffine.eval
            (profile.paperIndicatorFreshPolynomial center z atoms B r I J)
            (fun t ↦ atoms t (arbitrarySupportWord I J t)) =
          profile.paperIndicatorFreshZ center z atoms B ∧
        exteriorFamilyMaxL2OpNorm B *
            Real.exp (-paperIsolatedCoefficientLoss d c₀) ≤
          ‖MultiAffine.topCoeff
            (profile.paperIndicatorFreshPolynomial center z atoms B r I J)‖ := by
  obtain ⟨r, I, J, heval, hcoefficient⟩ :=
    profile.exists_paperIndicatorFreshZ_isolatedFullMonomial
      center z atoms B
  refine ⟨r, I, J, heval, ?_⟩
  rw [exp_neg_paperIsolatedCoefficientLoss hc₀, mul_comm]
  exact hcoefficient

/-- Log-scale form used in the one-fresh-closure argument.  If `M_B` is
positive, the selected coefficient lies at logarithmic distance at most the
explicit paper loss from `M_B`. -/
theorem exists_paperIndicatorFreshZ_isolatedFullMonomial_logScale
    {d : ℕ} {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < exteriorFamilyMaxL2OpNorm B) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        MultiAffine.eval
            (profile.paperIndicatorFreshPolynomial center z atoms B r I J)
            (fun t ↦ atoms t (arbitrarySupportWord I J t)) =
          profile.paperIndicatorFreshZ center z atoms B ∧
        Real.log (exteriorFamilyMaxL2OpNorm B) -
            Real.log ‖MultiAffine.topCoeff
              (profile.paperIndicatorFreshPolynomial center z atoms B r I J)‖ ≤
          paperIsolatedCoefficientLoss d c₀ := by
  obtain ⟨r, I, J, heval, hcoefficient⟩ :=
    profile.exists_paperIndicatorFreshZ_isolatedFullMonomial_exp
      hc₀ center z atoms B
  refine ⟨r, I, J, heval, ?_⟩
  exact log_scale_sub_log_coefficient_le_of_exp_loss hB hcoefficient

/-- Literal flat-sample form.  On nonvanishing right-edge coefficients, the
selected polynomial evaluates to the alternating trace of the actual sampled
companion transfers, while retaining the same full-monomial lower bound. -/
theorem exists_paperIndicatorFlatSample_isolatedFullMonomial
    (N d : ℕ) [NeZero N] {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (start : ZMod N) (ω : Fin (N * (d + 2)) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hβ : ∀ t : Fin (d + 1),
      paperIndicatorBetaRaw N d profile ω
        (paperIndicatorFreshRowSite N d start t) ≠ 0) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        MultiAffine.eval
            (profile.paperIndicatorFreshPolynomial center z
              (paperIndicatorFreshAtoms N d start ω) B r I J)
            (fun t ↦ paperIndicatorFreshAtoms N d start ω t
              (arbitrarySupportWord I J t)) =
          paperIndicatorFreshBlockAlternatingTrace
            N d profile center z start ω B ∧
        paperIsolatedCoefficientFactor d c₀ *
            exteriorFamilyMaxL2OpNorm B ≤
          ‖MultiAffine.topCoeff
            (profile.paperIndicatorFreshPolynomial center z
              (paperIndicatorFreshAtoms N d start ω) B r I J)‖ := by
  obtain ⟨r, I, J, hcoefficient⟩ :=
    profile.exists_paperIndicatorFreshPolynomial_topCoeff_maxL2OpNorm_lower_bound
      center z (paperIndicatorFreshAtoms N d start ω) B
  refine ⟨r, I, J, ?_, ?_⟩
  · exact eval_paperIndicatorFreshPolynomial_flatSample
      N d profile center z start ω B r I J hβ
  · calc
      paperIsolatedCoefficientFactor d c₀ * exteriorFamilyMaxL2OpNorm B =
          (Real.sqrt (c₀ / (d + 2 : ℝ))) ^ (d + 1) *
            (exteriorFamilyMaxL2OpNorm B /
              (Fintype.card (ExteriorFamilyEntry (d + 1)) : ℝ)) := by
        rw [paperIsolatedCoefficientFactor]
        ring
      _ ≤ ‖MultiAffine.topCoeff
            (profile.paperIndicatorFreshPolynomial center z
              (paperIndicatorFreshAtoms N d start ω) B r I J)‖ :=
        hcoefficient

end PaperIndicatorWeights

end CircularLawSection4
