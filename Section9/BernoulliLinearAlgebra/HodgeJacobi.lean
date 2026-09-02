import BernoulliLinearAlgebra.VolumeComparison

/-!
# Hodge--Jacobi complementary-minor control

This file isolates the Hodge--Jacobi step in Section 9.4.1.  Mathlib has the
adjugate formula for first-order cofactors, but currently has no general
Jacobi theorem identifying every `k`-minor of a nonsingular inverse with the
complementary `(n-k)`-minor of the original matrix.

`ComplementaryMinorCertificate` records exactly that missing entrywise
identity, including its unit-modulus sign/phase.  Everything after this
certificate is proved here: complementary subsets reindex the complete
Hilbert--Schmidt sum, giving

`‖∧^k E⁻¹‖_HS = ‖det E‖⁻¹ ‖∧^(n-k) E‖_HS`,

and uniform determinant/compound bounds produce the `ExteriorConditioning`
needed by `gramVolume_remove_left`.  Thus instantiating the certificate with
a future general Jacobi-minor theorem is the only remaining library-facing
gap; no estimate or summation argument is assumed.
-/

open scoped BigOperators Matrix Matrix.Norms.Frobenius

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix Set Set.powersetCard

section ComplementReindex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reindexing both subset variables by complement and exchanging their
roles preserves the complete double sum.  The exchange is the transpose in
Jacobi's complementary-minor identity. -/
theorem sum_complement_complement_swap {k m : ℕ}
    (hm : m + k = Fintype.card ι)
    (f : powersetCard ι m → powersetCard ι m → ℝ) :
    (∑ s : powersetCard ι k, ∑ t : powersetCard ι k,
        f (powersetCard.compl hm t) (powersetCard.compl hm s)) =
      ∑ u : powersetCard ι m, ∑ v : powersetCard ι m, f u v := by
  let c : powersetCard ι k ≃ powersetCard ι m := powersetCard.compl hm
  calc
    (∑ s : powersetCard ι k, ∑ t : powersetCard ι k,
        f (c t) (c s)) =
        ∑ s : powersetCard ι k, ∑ u : powersetCard ι m, f u (c s) := by
          apply Finset.sum_congr rfl
          intro s _
          exact c.sum_comp (fun u ↦ f u (c s))
    _ = ∑ v : powersetCard ι m, ∑ u : powersetCard ι m, f u v :=
      c.sum_comp (fun v ↦ ∑ u : powersetCard ι m, f u v)
    _ = ∑ u : powersetCard ι m, ∑ v : powersetCard ι m, f u v :=
      Finset.sum_comm

end ComplementReindex

section Certificate

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- An entrywise Jacobi complementary-minor certificate.

For row set `s` and column set `t`, the corresponding inverse minor is the
complementary minor with row and column roles exchanged, multiplied by
`det(E)⁻¹` and a unit-modulus phase.  Over an ordered finite basis that phase
is the usual sign. -/
structure ComplementaryMinorCertificate (E : Matrix ι ι ℂ)
    (k m : ℕ) (hm : m + k = Fintype.card ι) where
  det_isUnit : IsUnit E.det
  phase : powersetCard ι k → powersetCard ι k → ℂ
  phase_norm : ∀ s t, ‖phase s t‖ = 1
  jacobi : ∀ s t,
    minor k E⁻¹ s t =
      phase s t * ((E.det)⁻¹ *
        minor m E (powersetCard.compl hm t) (powersetCard.compl hm s))

/-- Taking absolute values removes the Jacobi sign/phase. -/
theorem ComplementaryMinorCertificate.minor_norm
    {E : Matrix ι ι ℂ} {k m : ℕ}
    {hm : m + k = Fintype.card ι}
    (h : ComplementaryMinorCertificate E k m hm)
    (s t : powersetCard ι k) :
    ‖minor k E⁻¹ s t‖ =
      ‖E.det‖⁻¹ *
        ‖minor m E (powersetCard.compl hm t)
          (powersetCard.compl hm s)‖ := by
  rw [h.jacobi, norm_mul, norm_mul, h.phase_norm, one_mul, norm_inv]

/-- Squared Frobenius energy form of Hodge--Jacobi duality. -/
theorem ComplementaryMinorCertificate.compoundEnergyReal_inverse_eq
    {E : Matrix ι ι ℂ} {k m : ℕ}
    {hm : m + k = Fintype.card ι}
    (h : ComplementaryMinorCertificate E k m hm) :
    compoundEnergyReal k E⁻¹ =
      ‖E.det‖⁻¹ ^ 2 * compoundEnergyReal m E := by
  rw [compoundEnergyReal_eq_sum_normSq,
    compoundEnergyReal_eq_sum_normSq]
  calc
    (∑ s : powersetCard ι k, ∑ t : powersetCard ι k,
        Complex.normSq (minor k E⁻¹ s t)) =
        ∑ s : powersetCard ι k, ∑ t : powersetCard ι k,
          ‖E.det‖⁻¹ ^ 2 *
            Complex.normSq
              (minor m E (powersetCard.compl hm t)
                (powersetCard.compl hm s)) := by
          apply Finset.sum_congr rfl
          intro s _
          apply Finset.sum_congr rfl
          intro t _
          rw [Complex.normSq_eq_norm_sq, h.minor_norm s t, mul_pow,
            ← Complex.normSq_eq_norm_sq]
    _ = ‖E.det‖⁻¹ ^ 2 *
        (∑ s : powersetCard ι k, ∑ t : powersetCard ι k,
          Complex.normSq
            (minor m E (powersetCard.compl hm t)
              (powersetCard.compl hm s))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.mul_sum]
    _ = ‖E.det‖⁻¹ ^ 2 *
        (∑ u : powersetCard ι m, ∑ v : powersetCard ι m,
          Complex.normSq (minor m E u v)) := by
          congr 1
          exact sum_complement_complement_swap hm
            (fun u v ↦ Complex.normSq (minor m E u v))

/-- Frobenius-norm form of the exact Hodge identity used in the paper. -/
theorem ComplementaryMinorCertificate.compound_inverse_norm_eq
    {E : Matrix ι ι ℂ} {k m : ℕ}
    {hm : m + k = Fintype.card ι}
    (h : ComplementaryMinorCertificate E k m hm) :
    ‖compound k E⁻¹‖ = ‖E.det‖⁻¹ * ‖compound m E‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))]
  simpa only [compoundEnergyReal, mul_pow] using
    h.compoundEnergyReal_inverse_eq

/-- A certificate plus separate determinant and complementary-compound
bounds gives the corresponding inverse-compound bound. -/
theorem ComplementaryMinorCertificate.compound_inverse_norm_le
    {E : Matrix ι ι ℂ} {k m : ℕ}
    {hm : m + k = Fintype.card ι}
    (h : ComplementaryMinorCertificate E k m hm)
    {D L : ℝ} (hD : 0 ≤ D)
    (hdet : ‖E.det‖⁻¹ ≤ D) (hcomp : ‖compound m E‖ ≤ L) :
    ‖compound k E⁻¹‖ ≤ D * L := by
  rw [h.compound_inverse_norm_eq]
  exact mul_le_mul hdet hcomp (norm_nonneg _) hD

end Certificate

section ConditioningConstructor

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- Uniform complementary-minor certificates and a bound for their exact
Hodge products construct the `ExteriorConditioning` consumed by the volume
comparison module. -/
theorem exteriorConditioning_of_complementaryMinorCertificates
    {E : Matrix ι ι ℂ} {K : ℝ}
    (hK : 1 ≤ K)
    (hforward : ∀ q : ℕ, ‖compound q E‖ ≤ K)
    (hcert : ∀ (k : ℕ) (hk : k ≤ Fintype.card ι),
      ComplementaryMinorCertificate E k (Fintype.card ι - k)
        (Nat.sub_add_cancel hk))
    (hproduct : ∀ (k : ℕ) (_hk : k ≤ Fintype.card ι),
      ‖E.det‖⁻¹ * ‖compound (Fintype.card ι - k) E‖ ≤ K) :
    ExteriorConditioning E K where
  det_isUnit := (hcert 0 (Nat.zero_le _)).det_isUnit
  one_le := hK
  forward := hforward
  inverse := by
    intro k
    by_cases hk : k ≤ Fintype.card ι
    · exact (hcert k hk).compound_inverse_norm_eq.trans_le (hproduct k hk)
    · have hcard : Fintype.card ι < k := Nat.lt_of_not_ge hk
      have hzero : compound k E⁻¹ = 0 := by
        ext s
        exact ((not_le_of_gt hcard) (by
          rw [← s.prop]
          exact Finset.card_le_univ s.val)).elim
      rw [hzero, norm_zero]
      exact le_trans zero_le_one hK

/-- A convenient quantitative constructor.  If all compounds of `E` are at
most `L` and `‖det E‖⁻¹ ≤ D`, the common conditioning constant may be taken
as `max 1 (max L (D * L))`. -/
theorem exteriorConditioning_of_hodgeBounds
    {E : Matrix ι ι ℂ} {D L : ℝ}
    (hD : 0 ≤ D)
    (hdet : ‖E.det‖⁻¹ ≤ D)
    (hforward : ∀ q : ℕ, ‖compound q E‖ ≤ L)
    (hcert : ∀ (k : ℕ) (hk : k ≤ Fintype.card ι),
      ComplementaryMinorCertificate E k (Fintype.card ι - k)
        (Nat.sub_add_cancel hk)) :
    ExteriorConditioning E (max 1 (max L (D * L))) := by
  apply exteriorConditioning_of_complementaryMinorCertificates
  · exact le_max_left _ _
  · intro q
    exact (hforward q).trans (le_trans (le_max_left _ _) (le_max_right _ _))
  · exact hcert
  · intro k hk
    have hmul :
        ‖E.det‖⁻¹ * ‖compound (Fintype.card ι - k) E‖ ≤ D * L :=
      mul_le_mul hdet (hforward _) (norm_nonneg _) hD
    exact hmul.trans (le_trans (le_max_right _ _) (le_max_right _ _))

end ConditioningConstructor

end BernoulliLinearAlgebra
