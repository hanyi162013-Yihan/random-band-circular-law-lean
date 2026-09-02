import CircularLawSection4.OrderedCoefficientL2Contraction
import CircularLawSection4.OperatorNormMaxEntry

/-!
# Isolated entries for the actual ordered coefficient family

The arbitrary-endpoint singleton certificate for the actual ordered
reset/star matrices is used to transport the Boolean isolated-entry bounds
to `orderedCoefficient` itself.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

/-- Exact modulus of an arbitrary entry isolated by the actual ordered
coefficient word. -/
theorem norm_fullMonomialCoefficient_orderedCoefficient_arbitrary_eq
    {d : ℕ}
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (r : ExteriorDegree (d + 1))
    (I J : ExteriorIndex (d + 1) r) :
    ‖fullMonomialCoefficient B (orderedCoefficient d)
      (arbitrarySupportWord I J)‖ = ‖B r J I‖ := by
  simpa using norm_fullMonomialCoefficient_eq_of_singleton B
    (orderedCoefficient d) (arbitrarySupportWord I J) r I J
    (orderedCoefficient_arbitrarySingletonCertificate r I J)

/-- Quantitative arbitrary-entry isolation for the actual ordered
coefficient family. -/
theorem isolated_orderedCoefficient_arbitrary_lower_bound
    {d : ℕ} (weight : ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (r : ExteriorDegree (d + 1))
    (I J : ExteriorIndex (d + 1) r)
    (bmin entryLower : ℝ) (hbmin : 0 ≤ bmin)
    (hweight : ∀ t : Fin (d + 1),
      bmin ≤ ‖weight (arbitrarySupportWord I J t)‖)
    (hentry : entryLower ≤ ‖B r J I‖)
    (hentry_nonneg : 0 ≤ entryLower) :
    bmin ^ (d + 1) * entryLower ≤
      ‖weightedFullMonomialCoefficient weight B (orderedCoefficient d)
        (arbitrarySupportWord I J)‖ := by
  exact isolated_full_monomial_lower_bound weight B (orderedCoefficient d)
    (arbitrarySupportWord I J) r I J
    (orderedCoefficient_arbitrarySingletonCertificate r I J)
    bmin entryLower hbmin hweight hentry hentry_nonneg

/-- End-to-end maximal-entry lower bound for the actual ordered coefficient
family, with the maximizing degree and coordinates chosen internally. -/
theorem exists_isolated_orderedCoefficient_maxEntry_lower_bound
    {d : ℕ} (weight : ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (bmin : ℝ) (hbmin : 0 ≤ bmin)
    (hweight : ∀ ell : ResetLabel (d + 1), bmin ≤ ‖weight ell‖) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        bmin ^ (d + 1) * exteriorFamilyMaxEntryNorm B ≤
          ‖weightedFullMonomialCoefficient weight B (orderedCoefficient d)
            (arbitrarySupportWord I J)‖ := by
  obtain ⟨r, I, J, hentry⟩ :=
    exists_entry_eq_exteriorFamilyMaxEntryNorm B
  refine ⟨r, I, J, ?_⟩
  apply isolated_orderedCoefficient_arbitrary_lower_bound
    weight B r I J bmin (exteriorFamilyMaxEntryNorm B) hbmin
  · intro t
    exact hweight _
  · exact hentry.ge
  · rw [← hentry]
    exact norm_nonneg _

/-- End-to-end maximal Euclidean operator-norm lower bound for the actual
ordered coefficient family. -/
theorem exists_isolated_orderedCoefficient_maxL2OpNorm_lower_bound
    {d : ℕ} (weight : ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (bmin : ℝ) (hbmin : 0 ≤ bmin)
    (hweight : ∀ ell : ResetLabel (d + 1), bmin ≤ ‖weight ell‖) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        bmin ^ (d + 1) *
            (exteriorFamilyMaxL2OpNorm B /
              (Fintype.card (ExteriorFamilyEntry (d + 1)) : ℝ)) ≤
          ‖weightedFullMonomialCoefficient weight B (orderedCoefficient d)
            (arbitrarySupportWord I J)‖ := by
  obtain ⟨r, I, J, hcoefficient⟩ :=
    exists_isolated_orderedCoefficient_maxEntry_lower_bound
      weight B bmin hbmin hweight
  refine ⟨r, I, J, ?_⟩
  apply le_trans _ hcoefficient
  exact mul_le_mul_of_nonneg_left
    (exteriorFamilyMaxL2OpNorm_div_familyEntryCard_le_maxEntry B)
    (pow_nonneg hbmin (d + 1))

end CircularLawSection4
