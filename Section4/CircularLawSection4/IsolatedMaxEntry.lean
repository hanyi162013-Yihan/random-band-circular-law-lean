import CircularLawSection4.ArbitraryResetWord

/-!
# Choosing the isolated exterior entry

The manuscript chooses an exterior degree and two basis coordinates carrying
a large matrix entry before applying the singleton reset word.  This module
performs that finite choice inside Lean for the concrete Boolean support
model.  The comparison made here is with the maximum coordinate-entry norm;
the analytic comparison between that norm and the Euclidean operator norm is
kept separate.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

/-- A dependent index for one matrix entry in one exterior degree. -/
abbrev ExteriorFamilyEntry (d : ℕ) :=
  Σ q : ExteriorDegree d, ExteriorIndex d q × ExteriorIndex d q

/-- The empty exterior coordinate supplies a canonical family entry. -/
def emptyExteriorIndex (d : ℕ) : ExteriorIndex d (0 : ExteriorDegree d) :=
  ⟨∅, by simp⟩

instance exteriorFamilyEntryNonempty (d : ℕ) : Nonempty (ExteriorFamilyEntry d) :=
  ⟨⟨0, emptyExteriorIndex d, emptyExteriorIndex d⟩⟩

/-- Maximum modulus of all coordinate entries in an exterior family. -/
noncomputable def exteriorFamilyMaxEntryNorm {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun e : ExteriorFamilyEntry d =>
    ‖B e.1 e.2.2 e.2.1‖

/-- Some degree and coordinate pair attain the finite maximum entry norm. -/
theorem exists_entry_eq_exteriorFamilyMaxEntryNorm {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ) :
    ∃ r : ExteriorDegree d, ∃ I J : ExteriorIndex d r,
      ‖B r J I‖ = exteriorFamilyMaxEntryNorm B := by
  classical
  obtain ⟨e, _, he⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty : (Finset.univ : Finset (ExteriorFamilyEntry d)).Nonempty)
    (fun e : ExteriorFamilyEntry d => ‖B e.1 e.2.2 e.2.1‖)
  rcases e with ⟨r, I, J⟩
  exact ⟨r, I, J, by simpa [exteriorFamilyMaxEntryNorm] using he.symm⟩

/-- End-to-end isolated full-monomial lower bound in the Boolean support
model, with the maximizing degree and entry chosen internally. -/
theorem exists_isolated_booleanSupport_maxEntry_lower_bound {d : ℕ}
    (weight : ResetLabel d → ℂ)
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (bmin : ℝ) (hbmin : 0 ≤ bmin)
    (hweight : ∀ ℓ : ResetLabel d, bmin ≤ ‖weight ℓ‖) :
    ∃ r : ExteriorDegree d, ∃ I J : ExteriorIndex d r,
      bmin ^ d * exteriorFamilyMaxEntryNorm B ≤
        ‖weightedFullMonomialCoefficient weight B booleanSupportK
          (arbitrarySupportWord I J)‖ := by
  obtain ⟨r, I, J, hentry⟩ := exists_entry_eq_exteriorFamilyMaxEntryNorm B
  refine ⟨r, I, J, ?_⟩
  apply isolated_booleanSupport_arbitrary_lower_bound
    weight B r I J bmin (exteriorFamilyMaxEntryNorm B) hbmin
  · intro t
    exact hweight _
  · exact hentry.ge
  · rw [← hentry]
    exact norm_nonneg _

end CircularLawSection4
