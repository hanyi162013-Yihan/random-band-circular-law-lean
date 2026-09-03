import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Manuscript (3.1): inserting deterministic entries preserves independence

This elementary lemma supplies the off-band zeros of the actual matrix.
No extra random coordinates or enlarged sample space are assumed.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
namespace ShortRingAnchor

/-- Manuscript (3.1), entry independence: a mutually independent subfamily
remains independent after inserting deterministic constants elsewhere. -/
theorem iIndepFun_of_constant_outside
    {Omega I E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (f : I → Omega → E) (p : I → Prop) (c : I → E)
    (hactive : iIndepFun (fun i : Subtype p => f i.val) mu)
    (hconstant : ∀ i, ¬ p i → ∀ sample, f i sample = c i) :
    iIndepFun f mu := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  by_cases hbad : ∃ i ∈ S, ¬ p i ∧ c i ∉ sets i
  · obtain ⟨i, hi, hpi, hci⟩ := hbad
    have hempty : f i ⁻¹' sets i = ∅ := by
      ext sample
      simp [hconstant i hpi sample, hci]
    have hinter : (⋂ j ∈ S, f j ⁻¹' sets j) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro sample hs
      have h := mem_iInter₂.mp hs i hi
      simp only [hempty, mem_empty_iff_false] at h
    rw [hinter, measure_empty]
    symm
    apply Finset.prod_eq_zero hi
    rw [hempty, measure_empty]
  · have hgood : ∀ i ∈ S, ¬ p i → c i ∈ sets i := by
      intro i hi hpi
      by_contra hci
      exact hbad ⟨i, hi, hpi, hci⟩
    have hinactive (i : I) (hi : i ∈ S) (hpi : ¬ p i) :
        f i ⁻¹' sets i = univ := by
      ext sample
      simp [hconstant i hpi sample, hgood i hi hpi]
    have hinter : (⋂ i ∈ S, f i ⁻¹' sets i) =
        ⋂ i ∈ S.subtype p, f i.val ⁻¹' sets i.val := by
      ext sample
      constructor
      · intro hs
        apply mem_iInter₂.mpr
        intro i hi
        exact mem_iInter₂.mp hs i.val (by simpa using hi)
      · intro hs
        apply mem_iInter₂.mpr
        intro i hi
        by_cases hpi : p i
        · exact mem_iInter₂.mp hs ⟨i, hpi⟩ (by simpa using hi)
        · rw [hinactive i hi hpi]
          trivial
    rw [hinter, hactive.measure_inter_preimage_eq_mul (S.subtype p)
      (sets := fun i => sets i.val) (fun i hi => hsets i.val (by simpa using hi))]
    rw [Finset.prod_subtype_eq_prod_filter (fun i => mu (f i ⁻¹' sets i))]
    apply Finset.prod_filter_of_ne
    intro i hi hne
    by_contra hpi
    apply hne
    rw [hinactive i hi hpi, measure_univ]

end ShortRingAnchor
