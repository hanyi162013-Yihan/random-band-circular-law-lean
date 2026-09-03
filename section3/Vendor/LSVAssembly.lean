/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/LSVAssembly.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.QuadraticLinearization
import Vendor.FiniteProbability

/-! The final distance-to-span and finite-union step, without model-specific interfaces. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace HighBandLSV

variable {Omega : Type*} [MeasurableSpace Omega]

theorem lsv_probability_from_cover {N : Nat} (hN : 0 < N)
    (mu : Measure Omega) (X : Omega → Matrix (Fin N) (Fin N) Complex)
    (z : Complex) (R s Bcol Bbad : Real) (good cap : Set Omega)
    (hcap : hsEvent X R ⊆ cap)
    (hbad : mu (cap \ good) ≤ ENNReal.ofReal Bbad)
    (hcol : ∀ j, mu (closedColumnEvent (fun w => shifted (X w) z)
      (s * Real.sqrt N) j ∩ good) ≤ ENNReal.ofReal Bcol) :
    mu (leastSingularBadEvent (fun w => shifted (X w) z) s ∩ hsEvent X R) ≤
      ENNReal.ofReal ((N : Real) * Bcol) + ENNReal.ofReal Bbad := by
  classical
  let E : Fin N → Set Omega := fun j =>
    closedColumnEvent (fun w => shifted (X w) z) (s * Real.sqrt N) j ∩ good
  have hcover : leastSingularBadEvent (fun w => shifted (X w) z) s ∩ hsEvent X R ⊆
      (⋃ j, E j) ∪ (cap \ good) := by
    intro w hw
    by_cases hg : w ∈ good
    · obtain ⟨j, hj⟩ := small_lsv_implies_close_column hN (shifted (X w) z) hw.1
      exact Or.inl (Set.mem_iUnion.mpr ⟨j, hj, hg⟩)
    · exact Or.inr ⟨hcap hw.2, hg⟩
  have hsum : mu (⋃ j, E j) ≤ ENNReal.ofReal ((N : Real) * Bcol) := by
    calc
      mu (⋃ j, E j) ≤ ∑ j, mu (E j) := measure_iUnion_fintype_le mu E
      _ ≤ ∑ _j : Fin N, ENNReal.ofReal Bcol := Finset.sum_le_sum (fun j _ => hcol j)
      _ = ENNReal.ofReal ((N : Real) * Bcol) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg N)]
        simp
  exact (measure_mono hcover).trans ((measure_union_le _ _).trans (add_le_add hsum hbad))

theorem prefactor_threshold_bound {P N W kappa t : Real}
    (hP : 0 < P) (ht : 0 ≤ t)
    (hlog : Real.log P ≤ Section5Formalization.finalExponentGap N W kappa) :
    P * (tau N W kappa t / delta N W kappa) ≤ t := by
  have hexp : P * Real.exp (-Section5Formalization.finalExponentGap N W kappa) ≤ 1 := by
    calc
      P * Real.exp (-Section5Formalization.finalExponentGap N W kappa) =
          Real.exp (Real.log P - Section5Formalization.finalExponentGap N W kappa) := by
            rw [Real.exp_sub, Real.exp_log hP, Real.exp_neg]
            rfl
      _ ≤ 1 := Real.exp_le_one_iff.mpr (sub_nonpos.mpr hlog)
  rw [threshold_ratio]
  have hmul := mul_le_mul_of_nonneg_left hexp ht
  simpa [Section5Formalization.finalExponentGap, mul_assoc, mul_left_comm, mul_comm] using hmul

theorem dimension_loss_column_union_bound {N W kappa t D : Real}
    (hN : 0 < N) (hW : 0 < W) (ht : 0 ≤ t) (hD : 0 ≤ D)
    (hlog : Real.log (dimensionLossColumnPrefactor N W) ≤
      Section5Formalization.finalExponentGap N W kappa) :
    N * (D * Real.sqrt N * Real.sqrt W * (tau N W kappa t * Real.sqrt N) /
      delta N W kappa) ≤ D * t := by
  have hP : 0 < dimensionLossColumnPrefactor N W := by
    unfold dimensionLossColumnPrefactor columnPrefactor
    positivity
  have hb := prefactor_threshold_bound hP ht hlog
  calc
    _ = D * (dimensionLossColumnPrefactor N W *
        (tau N W kappa t / delta N W kappa)) := by
      unfold dimensionLossColumnPrefactor columnPrefactor
      ring
    _ ≤ D * t := mul_le_mul_of_nonneg_left hb hD

end HighBandLSV

#print axioms HighBandLSV.lsv_probability_from_cover
#print axioms HighBandLSV.dimension_loss_column_union_bound

