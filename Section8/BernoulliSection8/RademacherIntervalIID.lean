import BernoulliSection8.RademacherEnergy
import BernoulliSection9.InterfaceOperatorControl
import BernoulliSection10.PhysicalProbabilityInstances
import BernoulliSection10.FiniteIIDCoordinates

/-! # Literal Rademacher interval square families -/

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator NNReal

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10 BernoulliLinearAlgebra

/-- All unnormalized atoms of the physical interval as a Section 9 iid family. -/
def rademacherIntervalFamily (W s : ℕ) :
    IidSubgaussianFamily (IntervalRows W s) (intervalRowsLaw W s rademacherLaw)
      (Fin (s * W) × Fin (3 * W)) where
  atom p x := x p.1 p.2
  measurable_atom p := by fun_prop
  independent := by
    apply (iIndepFun_iff_map_fun_eq_pi_map
      (f := fun (p : Fin (s * W) × Fin (3 * W)) (x : IntervalRows W s) => x p.1 p.2)
      (fun p =>
        (intervalAtom_measurePreserving rademacherLaw W s p.1 p.2).measurable.aemeasurable)).2
    have hmap (p : Fin (s * W) × Fin (3 * W)) :
        Measure.map (fun x : IntervalRows W s => x p.1 p.2)
          (intervalRowsLaw W s rademacherLaw) = rademacherLaw :=
      (intervalAtom_measurePreserving rademacherLaw W s p.1 p.2).map_eq
    simp_rw [hmap]
    exact (measurePreserving_iid_uncurry rademacherLaw).map_eq
  identically_distributed p q :=
    ⟨(intervalAtom_measurePreserving rademacherLaw W s p.1 p.2).measurable.aemeasurable,
      (intervalAtom_measurePreserving rademacherLaw W s q.1 q.2).measurable.aemeasurable,
      (intervalAtom_measurePreserving rademacherLaw W s p.1 p.2).map_eq.trans
        (intervalAtom_measurePreserving rademacherLaw W s q.1 q.2).map_eq.symm⟩
  centered p := by
    exact (real_integral_comp_measurePreserving
      (intervalAtom_measurePreserving rademacherLaw W s p.1 p.2)
      measurable_id).trans rademacherLaw_mean_zero
  variance_one p := by
    exact (real_integral_comp_measurePreserving
      (intervalAtom_measurePreserving rademacherLaw W s p.1 p.2)
      (by fun_prop : Measurable (fun x : ℝ => x ^ 2))).trans
      rademacherLaw_second_moment
  subgaussianParameter := 1
  subgaussian p := by
    have hp := intervalAtom_measurePreserving rademacherLaw W s p.1 p.2
    apply (HasSubgaussianMGF.id_map_iff hp.measurable.aemeasurable).mp
    rw [hp.map_eq]
    exact rademacherLaw_subgaussian

/-- Select every entry in one of the three blocks of a specified site. -/
def intervalSquareEntryEmbedding {W s : ℕ} (j : Fin s) (b : Fin 3) :
    (Fin W × Fin W) ↪ (Fin (s * W) × Fin (3 * W)) where
  toFun p := (intervalRowIndex j p.1, physicalAtomIndex b p.2)
  inj' := by
    intro p q h
    have hrow := congrArg Prod.fst h
    have hcol := congrArg Prod.snd h
    exact Prod.ext
      (Prod.mk.inj (finProdFinEquiv.injective hrow)).2
      (Prod.mk.inj (finProdFinEquiv.injective hcol)).2

/-- A literal independent Rademacher square, with no matrix-law certificate
left for the caller. Block labels 0,1,2 are B,A,C. -/
def rademacherIntervalSquare (W s : ℕ) (j : Fin s) (b : Fin 3) :
    IidSubgaussianSquare (IntervalRows W s)
      (intervalRowsLaw W s rademacherLaw) W :=
  (rademacherIntervalFamily W s).squareRestriction
    (intervalSquareEntryEmbedding j b)

@[simp] theorem rademacherIntervalSquare_subgaussianParameter
    (W s : ℕ) (j : Fin s) (b : Fin 3) :
    (rademacherIntervalSquare W s j b).subgaussianParameter = 1 := rfl

@[simp] theorem rademacherIntervalSquare_opNormConstant
    (W s : ℕ) (j : Fin s) (b : Fin 3) :
    subgaussianOpNormConstant (rademacherIntervalSquare W s j b) =
      40 * Real.sqrt 2 := by
  norm_num [subgaussianOpNormConstant, subgaussianEnvelope]

end BernoulliSection8
