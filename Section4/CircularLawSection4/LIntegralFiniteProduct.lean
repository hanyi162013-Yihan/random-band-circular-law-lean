import Mathlib.MeasureTheory.Integral.Pi

/-!
# `lintegral` of a finite coordinate product

The Bochner-integral analogue is available in mathlib.  This extended
nonnegative version is useful for identifying finite products of conditional
probability laws without imposing finiteness on the individual integrals.
-/

open MeasureTheory
open scoped ENNReal MeasureTheory BigOperators

namespace CircularLawSection4

/-- Tonelli factorization for a finite product of nonnegative measurable
coordinate functions. -/
theorem lintegral_fin_prod_eq_prod {n : ℕ} {E : Type*}
    [MeasurableSpace E]
    (mu : Fin n → Measure E) [∀ i, SigmaFinite (mu i)]
    (f : Fin n → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi mu =
      ∏ i, ∫⁻ y, f i y ∂mu i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp := measurePreserving_piFinSuccAbove mu 0
      rw [hp.symm.lintegral_map_equiv]
      simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk,
        Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      rw [MeasureTheory.lintegral_prod]
      · have hg : Measurable (fun y : Fin n → E =>
            ∏ i, f (Fin.succ i) (y i)) :=
          Finset.measurable_prod _ fun i _ =>
            (hf (Fin.succ i)).comp (measurable_pi_apply i)
        simp only [Prod.fst, Prod.snd]
        rw [show (fun x : E => ∫⁻ y : Fin n → E,
              f 0 x * ∏ i, f (Fin.succ i) (y i)
                ∂Measure.pi (fun j => mu (Fin.succ j))) =
            (fun x : E => f 0 x * ∫⁻ y : Fin n → E,
              ∏ i, f (Fin.succ i) (y i)
                ∂Measure.pi (fun j => mu (Fin.succ j))) by
          funext x
          exact lintegral_const_mul (f 0 x) hg]
        rw [ih (fun j => mu (Fin.succ j)) (fun j => f (Fin.succ j))
          (fun j => hf (Fin.succ j))]
        rw [lintegral_mul_const _ (hf 0)]
      · fun_prop

end CircularLawSection4
