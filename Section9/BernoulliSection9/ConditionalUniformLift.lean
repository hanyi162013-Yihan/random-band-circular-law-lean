import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Uniform estimates with an independent random parameter

This module supplies the measure-theoretic bridge used when a theorem is
proved uniformly for every deterministic deformation, frame, or endpoint
parameter and that parameter is subsequently allowed to be random but
independent of the fresh packet variables.

The proof goes through regular conditional distributions.  Independence
identifies the conditional law of the fresh variable with its unconditional
law; the standard conditional-distribution integral formula then gives the
parameterized conditional expectation identity.  No regular conditional
probability or measurable-selection hypothesis is left to a caller beyond
the standard-Borel hypothesis on the fresh-variable state space.
-/

open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace BernoulliSection9

open MeasureTheory ProbabilityTheory

universe u v w z

/-- If `Q` and `X` are independent, the conditional distribution of `X`
given `Q` is the constant kernel carrying the unconditional law of `X`.

This is the kernel-level form of the random-parameter lifting principle. -/
theorem condDistrib_ae_eq_const_of_indepFun
    {Omega : Type u} {Param : Type v} {Fresh : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Param]
    [MeasurableSpace Fresh] [StandardBorelSpace Fresh] [Nonempty Fresh]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Q : Omega → Param) (X : Omega → Fresh)
    (hQ : AEMeasurable Q mu) (hX : AEMeasurable X mu)
    (h_indep : IndepFun Q X mu) :
    condDistrib X Q mu =ᵐ[mu.map Q]
      Kernel.const Param (mu.map X) := by
  apply (condDistrib_ae_eq_iff_measure_eq_compProd Q hX
    (Kernel.const Param (mu.map X))).2
  rw [Measure.compProd_const]
  exact h_indep.map_prod_eq_prod_map_map hQ hX

/-- Parameterized Fubini formula for independent random variables.  It is
often the shortest route when only an unconditional random-parameter bound
is needed. -/
theorem integral_parameterized_eq_integral_integral_map_of_indepFun
    {Omega : Type u} {Param : Type v} {Fresh : Type w} {E : Type z}
    [MeasurableSpace Omega] [MeasurableSpace Param] [MeasurableSpace Fresh]
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Q : Omega → Param) (X : Omega → Fresh)
    (hQ : AEMeasurable Q mu) (hX : AEMeasurable X mu)
    (h_indep : IndepFun Q X mu)
    (f : Param × Fresh → E) (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun omega ↦ f (Q omega, X omega)) mu) :
    ∫ omega, f (Q omega, X omega) ∂mu =
      ∫ q, ∫ x, f (q, x) ∂(mu.map X) ∂(mu.map Q) := by
  have hQX : AEMeasurable (fun omega ↦ (Q omega, X omega)) mu :=
    hQ.prodMk hX
  have hf_joint : Integrable f (mu.map fun omega ↦ (Q omega, X omega)) :=
    (integrable_map_measure hf.aestronglyMeasurable hQX).2 hf_int
  have hjoint := h_indep.map_prod_eq_prod_map_map hQ hX
  calc
    ∫ omega, f (Q omega, X omega) ∂mu =
        ∫ p, f p ∂(mu.map fun omega ↦ (Q omega, X omega)) := by
          symm
          exact integral_map hQX hf.aestronglyMeasurable
    _ = ∫ p, f p ∂((mu.map Q).prod (mu.map X)) := by rw [hjoint]
    _ = ∫ q, ∫ x, f (q, x) ∂(mu.map X) ∂(mu.map Q) := by
      rw [hjoint] at hf_joint
      exact integral_prod f hf_joint

/-- Conditional expectation of a jointly measurable function of an
independent random parameter and a fresh random variable.

The right side freezes the realized parameter and integrates only over the
unconditional law of the fresh variable. -/
theorem condExp_parameterized_ae_eq_integral_map_of_indepFun
    {Omega : Type u} {Param : Type v} {Fresh : Type w} {E : Type z}
    [MeasurableSpace Omega] [MeasurableSpace Param]
    [MeasurableSpace Fresh] [StandardBorelSpace Fresh] [Nonempty Fresh]
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Q : Omega → Param) (X : Omega → Fresh)
    (hQ : Measurable Q) (hX : AEMeasurable X mu)
    (h_indep : IndepFun Q X mu)
    (f : Param × Fresh → E) (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun omega ↦ f (Q omega, X omega)) mu) :
    mu[fun omega ↦ f (Q omega, X omega) |
        MeasurableSpace.comap Q inferInstance] =ᵐ[mu]
      fun omega ↦ ∫ x, f (Q omega, x) ∂(mu.map X) := by
  have hcond := condExp_prod_ae_eq_integral_condDistrib
    (μ := mu) hQ hX hf hf_int
  have hkernel := condDistrib_ae_eq_const_of_indepFun
    mu Q X hQ.aemeasurable hX h_indep
  have hkernel_comp : ∀ᵐ omega ∂mu,
      condDistrib X Q mu (Q omega) = Kernel.const Param (mu.map X) (Q omega) :=
    ae_of_ae_map hQ.aemeasurable hkernel
  refine hcond.trans ?_
  filter_upwards [hkernel_comp] with omega homega
  rw [homega, Kernel.const_apply]

/-- A uniform deterministic-parameter integral bound becomes an almost-sure
conditional bound after replacing that parameter by an independent random
one.  The deterministic hypothesis is stated directly against the law of
the fresh variable. -/
theorem condExp_parameterized_ae_le_of_indepFun
    {Omega : Type u} {Param : Type v} {Fresh : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Param]
    [MeasurableSpace Fresh] [StandardBorelSpace Fresh] [Nonempty Fresh]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Q : Omega → Param) (X : Omega → Fresh)
    (hQ : Measurable Q) (hX : AEMeasurable X mu)
    (h_indep : IndepFun Q X mu)
    (loss : Param × Fresh → Real) (hloss : StronglyMeasurable loss)
    (hloss_int : Integrable (fun omega ↦ loss (Q omega, X omega)) mu)
    (bound : Real)
    (h_uniform : ∀ q, ∫ x, loss (q, x) ∂(mu.map X) ≤ bound) :
    ∀ᵐ omega ∂mu,
      mu[fun eta ↦ loss (Q eta, X eta) |
          MeasurableSpace.comap Q inferInstance] omega ≤ bound := by
  have heq := condExp_parameterized_ae_eq_integral_map_of_indepFun
    mu Q X hQ hX h_indep loss hloss hloss_int
  filter_upwards [heq] with omega homega
  rw [homega]
  exact h_uniform (Q omega)

/-- Version of `condExp_parameterized_ae_le_of_indepFun` whose uniform
hypothesis is written on the original probability space, as in a fixed-
parameter theorem. -/
theorem condExp_parameterized_ae_le_of_fixed_integral_bound
    {Omega : Type u} {Param : Type v} {Fresh : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Param]
    [MeasurableSpace Fresh] [StandardBorelSpace Fresh] [Nonempty Fresh]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Q : Omega → Param) (X : Omega → Fresh)
    (hQ : Measurable Q) (hX : AEMeasurable X mu)
    (h_indep : IndepFun Q X mu)
    (loss : Param × Fresh → Real) (hloss : StronglyMeasurable loss)
    (hloss_int : Integrable (fun omega ↦ loss (Q omega, X omega)) mu)
    (bound : Real)
    (h_uniform : ∀ q, ∫ omega, loss (q, X omega) ∂mu ≤ bound) :
    ∀ᵐ omega ∂mu,
      mu[fun eta ↦ loss (Q eta, X eta) |
          MeasurableSpace.comap Q inferInstance] omega ≤ bound := by
  apply condExp_parameterized_ae_le_of_indepFun
    mu Q X hQ hX h_indep loss hloss hloss_int bound
  intro q
  rw [integral_map hX]
  · exact h_uniform q
  · exact (hloss.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable

/-- Unconditional consequence of the fixed-parameter uniform bound.  This is
the exact form needed when a deterministic theorem is uniform in a parameter
and the application substitutes an independent random parameter. -/
theorem integral_parameterized_le_of_fixed_integral_bound
    {Omega : Type u} {Param : Type v} {Fresh : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Param]
    [MeasurableSpace Fresh] [StandardBorelSpace Fresh] [Nonempty Fresh]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Q : Omega → Param) (X : Omega → Fresh)
    (hQ : Measurable Q) (hX : AEMeasurable X mu)
    (h_indep : IndepFun Q X mu)
    (loss : Param × Fresh → Real) (hloss : StronglyMeasurable loss)
    (hloss_int : Integrable (fun omega ↦ loss (Q omega, X omega)) mu)
    (bound : Real)
    (h_uniform : ∀ q, ∫ omega, loss (q, X omega) ∂mu ≤ bound) :
    ∫ omega, loss (Q omega, X omega) ∂mu ≤ bound := by
  have hcond := condExp_parameterized_ae_le_of_fixed_integral_bound
    mu Q X hQ hX h_indep loss hloss hloss_int bound h_uniform
  calc
    ∫ omega, loss (Q omega, X omega) ∂mu =
        ∫ omega,
          mu[fun eta ↦ loss (Q eta, X eta) |
            MeasurableSpace.comap Q inferInstance] omega ∂mu := by
      symm
      exact integral_condExp hQ.comap_le
    _ ≤ ∫ _omega, bound ∂mu :=
      integral_mono_ae integrable_condExp (integrable_const bound) hcond
    _ = bound := by simp

end BernoulliSection9
