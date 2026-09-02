import CircularLawSection4.MultiaffineUntruncated
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Directional conditional densities

This module formalizes the conditional-density branch through an explicit
Markov-kernel interface.  The outer variable is the collection of all
orthogonal components `V`.  Conditional on `V = v`, the scalar directional
components `U` have a recursive IID product law whose one-dimensional law
satisfies a uniform interval bound.
-/

open scoped ENNReal MeasureTheory ProbabilityTheory Topology
open Set MeasureTheory Filter Measure ProbabilityTheory

namespace CircularLawSection4

/-- The untruncated real IID theorem with an abstract interval bound, rather
than a `withDensity` presentation. -/
theorem iid_real_positiveLogLoss_of_intervalBound
    (ν : Measure ℝ) [SFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ} (hL : 0 ≤ L)
    (hν : RealIntervalBound ν (ENNReal.ofReal L))
    {n : ℕ} (p : MultiAffine ℝ (n + 1))
    (htop : 0 < ‖p.topCoeff‖) :
    iidMeasure ν (n + 1) {x | ‖p.eval x‖ = 0} = 0 ∧
      (fun x => positiveLogLoss ‖p.topCoeff‖ ‖p.eval x‖) =ᵐ[iidMeasure ν (n + 1)]
        (fun x => max 0 (Real.log (‖p.topCoeff‖ / ‖p.eval x‖))) ∧
      Integrable (fun x => positiveLogLoss ‖p.topCoeff‖ ‖p.eval x‖)
        (iidMeasure ν (n + 1)) ∧
      ∫ x, positiveLogLoss ‖p.topCoeff‖ ‖p.eval x‖ ∂iidMeasure ν (n + 1) ≤
        (Real.log (max 1 (((n + 1 : ℕ) : ℝ) * (2 * L))) + 1) /
          (((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  let _ := iidMeasure_isProbability ν (n + 1)
  apply zeroSet_aeLog_and_integrable_positiveLogLoss_of_power_smallBall
    (iidMeasure ν (n + 1))
    (fun x => ‖p.eval x‖) p.continuous_eval_real.norm.measurable
    (fun x => norm_nonneg _)
    ‖p.topCoeff‖ (((n + 1 : ℕ) : ℝ) * (2 * L)) htop
    (n + 1) 1 (Nat.succ_pos n) Nat.one_pos
  intro ρ hρ
  change iidMeasure ν (n + 1)
      (closedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤ _
  calc
    iidMeasure ν (n + 1)
        (closedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) *
          ((2 : ℝ≥0∞) * ENNReal.ofReal L) * ENNReal.ofReal ρ :=
      iid_real_multiaffine_bound ν hν hρ p htop
    _ = ENNReal.ofReal
        ((((n + 1 : ℕ) : ℝ) * (2 * L)) * ρ ^ 1) := by
      rw [pow_one, ← ENNReal.ofReal_natCast (n + 1),
        ← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_mul zero_le_two,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg (n + 1)),
        ← ENNReal.ofReal_mul
          (mul_nonneg (Nat.cast_nonneg (n + 1)) (mul_nonneg zero_le_two hL))]

/-- An explicit conditional-product interface at a fixed number of scalar
directional coordinates.  The equality field exposes the exact trust
boundary: measurability is supplied by the Markov kernel, while every fiber
is certified to be the recursive IID law of its conditional coordinate
measure. -/
structure DirectionalIIDKernel (V : Type*) [MeasurableSpace V] (k : ℕ) where
  vLaw : ProbabilityMeasure V
  coordinateLaw : V → ProbabilityMeasure ℝ
  conditionalULaw : Kernel V (Fin k → ℝ)
  conditionalULaw_isMarkov : IsMarkovKernel conditionalULaw
  conditionalULaw_eq_iid : ∀ v,
    conditionalULaw v = iidMeasure (coordinateLaw v : Measure ℝ) k

namespace DirectionalIIDKernel

variable {V : Type*} [MeasurableSpace V] {k : ℕ}

/-- The actual joint law of `(V,U)` obtained from the outer law and the
conditional kernel. -/
noncomputable def jointMeasure (M : DirectionalIIDKernel V k) :
    Measure (V × (Fin k → ℝ)) :=
  (M.vLaw : Measure V) ⊗ₘ M.conditionalULaw

theorem jointMeasure_isProbability (M : DirectionalIIDKernel V k) :
    IsProbabilityMeasure M.jointMeasure := by
  let _ := M.conditionalULaw_isMarkov
  unfold jointMeasure
  infer_instance

end DirectionalIIDKernel

/-- The joint small-ball event for a family of multiaffine polynomials whose
coefficients may depend on the conditioned variable `v`. -/
def directionalClosedSmallBall {V : Type*} [MeasurableSpace V] {k : ℕ}
    (p : V → MultiAffine ℝ k) (ρ : ℝ) : Set (V × (Fin k → ℝ)) :=
  {z | ‖(p z.1).eval z.2‖ ≤ ‖(p z.1).topCoeff‖ * ρ ^ k}

/-- Conditional small-ball followed by averaging over all orthogonal
components. -/
theorem directional_joint_smallBall_le
    {V : Type*} [MeasurableSpace V] {n : ℕ}
    (M : DirectionalIIDKernel V (n + 1))
    {L : ℝ} (hL : 0 ≤ L)
    (hinterval : ∀ v,
      RealIntervalBound (M.coordinateLaw v : Measure ℝ) (ENNReal.ofReal L))
    {ρ : ℝ} (hρ : 0 < ρ)
    (p : V → MultiAffine ℝ (n + 1))
    (htop : ∀ v, 0 < ‖(p v).topCoeff‖)
    (hmeas : MeasurableSet (directionalClosedSmallBall p ρ)) :
    M.jointMeasure (directionalClosedSmallBall p ρ) ≤
      ENNReal.ofReal ((((n + 1 : ℕ) : ℝ) * (2 * L)) * ρ) := by
  let _ := M.conditionalULaw_isMarkov
  rw [DirectionalIIDKernel.jointMeasure, Measure.compProd_apply hmeas]
  calc
    (∫⁻ v, M.conditionalULaw v
        (Prod.mk v ⁻¹' directionalClosedSmallBall p ρ) ∂(M.vLaw : Measure V)) ≤
      ∫⁻ _v : V,
        ENNReal.ofReal ((((n + 1 : ℕ) : ℝ) * (2 * L)) * ρ)
          ∂(M.vLaw : Measure V) := by
      apply lintegral_mono
      intro v
      change M.conditionalULaw v
          (Prod.mk v ⁻¹' directionalClosedSmallBall p ρ) ≤ _
      rw [M.conditionalULaw_eq_iid v]
      change iidMeasure (M.coordinateLaw v : Measure ℝ) (n + 1)
          (closedSmallBall (p v) (‖(p v).topCoeff‖ * ρ ^ (n + 1))) ≤ _
      calc
        iidMeasure (M.coordinateLaw v : Measure ℝ) (n + 1)
            (closedSmallBall (p v) (‖(p v).topCoeff‖ * ρ ^ (n + 1))) ≤
          ((n + 1 : ℕ) : ℝ≥0∞) *
              ((2 : ℝ≥0∞) * ENNReal.ofReal L) * ENNReal.ofReal ρ :=
          iid_real_multiaffine_bound (M.coordinateLaw v : Measure ℝ)
            (hinterval v) hρ (p v) (htop v)
        _ = ENNReal.ofReal ((((n + 1 : ℕ) : ℝ) * (2 * L)) * ρ) := by
          rw [← ENNReal.ofReal_natCast (n + 1),
            ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_mul zero_le_two,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg (n + 1)),
            ← ENNReal.ofReal_mul
              (mul_nonneg (Nat.cast_nonneg (n + 1)) (mul_nonneg zero_le_two hL))]
    _ = ENNReal.ofReal ((((n + 1 : ℕ) : ℝ) * (2 * L)) * ρ) := by simp

/-- The untruncated logarithmic loss on the joint `(V,U)` space. -/
noncomputable def directionalPositiveLogLoss
    {V : Type*} [MeasurableSpace V] {k : ℕ}
    (p : V → MultiAffine ℝ k) (z : V × (Fin k → ℝ)) : ℝ :=
  positiveLogLoss ‖(p z.1).topCoeff‖ ‖(p z.1).eval z.2‖

/-- Directional-density branch, including the removal of the zero set and
the untruncated logarithmic expectation.  The measurability assumptions are
stated only for the two scalar quantities that the conclusion uses; no
measurable structure on the syntax type `MultiAffine` is hidden. -/
theorem directional_joint_positiveLogLoss
    {V : Type*} [MeasurableSpace V] {n : ℕ}
    (M : DirectionalIIDKernel V (n + 1))
    {L : ℝ} (hL : 0 ≤ L)
    (hinterval : ∀ v,
      RealIntervalBound (M.coordinateLaw v : Measure ℝ) (ENNReal.ofReal L))
    (p : V → MultiAffine ℝ (n + 1))
    (htop : ∀ v, 0 < ‖(p v).topCoeff‖)
    (heval : Measurable
      (fun z : V × (Fin (n + 1) → ℝ) => ‖(p z.1).eval z.2‖))
    (htopMeas : Measurable (fun v => ‖(p v).topCoeff‖)) :
    M.jointMeasure {z | ‖(p z.1).eval z.2‖ = 0} = 0 ∧
      (fun z => directionalPositiveLogLoss p z) =ᵐ[M.jointMeasure]
        (fun z => max 0
          (Real.log (‖(p z.1).topCoeff‖ / ‖(p z.1).eval z.2‖))) ∧
      Integrable (fun z => directionalPositiveLogLoss p z) M.jointMeasure ∧
      ∫ z, directionalPositiveLogLoss p z ∂M.jointMeasure ≤
        (Real.log (max 1 (((n + 1 : ℕ) : ℝ) * (2 * L))) + 1) /
          (((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  let _ := M.conditionalULaw_isMarkov
  let _ : IsProbabilityMeasure M.jointMeasure := M.jointMeasure_isProbability
  have hloss : Measurable (fun z => directionalPositiveLogLoss p z) := by
    unfold directionalPositiveLogLoss positiveLogLoss
    exact measurable_const.max
      ((Real.measurable_log.comp (htopMeas.comp measurable_fst)).sub
        (Real.measurable_log.comp heval))
  have hzeroMeas : MeasurableSet {z : V × (Fin (n + 1) → ℝ) |
      ‖(p z.1).eval z.2‖ = 0} := measurableSet_eq_fun heval measurable_const
  have hfiberZero : ∀ v, M.conditionalULaw v
      (Prod.mk v ⁻¹' {z : V × (Fin (n + 1) → ℝ) |
        ‖(p z.1).eval z.2‖ = 0}) = 0 := by
    intro v
    rw [M.conditionalULaw_eq_iid v]
    have hv := iid_real_positiveLogLoss_of_intervalBound
      (M.coordinateLaw v : Measure ℝ) hL (hinterval v) (p v) (htop v)
    exact hv.1
  have hzero : M.jointMeasure {z | ‖(p z.1).eval z.2‖ = 0} = 0 := by
    rw [DirectionalIIDKernel.jointMeasure,
      Measure.compProd_apply hzeroMeas]
    simp_rw [hfiberZero]
    simp
  refine ⟨hzero, ?_, ?_⟩
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with z hz
    apply positiveLogLoss_eq_log_div (htop z.1)
    have hne : ‖(p z.1).eval z.2‖ ≠ 0 := by
      simpa only [Set.mem_ofPred_eq] using hz
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  · have hkR : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    apply integrable_and_expectation_le_of_exponential_tail M.jointMeasure
      (fun z => directionalPositiveLogLoss p z) hloss
      (fun z => positiveLogLoss_nonneg _ _)
      (((n + 1 : ℕ) : ℝ) * (2 * L))
      (((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) (div_pos (by norm_num) hkR)
    intro t ht
    let ρ : ℝ := Real.exp (-t / ((n + 1 : ℕ) : ℝ))
    have hρ : 0 < ρ := Real.exp_pos _
    have hρpow : ρ ^ (n + 1) = Real.exp (-t) := by
      dsimp [ρ]
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp [ne_of_gt hkR]
    have hρrate :
        ρ = Real.exp
          ((-(((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) * t) := by
      dsimp [ρ]
      congr 1
      field_simp [ne_of_gt hkR]
      norm_num
    have htailMeas : MeasurableSet
        {z | t < directionalPositiveLogLoss p z} :=
      measurableSet_lt measurable_const hloss
    rw [DirectionalIIDKernel.jointMeasure,
      Measure.compProd_apply htailMeas]
    calc
      (∫⁻ v, M.conditionalULaw v
          (Prod.mk v ⁻¹' {z | t < directionalPositiveLogLoss p z})
          ∂(M.vLaw : Measure V)) ≤
        ∫⁻ _v : V, ENNReal.ofReal
          ((((n + 1 : ℕ) : ℝ) * (2 * L)) *
            Real.exp ((-(((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) * t))
          ∂(M.vLaw : Measure V) := by
        apply lintegral_mono
        intro v
        change M.conditionalULaw v
            {u | t < positiveLogLoss ‖(p v).topCoeff‖ ‖(p v).eval u‖} ≤ _
        rw [M.conditionalULaw_eq_iid v]
        calc
          iidMeasure (M.coordinateLaw v : Measure ℝ) (n + 1)
              {u | t < positiveLogLoss ‖(p v).topCoeff‖ ‖(p v).eval u‖} ≤
            iidMeasure (M.coordinateLaw v : Measure ℝ) (n + 1)
              (closedSmallBall (p v)
                (‖(p v).topCoeff‖ * ρ ^ (n + 1))) := by
              apply measure_mono
              intro u hu
              change ‖(p v).eval u‖ ≤ ‖(p v).topCoeff‖ * ρ ^ (n + 1)
              have hle := positiveLogLoss_tail_imp_radius_le
                (htop v) (norm_nonneg _) ht hu
              simpa only [hρpow] using hle
          _ ≤ ((n + 1 : ℕ) : ℝ≥0∞) *
                ((2 : ℝ≥0∞) * ENNReal.ofReal L) * ENNReal.ofReal ρ :=
            iid_real_multiaffine_bound (M.coordinateLaw v : Measure ℝ)
              (hinterval v) hρ (p v) (htop v)
          _ = ENNReal.ofReal
              ((((n + 1 : ℕ) : ℝ) * (2 * L)) *
                Real.exp
                  ((-(((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) * t)) := by
            rw [hρrate, ← ENNReal.ofReal_natCast (n + 1),
              ← ENNReal.ofReal_ofNat 2,
              ← ENNReal.ofReal_mul zero_le_two,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg (n + 1)),
              ← ENNReal.ofReal_mul
                (mul_nonneg (Nat.cast_nonneg (n + 1))
                  (mul_nonneg zero_le_two hL))]
      _ = ENNReal.ofReal
          ((((n + 1 : ℕ) : ℝ) * (2 * L)) *
            Real.exp ((-(((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) * t)) := by simp

end CircularLawSection4
