import CircularLawSection4.RealInputComplexMultiaffine
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite independent products with non-identical coordinate laws

Conditioning independent complex atoms on their orthogonal coordinates leaves
the directional coordinates independent, but their conditional laws normally
depend on the corresponding orthogonal coordinate.  This module supplies the
heterogeneous (not necessarily identically distributed) product version of the
real multiaffine small-ball and logarithmic estimates.
-/

open scoped ENNReal MeasureTheory
open MeasureTheory Set

namespace CircularLawSection4

/-- Recursive product of the first `n` measures in a sequence. -/
noncomputable def independentMeasure (ν : ℕ → Measure ℝ)
    [∀ j, SFinite (ν j)] : (n : ℕ) → Measure (Fin n → ℝ)
  | 0 => Measure.dirac fun i => Fin.elim0 i
  | n + 1 => Measure.map joinLast ((independentMeasure ν n).prod (ν n))

theorem independentMeasure_isProbability (ν : ℕ → Measure ℝ)
    [∀ j, SFinite (ν j)] [∀ j, IsProbabilityMeasure (ν j)] :
    ∀ n, IsProbabilityMeasure (independentMeasure ν n)
  | 0 => by
      simp only [independentMeasure]
      infer_instance
  | n + 1 => by
      let _ := independentMeasure_isProbability ν n
      simp only [independentMeasure]
      exact Measure.isProbabilityMeasure_map measurable_joinLast.aemeasurable

/-- The recursive heterogeneous product is mathlib's finite product measure. -/
theorem independentMeasure_eq_pi (ν : ℕ → Measure ℝ)
    [∀ j, SigmaFinite (ν j)] :
    ∀ n, independentMeasure ν n = Measure.pi (fun i : Fin n => ν i)
  | 0 => by
      symm
      apply Measure.pi_eq
      intro s hs
      simp [independentMeasure]
  | n + 1 => by
      symm
      apply Measure.pi_eq
      intro s hs
      have hrect : MeasurableSet (Set.pi Set.univ s) :=
        MeasurableSet.pi Set.countable_univ (fun i _ => hs i)
      have hprefix : MeasurableSet
          (Set.pi Set.univ (fun i : Fin n => s i.castSucc)) :=
        MeasurableSet.pi Set.countable_univ (fun i _ => hs i.castSucc)
      have hpre :
          joinLast ⁻¹' Set.pi Set.univ s =
            Set.pi Set.univ (fun i : Fin n => s i.castSucc) ×ˢ
              s (Fin.last n) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
          Set.mem_prod]
        constructor
        · intro hy
          exact ⟨fun i => by simpa using hy i.castSucc,
            by simpa using hy (Fin.last n)⟩
        · rintro ⟨hp, hl⟩ i
          refine Fin.lastCases (by simpa using hl)
            (fun j => by simpa using hp j) i
      rw [independentMeasure, Measure.map_apply measurable_joinLast hrect,
        hpre, Measure.prod_prod, independentMeasure_eq_pi,
        Measure.pi_pi, Fin.prod_univ_castSucc]
      simp

theorem independentMeasure_prefixSmallBallConsistent
    (ν : ℕ → Measure ℝ) [∀ j, SFinite (ν j)]
    [∀ j, IsProbabilityMeasure (ν j)] :
    PrefixSmallBallConsistent (independentMeasure ν) := by
  intro n p r
  let _ := independentMeasure_isProbability ν n
  have hs : MeasurableSet (openSmallBall p r) :=
    measurableSet_openSmallBall_real p r
  rw [independentMeasure,
    Measure.map_apply measurable_joinLast (hs.preimage measurable_dropLast)]
  have hpre :
      joinLast ⁻¹' (MultiAffine.dropLast ⁻¹' openSmallBall p r) =
        Prod.fst ⁻¹' openSmallBall p r := by
    ext y
    simp only [mem_preimage, dropLast_joinLast]
  rw [hpre, ← Measure.map_apply measurable_fst hs, Measure.map_fst_prod]
  simp

theorem independentMeasure_oneCoordinateSmallBall_real
    (ν : ℕ → Measure ℝ) [∀ j, SFinite (ν j)]
    [∀ j, IsProbabilityMeasure (ν j)]
    {L : ℝ≥0∞} (hν : ∀ j, RealIntervalBound (ν j) L)
    {ρ : ℝ} (hρ : 0 < ρ) :
    OneCoordinateSmallBall (independentMeasure ν) ρ
      ((2 : ℝ≥0∞) * L * ENNReal.ofReal ρ) := by
  intro n p₀ p₁ ε hε
  let _ := independentMeasure_isProbability ν n
  let good : Set (Fin (n + 1) → ℝ) :=
    {x | ‖(MultiAffine.affine p₀ p₁).eval x‖ ≤ ε * ρ ∧
      ε ≤ ‖p₁.eval (MultiAffine.dropLast x)‖}
  have hgood : MeasurableSet good := by
    simpa only [good] using measurableSet_oneCoordinateEvent_real p₀ p₁ ε ρ
  change independentMeasure ν (n + 1) good ≤
    (2 : ℝ≥0∞) * L * ENNReal.ofReal ρ
  rw [independentMeasure, Measure.map_apply measurable_joinLast hgood,
    Measure.prod_apply (hgood.preimage measurable_joinLast)]
  calc
    (∫⁻ y, ν n (Prod.mk y ⁻¹' (joinLast ⁻¹' good))
        ∂independentMeasure ν n) ≤
        ∫⁻ _y : Fin n → ℝ,
          (2 : ℝ≥0∞) * L * ENNReal.ofReal ρ
          ∂independentMeasure ν n := by
      apply lintegral_mono
      intro y
      by_cases hslope : ε ≤ |p₁.eval y|
      · simpa [good, MultiAffine.eval_affine, Real.norm_eq_abs, hslope] using
          real_affine_smallBall_of_intervalBound (hν n) hρ.le hε hslope
      · simp [good, MultiAffine.eval_affine, Real.norm_eq_abs, hslope]
    _ = (2 : ℝ≥0∞) * L * ENNReal.ofReal ρ := by simp

/-- Heterogeneous independent real product small-ball estimate. -/
theorem independent_real_multiaffine_bound
    (ν : ℕ → Measure ℝ) [∀ j, SFinite (ν j)]
    [∀ j, IsProbabilityMeasure (ν j)]
    {L : ℝ≥0∞} (hν : ∀ j, RealIntervalBound (ν j) L)
    {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ} (p : MultiAffine ℝ (n + 1))
    (htop : 0 < ‖p.topCoeff‖) :
    independentMeasure ν (n + 1)
        (closedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) * L) *
        ENNReal.ofReal ρ := by
  exact closedSmallBall_topCoeff_le_mul_rho_of_oneCoordinate hρ
    (independentMeasure_prefixSmallBallConsistent ν)
    (independentMeasure_oneCoordinateSmallBall_real ν hν hρ) p htop

/-- Heterogeneous independent real product, complex-coefficient small ball. -/
theorem independent_realInput_complex_multiaffine_bound
    (ν : ℕ → Measure ℝ) [∀ j, SFinite (ν j)]
    [∀ j, IsProbabilityMeasure (ν j)]
    {L : ℝ≥0∞} (hν : ∀ j, RealIntervalBound (ν j) L)
    {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ} (p : MultiAffine ℂ (n + 1))
    (htop : 0 < ‖p.topCoeff‖) :
    independentMeasure ν (n + 1)
        (realInputClosedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) * ((4 : ℝ≥0∞) * L) *
        ENNReal.ofReal ρ := by
  have hprefix : RealInputPrefixSmallBallConsistent (independentMeasure ν) := by
    intro k q r
    let _ := independentMeasure_isProbability ν k
    have hs : MeasurableSet (realInputOpenSmallBall q r) :=
      measurableSet_realInputOpenSmallBall q r
    rw [independentMeasure,
      Measure.map_apply measurable_joinLast (hs.preimage measurable_dropLast)]
    have hpre :
        joinLast ⁻¹' (MultiAffine.dropLast ⁻¹' realInputOpenSmallBall q r) =
          Prod.fst ⁻¹' realInputOpenSmallBall q r := by
      ext y
      simp only [mem_preimage, dropLast_joinLast]
    rw [hpre, ← Measure.map_apply measurable_fst hs, Measure.map_fst_prod]
    simp
  have hone : RealInputOneCoordinateSmallBall (independentMeasure ν) ρ
      ((4 : ℝ≥0∞) * L * ENNReal.ofReal ρ) := by
    intro k p₀ p₁ ε hε
    let _ := independentMeasure_isProbability ν k
    let good : Set (Fin (k + 1) → ℝ) :=
      {x | ‖realInputEval (.affine p₀ p₁) x‖ ≤ ε * ρ ∧
        ε ≤ ‖realInputEval p₁ (MultiAffine.dropLast x)‖}
    have hgood : MeasurableSet good := by
      simpa only [good] using
        measurableSet_realInputOneCoordinateEvent p₀ p₁ ε ρ
    change independentMeasure ν (k + 1) good ≤
      (4 : ℝ≥0∞) * L * ENNReal.ofReal ρ
    rw [independentMeasure, Measure.map_apply measurable_joinLast hgood,
      Measure.prod_apply (hgood.preimage measurable_joinLast)]
    calc
      (∫⁻ y, ν k (Prod.mk y ⁻¹' (joinLast ⁻¹' good))
          ∂independentMeasure ν k) ≤
          ∫⁻ _y : Fin k → ℝ,
            (4 : ℝ≥0∞) * L * ENNReal.ofReal ρ
            ∂independentMeasure ν k := by
        apply lintegral_mono
        intro y
        by_cases hslope : ε ≤ ‖realInputEval p₁ y‖
        · simpa [good, realInputEval_affine, hslope] using
            complexAffine_realInput_smallBall_of_intervalBound
              (hν k) hρ.le hε hslope
        · simp [good, realInputEval_affine, hslope]
      _ = (4 : ℝ≥0∞) * L * ENNReal.ofReal ρ := by simp
  calc
    independentMeasure ν (n + 1)
        (realInputClosedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) *
        ((4 : ℝ≥0∞) * L * ENNReal.ofReal ρ) :=
      realInputClosedSmallBall_topCoeff_le hρ hprefix hone p htop
    _ = ((n + 1 : ℕ) : ℝ≥0∞) * ((4 : ℝ≥0∞) * L) *
        ENNReal.ofReal ρ := by ring

/-- Untruncated logarithmic loss for heterogeneous real coordinates and
complex coefficients. -/
theorem independent_realInput_complex_positiveLogLoss
    (ν : ℕ → Measure ℝ) [∀ j, SFinite (ν j)]
    [∀ j, IsProbabilityMeasure (ν j)]
    {L : ℝ} (hL : 0 ≤ L)
    (hν : ∀ j, RealIntervalBound (ν j) (ENNReal.ofReal L))
    {n : ℕ} (p : MultiAffine ℂ (n + 1))
    (htop : 0 < ‖p.topCoeff‖) :
    independentMeasure ν (n + 1)
        {x | ‖realInputEval p x‖ = 0} = 0 ∧
      (fun x => positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p x‖) =ᵐ[
        independentMeasure ν (n + 1)]
        (fun x => max 0
          (Real.log (‖p.topCoeff‖ / ‖realInputEval p x‖))) ∧
      Integrable
        (fun x => positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p x‖)
        (independentMeasure ν (n + 1)) ∧
      ∫ x, positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p x‖
          ∂independentMeasure ν (n + 1) ≤
        (Real.log (max 1 (((n + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
          (((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  let _ := independentMeasure_isProbability ν (n + 1)
  apply zeroSet_aeLog_and_integrable_positiveLogLoss_of_power_smallBall
    (independentMeasure ν (n + 1))
    (fun x => ‖realInputEval p x‖) p.continuous_realInputEval.norm.measurable
    (fun x => norm_nonneg _)
    ‖p.topCoeff‖ (((n + 1 : ℕ) : ℝ) * (4 * L)) htop
    (n + 1) 1 (Nat.succ_pos n) Nat.one_pos
  intro ρ hρ
  change independentMeasure ν (n + 1)
      (realInputClosedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤ _
  calc
    independentMeasure ν (n + 1)
        (realInputClosedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) *
          ((4 : ℝ≥0∞) * ENNReal.ofReal L) * ENNReal.ofReal ρ :=
      independent_realInput_complex_multiaffine_bound ν hν hρ p htop
    _ = ENNReal.ofReal
        ((((n + 1 : ℕ) : ℝ) * (4 * L)) * ρ ^ 1) := by
      rw [pow_one, ← ENNReal.ofReal_natCast (n + 1),
        ← ENNReal.ofReal_ofNat 4,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
        ← ENNReal.ofReal_mul (Nat.cast_nonneg (n + 1)),
        ← ENNReal.ofReal_mul
          (mul_nonneg (Nat.cast_nonneg (n + 1))
            (mul_nonneg (by norm_num) hL))]

/-- Finite-family presentation of the heterogeneous small-ball estimate. -/
theorem pi_realInput_complex_multiaffine_bound
    {n : ℕ} (μ : Fin (n + 1) → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] [∀ i, IsProbabilityMeasure (μ i)]
    {L : ℝ≥0∞} (hμ : ∀ i, RealIntervalBound (μ i) L)
    {ρ : ℝ} (hρ : 0 < ρ) (p : MultiAffine ℂ (n + 1))
    (htop : 0 < ‖p.topCoeff‖) :
    Measure.pi μ
        (realInputClosedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) * ((4 : ℝ≥0∞) * L) *
        ENNReal.ofReal ρ := by
  let ν : ℕ → Measure ℝ := fun j => μ (Fin.ofNat (n + 1) j)
  have hν : ∀ j, RealIntervalBound (ν j) L := fun j => hμ _
  have hmeasure : independentMeasure ν (n + 1) = Measure.pi μ := by
    rw [independentMeasure_eq_pi]
    congr 1
    funext i
    simpa [ν, Fin.ofNat_eq_cast]
  rw [← hmeasure]
  exact independent_realInput_complex_multiaffine_bound ν hν hρ p htop

/-- Finite-family presentation of the untruncated logarithmic estimate. -/
theorem pi_realInput_complex_positiveLogLoss
    {n : ℕ} (μ : Fin (n + 1) → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] [∀ i, IsProbabilityMeasure (μ i)]
    {L : ℝ} (hL : 0 ≤ L)
    (hμ : ∀ i, RealIntervalBound (μ i) (ENNReal.ofReal L))
    (p : MultiAffine ℂ (n + 1)) (htop : 0 < ‖p.topCoeff‖) :
    Measure.pi μ {x | ‖realInputEval p x‖ = 0} = 0 ∧
      (fun x => positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p x‖) =ᵐ[
        Measure.pi μ]
        (fun x => max 0
          (Real.log (‖p.topCoeff‖ / ‖realInputEval p x‖))) ∧
      Integrable
        (fun x => positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p x‖)
        (Measure.pi μ) ∧
      ∫ x, positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p x‖
          ∂Measure.pi μ ≤
        (Real.log (max 1 (((n + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
          (((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  let ν : ℕ → Measure ℝ := fun j => μ (Fin.ofNat (n + 1) j)
  have hν : ∀ j, RealIntervalBound (ν j) (ENNReal.ofReal L) := fun j => hμ _
  have hmeasure : independentMeasure ν (n + 1) = Measure.pi μ := by
    rw [independentMeasure_eq_pi]
    congr 1
    funext i
    simpa [ν, Fin.ofNat_eq_cast]
  rw [← hmeasure]
  exact independent_realInput_complex_positiveLogLoss ν hL hν p htop

end CircularLawSection4
