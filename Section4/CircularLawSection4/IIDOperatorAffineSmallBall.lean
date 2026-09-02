import CircularLawSection4.OperatorAffineLog
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Operator-affine small-ball bounds under finite IID laws

This file identifies the recursively constructed `iidMeasure` with the
standard finite product measure.  The standard product-measure coordinate
splitting equivalence can then freeze every coordinate except an arbitrary
chosen one, so the one-coordinate operator-affine bounds apply without
requiring that the chosen coordinate be last.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace CircularLawSection4

universe u w x

section IIDProduct

variable {K : Type u} [MeasurableSpace K]

/-- The recursive finite IID law agrees with mathlib's finite product
measure. -/
theorem iidMeasure_eq_pi (ν : Measure K) [SigmaFinite ν] :
    ∀ n : ℕ, iidMeasure ν n = Measure.pi (fun _ : Fin n => ν) := by
  intro n
  induction n with
  | zero =>
      symm
      apply Measure.pi_eq
      intro s hs
      simp [iidMeasure]
  | succ n ih =>
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
        · rintro ⟨hprefix', hlast⟩ i
          refine Fin.lastCases (by simpa using hlast)
            (fun j => by simpa using hprefix' j) i
      rw [iidMeasure, Measure.map_apply measurable_joinLast hrect, hpre,
        Measure.prod_prod, ih, Measure.pi_pi,
        Fin.prod_univ_castSucc]

end IIDProduct

section Measurability

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type w} {F : Type x}
variable [NormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- A finite operator-affine expression is continuous in all of its scalar
coordinates. -/
theorem continuous_operatorAffine_fin {n : ℕ} (b : Fin n → 𝕜)
    (M : Fin n → E →L[𝕜] F) (z : 𝕜) (M₀ : E →L[𝕜] F) :
    Continuous (fun ξ : Fin n → 𝕜 => operatorAffine b ξ M z M₀) := by
  unfold operatorAffine
  fun_prop

/-- The lower-tail event for a finite operator-affine expression is
measurable. -/
theorem measurableSet_operatorAffine_norm_le {n : ℕ} (b : Fin n → 𝕜)
    (M : Fin n → E →L[𝕜] F) (z : 𝕜) (M₀ : E →L[𝕜] F) (r : ℝ) :
    MeasurableSet {ξ : Fin n → 𝕜 | ‖operatorAffine b ξ M z M₀‖ ≤ r} := by
  change MeasurableSet
    ((fun ξ : Fin n → 𝕜 => ‖operatorAffine b ξ M z M₀‖) ⁻¹' Set.Iic r)
  exact (continuous_operatorAffine_fin b M z M₀).norm.measurable measurableSet_Iic

end Measurability

section ArbitraryCoordinate

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type w} {F : Type x}
variable [NormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- Fubini lifting principle for an operator-affine lower-tail bound at an
arbitrary coordinate of a finite recursive IID vector. -/
theorem iid_operatorAffine_smallBall_of_oneCoordinate
    {ν : Measure 𝕜} [SigmaFinite ν] [IsProbabilityMeasure ν]
    {n : ℕ} (s : Fin (n + 1)) (b : Fin (n + 1) → 𝕜)
    (M : Fin (n + 1) → E →L[𝕜] F) (z : 𝕜) (M₀ : E →L[𝕜] F)
    {ε ρ : ℝ} {C : ℝ≥0∞}
    (hone : ∀ R : E →L[𝕜] F,
      ν {u | ‖R + (b s * u) • M s‖ ≤ ε * ρ} ≤ C) :
    iidMeasure ν (n + 1)
        {ξ | ‖operatorAffine b ξ M z M₀‖ ≤ ε * ρ} ≤ C := by
  let good : Set (Fin (n + 1) → 𝕜) :=
    {ξ | ‖operatorAffine b ξ M z M₀‖ ≤ ε * ρ}
  have hgood : MeasurableSet good := by
    simpa only [good] using
      measurableSet_operatorAffine_norm_le b M z M₀ (ε * ρ)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => 𝕜) s
  have hpres : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) => ν))
      (ν.prod (Measure.pi (fun _ : Fin n => ν))) := by
    simpa only [e] using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ν) s)
  rw [iidMeasure_eq_pi, ← hpres.symm.map_eq,
    Measure.map_apply e.symm.measurable hgood,
    Measure.prod_apply_symm (hgood.preimage e.symm.measurable)]
  calc
    (∫⁻ y, ν ((fun u => (u, y)) ⁻¹' (e.symm ⁻¹' good))
        ∂Measure.pi (fun _ : Fin n => ν)) ≤
        ∫⁻ _y : Fin n → 𝕜, C ∂Measure.pi (fun _ : Fin n => ν) := by
      apply lintegral_mono
      intro y
      let R : E →L[𝕜] F :=
        (∑ j : Fin n, (b (s.succAbove j) * y j) • M (s.succAbove j)) -
          z • M₀
      have haffine (u : 𝕜) :
          operatorAffine b (s.insertNth u y) M z M₀ =
            R + (b s * u) • M s := by
        rw [operatorAffine, s.sum_univ_succAbove]
        simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        dsimp only [R]
        abel
      have hsection :
          (fun u => (u, y)) ⁻¹' (e.symm ⁻¹' good) =
            {u | ‖R + (b s * u) • M s‖ ≤ ε * ρ} := by
        ext u
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, good, e,
          MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
        change ‖operatorAffine b (s.insertNth u y) M z M₀‖ ≤ ε * ρ ↔
          ‖R + (b s * u) • M s‖ ≤ ε * ρ
        rw [haffine]
      change ν ((fun u => (u, y)) ⁻¹' (e.symm ⁻¹' good)) ≤ C
      rw [hsection]
      exact hone R
    _ = C := by simp

end ArbitraryCoordinate

section RealBound

variable {E : Type w} {F : Type x}
variable [NormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [NormedSpace ℝ E] [NormedSpace ℝ F]

/-- Real bounded-density small-ball estimate for an operator-affine function
of a finite IID vector, using any prescribed coordinate. -/
theorem real_iid_operatorAffine_arbitraryCoordinate_smallBall
    {ν : Measure ℝ} [SigmaFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ≥0∞} (hν : RealIntervalBound ν L)
    {n : ℕ} (s : Fin (n + 1)) (b : Fin (n + 1) → ℝ)
    (M : Fin (n + 1) → E →L[ℝ] F) (z : ℝ) (M₀ : E →L[ℝ] F)
    (x : E) (ell : StrongDual ℝ F) (hx : ‖x‖ ≤ 1) (hell : ‖ell‖ ≤ 1)
    {ε ρ : ℝ} (hρ : 0 ≤ ρ) (hε : 0 < ε)
    (hslope : ε ≤ |b s * ell (M s x)|) :
    iidMeasure ν (n + 1)
        {ξ | ‖operatorAffine b ξ M z M₀‖ ≤ ε * ρ} ≤
      (2 : ℝ≥0∞) * L * ENNReal.ofReal ρ := by
  apply iid_operatorAffine_smallBall_of_oneCoordinate s b M z M₀
  intro R
  exact real_operatorAffine_oneCoordinate_smallBall
    hν R (M s) (b s) x ell hx hell hρ hε hslope

end RealBound

section ComplexBound

variable {E : Type w} {F : Type x}
variable [NormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [NormedSpace ℂ E] [NormedSpace ℂ F]

/-- Complex bounded-density small-ball estimate for an operator-affine
function of a finite IID vector, using any prescribed coordinate. -/
theorem complex_iid_operatorAffine_arbitraryCoordinate_smallBall
    {ν : Measure ℂ} [SigmaFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ≥0∞} (hν : ComplexBallBound ν L)
    {n : ℕ} (s : Fin (n + 1)) (b : Fin (n + 1) → ℂ)
    (M : Fin (n + 1) → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F)
    (x : E) (ell : StrongDual ℂ F) (hx : ‖x‖ ≤ 1) (hell : ‖ell‖ ≤ 1)
    {ε ρ : ℝ} (hρ : 0 ≤ ρ) (hε : 0 < ε)
    (hslope : ε ≤ ‖b s * ell (M s x)‖) :
    iidMeasure ν (n + 1)
        {ξ | ‖operatorAffine b ξ M z M₀‖ ≤ ε * ρ} ≤
      ENNReal.ofReal Real.pi * L * ENNReal.ofReal ρ ^ 2 := by
  apply iid_operatorAffine_smallBall_of_oneCoordinate s b M z M₀
  intro R
  exact complex_operatorAffine_oneCoordinate_smallBall
    hν R (M s) (b s) x ell hx hell hρ hε hslope

end ComplexBound

end CircularLawSection4
