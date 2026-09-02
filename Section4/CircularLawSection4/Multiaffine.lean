import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.NoncommRing

/-!
# The multiaffine small-ball induction from Section 4

This file formalizes the recursive algebra and the probabilistic induction in
the manuscript's multiaffine density lemma.  Its two explicit upstream inputs
are the integrated `OneCoordinateSmallBall` estimate at positive scales and
the open-small-ball marginal identity `PrefixSmallBallConsistent`.  Deriving
them from independent bounded-density product laws (including measurability
and Fubini) is not claimed here; they are theorem parameters, not axioms.
-/

open scoped ENNReal
open MeasureTheory Set

namespace CircularLawSection4

universe u

/-- A recursively presented polynomial that is affine in each of `n` variables.

`affine p₀ p₁` represents `p₀(x) + xₙ * p₁(x)`.  Thus every constructor adds
one fresh variable, and no variable can occur with power greater than one. -/
inductive MultiAffine (R : Type u) : ℕ → Type u where
  | const (c : R) : MultiAffine R 0
  | affine {n : ℕ} (p₀ p₁ : MultiAffine R n) : MultiAffine R (n + 1)

namespace MultiAffine

variable {R : Type u}

/-- Delete the last coordinate of a vector. -/
def dropLast {n : ℕ} (x : Fin (n + 1) → R) : Fin n → R :=
  fun i => x i.castSucc

/-- Evaluation of a recursive multiaffine polynomial. -/
def eval [Semiring R] : {n : ℕ} → MultiAffine R n → (Fin n → R) → R
  | 0, const c, _ => c
  | _ + 1, affine p₀ p₁, x =>
      eval p₀ (dropLast x) + x (Fin.last _) * eval p₁ (dropLast x)

/-- Coefficient of the full monomial `x₀ ⋯ xₙ₋₁`. -/
def topCoeff [Semiring R] : {n : ℕ} → MultiAffine R n → R
  | 0, const c => c
  | _ + 1, affine _ p₁ => topCoeff p₁

@[simp] theorem eval_const [Semiring R] (c : R) (x : Fin 0 → R) :
    eval (const c) x = c := rfl

@[simp] theorem eval_affine [Semiring R] {n : ℕ}
    (p₀ p₁ : MultiAffine R n) (x : Fin (n + 1) → R) :
    eval (affine p₀ p₁) x =
      eval p₀ (dropLast x) + x (Fin.last n) * eval p₁ (dropLast x) := rfl

@[simp] theorem topCoeff_const [Semiring R] (c : R) :
    topCoeff (const c) = c := rfl

@[simp] theorem topCoeff_affine [Semiring R] {n : ℕ}
    (p₀ p₁ : MultiAffine R n) :
    topCoeff (affine p₀ p₁) = topCoeff p₁ := rfl

/-- Changing only the fresh last coordinate changes evaluation linearly, with
slope equal to the evaluation of `p₁` on the frozen prefix. -/
theorem eval_updateLast_sub [Ring R] {n : ℕ} (p₀ p₁ : MultiAffine R n)
    (x : Fin (n + 1) → R) (a b : R) :
    eval (affine p₀ p₁) (Function.update x (Fin.last n) a) -
        eval (affine p₀ p₁) (Function.update x (Fin.last n) b) =
      (a - b) * eval p₁ (dropLast x) := by
  simp only [eval_affine]
  have hdrop (c : R) :
      dropLast (Function.update x (Fin.last n) c) = dropLast x := by
    funext i
    simp [dropLast, Fin.castSucc_ne_last]
  rw [hdrop a, hdrop b]
  simp
  noncomm_ring

end MultiAffine

section SmallBall

variable {K : Type u} [SeminormedRing K] [MeasurableSpace K]

/-- The closed small-ball event for a multiaffine polynomial. -/
def closedSmallBall {n : ℕ} (p : MultiAffine K n) (r : ℝ) : Set (Fin n → K) :=
  {x | ‖p.eval x‖ ≤ r}

/-- The open small-ball event.  The strict version is what makes the
zero-variable base case empty even when the radius is the top coefficient. -/
def openSmallBall {n : ℕ} (p : MultiAffine K n) (r : ℝ) : Set (Fin n → K) :=
  {x | ‖p.eval x‖ < r}

/-- The exact marginal-consistency input used by the induction: forgetting
the fresh last coordinate preserves every recursive open-small-ball event.

Independent product laws are the intended source of this equality.  Their
construction, including the required measurability/Fubini facts, is kept as
an explicit upstream interface rather than hidden in this definition. -/
def PrefixSmallBallConsistent
    (μ : (n : ℕ) → Measure (Fin n → K)) : Prop :=
  ∀ (n : ℕ) (p : MultiAffine K n) (r : ℝ),
    μ (n + 1) (MultiAffine.dropLast ⁻¹' openSmallBall p r) =
      μ n (openSmallBall p r)

/-- The integrated one-coordinate analytic input used by the induction.

At every *positive* slope threshold `ε`, the event that the affine expression
lies in a ball of radius `ε * ρ` while its frozen slope has norm at least `ε`
has cost at most `δ`.  Deriving this integrated statement from independent
real/complex variables of bounded density is an explicit upstream task; once
it is supplied, the theorem below proves the complete `k * δ` induction. -/
def OneCoordinateSmallBall
    (μ : (n : ℕ) → Measure (Fin n → K)) (ρ : ℝ) (δ : ℝ≥0∞) : Prop :=
  ∀ (n : ℕ) (p₀ p₁ : MultiAffine K n) (ε : ℝ),
    0 < ε → μ (n + 1)
        {x | ‖(MultiAffine.affine p₀ p₁).eval x‖ ≤ ε * ρ ∧
          ε ≤ ‖p₁.eval (MultiAffine.dropLast x)‖} ≤ δ

/-- One induction step: a small value either occurs with a sufficiently large
fresh slope (cost `δ`) or the recursively defined slope polynomial is itself
small. -/
theorem oneStep_closedSmallBall
    {μ : (n : ℕ) → Measure (Fin n → K)} {ρ : ℝ} {δ : ℝ≥0∞}
    (hprefix : PrefixSmallBallConsistent μ)
    (hone : OneCoordinateSmallBall μ ρ δ)
    {n : ℕ} (p₀ p₁ : MultiAffine K n) (ε : ℝ) (hε : 0 < ε) :
    μ (n + 1) (closedSmallBall (MultiAffine.affine p₀ p₁) (ε * ρ)) ≤
      δ + μ n (openSmallBall p₁ ε) := by
  let good : Set (Fin (n + 1) → K) :=
    {x | ‖(MultiAffine.affine p₀ p₁).eval x‖ ≤ ε * ρ ∧
      ε ≤ ‖p₁.eval (MultiAffine.dropLast x)‖}
  let bad : Set (Fin (n + 1) → K) :=
    MultiAffine.dropLast ⁻¹' openSmallBall p₁ ε
  have hsub :
      closedSmallBall (MultiAffine.affine p₀ p₁) (ε * ρ) ⊆ good ∪ bad := by
    intro x hx
    simp only [closedSmallBall, mem_ofPred_eq] at hx
    simp only [good, bad, mem_union, mem_ofPred_eq, mem_preimage, openSmallBall]
    by_cases hslope : ε ≤ ‖p₁.eval (MultiAffine.dropLast x)‖
    · exact Or.inl ⟨hx, hslope⟩
    · exact Or.inr (lt_of_not_ge hslope)
  have hgood : μ (n + 1) good ≤ δ := by
    simpa only [good] using hone n p₀ p₁ ε hε
  have hbad : μ (n + 1) bad = μ n (openSmallBall p₁ ε) := by
    simpa only [bad] using hprefix n p₁ ε
  calc
    μ (n + 1) (closedSmallBall (MultiAffine.affine p₀ p₁) (ε * ρ)) ≤
        μ (n + 1) (good ∪ bad) := measure_mono hsub
    _ ≤ μ (n + 1) good + μ (n + 1) bad := measure_union_le _ _
    _ ≤ δ + μ n (openSmallBall p₁ ε) :=
      add_le_add hgood (le_of_eq hbad)

/-- The recursive open-ball estimate.  Its zero-dimensional base case is
empty, and every fresh coordinate adds exactly one copy of `δ`. -/
theorem openSmallBall_topCoeff_le
    {μ : (n : ℕ) → Measure (Fin n → K)} {ρ : ℝ} {δ : ℝ≥0∞}
    (hρ : 0 < ρ) (hprefix : PrefixSmallBallConsistent μ)
    (hone : OneCoordinateSmallBall μ ρ δ) :
    ∀ {n : ℕ} (p : MultiAffine K n),
      0 < ‖p.topCoeff‖ →
        μ n (openSmallBall p (‖p.topCoeff‖ * ρ ^ n)) ≤
          (n : ℝ≥0∞) * δ := by
  intro n p htop
  induction p with
  | const c =>
      simp [openSmallBall]
  | @affine n p₀ p₁ ih₀ ih₁ =>
      have htop₁ : 0 < ‖p₁.topCoeff‖ := by simpa using htop
      have hscale : 0 < ‖p₁.topCoeff‖ * ρ ^ n :=
        mul_pos htop₁ (pow_pos hρ n)
      have hsub :
          openSmallBall (MultiAffine.affine p₀ p₁)
              (‖p₁.topCoeff‖ * ρ ^ (n + 1)) ⊆
            closedSmallBall (MultiAffine.affine p₀ p₁)
              ((‖p₁.topCoeff‖ * ρ ^ n) * ρ) := by
        intro x hx
        have hx' :
            ‖(MultiAffine.affine p₀ p₁).eval x‖ <
              ‖p₁.topCoeff‖ * ρ ^ (n + 1) := by
          simpa only [openSmallBall, mem_ofPred_eq] using hx
        simpa only [closedSmallBall, mem_ofPred_eq, pow_succ, mul_assoc] using
          le_of_lt hx'
      calc
        μ (n + 1) (openSmallBall (MultiAffine.affine p₀ p₁)
            (‖(MultiAffine.affine p₀ p₁).topCoeff‖ * ρ ^ (n + 1))) ≤
            μ (n + 1) (closedSmallBall (MultiAffine.affine p₀ p₁)
              ((‖p₁.topCoeff‖ * ρ ^ n) * ρ)) := by
          simpa using measure_mono hsub
        _ ≤ δ + μ n (openSmallBall p₁ (‖p₁.topCoeff‖ * ρ ^ n)) :=
          oneStep_closedSmallBall hprefix hone p₀ p₁ _ hscale
        _ ≤ δ + (n : ℝ≥0∞) * δ :=
          add_le_add (le_refl δ) (ih₁ htop₁)
        _ = ((n + 1 : ℕ) : ℝ≥0∞) * δ := by
          simp [add_mul, add_comm]

/-- Manuscript-shaped multiaffine induction for at least one variable.

This is the formal `k * δ` accumulation for the manuscript's multiaffine
small-ball branch.  Substituting an available one-coordinate cost
`δ = 2 L ρ` or `δ = π L ρ²` gives its real or complex rate. -/
theorem closedSmallBall_topCoeff_le
    {μ : (n : ℕ) → Measure (Fin n → K)} {ρ : ℝ} {δ : ℝ≥0∞}
    (hρ : 0 < ρ) (hprefix : PrefixSmallBallConsistent μ)
    (hone : OneCoordinateSmallBall μ ρ δ)
    {n : ℕ} (p : MultiAffine K (n + 1)) (htop : 0 < ‖p.topCoeff‖) :
    μ (n + 1) (closedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) * δ := by
  cases p with
  | affine p₀ p₁ =>
      have htop₁ : 0 < ‖p₁.topCoeff‖ := by simpa using htop
      have hscale : 0 < ‖p₁.topCoeff‖ * ρ ^ n :=
        mul_pos htop₁ (pow_pos hρ n)
      calc
        μ (n + 1) (closedSmallBall (MultiAffine.affine p₀ p₁)
            (‖(MultiAffine.affine p₀ p₁).topCoeff‖ * ρ ^ (n + 1))) ≤
            δ + μ n (openSmallBall p₁ (‖p₁.topCoeff‖ * ρ ^ n)) := by
          simpa [pow_succ, mul_assoc] using
            oneStep_closedSmallBall hprefix hone p₀ p₁
              (‖p₁.topCoeff‖ * ρ ^ n) hscale
        _ ≤ δ + (n : ℝ≥0∞) * δ :=
          add_le_add (le_refl δ)
            (openSmallBall_topCoeff_le hρ hprefix hone p₁ htop₁)
        _ = ((n + 1 : ℕ) : ℝ≥0∞) * δ := by
          simp [add_mul, add_comm]

/-- Explicit linear-in-`k` and linear-in-`ρ` specialization. -/
theorem closedSmallBall_topCoeff_le_mul_rho_of_oneCoordinate
    {μ : (n : ℕ) → Measure (Fin n → K)} {ρ : ℝ} {C : ℝ≥0∞}
    (hρ : 0 < ρ) (hprefix : PrefixSmallBallConsistent μ)
    (hone : OneCoordinateSmallBall μ ρ (C * ENNReal.ofReal ρ))
    {n : ℕ} (p : MultiAffine K (n + 1)) (htop : 0 < ‖p.topCoeff‖) :
    μ (n + 1) (closedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) * C * ENNReal.ofReal ρ := by
  simpa only [mul_assoc] using
    closedSmallBall_topCoeff_le hρ hprefix hone p htop

/-- Explicit linear-in-`k` and quadratic-in-`ρ` specialization, matching the
planar-density branch. -/
theorem closedSmallBall_topCoeff_le_mul_rho_sq_of_oneCoordinate
    {μ : (n : ℕ) → Measure (Fin n → K)} {ρ : ℝ} {C : ℝ≥0∞}
    (hρ : 0 < ρ) (hprefix : PrefixSmallBallConsistent μ)
    (hone : OneCoordinateSmallBall μ ρ (C * ENNReal.ofReal ρ ^ 2))
    {n : ℕ} (p : MultiAffine K (n + 1)) (htop : 0 < ‖p.topCoeff‖) :
    μ (n + 1) (closedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) * C * ENNReal.ofReal ρ ^ 2 := by
  simpa only [mul_assoc] using
    closedSmallBall_topCoeff_le hρ hprefix hone p htop

end SmallBall

end CircularLawSection4
