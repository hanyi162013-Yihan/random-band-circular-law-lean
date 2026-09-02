import CircularLawSection4.Multiaffine

/-!
# Deterministic translations of recursive multiaffine polynomials

Substituting `x i + t i` for every variable preserves multiaffinity.  This
file constructs the translated polynomial recursively, proves its evaluation
identity, and shows that its full square-free monomial coefficient is
unchanged.  Algebraically, every term introduced by the deterministic shift
has lower degree in at least one coordinate.
-/

namespace CircularLawSection4
namespace MultiAffine

universe u

variable {R : Type u}

/-- Coefficientwise addition of recursive multiaffine polynomials. -/
def add [Add R] : {n : ℕ} → MultiAffine R n → MultiAffine R n → MultiAffine R n
  | 0, const a, const b => const (a + b)
  | _ + 1, affine p₀ p₁, affine q₀ q₁ => affine (add p₀ q₀) (add p₁ q₁)

/-- Coefficientwise multiplication by a scalar. -/
def scale [Mul R] (c : R) : {n : ℕ} → MultiAffine R n → MultiAffine R n
  | 0, const a => const (c * a)
  | _ + 1, affine p₀ p₁ => affine (scale c p₀) (scale c p₁)

@[simp] theorem eval_add [Semiring R] {n : ℕ}
    (p q : MultiAffine R n) (x : Fin n → R) :
    eval (add p q) x = eval p x + eval q x := by
  induction p with
  | const a =>
      cases q with
      | const b => simp [add]
  | @affine n p₀ p₁ ih₀ ih₁ =>
      cases q with
      | affine q₀ q₁ =>
          simp only [add, eval_affine, ih₀, ih₁]
          noncomm_ring

@[simp] theorem topCoeff_add [Semiring R] {n : ℕ}
    (p q : MultiAffine R n) :
    topCoeff (add p q) = topCoeff p + topCoeff q := by
  induction p with
  | const a =>
      cases q with
      | const b => simp [add]
  | affine p₀ p₁ ih₀ ih₁ =>
      cases q with
      | affine q₀ q₁ => simp [add, ih₁]

@[simp] theorem eval_scale [CommSemiring R] (c : R) {n : ℕ}
    (p : MultiAffine R n) (x : Fin n → R) :
    eval (scale c p) x = c * eval p x := by
  induction p with
  | const a => simp [scale]
  | affine p₀ p₁ ih₀ ih₁ =>
      simp only [scale, eval_affine, ih₀, ih₁]
      ring

@[simp] theorem topCoeff_scale [Semiring R] (c : R) {n : ℕ}
    (p : MultiAffine R n) :
    topCoeff (scale c p) = c * topCoeff p := by
  induction p with
  | const a => simp [scale]
  | affine p₀ p₁ ih₀ ih₁ => simp [scale, ih₁]

/-- Translate every variable by a deterministic vector `t`.

For the fresh last variable,
`p₀ + (xₙ + tₙ) p₁ = (p₀ + tₙ p₁) + xₙ p₁`; the prefix polynomials are
translated recursively. -/
def translate [CommSemiring R] :
    {n : ℕ} → MultiAffine R n → (Fin n → R) → MultiAffine R n
  | 0, const c, _ => const c
  | n + 1, affine p₀ p₁, t =>
      let q₀ := translate p₀ (dropLast t)
      let q₁ := translate p₁ (dropLast t)
      affine (add q₀ (scale (t (Fin.last n)) q₁)) q₁

/-- Evaluation after translating the polynomial equals evaluation at the
coordinatewise translated point. -/
theorem eval_translate [CommSemiring R] :
    ∀ {n : ℕ} (p : MultiAffine R n) (t x : Fin n → R),
      eval (translate p t) x = eval p (fun i => x i + t i)
  | 0, const c, _, _ => by simp [translate]
  | n + 1, affine p₀ p₁, t, x => by
      simp only [translate, eval_affine, eval_add, eval_scale,
        eval_translate p₀, eval_translate p₁]
      change
        eval p₀ (fun i => x i.castSucc + t i.castSucc) +
            t (Fin.last n) * eval p₁ (fun i => x i.castSucc + t i.castSucc) +
          x (Fin.last n) * eval p₁ (fun i => x i.castSucc + t i.castSucc) =
        eval p₀ (fun i => x i.castSucc + t i.castSucc) +
          (x (Fin.last n) + t (Fin.last n)) *
            eval p₁ (fun i => x i.castSucc + t i.castSucc)
      ring

/-- A coordinatewise deterministic translation does not alter the
coefficient of the full monomial `x₀ ⋯ xₙ₋₁`. -/
@[simp] theorem topCoeff_translate [CommSemiring R] :
    ∀ {n : ℕ} (p : MultiAffine R n) (t : Fin n → R),
      topCoeff (translate p t) = topCoeff p
  | 0, const c, _ => by simp [translate]
  | _ + 1, affine p₀ p₁, t => by
      simp [translate, topCoeff_translate p₁ (dropLast t)]

end MultiAffine
end CircularLawSection4
