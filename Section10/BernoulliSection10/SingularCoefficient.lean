import BernoulliSection10.ExteriorSingularFrames
import BernoulliSection10.ExteriorFrameRelabel

/-!
# A scalar reset coefficient controls the product norm

After the core and past are frozen, their top singular frames provide a
single decomposable scalar coefficient. Both frames and their coordinate
labels are constructed in this module. The conclusion is uniform over
the middle matrix, so it can be integrated without a measurable choice
of singular frames as functions of the core and past.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection10

open Matrix BernoulliLinearAlgebra Set Set.powersetCard

set_option maxHeartbeats 800000

theorem matrix_entry_norm_le_operatorNorm
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  let T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A
  calc
    ‖A i j‖ = ‖(T (WithLp.toLp 2 (Pi.single j 1))) i‖ := by
      simp [T, Matrix.toEuclideanCLM_toLp, Matrix.mulVec_single_one]
    _ ≤ ‖T (WithLp.toLp 2 (Pi.single j 1))‖ := PiLp.norm_apply_le _ i
    _ ≤ ‖T‖ := by simpa using T.le_opNorm (WithLp.toLp 2 (Pi.single j 1))
    _ = ‖A‖ := Matrix.l2_opNorm_toEuclideanCLM A

theorem diagonal_sandwich_coefficient_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (d e : n → ℝ) (Q : Matrix n n ℂ) (a b : n)
    (hda : 0 ≤ d a) (heb : 0 ≤ e b) :
    d a * e b * ‖Q a b‖ ≤
      ‖diagonal (fun i => (d i : ℂ)) * Q * diagonal (fun i => (e i : ℂ))‖ := by
  have h := matrix_entry_norm_le_operatorNorm
    (diagonal (fun i => (d i : ℂ)) * Q * diagonal (fun i => (e i : ℂ))) a b
  simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hda, abs_of_nonneg heb,
    mul_assoc, mul_comm, mul_left_comm] using h

theorem singular_sandwich_coefficient_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (U₁ V₁ U₂ V₂ : unitaryGroup n ℂ) (d e : n → ℝ)
    (Q : Matrix n n ℂ) (a b : n) (hda : 0 ≤ d a) (heb : 0 ≤ e b) :
    d a * e b * ‖(star (V₁ : Matrix n n ℂ) * Q * (U₂ : Matrix n n ℂ)) a b‖ ≤
      ‖((U₁ : Matrix n n ℂ) * diagonal (fun i => (d i : ℂ)) * star (V₁ : Matrix n n ℂ)) *
        Q * ((U₂ : Matrix n n ℂ) * diagonal (fun i => (e i : ℂ)) * star (V₂ : Matrix n n ℂ))‖ := by
  have heq :
      ((U₁ : Matrix n n ℂ) * diagonal (fun i => (d i : ℂ)) * star (V₁ : Matrix n n ℂ)) *
        Q * ((U₂ : Matrix n n ℂ) * diagonal (fun i => (e i : ℂ)) * star (V₂ : Matrix n n ℂ)) =
      (U₁ : Matrix n n ℂ) *
        (diagonal (fun i => (d i : ℂ)) *
          (star (V₁ : Matrix n n ℂ) * Q * (U₂ : Matrix n n ℂ)) *
            diagonal (fun i => (e i : ℂ))) * ((star V₂) : Matrix n n ℂ) := by
    simp only [Matrix.mul_assoc]
  rw [heq, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem V₂.property),
    CStarRing.norm_mem_unitary_mul _ U₁.property]
  exact diagonal_sandwich_coefficient_le d e _ a b hda heb

variable {W : Type*} [Fintype W] [LinearOrder W]

local instance singularCoefficientSumOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift' (fun x : W ⊕ W => (toLex x : W ⊕ₗ W))
    (fun _ _ h => toLex.injective h)

/-- A product of two exterior transfers admits the same-index scalar
test required by Proposition 10.10, with all frames constructed. -/
theorem exists_exterior_product_scalar_test
    (A B : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (hA : IsUnit A.det) (hB : IsUnit B.det)
    (r : ℕ) (hr : r ≤ Fintype.card (W ⊕ W)) :
    ∃ U V : unitaryGroup (W ⊕ W) ℂ, ∃ s : powersetCard (W ⊕ W) r,
      ∀ Q : Matrix (powersetCard (W ⊕ W) r) (powersetCard (W ⊕ W) r) ℂ,
        ‖compound r A‖ * ‖compound r B‖ *
          ‖((compound r (U : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ * Q *
            compound r (V : Matrix (W ⊕ W) (W ⊕ W) ℂ)) s s‖ ≤
            ‖compound r A * Q * compound r B‖ := by
  obtain ⟨U₁, V₁, d, a, hd, hAd, hAnorm⟩ :=
    exists_top_exterior_singular_frame A hA r hr
  obtain ⟨U₂, V₂, e, b, he, hBe, hBnorm⟩ :=
    exists_top_exterior_singular_frame B hB r hr
  obtain ⟨V, hV⟩ := exists_unitary_exterior_coefficient_relabel r V₁ U₂ a b
  refine ⟨V₁, V, a, fun Q => ?_⟩
  rw [hV Q, hAnorm, hBnorm, hAd, hBe]
  exact singular_sandwich_coefficient_le
    (exteriorUnitary r U₁) (exteriorUnitary r V₁)
    (exteriorUnitary r U₂) (exteriorUnitary r V₂) d e Q a b (hd a).le (he b).le

end BernoulliSection10
