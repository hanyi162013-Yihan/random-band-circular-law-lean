import BernoulliSection10.PacketFrame
import Mathlib.Logic.Equiv.Fintype

/-!
# Relabelling exterior frames without a sign ambiguity

Two selected sets of columns are matched in their increasing enumeration.
The finite partial bijection extends to a permutation of the entire state
space. Consequently the selected exterior columns agree exactly, rather
than only up to an unspecified orientation factor.
-/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliSection10

set_option maxHeartbeats 800000

open BernoulliLinearAlgebra Matrix Set Set.powersetCard

variable {W : Type*} [Fintype W] [LinearOrder W]

local instance exteriorFrameRelabelSumOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift' (fun x : W ⊕ W => (toLex x : W ⊕ₗ W))
    (fun _ _ h => toLex.injective h)

theorem unitary_submatrix_columns
    (U : unitaryGroup (W ⊕ W) ℂ) (σ : Equiv.Perm (W ⊕ W)) :
    (U : Matrix (W ⊕ W) (W ⊕ W) ℂ).submatrix id σ ∈
      unitaryGroup (W ⊕ W) ℂ := by
  rw [mem_unitaryGroup_iff']
  have h : star ((U : Matrix (W ⊕ W) (W ⊕ W) ℂ).submatrix id σ) *
      (U : Matrix (W ⊕ W) (W ⊕ W) ℂ).submatrix id σ =
      (star (U : Matrix (W ⊕ W) (W ⊕ W) ℂ) * U).submatrix σ σ := by
    ext i j
    rfl
  rw [h, Matrix.UnitaryGroup.star_mul_self U]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.one_apply]

/-- Every selected decomposable unit column can be represented at any
other coordinate subset by relabelling an actual unitary completion. -/
theorem exists_unitary_exterior_column_relabel
    (r : ℕ) (U : unitaryGroup (W ⊕ W) ℂ)
    (a b : powersetCard (W ⊕ W) r) :
    ∃ V : unitaryGroup (W ⊕ W) ℂ, ∀ t : powersetCard (W ⊕ W) r,
      compound r (V : Matrix (W ⊕ W) (W ⊕ W) ℂ) t a =
        compound r (U : Matrix (W ⊕ W) (W ⊕ W) ℂ) t b := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (ofFinEmbEquiv.symm a) (ofFinEmbEquiv.symm b)
    (ofFinEmbEquiv.symm a).injective (ofFinEmbEquiv.symm b).injective
  refine ⟨⟨(U : Matrix (W ⊕ W) (W ⊕ W) ℂ).submatrix id σ,
    unitary_submatrix_columns U σ⟩, ?_⟩
  intro t
  simp only [compound_apply]
  unfold minor
  congr 1
  ext i j
  change (U : Matrix (W ⊕ W) (W ⊕ W) ℂ) (ofFinEmbEquiv.symm t i)
      (σ (ofFinEmbEquiv.symm a j)) = _
  rw [hσ j]
  rfl

/-- A cross coefficient of two exterior frames is a same-index
coefficient of actual unitary frames, uniformly for every middle matrix. -/
theorem exists_unitary_exterior_coefficient_relabel
    (r : ℕ) (U V : unitaryGroup (W ⊕ W) ℂ)
    (a b : powersetCard (W ⊕ W) r) :
    ∃ V' : unitaryGroup (W ⊕ W) ℂ,
      ∀ Q : Matrix (powersetCard (W ⊕ W) r) (powersetCard (W ⊕ W) r) ℂ,
        ((compound r (U : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ * Q *
          compound r (V' : Matrix (W ⊕ W) (W ⊕ W) ℂ)) a a =
          ((compound r (U : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ * Q *
            compound r (V : Matrix (W ⊕ W) (W ⊕ W) ℂ)) a b := by
  obtain ⟨V', hV'⟩ := exists_unitary_exterior_column_relabel r V a b
  refine ⟨V', fun Q => ?_⟩
  simp only [Matrix.mul_apply, hV']

end BernoulliSection10
