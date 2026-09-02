import BernoulliSection10.SingularFrames
import BernoulliSection10.PacketFrame

/-!
# Singular frames in every exterior degree

The unitary matrices here are exterior powers of unitary matrices on the
original state space. Thus their columns are the decomposable wedges
required by the three-site reset estimate, not arbitrary exterior vectors.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection10

set_option maxHeartbeats 800000

open BernoulliLinearAlgebra Matrix Set Set.powersetCard

variable {W : Type*} [Fintype W] [LinearOrder W]

local instance exteriorSingularFramesSumOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift' (fun x : W ⊕ W => (toLex x : W ⊕ₗ W))
    (fun _ _ h => toLex.injective h)

def exteriorUnitary (r : ℕ) (U : unitaryGroup (W ⊕ W) ℂ) :
    unitaryGroup (powersetCard (W ⊕ W) r) ℂ :=
  ⟨compound r (U : Matrix (W ⊕ W) (W ⊕ W) ℂ), compound_mem_unitaryGroup r U⟩

/-- The singular diagonal in an exterior degree is constructed from the
positive singular values of the original matrix. -/
theorem exists_positive_exterior_singular_frames
    (A : Matrix (W ⊕ W) (W ⊕ W) ℂ) (hA : IsUnit A.det) (r : ℕ) :
    ∃ U V : unitaryGroup (W ⊕ W) ℂ,
      ∃ d : powersetCard (W ⊕ W) r → ℝ,
        (∀ s, 0 < d s) ∧
        compound r A = (exteriorUnitary r U : Matrix _ _ ℂ) *
          diagonal (fun s => (d s : ℂ)) *
            star (exteriorUnitary r V : Matrix _ _ ℂ) := by
  obtain ⟨U, V, σ, hσ, hAeq⟩ := exists_positive_singular_frames A hA
  let d : powersetCard (W ⊕ W) r → ℝ := fun s =>
    ∏ j : Fin r, σ (ofFinEmbEquiv.symm s j)
  refine ⟨U, V, d, ?_, ?_⟩
  · intro s
    exact Finset.prod_pos fun j _ => hσ _
  · have hd : compound r (diagonal (fun i => (σ i : ℂ))) =
        diagonal (fun s => (d s : ℂ)) := by
      ext s t
      rw [compound_diagonal_apply, Matrix.diagonal_apply]
      split_ifs <;> simp [d]
    rw [hAeq, compound_mul, compound_mul, hd]
    change compound r (U : Matrix (W ⊕ W) (W ⊕ W) ℂ) *
        diagonal (fun s => (d s : ℂ)) *
          compound r (V : Matrix (W ⊕ W) (W ⊕ W) ℂ)ᴴ =
      compound r (U : Matrix (W ⊕ W) (W ⊕ W) ℂ) *
        diagonal (fun s => (d s : ℂ)) *
          (compound r (V : Matrix (W ⊕ W) (W ⊕ W) ℂ))ᴴ
    rw [compound_conjTranspose]

theorem norm_exterior_singular_diagonal
    (U V : unitaryGroup (W ⊕ W) ℂ)
    (r : ℕ) (d : powersetCard (W ⊕ W) r → ℝ) :
    ‖(exteriorUnitary r U : Matrix _ _ ℂ) * diagonal (fun s => (d s : ℂ)) *
      star (exteriorUnitary r V : Matrix _ _ ℂ)‖ = ‖d‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem (exteriorUnitary r V).property),
    CStarRing.norm_mem_unitary_mul _ (exteriorUnitary r U).property,
    Matrix.l2_opNorm_diagonal]
  simp only [Pi.norm_def, Complex.nnnorm_real]

/-- A top singular wedge exists in every nonempty exterior degree; no
frame or maximizing index is supplied by the caller. -/
theorem exists_top_exterior_singular_frame
    (A : Matrix (W ⊕ W) (W ⊕ W) ℂ) (hA : IsUnit A.det)
    (r : ℕ) (hr : r ≤ Fintype.card (W ⊕ W)) :
    ∃ U V : unitaryGroup (W ⊕ W) ℂ,
      ∃ d : powersetCard (W ⊕ W) r → ℝ,
        ∃ s : powersetCard (W ⊕ W) r,
          (∀ t, 0 < d t) ∧
          compound r A = (exteriorUnitary r U : Matrix _ _ ℂ) *
            diagonal (fun t => (d t : ℂ)) *
              star (exteriorUnitary r V : Matrix _ _ ℂ) ∧
          ‖compound r A‖ = d s := by
  letI : Nonempty (powersetCard (W ⊕ W) r) := by
    rw [← Finite.card_pos_iff, Set.powersetCard.card, Nat.card_eq_fintype_card]
    exact Nat.choose_pos hr
  obtain ⟨U, V, d, hdpos, heq⟩ := exists_positive_exterior_singular_frames A hA r
  obtain ⟨s, _, hs⟩ := Finset.exists_max_image Finset.univ d Finset.univ_nonempty
  refine ⟨U, V, d, s, hdpos, heq, ?_⟩
  rw [heq, norm_exterior_singular_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (hdpos s).le).2
    intro t
    rw [Real.norm_eq_abs, abs_of_pos (hdpos t)]
    exact hs t (Finset.mem_univ t)
  · simpa only [Real.norm_eq_abs, abs_of_pos (hdpos s)] using norm_le_pi_norm d s

end BernoulliSection10
