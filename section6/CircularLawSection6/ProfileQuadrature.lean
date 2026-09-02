import CircularLawSection6.CenteredMesh
import CircularLawSection6.BVQuadrature

/-! # Uniform quadrature bounds for the actual profile sums

The normalization sum covers all centered residues. The core sum is an
ordinary integer interval only once its radius fits without cyclic overlap.
Neither estimate assumes a Riemann-sum limit as an input.
-/

open scoped BigOperators

noncomputable section

namespace CircularLawSection6.NoncompactProfile

theorem normalizer_eq_uniformMesh (p : NoncompactProfile)
    (N : ℕ) [NeZero N] (W : ℝ) :
    p.normalizer N W =
      ∑ i ∈ Finset.range N, p.f (-((N / 2 : ℕ) : ℝ) / W + (i : ℝ) * W⁻¹) := by
  rw [p.normalizer_eq_integerSum, Int.Ico_eq_finset_map, Finset.sum_map]
  have hlen : ((((N + 1) / 2 : ℕ) : ℤ) - (-((N / 2 : ℕ) : ℤ))).toNat = N := by omega
  rw [hlen]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply, Int.cast_add, Int.cast_natCast, Int.cast_neg]
  ring

theorem rawCoreMass_eq_uniformMesh (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (hsize : 2 * H + 1 ≤ N) (W : ℝ) :
    p.rawCoreMass N H W =
      ∑ i ∈ Finset.range (2 * H + 1), p.f (-(H : ℝ) / W + (i : ℝ) * W⁻¹) := by
  rw [p.rawCoreMass_eq_integerSum N H hsize, Int.Icc_eq_finset_map, Finset.sum_map]
  have hlen : ((H : ℤ) + 1 - (-(H : ℤ))).toNat = 2 * H + 1 := by omega
  rw [hlen]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply, Int.cast_add, Int.cast_natCast, Int.cast_neg]
  ring

theorem normalizer_quadrature_error (p : NoncompactProfile)
    (N : ℕ) [NeZero N] {W : ℝ} (hW : 0 < W) :
    |p.normalizer N W / W -
        ∫ x in -((N / 2 : ℕ) : ℝ) / W..(((N + 1) / 2 : ℕ) : ℝ) / W, p.f x| ≤
      (eVariationOn p.f Set.univ).toReal / W := by
  have h := uniformMesh_error_le p.continuous p.boundedVariation
    (-((N / 2 : ℕ) : ℝ) / W) N (δ := W⁻¹) (inv_nonneg.2 hW.le)
  have hn : (N : ℝ) = ((N / 2 : ℕ) : ℝ) + (((N + 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show N = N / 2 + (N + 1) / 2 by omega)
  have hend : -((N / 2 : ℕ) : ℝ) / W + (N : ℝ) * W⁻¹ =
      (((N + 1) / 2 : ℕ) : ℝ) / W := by rw [hn]; ring
  rw [hend, ← p.normalizer_eq_uniformMesh] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem rawCoreMass_quadrature_error (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (hsize : 2 * H + 1 ≤ N) {W : ℝ} (hW : 0 < W) :
    |p.rawCoreMass N H W / W - ∫ x in -(H : ℝ) / W..((H : ℝ) + 1) / W, p.f x| ≤
      (eVariationOn p.f Set.univ).toReal / W := by
  have h := uniformMesh_error_le p.continuous p.boundedVariation
    (-(H : ℝ) / W) (2 * H + 1) (δ := W⁻¹) (inv_nonneg.2 hW.le)
  have hend : -(H : ℝ) / W + ((2 * H + 1 : ℕ) : ℝ) * W⁻¹ =
      ((H : ℝ) + 1) / W := by push_cast; ring
  rw [hend, ← p.rawCoreMass_eq_uniformMesh N H hsize] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

end CircularLawSection6.NoncompactProfile
