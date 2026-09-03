/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/AnisotropicNetGeometry.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.AnisotropicLabels

/-! A finite anisotropic cover built from two real ball covers. -/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace HighBandLSV.Anisotropic
variable {I : Type*} [Fintype I] {h : Real}

def shearedImag (q : Label h) (u : CV I) : RV I :=
  imagPart (rotate q.1 u) - angle q • realPart (rotate q.1 u)

def center (q : Label h) (a d : RV I) : CV I :=
  unrotate q.1 (join a (angle q • a + d))

theorem center_reconstruct (q : Label h) (u : CV I) :
    center q (realPart (rotate q.1 u)) (shearedImag q u) = u := by
  unfold center shearedImag
  rw [add_sub_cancel, join_parts, unrotate_rotate]

theorem shearedImag_norm_le (hh : 0 ≤ h) (q : Label h) {u : CV I}
    (hu : u ∈ blockClass q) : ‖shearedImag q u‖ ≤ yRadius q + 2 * h := by
  let a := realPart (rotate q.1 u)
  let b := imagPart (rotate q.1 u)
  have he : shearedImag q u = residual a b + (shear a b - angle q) • a := by
    unfold shearedImag residual
    dsimp [a, b]
    module
  have ha : ‖a‖ ≤ 1 := (realPart_norm_le _).trans (by simpa using hu.1)
  have halpha : |shear a b - angle q| ≤ h := hu.2.2.2.2.2.2
  have hy : ‖residual a b‖ ≤ yRadius q + h := hu.2.2.2.2.2.1
  rw [he]
  calc
    ‖residual a b + (shear a b - angle q) • a‖ ≤
        ‖residual a b‖ + ‖(shear a b - angle q) • a‖ := norm_add_le _ _
    _ = ‖residual a b‖ + |shear a b - angle q| * ‖a‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ yRadius q + 2 * h := by
      have hm := mul_le_mul halpha ha (norm_nonneg a) hh
      nlinarith

theorem center_dist_le {eps : Real} (heps : 0 ≤ eps) (q : Label h)
    (hq : |angle q| ≤ 1) (a d a' d' : RV I)
    (ha : dist a a' ≤ eps) (hd : dist d d' ≤ eps) :
    dist (center q a d) (center q a' d') ≤ 3 * eps := by
  rw [dist_eq_norm, center, center, unrotate_sub, norm_unrotate, join_sub]
  have he : angle q • a + d - (angle q • a' + d') =
      angle q • (a - a') + (d - d') := by module
  rw [he]
  have h1 := norm_join_le (a - a') (angle q • (a - a') + (d - d'))
  have h2 := norm_add_le (angle q • (a - a')) (d - d')
  rw [norm_smul, Real.norm_eq_abs] at h2
  have h3 := mul_le_mul_of_nonneg_right hq (norm_nonneg (a - a'))
  rw [dist_eq_norm] at ha hd
  linarith

theorem exists_external_cover {eps : Real} (hh : 0 ≤ h) (heps : 0 ≤ eps)
    (q : Label h) (hq : admissible q) (Fa Fb : Finset (RV I))
    (hFa : ∀ a : RV I, ‖a‖ ≤ xRadius q + h → ∃ a' ∈ Fa, dist a a' ≤ eps)
    (hFb : ∀ d : RV I, ‖d‖ ≤ yRadius q + 2 * h → ∃ d' ∈ Fb, dist d d' ≤ eps) :
    ∃ F : Finset (CV I), F.card ≤ Fa.card * Fb.card ∧
      ∀ u ∈ blockClass q, ∃ v ∈ F, dist u v ≤ 3 * eps := by
  classical
  let F := (Fa.product Fb).image (fun p => center q p.1 p.2)
  refine ⟨F, ?_, ?_⟩
  · exact (Finset.card_image_le).trans_eq (Finset.card_product Fa Fb)
  · intro u hu
    obtain ⟨a', ha', hea⟩ := hFa (realPart (rotate q.1 u)) hu.2.2.2.1
    obtain ⟨d', hd', hed⟩ := hFb (shearedImag q u) (shearedImag_norm_le hh q hu)
    refine ⟨center q a' d', Finset.mem_image.mpr ⟨(a', d'), ?_, rfl⟩, ?_⟩
    · exact Finset.mem_product.mpr ⟨ha', hd'⟩
    · rw [← center_reconstruct q u]
      exact center_dist_le heps q hq.2.2 _ _ a' d' hea hed

end HighBandLSV.Anisotropic

#print axioms HighBandLSV.Anisotropic.exists_external_cover

