/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/AnisotropicNets.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.AnisotropicNetGeometry

/-! Actual internal anisotropic nets, with the sharp real dimension in the entropy exponent. -/

noncomputable section
open scoped BigOperators
namespace HighBandLSV.Anisotropic

private theorem first_ball_base {R h : Real} (hh : 0 < h) :
    (2 * (R + h) + h / 6) / (h / 6) ≤ 25 * max R h / h := by
  have he : (2 * (R + h) + h / 6) / (h / 6) = (12 * R + 13 * h) / h := by
    field_simp
    ring
  rw [he]
  apply div_le_div_of_nonneg_right _ hh.le
  nlinarith [le_max_left R h, le_max_right R h]

private theorem second_ball_base {R h : Real} (hh : 0 < h) :
    (2 * (R + 2 * h) + h / 6) / (h / 6) ≤ 37 * max R h / h := by
  have he : (2 * (R + 2 * h) + h / 6) / (h / 6) = (12 * R + 25 * h) / h := by
    field_simp
    ring
  rw [he]
  apply div_le_div_of_nonneg_right _ hh.le
  nlinarith [le_max_left R h, le_max_right R h]

theorem exists_internal_anisotropic_net {I : Type*} [Fintype I] {h : Real}
    (hh : 0 < h) (q : Label h) (hq : admissible q) :
    ∃ G : Finset (CV I),
      (∀ v ∈ G, v ∈ blockClass q) ∧
      (∀ u ∈ blockClass q, ∃ v ∈ G, dist u v ≤ h) ∧
      (G.card : Real) ≤ (1024 * labelWeight q / h ^ 2) ^ Fintype.card I := by
  classical
  have hx0 : 0 ≤ xRadius q := radius_nonneg hh.le _
  have hy0 : 0 ≤ yRadius q := radius_nonneg hh.le _
  have heps : 0 < h / 6 := by positivity
  obtain ⟨Fa, _, hFaCover, hFaCard⟩ :=
    Section5Formalization.exists_volumetric_closedBall_net (E := RV I)
      (by linarith : 0 ≤ xRadius q + h) heps
  obtain ⟨Fb, _, hFbCover, hFbCard⟩ :=
    Section5Formalization.exists_volumetric_closedBall_net (E := RV I)
      (by linarith : 0 ≤ yRadius q + 2 * h) heps
  have hFaDim : (Fa.card : Real) ≤
      ((2 * (xRadius q + h) + h / 6) / (h / 6)) ^ Fintype.card I := by
    simpa [RV, EuclideanSpace, Module.finrank_pi_fintype] using hFaCard
  have hFbDim : (Fb.card : Real) ≤
      ((2 * (yRadius q + 2 * h) + h / 6) / (h / 6)) ^ Fintype.card I := by
    simpa [RV, EuclideanSpace, Module.finrank_pi_fintype] using hFbCard
  have hFa : (Fa.card : Real) ≤ (25 * max (xRadius q) h / h) ^ Fintype.card I :=
    hFaDim.trans (pow_le_pow_left₀ (by positivity) (first_ball_base hh) _)
  have hFb : (Fb.card : Real) ≤ (37 * max (yRadius q) h / h) ^ Fintype.card I :=
    hFbDim.trans (pow_le_pow_left₀ (by positivity) (second_ball_base hh) _)
  obtain ⟨F, hFCard, hFCover⟩ := exists_external_cover hh.le heps.le q hq Fa Fb hFaCover hFbCover
  obtain ⟨G, hGInside, hGCard, hGCover⟩ :=
    InternalNet.exists_internal_net (blockClass q) F (3 * (h / 6)) hFCover
  have heq : 2 * (3 * (h / 6)) = h := by ring
  rw [heq] at hGCover
  refine ⟨G, hGInside, hGCover, ?_⟩
  have hcard : (G.card : Real) ≤ (Fa.card : Real) * Fb.card := by
    exact_mod_cast hGCard.trans hFCard
  calc
    (G.card : Real) ≤ (Fa.card : Real) * Fb.card := hcard
    _ ≤ (25 * max (xRadius q) h / h) ^ Fintype.card I *
        (37 * max (yRadius q) h / h) ^ Fintype.card I := by gcongr
    _ = (925 * labelWeight q / h ^ 2) ^ Fintype.card I := by
      rw [← mul_pow]
      congr 1
      unfold labelWeight
      ring
    _ ≤ (1024 * labelWeight q / h ^ 2) ^ Fintype.card I := by
      have hw : 0 ≤ labelWeight q := by
        unfold labelWeight
        positivity
      gcongr
      norm_num

end HighBandLSV.Anisotropic

#print axioms HighBandLSV.Anisotropic.exists_internal_anisotropic_net

