/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/PlanarNets.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Section5Formalization.VolumetricNet
import Vendor.RandomMatrixModel

/-!
# Radial block nets for the planar-density branch

For genuinely complex atoms, radial annuli give the required entropy/small-ball
cancellation without the real/imaginary Gram decomposition. The final mesh and
partition remain the prescribed Appendix B choices.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set Metric

noncomputable section

namespace HighBandLSV.PlanarNets

theorem exists_compact_net
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
    (A : Set E) (hA : IsCompact A) {R h : Real} (hR : 0 ≤ R) (hh : 0 < h)
    (hAR : ∀ x ∈ A, ‖x‖ ≤ R) :
    ∃ net : Finset E, (∀ y ∈ net, y ∈ A) ∧
      (∀ x ∈ A, ∃ y ∈ net, dist x y ≤ h) ∧
      (net.card : Real) ≤ ((2 * R + h) / h) ^ Module.finrank Real E := by
  letI : ProperSpace E := FiniteDimensional.proper Real E
  let epsilon : NNReal := ⟨h, hh.le⟩
  obtain ⟨C, hCA, hCfinite, hCcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact (ε := epsilon / 2) (by
      apply div_ne_zero
      · intro hepsilon
        have he := congrArg (fun x : NNReal => (x : Real)) hepsilon
        exact hh.ne' he
      · norm_num) hA
  have hpacking_le : Metric.packingNumber epsilon A ≤
      Metric.externalCoveringNumber (epsilon / 2) A := by
    have he : (2 : NNReal) * (epsilon / 2) = epsilon := by ring
    simpa only [he] using
      Metric.packingNumber_two_mul_le_externalCoveringNumber (epsilon / 2) A
  have hpacking_lt : Metric.packingNumber epsilon A < ⊤ :=
    (hpacking_le.trans hCcover.externalCoveringNumber_le_encard).trans_lt
      (Set.encard_lt_top_iff.mpr hCfinite)
  let S := Metric.maximalSeparatedSet epsilon A
  have hSfinite : S.Finite := by
    apply Set.encard_lt_top_iff.mp
    rw [show S.encard = Metric.packingNumber epsilon A from
      Metric.encard_maximalSeparatedSet hpacking_lt.ne]
    exact hpacking_lt
  let net := hSfinite.toFinset
  have hmem : ∀ y ∈ net, y ∈ A := by
    intro y hy
    exact Metric.maximalSeparatedSet_subset (hSfinite.mem_toFinset.mp hy)
  have hcover : ∀ x ∈ A, ∃ y ∈ net, dist x y ≤ h := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Metric.isCover_maximalSeparatedSet hpacking_lt.ne hx
    exact ⟨y, hSfinite.mem_toFinset.mpr hy, by exact_mod_cast hxy⟩
  have hsep : ∀ x ∈ net, ∀ y ∈ net, x ≠ y → h ≤ ‖x - y‖ := by
    intro x hx y hy hxy
    have hs := Metric.isSeparated_maximalSeparatedSet
      (hSfinite.mem_toFinset.mp hx) (hSfinite.mem_toFinset.mp hy) hxy
    change (epsilon : ENNReal) < edist x y at hs
    rw [edist_dist] at hs
    have hd : h < dist x y := ENNReal.coe_lt_ofReal.mp hs
    simpa [dist_eq_norm] using hd.le
  exact ⟨net, hmem, hcover, Section5Formalization.card_le_of_norm_le_of_separated net hR hh
    (fun x hx => hAR x (hmem x hx)) hsep⟩

theorem real_finrank_complex_euclidean (I : Type*) [Fintype I] :
    Module.finrank Real (EuclideanSpace Complex I) = 2 * Fintype.card I := by
  rw [← Module.finrank_mul_finrank Real Complex (EuclideanSpace Complex I)]
  simp

/-- An internal annular net has the exact squared-radius entropy useful for
complex small-ball estimates. -/
theorem exists_annular_net (I : Type*) [Fintype I] {R h : Real} (hR : 0 ≤ R) (hh : 0 < h) :
    ∃ net : Finset (EuclideanSpace Complex I),
      (∀ y ∈ net, R ≤ ‖y‖ ∧ ‖y‖ ≤ R + h) ∧
      (∀ x : EuclideanSpace Complex I, R ≤ ‖x‖ → ‖x‖ ≤ R + h →
        ∃ y ∈ net, dist x y ≤ h) ∧
      (net.card : Real) ≤ (25 * (max R h) ^ 2 / h ^ 2) ^ Fintype.card I := by
  let A : Set (EuclideanSpace Complex I) := {x | R ≤ ‖x‖ ∧ ‖x‖ ≤ R + h}
  have hc : IsClosed A :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  have hA : IsCompact A := (isCompact_closedBall (0 : EuclideanSpace Complex I) (R + h)).of_isClosed_subset
    hc (by intro x hx; simpa using hx.2)
  obtain ⟨net, hmem, hcover, hcard⟩ := exists_compact_net A hA (by linarith : 0 ≤ R + h) hh
    (fun _ hx => hx.2)
  refine ⟨net, hmem, fun x hlo hhi => hcover x ⟨hlo, hhi⟩, ?_⟩
  rw [real_finrank_complex_euclidean] at hcard
  calc
    (net.card : Real) ≤ ((2 * (R + h) + h) / h) ^ (2 * Fintype.card I) := hcard
    _ ≤ (5 * max R h / h) ^ (2 * Fintype.card I) := by
      gcongr
      nlinarith [le_max_left R h, le_max_right R h]
    _ = (25 * (max R h) ^ 2 / h ^ 2) ^ Fintype.card I := by
      rw [pow_mul]
      congr 1
      ring

def levelCount (h : Real) : Nat := ⌈1 / h⌉₊ + 1

def levelRadius {h : Real} (q : Fin (levelCount h)) : Real := (q.val : Real) * h

def weight {h : Real} (q : Fin (levelCount h)) : Real := (max (levelRadius q) h) ^ 2

theorem levelRadius_nonneg {h : Real} (hh : 0 ≤ h) (q : Fin (levelCount h)) :
    0 ≤ levelRadius q := mul_nonneg (Nat.cast_nonneg _) hh

theorem weight_pos {h : Real} (hh : 0 < h) (q : Fin (levelCount h)) : 0 < weight q :=
  sq_pos_of_pos (lt_of_lt_of_le hh (le_max_right _ _))

theorem radius_zero_or_ge_mesh {h : Real} (hh : 0 < h) (q : Fin (levelCount h)) :
    levelRadius q = 0 ∨ h ≤ levelRadius q := by
  by_cases hq : q.val = 0
  · left
    simp [levelRadius, hq]
  · right
    have hq1 : (1 : Real) ≤ (q.val : Real) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
    unfold levelRadius
    nlinarith

theorem exists_level {h x : Real} (hh : 0 < h) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ q : Fin (levelCount h), levelRadius q ≤ x ∧ x ≤ levelRadius q + h := by
  have hfloor : (⌊x / h⌋₊ : Real) ≤ x / h := Nat.floor_le (div_nonneg hx hh.le)
  have hceil : (1 : Real) / h ≤ (⌈1 / h⌉₊ : Real) := Nat.le_ceil _
  have hq : ⌊x / h⌋₊ ≤ ⌈1 / h⌉₊ := by
    exact_mod_cast hfloor.trans ((div_le_div_of_nonneg_right hx1 hh.le).trans hceil)
  let q : Fin (levelCount h) := ⟨⌊x / h⌋₊, Nat.lt_succ_of_le hq⟩
  refine ⟨q, (le_div_iff₀ hh).mp hfloor, ?_⟩
  have hupper := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (x / h))
  change x ≤ (⌊x / h⌋₊ : Real) * h + h
  nlinarith

theorem levelCount_bound {h : Real} (hh : 0 < h) (hh1 : h ≤ 1) :
    (levelCount h : Real) ≤ 3 / h := by
  have hc := Nat.ceil_lt_add_one (by positivity : (0 : Real) ≤ 1 / h)
  unfold levelCount
  push_cast
  apply (le_div_iff₀ hh).mpr
  have hx := mul_lt_mul_of_pos_right hc hh
  have hcancel : ((1 : Real) / h) * h = 1 := div_mul_cancel₀ 1 hh.ne'
  nlinarith

theorem weight_upper_of_small {h d : Real} (hh : 0 < h) (hhd : h ≤ d)
    (q : Fin (levelCount h)) (hR : levelRadius q ≤ d) : weight q ≤ d ^ 2 := by
  apply (sq_le_sq₀ (le_trans hh.le (le_max_right _ _)) (hh.le.trans hhd)).mpr
  exact max_le hR hhd

theorem weight_lower_of_large {h a x : Real} (hh : 0 < h) (ha : 0 ≤ a)
    (hha : h ≤ a / 2) (q : Fin (levelCount h)) (hlarge : a ≤ x)
    (happrox : x ≤ levelRadius q + h) : a ^ 2 / 4 ≤ weight q := by
  have hR : a / 2 ≤ max (levelRadius q) h := by
    linarith [le_max_left (levelRadius q) h]
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ a / 2)
    (hh.le.trans (le_max_right _ _))).mpr hR
  unfold weight
  nlinarith

#print axioms exists_annular_net
#print axioms exists_level

end HighBandLSV.PlanarNets

