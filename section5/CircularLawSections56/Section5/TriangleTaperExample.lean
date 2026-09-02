import CircularLawSections56.Section5.PolynomialTaperProfile

/-! # A concrete non-vacuous taper: the triangular tent

This explicit profile satisfies every manuscript condition, including global
bounded variation and boundary vanishing. It can be passed directly to either
the real or the complex full taper endpoint.
-/

open Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 800000
set_option autoImplicit false

namespace CircularLawSections56.Section5

def triangleTaper (x : ℝ) : ℝ := max 0 (1 - |x|)

theorem triangleTaper_bounds (x : ℝ) : 0 ≤ triangleTaper x ∧ triangleTaper x ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (by linarith [abs_nonneg x])⟩

theorem triangleTaper_monotone_left : MonotoneOn triangleTaper (Iic 0) := by
  intro a ha b hb hab
  change a ≤ 0 at ha
  change b ≤ 0 at hb
  simp only [triangleTaper, abs_of_nonpos ha, abs_of_nonpos hb]
  exact max_le_max le_rfl (by linarith)

theorem triangleTaper_antitone_right : AntitoneOn triangleTaper (Ici 0) := by
  intro a ha b hb hab
  change 0 ≤ a at ha
  change 0 ≤ b at hb
  simp only [triangleTaper, abs_of_nonneg ha, abs_of_nonneg hb]
  exact max_le_max le_rfl (by linarith)

theorem triangleTaper_boundedVariation : BoundedVariationOn triangleTaper univ := by
  have hbound (x : ℝ) : |triangleTaper x| ≤ 1 := by
    rw [abs_of_nonneg (triangleTaper_bounds x).1]
    exact (triangleTaper_bounds x).2
  have hl : BoundedVariationOn triangleTaper (Iic 0) :=
    triangleTaper_monotone_left.boundedVariationOn (fun x _ => hbound x)
  have hr : BoundedVariationOn triangleTaper (Ici 0) := by
    have hv := eVariationOn.comp_le_of_antitoneOn triangleTaper (fun x : ℝ => -x)
      (t := Ici (0 : ℝ)) (s := Iic (0 : ℝ))
      (fun _ _ _ _ hab => neg_le_neg hab) (by
        intro x hx
        change 0 ≤ x at hx
        change -x ≤ 0
        linarith)
    have hb : BoundedVariationOn (triangleTaper ∘ fun x : ℝ => -x) (Ici 0) :=
      ne_of_lt (hv.trans_lt (lt_top_iff_ne_top.2 hl))
    have he : (triangleTaper ∘ fun x : ℝ => -x) = triangleTaper := by
      funext x
      simp only [Function.comp_apply, triangleTaper, abs_neg]
    rw [he] at hb
    exact hb
  have hunion : Iic (0 : ℝ) ∪ Ici 0 = univ := by
    ext x
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total x 0
  unfold BoundedVariationOn at hl hr ⊢
  rw [← hunion, eVariationOn.union triangleTaper isGreatest_Iic isLeast_Ici]
  exact ENNReal.add_ne_top.2 ⟨hl, hr⟩

def triangleTaperProfile : PolynomialTaperProfile where
  f := triangleTaper
  lower := 1
  upper := 1
  exponent := 1
  lower_pos := by norm_num
  upper_pos := by norm_num
  exponent_nonneg := by norm_num
  nonneg := fun x => (triangleTaper_bounds x).1
  boundedVariation := triangleTaper_boundedVariation
  vanishes := by
    intro x hx
    exact max_eq_left (by linarith)
  interior := by
    intro x _hx
    simp only [Real.rpow_one, one_mul]
    exact ⟨le_max_right _ _, (triangleTaper_bounds x).2⟩

@[simp] theorem triangleTaperProfile_value (x : ℝ) :
    triangleTaperProfile.f x = max 0 (1 - |x|) := rfl

theorem triangleTaperProfile_raw (W : ℕ) (i : Fin (2 * W + 1)) :
    triangleTaperProfile.raw W i = 1 - |taperGrid W i| := by
  exact max_eq_right (sub_nonneg.2 (taperGrid_abs_lt_one W i).le)

end CircularLawSections56.Section5
