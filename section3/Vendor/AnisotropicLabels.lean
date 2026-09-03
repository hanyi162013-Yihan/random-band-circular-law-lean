/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/AnisotropicLabels.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RealAnisotropicGeometry
import Vendor.PlanarNets

/-! Three scalar labels and one phase per complex block for real-entry matrices. -/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace HighBandLSV.Anisotropic

abbrev RadiusLabel (h : Real) := Fin (PlanarNets.levelCount h)
abbrev Label (h : Real) := Bool × RadiusLabel h × RadiusLabel h × RadiusLabel (h / 2)

def radius (h : Real) (q : RadiusLabel h) : Real := (q.val : Real) * h

def angle {h : Real} (q : Label h) : Real := -1 + 2 * radius (h / 2) q.2.2.2

def xRadius {h : Real} (q : Label h) : Real := radius h q.2.1

def yRadius {h : Real} (q : Label h) : Real := radius h q.2.2.1

def labelWeight {h : Real} (q : Label h) : Real := max (xRadius q) h * max (yRadius q) h

def chooseRadius {h x : Real} (hh : 0 < h) (hx : 0 ≤ x) (hx1 : x ≤ 1) : RadiusLabel h := by
  let k := Nat.floor (x / h)
  have hf : (k : Real) ≤ x / h := Nat.floor_le (div_nonneg hx hh.le)
  have hc : x / h ≤ (Nat.ceil (1 / h) : Real) :=
    (div_le_div_of_nonneg_right hx1 hh.le).trans (Nat.le_ceil (1 / h))
  have hk : k ≤ Nat.ceil (1 / h) := by exact_mod_cast hf.trans hc
  exact ⟨k, by unfold PlanarNets.levelCount; omega⟩

theorem chooseRadius_bounds {h x : Real} (hh : 0 < h) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    radius h (chooseRadius hh hx hx1) ≤ x ∧
      x ≤ radius h (chooseRadius hh hx hx1) + h := by
  have hf := Nat.floor_le (div_nonneg hx hh.le)
  have hg := Nat.lt_floor_add_one (x / h)
  constructor
  · exact (le_div_iff₀ hh).mp hf
  · have := (div_lt_iff₀ hh).mp hg
    change x ≤ (Nat.floor (x / h) : Real) * h + h
    push_cast at this
    nlinarith

theorem chooseRadius_mono {h x y : Real} (hh : 0 < h)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) (hxy : x ≤ y) :
    radius h (chooseRadius hh hx hx1) ≤ radius h (chooseRadius hh hy hy1) := by
  have hf := Nat.floor_mono (div_le_div_of_nonneg_right hxy hh.le)
  have hfc : (Nat.floor (x / h) : Real) ≤ Nat.floor (y / h) := by exact_mod_cast hf
  exact mul_le_mul_of_nonneg_right hfc hh.le

theorem radius_nonneg {h : Real} (hh : 0 ≤ h) (q : RadiusLabel h) : 0 ≤ radius h q := by
  unfold radius
  positivity

theorem label_card_bound {h : Real} (hh : 0 < h) (hh1 : h ≤ 1) :
    (Fintype.card (Label h) : Real) ≤ (5 / h) ^ 3 := by
  have hc := PlanarNets.levelCount_bound hh hh1
  have hd := PlanarNets.levelCount_bound (by positivity : 0 < h / 2)
    (by linarith : h / 2 ≤ 1)
  simp only [Label, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Nat.cast_mul,
    Nat.cast_ofNat]
  calc
    (2 : Real) * ((PlanarNets.levelCount h : Real) *
        ((PlanarNets.levelCount h : Real) * PlanarNets.levelCount (h / 2))) ≤
        2 * ((3 / h) * ((3 / h) * (3 / (h / 2)))) := by gcongr
    _ ≤ (5 / h) ^ 3 := by
      field_simp
      nlinarith

variable {I : Type*} [Fintype I]

def blockClass {h : Real} (q : Label h) : Set (CV I) :=
  {u | ‖u‖ ≤ 1 ∧
    ‖imagPart (rotate q.1 u)‖ ≤ ‖realPart (rotate q.1 u)‖ ∧
    xRadius q ≤ ‖realPart (rotate q.1 u)‖ ∧
    ‖realPart (rotate q.1 u)‖ ≤ xRadius q + h ∧
    yRadius q ≤ ‖residual (realPart (rotate q.1 u)) (imagPart (rotate q.1 u))‖ ∧
    ‖residual (realPart (rotate q.1 u)) (imagPart (rotate q.1 u))‖ ≤ yRadius q + h ∧
    |shear (realPart (rotate q.1 u)) (imagPart (rotate q.1 u)) - angle q| ≤ h}

def admissible {h : Real} (q : Label h) : Prop :=
  xRadius q ≤ 1 ∧ yRadius q ≤ xRadius q ∧ |angle q| ≤ 1

theorem exists_block_label {h : Real} (hh : 0 < h) (u : CV I) (hu : ‖u‖ ≤ 1) :
    ∃ q : Label h, admissible q ∧ u ∈ blockClass q := by
  obtain ⟨phase, hp⟩ := exists_dominant_phase u
  let a := realPart (rotate phase u)
  let b := imagPart (rotate phase u)
  have ha : ‖a‖ ≤ 1 := (realPart_norm_le _).trans (by simpa using hu)
  have hb : ‖residual a b‖ ≤ ‖a‖ := (residual_norm_le a b).trans hp
  have hb1 : ‖residual a b‖ ≤ 1 := hb.trans ha
  have halpha : |shear a b| ≤ 1 := shear_abs_le_one hp
  have ha0 : 0 ≤ (shear a b + 1) / 2 := by rw [abs_le] at halpha; linarith
  have ha1 : (shear a b + 1) / 2 ≤ 1 := by rw [abs_le] at halpha; linarith
  let qx := chooseRadius hh (norm_nonneg a) ha
  let qy := chooseRadius hh (norm_nonneg (residual a b)) hb1
  let qa := chooseRadius (by positivity : 0 < h / 2) ha0 ha1
  let q : Label h := (phase, qx, qy, qa)
  have hx := chooseRadius_bounds hh (norm_nonneg a) ha
  have hy := chooseRadius_bounds hh (norm_nonneg (residual a b)) hb1
  have hz := chooseRadius_bounds (by positivity : 0 < h / 2) ha0 ha1
  have hxy := chooseRadius_mono hh (norm_nonneg (residual a b)) hb1
    (norm_nonneg a) ha hb
  have hz0 : 0 ≤ radius (h / 2) qa := radius_nonneg (by positivity) qa
  refine ⟨q, ?_, ?_⟩
  · refine ⟨hx.1.trans ha, hxy, ?_⟩
    change |-1 + 2 * radius (h / 2) qa| ≤ 1
    rw [abs_le]
    constructor <;> linarith [hz.1]
  · refine ⟨hu, hp, hx.1, hx.2, hy.1, hy.2, ?_⟩
    change |shear a b - (-1 + 2 * radius (h / 2) qa)| ≤ h
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]

theorem small_block_weight {h d : Real} (hh : 0 < h) (hhd : h ≤ d)
    (q : Label h) {u : CV I} (hu : u ∈ blockClass q) (hsmall : ‖u‖ ≤ d) :
    labelWeight q ≤ d ^ 2 := by
  have hx : xRadius q ≤ d := hu.2.2.1.trans ((realPart_norm_le _).trans (by simpa using hsmall))
  have hy : yRadius q ≤ d := hu.2.2.2.2.1.trans
    ((residual_norm_le _ _).trans ((imagPart_norm_le _).trans (by simpa using hsmall)))
  unfold labelWeight
  have hx0 : 0 ≤ max (xRadius q) h := le_trans hh.le (le_max_right _ _)
  have hy0 : 0 ≤ max (yRadius q) h := le_trans hh.le (le_max_right _ _)
  nlinarith [mul_le_mul (max_le hx hhd) (max_le hy hhd) hy0 (by linarith : 0 ≤ d)]

theorem heavy_block_weight {h J : Real} (hh : 0 < h) (hJ : 0 < J)
    (hmesh : h * Real.sqrt J ≤ 1 / 4) (q : Label h) {u : CV I}
    (hu : u ∈ blockClass q) (hheavy : 1 / Real.sqrt J ≤ ‖u‖) :
    h / (4 * Real.sqrt J) ≤ labelWeight q := by
  have hs : 0 < Real.sqrt J := Real.sqrt_pos.2 hJ
  have hn : ‖u‖ ≤ 2 * ‖realPart (rotate q.1 u)‖ := by
    have h := norm_join_le (realPart (rotate q.1 u)) (imagPart (rotate q.1 u))
    rw [join_parts, norm_rotate] at h
    linarith [hu.2.1]
  have hupp := hu.2.2.2.1
  have hx : 1 / (4 * Real.sqrt J) ≤ xRadius q := by
    have hg := (div_le_iff₀ hs).mp hheavy
    apply (div_le_iff₀ (by positivity : 0 < 4 * Real.sqrt J)).2
    nlinarith [mul_le_mul_of_nonneg_right hn hs.le,
      mul_le_mul_of_nonneg_right hupp hs.le]
  have hxx := le_max_left (xRadius q) h
  unfold labelWeight
  calc
    h / (4 * Real.sqrt J) = (1 / (4 * Real.sqrt J)) * h := by ring
    _ ≤ max (xRadius q) h * max (yRadius q) h :=
      mul_le_mul (hx.trans hxx) (le_max_right _ _) hh.le (by positivity)

end HighBandLSV.Anisotropic

#print axioms HighBandLSV.Anisotropic.exists_block_label
#print axioms HighBandLSV.Anisotropic.heavy_block_weight

