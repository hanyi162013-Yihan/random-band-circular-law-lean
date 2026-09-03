/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealAnisotropicGeometry.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.InternalNet

/-! Real and imaginary block geometry used for the anisotropic nets. -/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace HighBandLSV.Anisotropic

abbrev RV (I : Type*) [Fintype I] := EuclideanSpace Real I
abbrev CV (I : Type*) [Fintype I] := EuclideanSpace Complex I

variable {I : Type*} [Fintype I]

def realPart (u : CV I) : RV I := WithLp.toLp 2 (fun i => (u i).re)
def imagPart (u : CV I) : RV I := WithLp.toLp 2 (fun i => (u i).im)
def join (a b : RV I) : CV I := WithLp.toLp 2 (fun i => (a i : Complex) + (b i : Complex) * Complex.I)

@[simp] theorem realPart_join (a b : RV I) : realPart (join a b) = a := by
  ext i
  simp [realPart, join]

@[simp] theorem imagPart_join (a b : RV I) : imagPart (join a b) = b := by
  ext i
  simp [imagPart, join]

@[simp] theorem join_parts (u : CV I) : join (realPart u) (imagPart u) = u := by
  ext i
  exact Complex.re_add_im (u i)

theorem norm_join_sq (a b : RV I) : ‖join a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  simp [PiLp.norm_sq_eq_of_L2, join, Complex.sq_norm, Complex.normSq_apply,
    Finset.sum_add_distrib, Real.norm_eq_abs, sq_abs]
  simp only [pow_two]

theorem parts_norm_sq (u : CV I) : ‖u‖ ^ 2 = ‖realPart u‖ ^ 2 + ‖imagPart u‖ ^ 2 := by
  rw [← norm_join_sq, join_parts]

theorem norm_join_le (a b : RV I) : ‖join a b‖ ≤ ‖a‖ + ‖b‖ := by
  have h := norm_join_sq a b
  nlinarith [norm_nonneg (join a b), norm_nonneg a, norm_nonneg b]

theorem realPart_norm_le (u : CV I) : ‖realPart u‖ ≤ ‖u‖ := by
  nlinarith [parts_norm_sq u, norm_nonneg u, norm_nonneg (realPart u), sq_nonneg ‖imagPart u‖]

theorem imagPart_norm_le (u : CV I) : ‖imagPart u‖ ≤ ‖u‖ := by
  nlinarith [parts_norm_sq u, norm_nonneg u, norm_nonneg (imagPart u), sq_nonneg ‖realPart u‖]

theorem join_sub (a b a' b' : RV I) : join a b - join a' b' = join (a - a') (b - b') := by
  ext i
  simp [join]
  ring

def rotate (phase : Bool) (u : CV I) : CV I := if phase then Complex.I • u else u

def unrotate (phase : Bool) (u : CV I) : CV I := if phase then (-Complex.I) • u else u

@[simp] theorem norm_rotate (phase : Bool) (u : CV I) : ‖rotate phase u‖ = ‖u‖ := by
  cases phase <;> simp [rotate, norm_smul]

@[simp] theorem norm_unrotate (phase : Bool) (u : CV I) : ‖unrotate phase u‖ = ‖u‖ := by
  cases phase <;> simp [unrotate, norm_smul]

@[simp] theorem unrotate_rotate (phase : Bool) (u : CV I) : unrotate phase (rotate phase u) = u := by
  cases phase <;> simp [unrotate, rotate, smul_smul]

@[simp] theorem rotate_unrotate (phase : Bool) (u : CV I) : rotate phase (unrotate phase u) = u := by
  cases phase <;> simp [unrotate, rotate, smul_smul]

theorem unrotate_sub (phase : Bool) (u v : CV I) :
    unrotate phase u - unrotate phase v = unrotate phase (u - v) := by
  cases phase <;> simp [unrotate, smul_sub]

theorem realPart_I (u : CV I) : realPart (Complex.I • u) = -imagPart u := by
  ext i
  simp [realPart, imagPart, Complex.mul_re]

theorem imagPart_I (u : CV I) : imagPart (Complex.I • u) = realPart u := by
  ext i
  simp [realPart, imagPart, Complex.mul_im]

theorem exists_dominant_phase (u : CV I) :
    ∃ phase, ‖imagPart (rotate phase u)‖ ≤ ‖realPart (rotate phase u)‖ := by
  by_cases h : ‖imagPart u‖ ≤ ‖realPart u‖
  · exact ⟨false, by simpa [rotate] using h⟩
  · refine ⟨true, ?_⟩
    simp only [rotate, Bool.true_eq, if_true, realPart_I, imagPart_I, norm_neg]
    linarith

section Gram
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]

def shear (a b : E) : Real := ⟪a, b⟫_ℝ / ‖a‖ ^ 2

def residual (a b : E) : E := b - shear a b • a

theorem residual_orthogonal (a b : E) : ⟪a, residual a b⟫_ℝ = 0 := by
  by_cases ha : a = 0
  · simp [ha]
  have hden : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)
  simp only [residual, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, shear]
  rw [div_mul_cancel₀ _ hden, sub_self]

theorem shear_abs_le_one {a b : E} (h : ‖b‖ ≤ ‖a‖) : |shear a b| ≤ 1 := by
  by_cases ha : a = 0
  · simp [shear, ha]
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hc : |⟪a, b⟫_ℝ| ≤ ‖a‖ * ‖b‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := Real) a b
  unfold shear
  rw [abs_div, abs_of_nonneg (sq_nonneg ‖a‖)]
  apply (div_le_one (sq_pos_of_pos han)).2
  nlinarith [mul_le_mul_of_nonneg_left h han.le]

theorem residual_pythagoras (a b : E) (beta : Real) :
    ‖b - beta • a‖ ^ 2 = ‖residual a b‖ ^ 2 +
      (shear a b - beta) ^ 2 * ‖a‖ ^ 2 := by
  have heq : b - beta • a = residual a b + (shear a b - beta) • a := by
    unfold residual
    module
  rw [heq, norm_add_sq_real]
  have ho : ⟪residual a b, a⟫_ℝ = 0 := by
    rw [real_inner_comm, residual_orthogonal]
  simp [inner_smul_right, ho, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem residual_norm_minimal (a b : E) (beta : Real) :
    ‖residual a b‖ ≤ ‖b - beta • a‖ := by
  have h := residual_pythagoras a b beta
  nlinarith [norm_nonneg (residual a b), norm_nonneg (b - beta • a),
    mul_nonneg (sq_nonneg (shear a b - beta)) (sq_nonneg ‖a‖)]

theorem residual_norm_le (a b : E) : ‖residual a b‖ ≤ ‖b‖ := by
  simpa using residual_norm_minimal a b 0

theorem gram_product_sq (a b : E) :
    (‖a‖ * ‖residual a b‖) ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫_ℝ ^ 2 := by
  by_cases ha : a = 0
  · simp [ha]
  have hden : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)
  have h := residual_pythagoras a b 0
  simp only [zero_smul, sub_zero, shear] at h
  have hh := congrArg (fun x : Real => ‖a‖ ^ 2 * x) h
  field_simp [hden] at hh
  nlinarith

theorem gram_product_symm (a b : E) :
    ‖a‖ * ‖residual a b‖ = ‖b‖ * ‖residual b a‖ := by
  have h1 := gram_product_sq a b
  have h2 := gram_product_sq b a
  rw [real_inner_comm a b] at h2
  nlinarith [mul_nonneg (norm_nonneg a) (norm_nonneg (residual a b)),
    mul_nonneg (norm_nonneg b) (norm_nonneg (residual b a))]

end Gram
end HighBandLSV.Anisotropic

#print axioms HighBandLSV.Anisotropic.gram_product_symm

