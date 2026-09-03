/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealWeightedGeometry.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RealAnisotropicGeometry

/-! Ellipticity on one block controls the full-column real Gram determinant.
This avoids introducing any unproved conditional density or density-scaling interface. -/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace HighBandLSV.Anisotropic

variable {N : Nat}

def weightReal (s : Fin N → Real) (a : RV (Fin N)) : RV (Fin N) :=
  WithLp.toLp 2 (fun i => s i * a i)

def restrictReal (B : Finset (Fin N)) (a : RV (Fin N)) : RV {i // i ∈ B} :=
  WithLp.toLp 2 (fun i => a i)

theorem weightReal_norm_sq (s : Fin N → Real) (a : RV (Fin N)) :
    ‖weightReal s a‖ ^ 2 = ∑ i, s i ^ 2 * a i ^ 2 := by
  simp [PiLp.norm_sq_eq_of_L2, weightReal, Real.norm_eq_abs, sq_abs, mul_pow]

theorem restrictReal_norm_sq (B : Finset (Fin N)) (a : RV (Fin N)) :
    ‖restrictReal B a‖ ^ 2 = ∑ i ∈ B, a i ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [restrictReal, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]
  exact Finset.sum_coe_sort B (fun i => a i ^ 2)

@[simp] theorem weightReal_sub (s : Fin N → Real) (a b : RV (Fin N)) :
    weightReal s (a - b) = weightReal s a - weightReal s b := by
  ext i
  simp [weightReal, mul_sub]

@[simp] theorem weightReal_smul (s : Fin N → Real) (a : RV (Fin N)) (t : Real) :
    weightReal s (t • a) = t • weightReal s a := by
  ext i
  simp [weightReal]
  ring

@[simp] theorem restrictReal_sub (B : Finset (Fin N)) (a b : RV (Fin N)) :
    restrictReal B (a - b) = restrictReal B a - restrictReal B b := by
  ext i
  rfl

@[simp] theorem restrictReal_smul (B : Finset (Fin N)) (a : RV (Fin N)) (t : Real) :
    restrictReal B (t • a) = t • restrictReal B a := by
  ext i
  rfl

theorem weighted_block_energy (s : Fin N → Real) (B : Finset (Fin N))
    (a : RV (Fin N)) {q : Real} (hq : 0 ≤ q)
    (hlower : ∀ i ∈ B, q ≤ s i ^ 2) :
    q * ‖restrictReal B a‖ ^ 2 ≤ ‖weightReal s a‖ ^ 2 := by
  rw [weightReal_norm_sq, restrictReal_norm_sq, Finset.mul_sum]
  calc
    ∑ i ∈ B, q * a i ^ 2 ≤ ∑ i ∈ B, s i ^ 2 * a i ^ 2 :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hlower i hi) (sq_nonneg _))
    _ ≤ ∑ i, s i ^ 2 * a i ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
        (fun i _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem weighted_block_residual (s : Fin N → Real) (B : Finset (Fin N))
    (a b : RV (Fin N)) {q : Real} (hq : 0 ≤ q)
    (hlower : ∀ i ∈ B, q ≤ s i ^ 2) :
    q * ‖residual (restrictReal B a) (restrictReal B b)‖ ^ 2 ≤
      ‖residual (weightReal s a) (weightReal s b)‖ ^ 2 := by
  let beta := shear (weightReal s a) (weightReal s b)
  have he : residual (weightReal s a) (weightReal s b) = weightReal s (b - beta • a) := by
    simp only [weightReal_sub, weightReal_smul, residual, beta]
  have hb := weighted_block_energy s B (b - beta • a) hq hlower
  have hm := residual_norm_minimal (restrictReal B a) (restrictReal B b) beta
  have hsq : ‖residual (restrictReal B a) (restrictReal B b)‖ ^ 2 ≤
      ‖restrictReal B b - beta • restrictReal B a‖ ^ 2 := by
    nlinarith [norm_nonneg (residual (restrictReal B a) (restrictReal B b)),
      norm_nonneg (restrictReal B b - beta • restrictReal B a)]
  rw [he]
  apply (mul_le_mul_of_nonneg_left hsq hq).trans
  simpa only [restrictReal_sub, restrictReal_smul] using hb

theorem weighted_block_gram_product (s : Fin N → Real) (B : Finset (Fin N))
    (a b : RV (Fin N)) {q : Real} (hq : 0 ≤ q)
    (hlower : ∀ i ∈ B, q ≤ s i ^ 2) :
    q * (‖restrictReal B a‖ * ‖residual (restrictReal B a) (restrictReal B b)‖) ≤
      ‖weightReal s a‖ * ‖residual (weightReal s a) (weightReal s b)‖ := by
  have h1 := weighted_block_energy s B a hq hlower
  have h2 := weighted_block_residual s B a b hq hlower
  have hm := mul_le_mul h1 h2 (by positivity) (sq_nonneg ‖weightReal s a‖)
  have hl : 0 ≤ q * (‖restrictReal B a‖ * ‖residual (restrictReal B a) (restrictReal B b)‖) := by
    positivity
  have hr : 0 ≤ ‖weightReal s a‖ * ‖residual (weightReal s a) (weightReal s b)‖ := by
    positivity
  nlinarith

end HighBandLSV.Anisotropic

#print axioms HighBandLSV.Anisotropic.weighted_block_gram_product

