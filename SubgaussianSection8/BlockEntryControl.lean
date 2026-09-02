import SubgaussianSection8.Interface
import BernoulliSection9.TerminalConcreteBounds

/-! Operator-norm control supplies the normalized entry bounds needed for every exterior degree. -/
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
namespace SubgaussianSection8
open BernoulliSection9 BernoulliSection10 BernoulliLinearAlgebra

theorem opNormConstant_nonneg (A : Atom) : 0 ≤ opNormConstant A := by
  unfold opNormConstant
  positivity

theorem opNormConstant_one_le (A : Atom) : 1 ≤ opNormConstant A := by
  have hs : (1 : ℝ) ≤ Real.sqrt (A.parameter + 1) :=
    Real.one_le_sqrt.mpr (le_add_of_nonneg_left (NNReal.coe_nonneg _))
  unfold opNormConstant
  linarith

def growthParameter (A : Atom) (z : ℂ) : ℂ := (3 * opNormConstant A + ‖z‖ : ℝ)

theorem growthParameter_norm (A : Atom) (z : ℂ) :
    ‖growthParameter A z‖ = 3 * opNormConstant A + ‖z‖ := by
  have hnonneg : 0 ≤ 3 * opNormConstant A + ‖z‖ :=
    add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (opNormConstant_nonneg A))
      (norm_nonneg z)
  simp only [growthParameter, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]

theorem step_entry_bounds_of_norm_sum_le
    {W : ℕ} (B D C : Matrix (Fin W) (Fin W) ℂ) (q : ℂ)
    (h : ‖D‖ + ‖B‖ + ‖C‖ ≤ ‖q‖) :
    (∀ i j, ‖stepL B i j‖ ≤ 1 + ‖q‖) ∧
    (∀ i j, ‖stepK D C i j‖ ≤ 1 + ‖q‖) := by
  have hB (a c : Fin W) : ‖B a c‖ ≤ 1 + ‖q‖ :=
    (norm_matrix_entry_le_l2_opNorm B a c).trans (by linarith [norm_nonneg D, norm_nonneg C])
  have hD (a c : Fin W) : ‖D a c‖ ≤ 1 + ‖q‖ :=
    (norm_matrix_entry_le_l2_opNorm D a c).trans (by linarith [norm_nonneg B, norm_nonneg C])
  have hC (a c : Fin W) : ‖C a c‖ ≤ 1 + ‖q‖ :=
    (norm_matrix_entry_le_l2_opNorm C a c).trans (by linarith [norm_nonneg D, norm_nonneg B])
  constructor
  · intro i j
    cases i with
    | inl a =>
      cases j with
      | inl c => exact hB a c
      | inr c => simp [stepL]; positivity
    | inr a =>
      cases j with
      | inl c => simp [stepL]; positivity
      | inr c => by_cases hac : a = c <;> simp [stepL, Matrix.one_apply, hac] <;> positivity
  · intro i j
    cases i with
    | inl a =>
      cases j with
      | inl c => exact hD a c
      | inr c => exact hC a c
    | inr a =>
      cases j with
      | inl c => by_cases hac : a = c <;> simp [stepK, Matrix.one_apply, hac] <;> positivity
      | inr c => simp [stepK]; positivity

theorem site_step_entry_bounds_of_good
    (A : Atom) (I : NguyenBottomSingularInput.{0, 0}) (hI : A.parameter ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (z : ℂ) (x : IntervalRows W s) (hx : x ∉ subgaussianInterfaceBadEvent A I W s)
    (j : Fin s) :
    (∀ a c, ‖stepL (intervalSiteBlocks z x j).B a c‖ ≤ 1 + ‖growthParameter A z‖) ∧
    (∀ a c, ‖stepK (intervalSiteBlocks z x j).D (intervalSiteBlocks z x j).C a c‖ ≤
      1 + ‖growthParameter A z‖) := by
  apply step_entry_bounds_of_norm_sum_le
  rw [growthParameter_norm]
  exact subgaussianSite_shifted_norm_sum_le_of_good A I hI W s hW x hx j z

end SubgaussianSection8
