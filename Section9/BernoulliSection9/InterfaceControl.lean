import BernoulliSection9.ExternalInputs
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Interface control for the normalized iid square

This file contains the deterministic singular-value bookkeeping and the
probability-event splice used at the beginning of Section 9.  The only
probabilistic hypotheses are the two fields of
`NguyenBottomSingularInput`; no matrix-elimination certificate is exposed.
-/

open scoped Matrix.Norms.L2Operator BigOperators ENNReal NNReal InnerProductSpace

noncomputable section

namespace BernoulliSection9

open MeasureTheory ProbabilityTheory Module InnerProductSpace

universe u

section Deterministic


set_option maxHeartbeats 1000000 in
/-- A lower bound on the last singular value is a lower bound for the map on
every vector.  This is the finite-dimensional min--max statement needed to
turn Nguyen's bottom-singular-value estimate into inverse control. -/
theorem smul_norm_le_norm_apply_of_le_bottomSingularValue
    {n : ℕ} (hn : 0 < n)
    (T : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
    {s : ℝ} (hs : 0 ≤ s) (hsv : s ≤ T.singularValues (n - 1))
    (x : EuclideanSpace ℂ (Fin n)) :
    s * ‖x‖ ≤ ‖T x‖ := by
  let H : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) := T.adjoint ∘ₗ T
  let hH : H.IsSymmetric := T.isSymmetric_adjoint_comp_self
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = n := by simp
  let b := hH.eigenvectorBasis hdim
  have hrePow (r : ℝ) : (((r : ℂ) ^ 2).re : ℝ) = r ^ 2 := by
    rw [← RCLike.re_eq_complex_re]
    exact RCLike.re_ofReal_pow r 2
  have hcoord (i : Fin n) :
      s ^ 2 ≤ hH.eigenvalues hdim i := by
    rw [← T.sq_singularValues_fin hdim i]
    have hi : i.val ≤ n - 1 := Nat.le_sub_one_of_lt i.isLt
    have hmono : T.singularValues (n - 1) ≤ T.singularValues i :=
      T.singularValues_antitone hi
    nlinarith [T.singularValues_nonneg i]
  have hpos : (H - ((s ^ 2 : ℝ) : ℂ) •
      (LinearMap.id : EuclideanSpace ℂ (Fin n) →ₗ[ℂ]
        EuclideanSpace ℂ (Fin n))).IsPositive := by
    refine ⟨hH.sub (LinearMap.IsSymmetric.id.smul (by simp)), ?_⟩
    intro y
    have hbH (i : Fin n) :
        b.repr (H y) i =
          hH.eigenvalues hdim i * b.repr y i := by
      simpa [b] using hH.eigenvectorBasis_apply_self_apply hdim y i
    have hscalar (a : ℝ) (z : ℂ) :
        RCLike.re (inner ℂ (((a : ℂ) * z)) z) = a * ‖z‖ ^ 2 := by
      rw [RCLike.inner_apply', map_mul (starRingEnd ℂ), starRingEnd_apply,
        RCLike.star_def,
        Complex.conj_ofReal]
      rw [mul_assoc, RCLike.conj_mul, RCLike.re_eq_complex_re,
        Complex.re_ofReal_mul, RCLike.ofReal_eq_complex_ofReal, hrePow]
    have hHy :
        RCLike.re (inner ℂ (H y) y) =
          ∑ i : Fin n, hH.eigenvalues hdim i * ‖b.repr y i‖ ^ 2 := by
      rw [← b.repr.inner_map_map, PiLp.inner_apply, map_sum]
      simp_rw [hbH, hscalar]
    have hsy :
        RCLike.re (inner ℂ (((s ^ 2 : ℝ) : ℂ) • y) y) =
          s ^ 2 * ‖y‖ ^ 2 := by
      rw [inner_smul_left, starRingEnd_apply, RCLike.star_def, Complex.conj_ofReal,
        inner_self_eq_norm_sq_to_K,
        RCLike.re_eq_complex_re, Complex.re_ofReal_mul,
        RCLike.ofReal_eq_complex_ofReal, hrePow]
    have hparseval : ∑ i : Fin n, ‖b.repr y i‖ ^ 2 = ‖y‖ ^ 2 := by
      calc
        ∑ i : Fin n, ‖b.repr y i‖ ^ 2 = ‖b.repr y‖ ^ 2 :=
          (EuclideanSpace.norm_sq_eq (b.repr y)).symm
        _ = ‖y‖ ^ 2 := by rw [b.repr.norm_map]
    have hre :
        RCLike.re (inner ℂ ((H - ((s ^ 2 : ℝ) : ℂ) •
          (LinearMap.id : EuclideanSpace ℂ (Fin n) →ₗ[ℂ]
            EuclideanSpace ℂ (Fin n))) y) y) =
          ∑ i : Fin n, (hH.eigenvalues hdim i - s ^ 2) * ‖b.repr y i‖ ^ 2 := by
      rw [LinearMap.sub_apply, inner_sub_left, map_sub, LinearMap.smul_apply,
        LinearMap.id_apply, hHy, hsy, ← hparseval, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hre]
    exact Finset.sum_nonneg fun i _ ↦
      mul_nonneg (sub_nonneg.mpr (hcoord i)) (sq_nonneg _)
  have hinner := hpos.re_inner_nonneg_left x
  have hsquare : s ^ 2 * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2 := by
    have hTx :
        RCLike.re (inner ℂ (H x) x) = ‖T x‖ ^ 2 := by
      simp [H, LinearMap.comp_apply, LinearMap.adjoint_inner_left,
        inner_self_eq_norm_sq_to_K]
      exact hrePow ‖T x‖
    have hsx :
        RCLike.re (inner ℂ (((s ^ 2 : ℝ) : ℂ) • x) x) =
          s ^ 2 * ‖x‖ ^ 2 := by
      rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
      rw [starRingEnd_apply, RCLike.star_def, Complex.conj_ofReal,
        RCLike.re_eq_complex_re, Complex.re_ofReal_mul,
        RCLike.ofReal_eq_complex_ofReal, hrePow]
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      inner_sub_left, map_sub, hTx, hsx] at hinner
    linarith
  nlinarith [norm_nonneg x, norm_nonneg (T x)]

/-- For a complex square matrix, the absolute determinant is exactly the
product of its (decreasing, zero-indexed) singular values. -/
theorem norm_det_eq_prod_matrixSingularValue {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ = ∏ j ∈ Finset.range n, matrixSingularValue A j := by
  let T := A.toEuclideanLin
  have hdet : T.normDet = ‖A.det‖ := by
    simpa [T, Matrix.toEuclideanLin_eq_toLin_orthonormal] using
      (T.normDet_eq_norm_det_toMatrix
        (EuclideanSpace.basisFun (Fin n) ℂ)
        (EuclideanSpace.basisFun (Fin n) ℂ))
  rw [← hdet, LinearMap.normDet_eq_prod_singularValues]
  simp [matrixSingularValue, T]

/-- Hadamard's inequality in operator-norm form.  This proof uses the
Gram--Schmidt basis of the images of a standard orthonormal basis, so no
singular-value inequality is hidden in the statement. -/
theorem normDet_le_pow_opNorm {n : ℕ}
    (T : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    T.normDet ≤ ‖T.toContinuousLinearMap‖ ^ n := by
  let b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) ℂ
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun i ↦ T (b i)
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) =
      Fintype.card (Fin n) := by simp
  let c : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    gramSchmidtOrthonormalBasis hdim v
  have hdet :
      ‖(T.toMatrix b.toBasis c.toBasis).det‖ = ‖c.toBasis.det v‖ := by
    rw [LinearMap.toMatrix_eq_basisToMatrix]
    rfl
  rw [T.normDet_eq_norm_det_toMatrix b c, hdet,
    gramSchmidtOrthonormalBasis_det hdim v, norm_prod]
  calc
    ∏ i : Fin n, ‖inner ℂ (c i) (v i)‖
        ≤ ∏ _i : Fin n, ‖T.toContinuousLinearMap‖ := by
          apply Finset.prod_le_prod
          · intro i _hi
            positivity
          · intro i _hi
            calc
              ‖inner ℂ (c i) (v i)‖ ≤ ‖c i‖ * ‖v i‖ :=
                norm_inner_le_norm _ _
              _ = ‖v i‖ := by simp [c]
              _ ≤ ‖T.toContinuousLinearMap‖ * ‖b i‖ :=
                T.toContinuousLinearMap.le_opNorm (b i)
              _ = ‖T.toContinuousLinearMap‖ := by simp [b]
    _ = ‖T.toContinuousLinearMap‖ ^ n := by simp

/-- Matrix form of Hadamard's inequality for mathlib's spectral C⋆-norm. -/
theorem norm_det_le_pow_norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ ≤ ‖A‖ ^ n := by
  let T := A.toEuclideanLin
  have hdet : T.normDet = ‖A.det‖ := by
    simpa [T, Matrix.toEuclideanLin_eq_toLin_orthonormal] using
      (T.normDet_eq_norm_det_toMatrix
        (EuclideanSpace.basisFun (Fin n) ℂ)
        (EuclideanSpace.basisFun (Fin n) ℂ))
  rw [← hdet, Matrix.cstar_norm_def]
  exact normDet_le_pow_opNorm T

/-- If the bottom singular value is at least `ε`, then the determinant is
at least `ε ^ n`.  This is the deterministic determinant step used after
each Cook estimate. -/
theorem pow_le_norm_det_of_le_matrixSMin {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) { ε : ℝ }
    (hε : 0 ≤ ε) (hmin : ε ≤ matrixSMin A) :
    ε ^ n ≤ ‖A.det‖ := by
  rw [norm_det_eq_prod_matrixSingularValue]
  have hmin' : ε ≤ matrixSingularValue A (n - 1) := by
    simpa [matrixSMin, ne_of_gt hn] using hmin
  calc
    ε ^ n = ∏ _j ∈ Finset.range n, ε := by simp
    _ ≤ ∏ j ∈ Finset.range n, matrixSingularValue A j := by
      gcongr with j hj
      exact le_trans hmin'
        (A.toEuclideanLin.singularValues_antitone
          (Nat.le_sub_one_of_lt (Finset.mem_range.mp hj)))

/-- A positive bottom-singular-value lower bound gives the reciprocal
operator-norm bound for the nonsingular inverse. -/
theorem norm_nonsing_inv_le_inv_of_le_matrixSMin {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) {s : ℝ}
    (hs : 0 < s) (hmin : s ≤ matrixSMin A) :
    ‖A⁻¹‖ ≤ s⁻¹ := by
  have hdetNorm : 0 < ‖A.det‖ :=
    lt_of_lt_of_le (pow_pos hs n)
      (pow_le_norm_det_of_le_matrixSMin hn A hs.le hmin)
  have hdet : A.det ≠ 0 := norm_pos_iff.mp hdetNorm
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  let F := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A
  let G := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A⁻¹
  have hmin' : s ≤ A.toEuclideanLin.singularValues (n - 1) := by
    simpa [matrixSMin, ne_of_gt hn, matrixSingularValue] using hmin
  rw [Matrix.cstar_norm_def]
  apply G.opNorm_le_bound (inv_nonneg.mpr hs.le)
  intro x
  have hlower :=
    smul_norm_le_norm_apply_of_le_bottomSingularValue hn A.toEuclideanLin
      hs.le hmin' (G x)
  have hcancel : A.toEuclideanLin (G x) = x := by
    change F (G x) = x
    change (F * G) x = x
    rw [← map_mul]
    simp [F, G, A.mul_nonsing_inv hunit]
  rw [hcancel] at hlower
  calc
    ‖G x‖ ≤ ‖x‖ / s := (le_div_iff₀ hs).2 (by simpa [mul_comm] using hlower)
    _ = s⁻¹ * ‖x‖ := by field_simp

end Deterministic

section NguyenSplice


/-- The paper's choice `exp (-a n / k²)` up to `sqrt n` (and always on
the fixed-index range), followed by the fixed bulk value `ε₀`. -/
def nguyenInterfaceEpsilon (I : NguyenBottomSingularInput)
    (n : ℕ) (a ε₀ : ℝ) (k : ℕ) : ℝ :=
  if k ≤ max I.k0 n.sqrt then
    Real.exp (-a * (n : ℝ) / (k : ℝ) ^ 2)
  else ε₀

/-- The concrete exponential scale used to splice the three Nguyen ranges.
The deliberately elementary choice `C + 1` avoids hiding any asymptotic
constant selection behind a certificate. -/
def nguyenInterfaceA (I : NguyenBottomSingularInput) : ℝ :=
  I.nguyenC + 1

/-- The constant `ε₀` used beyond the square-root transition. -/
def nguyenInterfaceEpsilon0 (I : NguyenBottomSingularInput) : ℝ :=
  Real.exp (-nguyenInterfaceA I)

/-- A common positive exponential rate for Nguyen's main term and its
exceptional `exp (-c n)` term. -/
def nguyenInterfaceRate (I : NguyenBottomSingularInput) : ℝ :=
  min (1 - I.theta) I.nguyenc

/-- A fixed fraction strictly below both `γ₀` and `1`; it makes the bulk
cutoff canonical rather than caller-chosen. -/
def nguyenInterfaceCutoffFraction (I : NguyenBottomSingularInput) : ℝ :=
  min (I.gamma0 / 4) (1 / 4)

/-- Half the cutoff fraction, reserved to absorb the natural-floor error. -/
def nguyenInterfaceCutoffRho (I : NguyenBottomSingularInput) : ℝ :=
  nguyenInterfaceCutoffFraction I / 2

/-- The paper's `⌊γn/2⌋`-type canonical cutoff, with a slightly smaller
explicit fraction to simplify all strict inequalities. -/
def nguyenInterfaceCutoff (I : NguyenBottomSingularInput) (n : ℕ) : ℕ :=
  ⌊nguyenInterfaceCutoffFraction I * (n : ℝ)⌋₊

/-- The raw-matrix threshold: fixed-index estimates use `ε / √n`,
whereas overcrowding uses `k ε / √n`. -/
def nguyenInterfaceThreshold (I : NguyenBottomSingularInput)
    (n : ℕ) (a ε₀ : ℝ) (k : ℕ) : ℝ :=
  if k ≤ I.k0 then
    nguyenInterfaceEpsilon I n a ε₀ k / Real.sqrt n
  else
    (k : ℝ) * nguyenInterfaceEpsilon I n a ε₀ k / Real.sqrt n

def nguyenInterfaceBadAt
    { Ω : Type* } [MeasurableSpace Ω] { μ : Measure Ω } { n : ℕ }
    (I : NguyenBottomSingularInput)
    (S : IidSubgaussianSquare Ω μ n)
    (a ε₀ : ℝ) (k : ℕ) : Set Ω :=
  { ω | matrixSingularValue (S.rawMatrix ω) (n - k) ≤
      nguyenInterfaceThreshold I n a ε₀ k }

/-- Explicit per-index failure bound after splicing Nguyen's fixed-index
and overcrowding estimates. -/
def nguyenInterfaceFailureAt (I : NguyenBottomSingularInput)
    (n : ℕ) (a ε₀ : ℝ) (k : ℕ) : ℝ :=
  if k ≤ I.k0 then
    nguyenFixedIndexBound I.nguyenC I.nguyenc
      (nguyenInterfaceEpsilon I n a ε₀ k) n k
  else
    nguyenOvercrowdingBound I.nguyenC I.nguyenc I.theta
      (nguyenInterfaceEpsilon I n a ε₀ k) n k

/-- The finite union of bottom-singular-value failures through index `K`. -/
def nguyenInterfaceBadEvent
    { Ω : Type* } [MeasurableSpace Ω] { μ : Measure Ω } { n : ℕ }
    (I : NguyenBottomSingularInput)
    (S : IidSubgaussianSquare Ω μ n)
    (a ε₀ : ℝ) (K : ℕ) : Set Ω :=
  ⋃ k ∈ Finset.Icc 1 K, nguyenInterfaceBadAt I S a ε₀ k

lemma nguyenInterfaceEpsilon_nonneg (I : NguyenBottomSingularInput)
    (n k : ℕ) (a ε₀ : ℝ) (hε₀ : 0 ≤ ε₀) :
    0 ≤ nguyenInterfaceEpsilon I n a ε₀ k := by
  unfold nguyenInterfaceEpsilon
  split_ifs <;> positivity

lemma nguyenInterfaceRate_pos (I : NguyenBottomSingularInput) :
    0 < nguyenInterfaceRate I := by
  exact lt_min (sub_pos.mpr I.theta_mem.2) I.c_pos

lemma nguyenInterfaceRate_le_delta (I : NguyenBottomSingularInput) :
    nguyenInterfaceRate I ≤ 1 - I.theta := min_le_left _ _

lemma nguyenInterfaceRate_le_c (I : NguyenBottomSingularInput) :
    nguyenInterfaceRate I ≤ I.nguyenc := min_le_right _ _

lemma nguyenInterfaceRate_le_one (I : NguyenBottomSingularInput) :
    nguyenInterfaceRate I ≤ 1 :=
  (nguyenInterfaceRate_le_delta I).trans (by linarith [I.theta_mem.1])

lemma nguyenInterfaceEpsilon0_pos (I : NguyenBottomSingularInput) :
    0 < nguyenInterfaceEpsilon0 I := Real.exp_pos _

lemma nguyenInterfaceCutoffFraction_pos (I : NguyenBottomSingularInput) :
    0 < nguyenInterfaceCutoffFraction I := by
  dsimp [nguyenInterfaceCutoffFraction]
  exact lt_min (div_pos I.gamma0_pos (by norm_num)) (by norm_num)

lemma nguyenInterfaceCutoffRho_pos (I : NguyenBottomSingularInput) :
    0 < nguyenInterfaceCutoffRho I := by
  dsimp [nguyenInterfaceCutoffRho]
  exact div_pos (nguyenInterfaceCutoffFraction_pos I) (by norm_num)

/-- For the explicit floor cutoff, one finite-size hypothesis supplies all
index, square-root, proportionality, and Nguyen-range conditions used below. -/
theorem nguyenInterfaceCutoff_spec (I : NguyenBottomSingularInput)
    (n : ℕ) (hn : 0 < n)
    (hlarge : 1 ≤ nguyenInterfaceCutoffRho I ^ 2 * (n : ℝ)) :
    1 ≤ nguyenInterfaceCutoff I n ∧
      nguyenInterfaceCutoff I n ≤ n ∧
      n ≤ (nguyenInterfaceCutoff I n) ^ 2 ∧
      nguyenInterfaceCutoffRho I * (n : ℝ) ≤
        (nguyenInterfaceCutoff I n : ℝ) ∧
      (nguyenInterfaceCutoff I n : ℝ) < I.gamma0 * n := by
  have hη : 0 < nguyenInterfaceCutoffFraction I :=
    nguyenInterfaceCutoffFraction_pos I
  have hρ : 0 < nguyenInterfaceCutoffRho I :=
    nguyenInterfaceCutoffRho_pos I
  have hρle : nguyenInterfaceCutoffRho I ≤ 1 := by
    dsimp [nguyenInterfaceCutoffRho, nguyenInterfaceCutoffFraction]
    have hm : min (I.gamma0 / 4) (1 / 4 : ℝ) ≤ 1 / 4 := min_le_right _ _
    linarith
  have hρn : 1 ≤ nguyenInterfaceCutoffRho I * (n : ℝ) := by
    have hrho_sq_le :
        nguyenInterfaceCutoffRho I ^ 2 ≤ nguyenInterfaceCutoffRho I := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hrho_sq_le
      (by positivity : 0 ≤ (n : ℝ))]
  have hηeq :
      nguyenInterfaceCutoffFraction I = 2 * nguyenInterfaceCutoffRho I := by
    dsimp [nguyenInterfaceCutoffRho]
    ring
  have harg0 :
      0 ≤ nguyenInterfaceCutoffFraction I * (n : ℝ) := by positivity
  have hfloorUpper :
      (nguyenInterfaceCutoff I n : ℝ) ≤
        nguyenInterfaceCutoffFraction I * (n : ℝ) := by
    exact Nat.floor_le harg0
  have hfloorLower :
      nguyenInterfaceCutoffRho I * (n : ℝ) ≤
        (nguyenInterfaceCutoff I n : ℝ) := by
    have hf := Nat.lt_floor_add_one
      (nguyenInterfaceCutoffFraction I * (n : ℝ))
    change nguyenInterfaceCutoffFraction I * (n : ℝ) <
      (nguyenInterfaceCutoff I n : ℝ) + 1 at hf
    rw [hηeq] at hf
    linarith
  have hK1 : 1 ≤ nguyenInterfaceCutoff I n := by
    exact_mod_cast hρn.trans hfloorLower
  have hηle : nguyenInterfaceCutoffFraction I ≤ 1 :=
    (min_le_right _ _).trans (by norm_num)
  have hKnR : (nguyenInterfaceCutoff I n : ℝ) ≤ (n : ℝ) :=
    hfloorUpper.trans (by nlinarith)
  have hKn : nguyenInterfaceCutoff I n ≤ n := by exact_mod_cast hKnR
  have hKsqR : (n : ℝ) ≤ (nguyenInterfaceCutoff I n : ℝ) ^ 2 := by
    have hsq := mul_self_le_mul_self
      (mul_nonneg hρ.le (by positivity : 0 ≤ (n : ℝ))) hfloorLower
    have hmult := mul_le_mul_of_nonneg_right hlarge
      (by positivity : 0 ≤ (n : ℝ))
    nlinarith
  have hKsq : n ≤ (nguyenInterfaceCutoff I n) ^ 2 := by
    exact_mod_cast hKsqR
  have hηγ : nguyenInterfaceCutoffFraction I < I.gamma0 := by
    have hm : nguyenInterfaceCutoffFraction I ≤ I.gamma0 / 4 :=
      min_le_left _ _
    nlinarith [I.gamma0_pos]
  have hKgamma :
      (nguyenInterfaceCutoff I n : ℝ) < I.gamma0 * n :=
    hfloorUpper.trans_lt
      (mul_lt_mul_of_pos_right hηγ (by exact_mod_cast hn))
  exact ⟨hK1, hKn, hKsq, hfloorLower, hKgamma⟩

/-- Numerical core of Nguyen's fixed-index range. -/
lemma nguyenFixedIndexMain_le_exp_neg (C : ℝ) (hC : 0 < C)
    (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    C ^ k *
        (Real.exp (-(C + 1) * (n : ℝ) / (k : ℝ) ^ 2)) ^ (k ^ 2) ≤
      Real.exp (-(n : ℝ)) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk1)
  have hCexp : C ≤ Real.exp C :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp C)
  have hpowC : C ^ k ≤ (Real.exp C) ^ k :=
    pow_le_pow_left₀ hC.le hCexp k
  have hepspow :
      (Real.exp (-(C + 1) * (n : ℝ) / (k : ℝ) ^ 2)) ^ (k ^ 2) =
        Real.exp (-(C + 1) * (n : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  calc
    C ^ k *
          (Real.exp (-(C + 1) * (n : ℝ) / (k : ℝ) ^ 2)) ^ (k ^ 2)
        ≤ (Real.exp C) ^ k *
            (Real.exp (-(C + 1) * (n : ℝ) / (k : ℝ) ^ 2)) ^ (k ^ 2) :=
      mul_le_mul_of_nonneg_right hpowC (pow_nonneg (Real.exp_pos _).le _)
    _ = Real.exp ((k : ℝ) * C) * Real.exp (-(C + 1) * (n : ℝ)) := by
      rw [← Real.exp_nat_mul, hepspow]
    _ = Real.exp ((k : ℝ) * C - (C + 1) * (n : ℝ)) := by
      rw [← Real.exp_add]
      congr 1 <;> ring
    _ ≤ Real.exp (-(n : ℝ)) := Real.exp_le_exp.mpr (by
      have hkRle : (k : ℝ) ≤ n := by exact_mod_cast hkn
      nlinarith)

/-- Numerical core of Nguyen's overcrowding range up to `sqrt n`. -/
lemma nguyenMediumMain_le_exp_neg (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ)
    (n k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ n.sqrt) :
    Real.rpow
        (C * Real.exp (-(C + 1) * (n : ℝ) / (k : ℝ) ^ 2))
        (δ * (k : ℝ) ^ 2) ≤
      Real.exp (-δ * (n : ℝ)) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk1)
  have hksqNat : k * k ≤ n := Nat.le_sqrt.mp hk
  have hksq : (k : ℝ) ^ 2 ≤ (n : ℝ) := by
    exact_mod_cast (show k ^ 2 ≤ n by simpa [pow_two] using hksqNat)
  have hbase :
      0 < C * Real.exp (-(C + 1) * (n : ℝ) / (k : ℝ) ^ 2) :=
    mul_pos hC (Real.exp_pos _)
  rw [show Real.rpow
      (C * Real.exp (-(C + 1) * (n : ℝ) / (k : ℝ) ^ 2))
      (δ * (k : ℝ) ^ 2) =
        Real.exp
          (Real.log
              (C * Real.exp (-(C + 1) * (n : ℝ) / (k : ℝ) ^ 2)) *
            (δ * (k : ℝ) ^ 2)) from
      Real.rpow_def_of_pos hbase (δ * (k : ℝ) ^ 2)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  have he : 0 ≤ δ * (k : ℝ) ^ 2 :=
    mul_nonneg hδ.le (sq_nonneg _)
  calc
    (Real.log C + (-(C + 1) * (n : ℝ) / (k : ℝ) ^ 2)) *
          (δ * (k : ℝ) ^ 2)
        = Real.log C * (δ * (k : ℝ) ^ 2) +
            (-(C + 1) * (n : ℝ) / (k : ℝ) ^ 2) *
              (δ * (k : ℝ) ^ 2) := by ring
    _ ≤ C * (δ * (k : ℝ) ^ 2) +
          (-(C + 1) * (n : ℝ) / (k : ℝ) ^ 2) *
            (δ * (k : ℝ) ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_right (Real.log_le_self hC.le) he) le_rfl
    _ = C * δ * (k : ℝ) ^ 2 - δ * (C + 1) * (n : ℝ) := by
      field_simp
      <;> ring
    _ ≤ -δ * (n : ℝ) := by
      have hprod : C * δ * ((k : ℝ) ^ 2 - (n : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hC.le hδ.le)
          (sub_nonpos.mpr hksq)
      nlinarith

/-- Numerical core of Nguyen's fixed-`ε₀` bulk range. -/
lemma nguyenBulkMain_le_exp_neg (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ)
    (n k : ℕ) (hk : n.sqrt < k) :
    Real.rpow (C * Real.exp (-(C + 1))) (δ * (k : ℝ) ^ 2) ≤
      Real.exp (-δ * (n : ℝ)) := by
  have hksqNat : n < k * k := Nat.sqrt_lt.mp hk
  have hksq : (n : ℝ) ≤ (k : ℝ) ^ 2 := by
    have : n ≤ k ^ 2 := (show n < k ^ 2 by simpa [pow_two] using hksqNat).le
    exact_mod_cast this
  have hbase : 0 < C * Real.exp (-(C + 1)) :=
    mul_pos hC (Real.exp_pos _)
  rw [show Real.rpow (C * Real.exp (-(C + 1))) (δ * (k : ℝ) ^ 2) =
      Real.exp
        (Real.log (C * Real.exp (-(C + 1))) * (δ * (k : ℝ) ^ 2)) from
      Real.rpow_def_of_pos hbase (δ * (k : ℝ) ^ 2)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  have he : 0 ≤ δ * (k : ℝ) ^ 2 :=
    mul_nonneg hδ.le (sq_nonneg _)
  calc
    (Real.log C + -(C + 1)) * (δ * (k : ℝ) ^ 2)
        ≤ (-1) * (δ * (k : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right (by
        have := Real.log_le_self hC.le
        linarith) he
    _ = -δ * (k : ℝ) ^ 2 := by ring
    _ ≤ -δ * (n : ℝ) := by nlinarith

/-- With the explicit choices `a = C + 1` and `ε₀ = exp (-(C+1))`, every
index in all three Nguyen ranges has the same exponential failure bound.
The factor `2` accounts for Nguyen's separate `exp (-c n)` exceptional
term. -/
theorem nguyenInterfaceFailureAt_le_exp
    (I : NguyenBottomSingularInput) (n k : ℕ)
    (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    nguyenInterfaceFailureAt I n (nguyenInterfaceA I)
        (nguyenInterfaceEpsilon0 I) k ≤
      2 * Real.exp (-nguyenInterfaceRate I * (n : ℝ)) := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hδ : 0 < 1 - I.theta := sub_pos.mpr I.theta_mem.2
  have hq0 : 0 < nguyenInterfaceRate I := nguyenInterfaceRate_pos I
  have hnoise :
      Real.exp (-I.nguyenc * (n : ℝ)) ≤
        Real.exp (-nguyenInterfaceRate I * (n : ℝ)) :=
    Real.exp_le_exp.mpr (by
      have := nguyenInterfaceRate_le_c I
      nlinarith)
  by_cases hk0 : k ≤ I.k0
  · have heps :
        nguyenInterfaceEpsilon I n (nguyenInterfaceA I)
            (nguyenInterfaceEpsilon0 I) k =
          Real.exp (-(I.nguyenC + 1) * (n : ℝ) / (k : ℝ) ^ 2) := by
      simp [nguyenInterfaceEpsilon, nguyenInterfaceA, hk0,
        le_trans hk0 (le_max_left _ _)]
    have hmain0 := nguyenFixedIndexMain_le_exp_neg I.nguyenC I.C_pos
      n k hk1 hkn
    have hmain :
        I.nguyenC ^ k *
            (nguyenInterfaceEpsilon I n (nguyenInterfaceA I)
              (nguyenInterfaceEpsilon0 I) k) ^ (k ^ 2) ≤
          Real.exp (-nguyenInterfaceRate I * (n : ℝ)) := by
      rw [heps]
      exact hmain0.trans (Real.exp_le_exp.mpr (by
        have := nguyenInterfaceRate_le_one I
        nlinarith))
    simp only [nguyenInterfaceFailureAt, if_pos hk0,
      nguyenFixedIndexBound]
    calc
      I.nguyenC ^ k *
            (nguyenInterfaceEpsilon I n (nguyenInterfaceA I)
              (nguyenInterfaceEpsilon0 I) k) ^ (k ^ 2) +
          Real.exp (-I.nguyenc * (n : ℝ))
          ≤ Real.exp (-nguyenInterfaceRate I * (n : ℝ)) +
              Real.exp (-nguyenInterfaceRate I * (n : ℝ)) :=
        add_le_add hmain hnoise
      _ = 2 * Real.exp (-nguyenInterfaceRate I * (n : ℝ)) := by ring
  · have hk0' : I.k0 < k := Nat.lt_of_not_ge hk0
    have hmainDelta :
        Real.rpow
            (I.nguyenC *
              nguyenInterfaceEpsilon I n (nguyenInterfaceA I)
                (nguyenInterfaceEpsilon0 I) k)
            ((1 - I.theta) * (k : ℝ) ^ 2) ≤
          Real.exp (-(1 - I.theta) * (n : ℝ)) := by
      by_cases hksqrt : k ≤ n.sqrt
      · have heps :
            nguyenInterfaceEpsilon I n (nguyenInterfaceA I)
                (nguyenInterfaceEpsilon0 I) k =
              Real.exp (-(I.nguyenC + 1) * (n : ℝ) / (k : ℝ) ^ 2) := by
          simp [nguyenInterfaceEpsilon, nguyenInterfaceA, hksqrt]
        rw [heps]
        exact nguyenMediumMain_le_exp_neg I.nguyenC (1 - I.theta)
          I.C_pos hδ n k hk1 hksqrt
      · have hksqrt' : n.sqrt < k := Nat.lt_of_not_ge hksqrt
        have hmax : ¬ k ≤ max I.k0 n.sqrt := by
          exact Nat.not_le_of_lt (max_lt_iff.mpr ⟨hk0', hksqrt'⟩)
        have heps :
            nguyenInterfaceEpsilon I n (nguyenInterfaceA I)
                (nguyenInterfaceEpsilon0 I) k =
              Real.exp (-(I.nguyenC + 1)) := by
          simp [nguyenInterfaceEpsilon, nguyenInterfaceEpsilon0,
            nguyenInterfaceA, hmax]
        rw [heps]
        exact nguyenBulkMain_le_exp_neg I.nguyenC (1 - I.theta)
          I.C_pos hδ n k hksqrt'
    have hmain :
        Real.rpow
            (I.nguyenC *
              nguyenInterfaceEpsilon I n (nguyenInterfaceA I)
                (nguyenInterfaceEpsilon0 I) k)
            ((1 - I.theta) * (k : ℝ) ^ 2) ≤
          Real.exp (-nguyenInterfaceRate I * (n : ℝ)) :=
      hmainDelta.trans (Real.exp_le_exp.mpr (by
        have := nguyenInterfaceRate_le_delta I
        nlinarith))
    simp only [nguyenInterfaceFailureAt, if_neg hk0,
      nguyenOvercrowdingBound]
    calc
      Real.rpow
            (I.nguyenC *
              nguyenInterfaceEpsilon I n (nguyenInterfaceA I)
                (nguyenInterfaceEpsilon0 I) k)
            ((1 - I.theta) * (k : ℝ) ^ 2) +
          Real.exp (-I.nguyenc * (n : ℝ))
          ≤ Real.exp (-nguyenInterfaceRate I * (n : ℝ)) +
              Real.exp (-nguyenInterfaceRate I * (n : ℝ)) :=
        add_le_add hmain hnoise
      _ = 2 * Real.exp (-nguyenInterfaceRate I * (n : ℝ)) := by ring

/-- Summing the uniform index bound through `K ≤ n` costs only the explicit
linear prefactor `2n`. -/
theorem sum_nguyenInterfaceFailureAt_le
    (I : NguyenBottomSingularInput) (n K : ℕ) (hKn : K ≤ n) :
    (∑ k ∈ Finset.Icc 1 K,
        nguyenInterfaceFailureAt I n (nguyenInterfaceA I)
          (nguyenInterfaceEpsilon0 I) k) ≤
      2 * (n : ℝ) * Real.exp (-nguyenInterfaceRate I * (n : ℝ)) := by
  have hsum :
      (∑ k ∈ Finset.Icc 1 K,
          nguyenInterfaceFailureAt I n (nguyenInterfaceA I)
            (nguyenInterfaceEpsilon0 I) k) ≤
        ∑ _k ∈ Finset.Icc 1 K,
          2 * Real.exp (-nguyenInterfaceRate I * (n : ℝ)) := by
    gcongr with k hk
    have hk' := Finset.mem_Icc.mp hk
    exact nguyenInterfaceFailureAt_le_exp I n k hk'.1 (hk'.2.trans hKn)
  calc
    (∑ k ∈ Finset.Icc 1 K,
        nguyenInterfaceFailureAt I n (nguyenInterfaceA I)
          (nguyenInterfaceEpsilon0 I) k)
        ≤ ∑ _k ∈ Finset.Icc 1 K,
            2 * Real.exp (-nguyenInterfaceRate I * (n : ℝ)) := hsum
    _ = (K : ℝ) *
          (2 * Real.exp (-nguyenInterfaceRate I * (n : ℝ))) := by
      simp [Nat.card_Icc]
    _ ≤ (n : ℝ) *
          (2 * Real.exp (-nguyenInterfaceRate I * (n : ℝ))) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hKn)
        (mul_nonneg (by norm_num) (Real.exp_pos _).le)
    _ = 2 * (n : ℝ) * Real.exp (-nguyenInterfaceRate I * (n : ℝ)) := by
      ring

/-- An explicit elementary absorption of the linear union-bound loss into
half of a positive exponential rate. -/
lemma two_mul_nat_exp_neg_le_exp_half (q : ℝ) (hq : 0 < q) (n : ℕ)
    (hlarge : 32 ≤ q ^ 2 * (n : ℝ)) :
    2 * (n : ℝ) * Real.exp (-q * (n : ℝ)) ≤
      Real.exp (-(q / 2) * (n : ℝ)) := by
  let x : ℝ := q * (n : ℝ) / 4
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxexp : x ≤ Real.exp x :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp x)
  have hxx : x * x ≤ Real.exp x * Real.exp x :=
    mul_le_mul hxexp hxexp hx0 (Real.exp_pos _).le
  have htwoxx : 2 * (n : ℝ) ≤ x * x := by
    have hmul := mul_le_mul_of_nonneg_right hlarge hn0
    dsimp [x]
    nlinarith
  have htwoexp : 2 * (n : ℝ) ≤ Real.exp (q * (n : ℝ) / 2) := by
    calc
      2 * (n : ℝ) ≤ x * x := htwoxx
      _ ≤ Real.exp x * Real.exp x := hxx
      _ = Real.exp (q * (n : ℝ) / 2) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [x]
        ring
  calc
    2 * (n : ℝ) * Real.exp (-q * (n : ℝ))
        ≤ Real.exp (q * (n : ℝ) / 2) * Real.exp (-q * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right htwoexp (Real.exp_pos _).le
    _ = Real.exp (-(q / 2) * (n : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- One-index form, directly exposing which of the two approved Nguyen
inputs was used. -/
theorem nguyenInterfaceBadAt_probability
    { Ω : Type u } [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] { n : ℕ }
    (I : NguyenBottomSingularInput.{u, u})
    (S : IidSubgaussianSquare Ω μ n)
    (hS : S.subgaussianParameter ≤ I.subgaussianBound)
    (a ε₀ : ℝ) (hε₀ : 0 ≤ ε₀) (k : ℕ)
    (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hkgamma : (k : ℝ) < I.gamma0 * n) :
    μ.real (nguyenInterfaceBadAt I S a ε₀ k) ≤
      nguyenInterfaceFailureAt I n a ε₀ k := by
  have hε : 0 ≤ nguyenInterfaceEpsilon I n a ε₀ k :=
    nguyenInterfaceEpsilon_nonneg I n k a ε₀ hε₀
  by_cases hk0 : k ≤ I.k0
  · have hN :
        μ.real { ω : Ω | matrixSingularValue (S.rawMatrix ω) (n - k) ≤
          nguyenInterfaceEpsilon I n a ε₀ k / Real.sqrt n } ≤
          nguyenFixedIndexBound I.nguyenC I.nguyenc
            (nguyenInterfaceEpsilon I n a ε₀ k) n k :=
      NguyenBottomSingularInput.fixedIndex.{u, u} I μ S k
        (nguyenInterfaceEpsilon I n a ε₀ k)
        hS hk1 hk0 hε hkn
    simpa [nguyenInterfaceBadAt, nguyenInterfaceThreshold,
      nguyenInterfaceFailureAt, hk0] using hN
  · have hk0' : I.k0 < k := Nat.lt_of_not_ge hk0
    have hN :
        μ.real { ω : Ω | matrixSingularValue (S.rawMatrix ω) (n - k) ≤
          (k : ℝ) * nguyenInterfaceEpsilon I n a ε₀ k / Real.sqrt n } ≤
          nguyenOvercrowdingBound I.nguyenC I.nguyenc I.theta
            (nguyenInterfaceEpsilon I n a ε₀ k) n k :=
      NguyenBottomSingularInput.overcrowding.{u, u} I μ S k
        (nguyenInterfaceEpsilon I n a ε₀ k)
        hS hk0' hkgamma hε hkn
    simpa [nguyenInterfaceBadAt, nguyenInterfaceThreshold,
      nguyenInterfaceFailureAt, hk0] using hN

/-- The union bound for all spliced Nguyen thresholds.  The remaining
purely numerical step in the paper is to bound this displayed finite sum by
`exp (-c n)` after choosing `a` large and `ε₀` small. -/
theorem nguyenInterfaceBadEvent_probability
    { Ω : Type u } [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] { n : ℕ }
    (I : NguyenBottomSingularInput.{u, u})
    (S : IidSubgaussianSquare Ω μ n)
    (hS : S.subgaussianParameter ≤ I.subgaussianBound)
    (a ε₀ : ℝ) (hε₀ : 0 ≤ ε₀) (K : ℕ)
    (hKn : K ≤ n) (hKgamma : (K : ℝ) < I.gamma0 * n) :
    μ.real (nguyenInterfaceBadEvent I S a ε₀ K) ≤
      ∑ k ∈ Finset.Icc 1 K, nguyenInterfaceFailureAt I n a ε₀ k := by
  refine (measureReal_biUnion_finset_le (Finset.Icc 1 K)
    (nguyenInterfaceBadAt I S a ε₀)).trans ?_
  gcongr with k hk
  have hk' := Finset.mem_Icc.mp hk
  exact nguyenInterfaceBadAt_probability μ I S hS a ε₀ hε₀ k hk'.1
    (hk'.2.trans hKn)
    (lt_of_le_of_lt (by exact_mod_cast hk'.2) hKgamma)

/-- Fully compressed Nguyen union bound.  The theorem displays both the
chosen thresholds and the finite-size cutoff; its conclusion is the paper's
`exp (-c n)` form with the explicit rate `nguyenInterfaceRate I / 2`. -/
theorem nguyenInterfaceBadEvent_probability_exp
    { Ω : Type u } [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] { n : ℕ }
    (I : NguyenBottomSingularInput.{u, u})
    (S : IidSubgaussianSquare Ω μ n)
    (hS : S.subgaussianParameter ≤ I.subgaussianBound) (K : ℕ)
    (hKn : K ≤ n) (hKgamma : (K : ℝ) < I.gamma0 * n)
    (hlarge : 32 ≤ nguyenInterfaceRate I ^ 2 * (n : ℝ)) :
    μ.real
        (nguyenInterfaceBadEvent I S (nguyenInterfaceA I)
          (nguyenInterfaceEpsilon0 I) K) ≤
      Real.exp (-(nguyenInterfaceRate I / 2) * (n : ℝ)) := by
  calc
    μ.real
        (nguyenInterfaceBadEvent I S (nguyenInterfaceA I)
          (nguyenInterfaceEpsilon0 I) K)
        ≤ ∑ k ∈ Finset.Icc 1 K,
            nguyenInterfaceFailureAt I n (nguyenInterfaceA I)
              (nguyenInterfaceEpsilon0 I) k :=
      nguyenInterfaceBadEvent_probability μ I S hS (nguyenInterfaceA I)
        (nguyenInterfaceEpsilon0 I) (nguyenInterfaceEpsilon0_pos I).le K
        hKn hKgamma
    _ ≤ 2 * (n : ℝ) * Real.exp (-nguyenInterfaceRate I * (n : ℝ)) :=
      sum_nguyenInterfaceFailureAt_le I n K hKn
    _ ≤ Real.exp (-(nguyenInterfaceRate I / 2) * (n : ℝ)) :=
      two_mul_nat_exp_neg_le_exp_half (nguyenInterfaceRate I)
        (nguyenInterfaceRate_pos I) n hlarge

/-- The compressed probability estimate at the canonical floor cutoff. -/
theorem nguyenInterfaceBadEvent_probability_exp_atCutoff
    { Ω : Type u } [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] { n : ℕ }
    (I : NguyenBottomSingularInput.{u, u})
    (S : IidSubgaussianSquare Ω μ n)
    (hS : S.subgaussianParameter ≤ I.subgaussianBound) (hn : 0 < n)
    (hcutoffLarge :
      1 ≤ nguyenInterfaceCutoffRho I ^ 2 * (n : ℝ))
    (hprobLarge : 32 ≤ nguyenInterfaceRate I ^ 2 * (n : ℝ)) :
    μ.real
        (nguyenInterfaceBadEvent I S (nguyenInterfaceA I)
          (nguyenInterfaceEpsilon0 I) (nguyenInterfaceCutoff I n)) ≤
      Real.exp (-(nguyenInterfaceRate I / 2) * (n : ℝ)) := by
  obtain ⟨_hK1, hKn, _hKsq, _hρK, hKgamma⟩ :=
    nguyenInterfaceCutoff_spec I n hn hcutoffLarge
  exact nguyenInterfaceBadEvent_probability_exp μ I S hS
    (nguyenInterfaceCutoff I n) hKn hKgamma hprobLarge

/-- Outside the union event, every selected singular value is strictly
above its appropriate (fixed-index or overcrowding) threshold. -/
theorem nguyenInterfaceThreshold_lt_of_good
    { Ω : Type* } [MeasurableSpace Ω] { μ : Measure Ω } { n : ℕ }
    (I : NguyenBottomSingularInput) (S : IidSubgaussianSquare Ω μ n)
    (a ε₀ : ℝ) (K k : ℕ) (ω : Ω)
    (hk : k ∈ Finset.Icc 1 K)
    (hgood : ω ∉ nguyenInterfaceBadEvent I S a ε₀ K) :
    nguyenInterfaceThreshold I n a ε₀ k <
      matrixSingularValue (S.rawMatrix ω) (n - k) := by
  by_contra h
  apply hgood
  exact Set.mem_iUnion_of_mem k <| Set.mem_iUnion_of_mem hk <| by
    exact not_lt.mp h

lemma nguyenInterfaceThreshold_fixed (I : NguyenBottomSingularInput)
    (n k : ℕ) (a ε₀ : ℝ) (hk : k ≤ I.k0) :
    nguyenInterfaceThreshold I n a ε₀ k =
      Real.exp (-a * (n : ℝ) / (k : ℝ) ^ 2) / Real.sqrt n := by
  simp [nguyenInterfaceThreshold, nguyenInterfaceEpsilon, hk,
    le_trans hk (le_max_left _ _)]

lemma nguyenInterfaceThreshold_medium (I : NguyenBottomSingularInput)
    (n k : ℕ) (a ε₀ : ℝ) (hk0 : I.k0 < k) (hk : k ≤ n.sqrt) :
    nguyenInterfaceThreshold I n a ε₀ k =
      (k : ℝ) * Real.exp (-a * (n : ℝ) / (k : ℝ) ^ 2) /
        Real.sqrt n := by
  have hk0n : ¬ k ≤ I.k0 := Nat.not_le_of_lt hk0
  simp [nguyenInterfaceThreshold, nguyenInterfaceEpsilon, hk0n, hk]

lemma nguyenInterfaceThreshold_bulk (I : NguyenBottomSingularInput)
    (n k : ℕ) (a ε₀ : ℝ) (hk0 : I.k0 < k) (hk : n.sqrt < k) :
    nguyenInterfaceThreshold I n a ε₀ k =
      (k : ℝ) * ε₀ / Real.sqrt n := by
  have hmax : max I.k0 n.sqrt < k := (max_lt_iff.mpr ⟨hk0, hk⟩)
  have hk0n : ¬ k ≤ I.k0 := Nat.not_le_of_lt hk0
  have hmaxn : ¬ k ≤ max I.k0 n.sqrt := Nat.not_le_of_lt hmax
  simp [nguyenInterfaceThreshold, nguyenInterfaceEpsilon, hk0n, hmaxn]

lemma nguyenInterfaceThreshold_nonneg (I : NguyenBottomSingularInput)
    (n k : ℕ) (a ε₀ : ℝ) (hε₀ : 0 ≤ ε₀) :
    0 ≤ nguyenInterfaceThreshold I n a ε₀ k := by
  have he := nguyenInterfaceEpsilon_nonneg I n k a ε₀ hε₀
  unfold nguyenInterfaceThreshold
  split_ifs <;> positivity

lemma nguyenInterfaceThreshold_pos (I : NguyenBottomSingularInput)
    (n k : ℕ) (a ε₀ : ℝ) (hn : 0 < n) (hk : 0 < k) (hε₀ : 0 < ε₀) :
    0 < nguyenInterfaceThreshold I n a ε₀ k := by
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have he : 0 < nguyenInterfaceEpsilon I n a ε₀ k := by
    unfold nguyenInterfaceEpsilon
    split_ifs <;> positivity
  unfold nguyenInterfaceThreshold
  split_ifs <;> positivity

/-- A pointwise floor for all singular values.  The bottom `K` values use
their individual Nguyen thresholds; monotonicity uses the `K`-th threshold
for the rest. -/
def nguyenInterfaceSpectrumFloor (I : NguyenBottomSingularInput)
    (n : ℕ) (a ε₀ : ℝ) (K j : ℕ) : ℝ :=
  if n - j ≤ K then
    nguyenInterfaceThreshold I n a ε₀ (n - j)
  else
    nguyenInterfaceThreshold I n a ε₀ K

/-- The spliced good event, plus singular-value monotonicity, controls every
singular value by `nguyenInterfaceSpectrumFloor`. -/
theorem nguyenInterfaceSpectrumFloor_lt_of_good
    { Ω : Type* } [MeasurableSpace Ω] { μ : Measure Ω } { n : ℕ }
    (I : NguyenBottomSingularInput) (S : IidSubgaussianSquare Ω μ n)
    (a ε₀ : ℝ) (K j : ℕ) (ω : Ω)
    (hK1 : 1 ≤ K) (hKn : K ≤ n) (hj : j < n)
    (hgood : ω ∉ nguyenInterfaceBadEvent I S a ε₀ K) :
    nguyenInterfaceSpectrumFloor I n a ε₀ K j <
      matrixSingularValue (S.rawMatrix ω) j := by
  by_cases hjK : n - j ≤ K
  · have hk1 : 1 ≤ n - j := Nat.sub_pos_of_lt hj
    have hmem : n - j ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨hk1, hjK⟩
    have h := nguyenInterfaceThreshold_lt_of_good I S a ε₀ K (n - j) ω hmem hgood
    simp only [nguyenInterfaceSpectrumFloor, if_pos hjK]
    have hid : n - (n - j) = j := tsub_tsub_cancel_of_le (Nat.le_of_lt hj)
    rw [hid] at h
    exact h
  · have hmem : K ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨hK1, le_rfl⟩
    have hK := nguyenInterfaceThreshold_lt_of_good I S a ε₀ K K ω hmem hgood
    have hjle : j ≤ n - K := by omega
    have hmono :
        matrixSingularValue (S.rawMatrix ω) (n - K) ≤
          matrixSingularValue (S.rawMatrix ω) j :=
      (S.rawMatrix ω).toEuclideanLin.singularValues_antitone hjle
    simpa [nguyenInterfaceSpectrumFloor, hjK] using hK.trans_le hmono

/-- Exact determinant consequence of the three-range Nguyen splice.  This
is the formal product statement preceding the paper's elementary
`O(n)` logarithmic estimate. -/
theorem prod_spectrumFloor_le_norm_det_of_good
    { Ω : Type* } [MeasurableSpace Ω] { μ : Measure Ω } { n : ℕ }
    (I : NguyenBottomSingularInput) (S : IidSubgaussianSquare Ω μ n)
    (a ε₀ : ℝ) (hε₀ : 0 ≤ ε₀) (K : ℕ) (ω : Ω)
    (hK1 : 1 ≤ K) (hKn : K ≤ n)
    (hgood : ω ∉ nguyenInterfaceBadEvent I S a ε₀ K) :
    (∏ j ∈ Finset.range n, nguyenInterfaceSpectrumFloor I n a ε₀ K j) ≤
      ‖(S.rawMatrix ω).det‖ := by
  rw [norm_det_eq_prod_matrixSingularValue]
  gcongr with j hj
  · intro i hi
    unfold nguyenInterfaceSpectrumFloor
    split_ifs <;> exact nguyenInterfaceThreshold_nonneg I n _ a ε₀ hε₀
  · exact (nguyenInterfaceSpectrumFloor_lt_of_good I S a ε₀ K j ω
      hK1 hKn (Finset.mem_range.mp hj) hgood).le

/-! ### Exponential compression of the spectrum-floor product -/

/-- A common raw threshold factor valid in all three Nguyen ranges. -/
def nguyenInterfaceProductBase (I : NguyenBottomSingularInput) : ℝ :=
  nguyenInterfaceEpsilon0 I / (I.k0 + 1 : ℝ)

/-- The preceding factor after paying the harmless `√3` normalization.
We use `2 ≥ √3`, hence the explicit divisor `2`. -/
def nguyenInterfaceNormalizedProductBase
    (I : NguyenBottomSingularInput) : ℝ :=
  nguyenInterfaceProductBase I / 2

lemma nguyenInterfaceEpsilon0_le_one (I : NguyenBottomSingularInput) :
    nguyenInterfaceEpsilon0 I ≤ 1 := by
  rw [nguyenInterfaceEpsilon0, nguyenInterfaceA]
  exact Real.exp_le_one_iff.mpr (by nlinarith [I.C_pos])

/-- One formula below all three displayed singular-value thresholds.  The
finite fixed-index range is paid for by `k/(k₀+1)`, while `ε₀` and the
exponential factor make the same formula valid in the medium and bulk
ranges. -/
lemma nguyenInterfaceThreshold_product_lower
    (I : NguyenBottomSingularInput) (n k : ℕ) (hk1 : 1 ≤ k) :
    nguyenInterfaceProductBase I *
          Real.exp (-nguyenInterfaceA I * (n : ℝ) / (k : ℝ) ^ 2) *
          (k : ℝ) / Real.sqrt n ≤
      nguyenInterfaceThreshold I n (nguyenInterfaceA I)
        (nguyenInterfaceEpsilon0 I) k := by
  have hd : 0 < (I.k0 + 1 : ℝ) := by positivity
  have he0 : 0 ≤ nguyenInterfaceEpsilon0 I :=
    (nguyenInterfaceEpsilon0_pos I).le
  have he0one : nguyenInterfaceEpsilon0 I ≤ 1 :=
    nguyenInterfaceEpsilon0_le_one I
  have hexpone :
      Real.exp (-nguyenInterfaceA I * (n : ℝ) / (k : ℝ) ^ 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have ha : 0 ≤ nguyenInterfaceA I := by
      dsimp [nguyenInterfaceA]
      nlinarith [I.C_pos]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (by positivity))
      (sq_nonneg _)
  by_cases hk0 : k ≤ I.k0
  · rw [nguyenInterfaceThreshold_fixed I n k (nguyenInterfaceA I)
      (nguyenInterfaceEpsilon0 I) hk0]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    have hratio : (k : ℝ) / (I.k0 + 1 : ℝ) ≤ 1 := by
      apply (div_le_one hd).mpr
      exact_mod_cast (hk0.trans (Nat.le_add_right I.k0 1))
    have hcoef : nguyenInterfaceEpsilon0 I *
        ((k : ℝ) / (I.k0 + 1 : ℝ)) ≤ 1 :=
      (mul_le_mul he0one hratio (by positivity) zero_le_one).trans_eq (mul_one 1)
    dsimp [nguyenInterfaceProductBase]
    calc
      (nguyenInterfaceEpsilon0 I / (I.k0 + 1 : ℝ)) *
            Real.exp (-nguyenInterfaceA I * (n : ℝ) / (k : ℝ) ^ 2) *
            (k : ℝ)
          = Real.exp (-nguyenInterfaceA I * (n : ℝ) / (k : ℝ) ^ 2) *
              (nguyenInterfaceEpsilon0 I *
                ((k : ℝ) / (I.k0 + 1 : ℝ))) := by field_simp
      _ ≤ Real.exp (-nguyenInterfaceA I * (n : ℝ) / (k : ℝ) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hcoef (Real.exp_pos _).le
      _ = _ := by ring
  · have hk0' : I.k0 < k := Nat.lt_of_not_ge hk0
    by_cases hks : k ≤ n.sqrt
    · rw [nguyenInterfaceThreshold_medium I n k (nguyenInterfaceA I)
        (nguyenInterfaceEpsilon0 I) hk0' hks]
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      have hcoef : nguyenInterfaceEpsilon0 I / (I.k0 + 1 : ℝ) ≤ 1 :=
        (div_le_one hd).mpr (he0one.trans (by exact_mod_cast Nat.le_add_left 1 I.k0))
      dsimp [nguyenInterfaceProductBase]
      calc
        (nguyenInterfaceEpsilon0 I / (I.k0 + 1 : ℝ)) *
              Real.exp (-nguyenInterfaceA I * (n : ℝ) / (k : ℝ) ^ 2) *
              (k : ℝ)
            ≤ 1 * Real.exp (-nguyenInterfaceA I * (n : ℝ) / (k : ℝ) ^ 2) *
                (k : ℝ) := by gcongr
        _ = _ := by ring
    · have hks' : n.sqrt < k := Nat.lt_of_not_ge hks
      rw [nguyenInterfaceThreshold_bulk I n k (nguyenInterfaceA I)
        (nguyenInterfaceEpsilon0 I) hk0' hks']
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      have hcoef :
          Real.exp (-nguyenInterfaceA I * (n : ℝ) / (k : ℝ) ^ 2) /
              (I.k0 + 1 : ℝ) ≤ 1 :=
        (div_le_one hd).mpr (hexpone.trans (by
          exact_mod_cast Nat.le_add_left 1 I.k0))
      dsimp [nguyenInterfaceProductBase]
      calc
        (nguyenInterfaceEpsilon0 I / (I.k0 + 1 : ℝ)) *
              Real.exp (-nguyenInterfaceA I * (n : ℝ) / (k : ℝ) ^ 2) *
              (k : ℝ)
            = nguyenInterfaceEpsilon0 I * (k : ℝ) *
                (Real.exp (-nguyenInterfaceA I * (n : ℝ) / (k : ℝ) ^ 2) /
                  (I.k0 + 1 : ℝ)) := by field_simp
        _ ≤ nguyenInterfaceEpsilon0 I * (k : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hcoef (mul_nonneg he0 (by positivity))
        _ = _ := by ring

/-- Reverse `0,…,n-1` into the paper's bottom-index convention `1,…,n`. -/
lemma prod_range_reverse (f : ℕ → ℝ) (n : ℕ) :
    (∏ j ∈ Finset.range n, f (n - j)) =
      ∏ k ∈ Finset.Icc 1 n, f k := by
  refine Finset.prod_bij (fun j _ ↦ n - j) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_Icc]
    have hj' := Finset.mem_range.mp hj
    omega
  · intro a ha b hb hab
    have ha' := Finset.mem_range.mp ha
    have hb' := Finset.mem_range.mp hb
    omega
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    refine ⟨n - k, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro j hj
    rfl

/-- The reciprocal-square bookkeeping for `min(k,K)`: the bottom `K`
indices cost at most `2`, and the remaining indices contribute the displayed
constant tail. -/
lemma sum_min_inv_sq_le (n K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) :
    (∑ k ∈ Finset.Icc 1 n, (((min k K : ℕ) : ℝ) ^ 2)⁻¹) ≤
      2 + (n : ℝ) / (K : ℝ) ^ 2 := by
  let s := Finset.Icc 1 K
  let t := Finset.Ioc K n
  have hdisj : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro k hks hkt
    have hks' := Finset.mem_Icc.mp hks
    have hkt' := Finset.mem_Ioc.mp hkt
    omega
  have hunion : s ∪ t = Finset.Icc 1 n := by
    ext k
    simp only [s, t, Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [← hunion, Finset.sum_union hdisj]
  have hfirstEq :
      (∑ k ∈ s, (((min k K : ℕ) : ℝ) ^ 2)⁻¹) =
        ∑ k ∈ s, (((k : ℕ) : ℝ) ^ 2)⁻¹ := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := (Finset.mem_Icc.mp hk).2
    rw [Nat.min_eq_left hk']
  have hfirst :
      (∑ k ∈ s, (((k : ℕ) : ℝ) ^ 2)⁻¹) ≤ 2 := by
    have hs : s = insert 1 (Finset.Ioc 1 K) := by
      ext k
      simp only [s, Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
      omega
    rw [hs, Finset.sum_insert (by simp)]
    norm_num
    have htail := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := K)
      one_ne_zero hK1
    linarith [inv_nonneg.mpr (by positivity : 0 ≤ (K : ℝ))]
  have hsecond :
      (∑ k ∈ t, (((min k K : ℕ) : ℝ) ^ 2)⁻¹) ≤
        (n : ℝ) / (K : ℝ) ^ 2 := by
    have hsecondEq :
        (∑ k ∈ t, (((min k K : ℕ) : ℝ) ^ 2)⁻¹) =
          ((t.card : ℕ) : ℝ) * ((K : ℝ) ^ 2)⁻¹ := by
      calc
        (∑ k ∈ t, (((min k K : ℕ) : ℝ) ^ 2)⁻¹) =
            ∑ _k ∈ t, ((K : ℝ) ^ 2)⁻¹ := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk' := (Finset.mem_Ioc.mp hk).1.le
          rw [Nat.min_eq_right hk']
        _ = ((t.card : ℕ) : ℝ) * ((K : ℝ) ^ 2)⁻¹ := by simp
    rw [hsecondEq]
    have hcard : t.card ≤ n := by
      dsimp [t]
      simpa [Nat.card_Ioc] using Nat.sub_le n K
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (inv_nonneg.mpr (sq_nonneg _))
  rw [hfirstEq]
  linarith

/-- The `min(k,K)` product is exactly a factorial followed by a constant
tail. -/
lemma prod_min_eq_factorial_mul_pow (n K : ℕ)
    (hK1 : 1 ≤ K) (hKn : K ≤ n) :
    (∏ k ∈ Finset.Icc 1 n, ((min k K : ℕ) : ℝ)) =
      (K.factorial : ℝ) * (K : ℝ) ^ (n - K) := by
  let s := Finset.Icc 1 K
  let t := Finset.Ioc K n
  have hdisj : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro k hks hkt
    have hks' := Finset.mem_Icc.mp hks
    have hkt' := Finset.mem_Ioc.mp hkt
    omega
  have hunion : s ∪ t = Finset.Icc 1 n := by
    ext k
    simp only [s, t, Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [← hunion, Finset.prod_union hdisj]
  have hfirst :
      (∏ k ∈ s, ((min k K : ℕ) : ℝ)) = (K.factorial : ℝ) := by
    calc
      (∏ k ∈ s, ((min k K : ℕ) : ℝ)) = ∏ k ∈ s, (k : ℝ) := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [Nat.min_eq_left (Finset.mem_Icc.mp hk).2]
      _ = (K.factorial : ℝ) := by
        dsimp [s]
        rw [← Finset.Ico_add_one_right_eq_Icc]
        simpa only [Nat.cast_prod] using congrArg (fun x : ℕ ↦ (x : ℝ))
          (Finset.prod_Ico_id_eq_factorial K)
  have hsecond :
      (∏ k ∈ t, ((min k K : ℕ) : ℝ)) = (K : ℝ) ^ (n - K) := by
    calc
      (∏ k ∈ t, ((min k K : ℕ) : ℝ)) = ∏ _k ∈ t, (K : ℝ) := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [Nat.min_eq_right (Finset.mem_Ioc.mp hk).1.le]
      _ = (K : ℝ) ^ (n - K) := by simp [t, Nat.card_Ioc]
  rw [hfirst, hsecond]

lemma prod_min_ratio_eq (n K : ℕ) (_hn : 0 < n)
    (hK1 : 1 ≤ K) (hKn : K ≤ n) :
    (∏ k ∈ Finset.Icc 1 n,
        (((min k K : ℕ) : ℝ) / (n : ℝ))) =
      ((K.factorial : ℝ) * (K : ℝ) ^ (n - K)) / (n : ℝ) ^ n := by
  rw [Finset.prod_div_distrib, prod_min_eq_factorial_mul_pow n K hK1 hKn]
  simp [Nat.card_Icc]

/-- Stirling's lower bound turns the `min(k,K)/n` product into a pure
exponential whenever `K ≥ ρn`. -/
lemma exp_ratioLoss_le_prod_min_ratio (n K : ℕ) (hn : 0 < n)
    (hK1 : 1 ≤ K) (hKn : K ≤ n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρK : ρ * (n : ℝ) ≤ (K : ℝ)) :
    Real.exp (-(1 + |Real.log ρ|) * (n : ℝ)) ≤
      ∏ k ∈ Finset.Icc 1 n,
        (((min k K : ℕ) : ℝ) / (n : ℝ)) := by
  let P : ℝ := ∏ k ∈ Finset.Icc 1 n,
    (((min k K : ℕ) : ℝ) / (n : ℝ))
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hP : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos fun k hk ↦ div_pos (by
      exact_mod_cast (lt_min (Finset.mem_Icc.mp hk).1 hK1)) hnR
  apply (Real.le_log_iff_exp_le hP).mp
  have hlogfac0 :
      (K : ℝ) * Real.log K - (K : ℝ) ≤ Real.log K.factorial := by
    have hs := Stirling.le_log_factorial_stirling
      (n := K) (Nat.ne_of_gt hK1)
    have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK1)
    have hlog2pi : 0 ≤ Real.log (2 * Real.pi) :=
      Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    nlinarith
  have hratio : ρ ≤ (K : ℝ) / (n : ℝ) := (le_div_iff₀ hnR).2 hρK
  have hlogratio : Real.log ρ ≤ Real.log ((K : ℝ) / (n : ℝ)) :=
    Real.log_le_log hρ hratio
  have hlogρ : -|Real.log ρ| ≤ Real.log ρ := neg_abs_le _
  have hlogratioN := mul_le_mul_of_nonneg_left hlogratio hnR.le
  have hlogρN := mul_le_mul_of_nonneg_left hlogρ hnR.le
  dsimp [P]
  rw [prod_min_ratio_eq n K hn hK1 hKn]
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow]
  rw [Real.log_div (ne_of_gt hKR) (ne_of_gt hnR)] at hlogratio
  rw [Real.log_div (ne_of_gt hKR) (ne_of_gt hnR)] at hlogratioN
  have hKnR : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast hKn
  calc
    -(1 + |Real.log ρ|) * (n : ℝ)
        = (n : ℝ) * (-|Real.log ρ|) - (n : ℝ) := by ring
    _ ≤ (n : ℝ) * Real.log ρ - (n : ℝ) :=
      sub_le_sub_right hlogρN _
    _ ≤ (n : ℝ) * (Real.log K - Real.log n) - (n : ℝ) :=
      sub_le_sub_right hlogratioN _
    _ = (n : ℝ) * Real.log K - (n : ℝ) * Real.log n - (n : ℝ) := by
      ring
    _ ≤ (n : ℝ) * Real.log K - (n : ℝ) * Real.log n - (K : ℝ) :=
      sub_le_sub_left hKnR _
    _ = ((K : ℝ) * Real.log K - (K : ℝ)) +
          (n - K : ℕ) * Real.log K - (n : ℝ) * Real.log n := by
      rw [Nat.cast_sub hKn]
      ring
    _ ≤ Real.log K.factorial + (n - K : ℕ) * Real.log K -
          (n : ℝ) * Real.log n := by
      linarith

/-- Pure numerical multiplication lemma combining the reciprocal-square
loss, Stirling's bound, and the constant normalized threshold factor. -/
lemma exp_productLoss_le_product (a B ρ : ℝ)
    (ha : 0 < a) (hB : 0 < B) (hρ : 0 < ρ)
    (n K : ℕ) (hn : 0 < n) (hK1 : 1 ≤ K) (hKn : K ≤ n)
    (hKsq : n ≤ K ^ 2) (hρK : ρ * (n : ℝ) ≤ (K : ℝ)) :
    Real.exp
        (-(3 * a + |Real.log B| + 1 + |Real.log ρ|) * (n : ℝ)) ≤
      ∏ k ∈ Finset.Icc 1 n,
        (B * Real.exp (-a * (n : ℝ) / ((min k K : ℕ) : ℝ) ^ 2) *
          (((min k K : ℕ) : ℝ) / (n : ℝ))) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK1
  have hbase :
      Real.exp (-|Real.log B| * (n : ℝ)) ≤
        ∏ _k ∈ Finset.Icc 1 n, B := by
    have hlogB : -|Real.log B| ≤ Real.log B := neg_abs_le _
    calc
      Real.exp (-|Real.log B| * (n : ℝ))
          ≤ Real.exp ((n : ℝ) * Real.log B) :=
        Real.exp_le_exp.mpr (by
          have := mul_le_mul_of_nonneg_right hlogB hnR.le
          nlinarith)
      _ = B ^ n := by
        rw [Real.exp_nat_mul, Real.exp_log hB]
      _ = ∏ _k ∈ Finset.Icc 1 n, B := by simp [Nat.card_Icc]
  have hsum0 := sum_min_inv_sq_le n K hK1 hKn
  have hfrac : (n : ℝ) / (K : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hKR)).mpr
    exact_mod_cast hKsq
  have hsum :
      (∑ k ∈ Finset.Icc 1 n, (((min k K : ℕ) : ℝ) ^ 2)⁻¹) ≤ 3 := by
    linarith
  have hexp :
      Real.exp (-3 * a * (n : ℝ)) ≤
        ∏ k ∈ Finset.Icc 1 n,
          Real.exp (-a * (n : ℝ) / ((min k K : ℕ) : ℝ) ^ 2) := by
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    have han : 0 ≤ a * (n : ℝ) := mul_nonneg ha.le hnR.le
    calc
      -3 * a * (n : ℝ) = -(a * (n : ℝ)) * 3 := by ring
      _ ≤ -(a * (n : ℝ)) *
          (∑ k ∈ Finset.Icc 1 n,
            (((min k K : ℕ) : ℝ) ^ 2)⁻¹) :=
        mul_le_mul_of_nonpos_left hsum (neg_nonpos.mpr han)
      _ = ∑ k ∈ Finset.Icc 1 n,
          (-a * (n : ℝ) / ((min k K : ℕ) : ℝ) ^ 2) := by
        simp_rw [div_eq_mul_inv]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have hratio := exp_ratioLoss_le_prod_min_ratio n K hn hK1 hKn ρ hρ hρK
  have hbaseNonneg :
      0 ≤ ∏ _k ∈ Finset.Icc 1 n, B := Finset.prod_nonneg fun _ _ ↦ hB.le
  have hexpNonneg :
      0 ≤ ∏ k ∈ Finset.Icc 1 n,
        Real.exp (-a * (n : ℝ) / ((min k K : ℕ) : ℝ) ^ 2) :=
    Finset.prod_nonneg fun _ _ ↦ (Real.exp_pos _).le
  calc
    Real.exp
        (-(3 * a + |Real.log B| + 1 + |Real.log ρ|) * (n : ℝ)) =
        Real.exp (-|Real.log B| * (n : ℝ)) *
          Real.exp (-3 * a * (n : ℝ)) *
          Real.exp (-(1 + |Real.log ρ|) * (n : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ (∏ _k ∈ Finset.Icc 1 n, B) *
          (∏ k ∈ Finset.Icc 1 n,
            Real.exp (-a * (n : ℝ) / ((min k K : ℕ) : ℝ) ^ 2)) *
          (∏ k ∈ Finset.Icc 1 n,
            (((min k K : ℕ) : ℝ) / (n : ℝ))) := by
      exact mul_le_mul
        (mul_le_mul hbase hexp (Real.exp_pos _).le hbaseNonneg)
        hratio (Real.exp_pos _).le (mul_nonneg hbaseNonneg hexpNonneg)
    _ = ∏ k ∈ Finset.Icc 1 n,
        (B * Real.exp (-a * (n : ℝ) / ((min k K : ℕ) : ℝ) ^ 2) *
          (((min k K : ℕ) : ℝ) / (n : ℝ))) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]

/-- Each normalized spectrum-floor term dominates the uniform formula used
by `exp_productLoss_le_product`. -/
lemma normalizedSpectrumFloor_lower (I : NguyenBottomSingularInput)
    (n K j : ℕ) (hn : 0 < n) (hK1 : 1 ≤ K) (hj : j < n) :
    nguyenInterfaceNormalizedProductBase I *
          Real.exp (-nguyenInterfaceA I * (n : ℝ) /
            ((min (n - j) K : ℕ) : ℝ) ^ 2) *
          (((min (n - j) K : ℕ) : ℝ) / (n : ℝ)) ≤
      nguyenInterfaceSpectrumFloor I n (nguyenInterfaceA I)
          (nguyenInterfaceEpsilon0 I) K j /
        Real.sqrt (3 * (n : ℝ)) := by
  let m := min (n - j) K
  have hm1 : 1 ≤ m := by
    dsimp [m]
    exact le_min (Nat.sub_pos_of_lt hj) hK1
  have hfloor :
      nguyenInterfaceSpectrumFloor I n (nguyenInterfaceA I)
          (nguyenInterfaceEpsilon0 I) K j =
        nguyenInterfaceThreshold I n (nguyenInterfaceA I)
          (nguyenInterfaceEpsilon0 I) m := by
    unfold nguyenInterfaceSpectrumFloor
    by_cases h : n - j ≤ K
    · simp [h, m]
    · simp [h, m, Nat.min_eq_right (Nat.le_of_not_ge h)]
  have hraw := nguyenInterfaceThreshold_product_lower I n m hm1
  rw [hfloor]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hsqrt3n : 0 < Real.sqrt (3 * (n : ℝ)) := by positivity
  have hsqrt3 : Real.sqrt 3 ≤ 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hs0 := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  have hdenom :
      Real.sqrt n * Real.sqrt (3 * (n : ℝ)) ≤ 2 * (n : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      Real.sqrt n * (Real.sqrt 3 * Real.sqrt n) =
          Real.sqrt 3 * (Real.sqrt n) ^ 2 := by ring
      _ = Real.sqrt 3 * (n : ℝ) := by rw [Real.sq_sqrt hnR.le]
      _ ≤ 2 * (n : ℝ) := mul_le_mul_of_nonneg_right hsqrt3 hnR.le
  have hbasepos : 0 < nguyenInterfaceProductBase I := by
    dsimp [nguyenInterfaceProductBase]
    exact div_pos (nguyenInterfaceEpsilon0_pos I) (by positivity)
  have hnum :
      0 ≤ nguyenInterfaceProductBase I *
        Real.exp (-nguyenInterfaceA I * (n : ℝ) / (m : ℝ) ^ 2) *
          (m : ℝ) := by
    positivity
  have hscale :
      nguyenInterfaceNormalizedProductBase I *
            Real.exp (-nguyenInterfaceA I * (n : ℝ) / (m : ℝ) ^ 2) *
            ((m : ℝ) / (n : ℝ)) ≤
        (nguyenInterfaceProductBase I *
            Real.exp (-nguyenInterfaceA I * (n : ℝ) / (m : ℝ) ^ 2) *
            (m : ℝ) / Real.sqrt n) /
          Real.sqrt (3 * (n : ℝ)) := by
    rw [div_div]
    calc
      nguyenInterfaceNormalizedProductBase I *
            Real.exp (-nguyenInterfaceA I * (n : ℝ) / (m : ℝ) ^ 2) *
            ((m : ℝ) / (n : ℝ)) =
          (nguyenInterfaceProductBase I *
            Real.exp (-nguyenInterfaceA I * (n : ℝ) / (m : ℝ) ^ 2) *
            (m : ℝ)) / (2 * (n : ℝ)) := by
        dsimp [nguyenInterfaceNormalizedProductBase]
        field_simp
      _ ≤ (nguyenInterfaceProductBase I *
            Real.exp (-nguyenInterfaceA I * (n : ℝ) / (m : ℝ) ^ 2) *
            (m : ℝ)) /
          (Real.sqrt n * Real.sqrt (3 * (n : ℝ))) :=
        div_le_div_of_nonneg_left hnum (mul_pos hsqrtn hsqrt3n) hdenom
  exact hscale.trans (div_le_div_of_nonneg_right hraw hsqrt3n.le)

/-- Explicit determinant-loss exponent for the normalized iid square. -/
def nguyenInterfaceDetLoss (I : NguyenBottomSingularInput) (ρ : ℝ) : ℝ :=
  3 * nguyenInterfaceA I +
    |Real.log (nguyenInterfaceNormalizedProductBase I)| +
    1 + |Real.log ρ|

/-- The elementary `O(n)` logarithmic estimate promised after the exact
spectrum-floor product: if `√n ≤ K` and `K ≥ ρn`, the normalized product is
at least `exp (-C n)` with the displayed constant. -/
theorem exp_neg_detLoss_le_prod_normalizedSpectrumFloor
    (I : NguyenBottomSingularInput)
    (n K : ℕ) (hn : 0 < n) (hK1 : 1 ≤ K) (hKn : K ≤ n)
    (hKsq : n ≤ K ^ 2) (ρ : ℝ) (hρ : 0 < ρ)
    (hρK : ρ * (n : ℝ) ≤ (K : ℝ)) :
    Real.exp (-nguyenInterfaceDetLoss I ρ * (n : ℝ)) ≤
      ∏ j ∈ Finset.range n,
        (nguyenInterfaceSpectrumFloor I n (nguyenInterfaceA I)
            (nguyenInterfaceEpsilon0 I) K j /
          Real.sqrt (3 * (n : ℝ))) := by
  have ha : 0 < nguyenInterfaceA I := by
    dsimp [nguyenInterfaceA]
    nlinarith [I.C_pos]
  have hB : 0 < nguyenInterfaceNormalizedProductBase I := by
    dsimp [nguyenInterfaceNormalizedProductBase, nguyenInterfaceProductBase]
    exact div_pos
      (div_pos (nguyenInterfaceEpsilon0_pos I) (by positivity)) (by norm_num)
  calc
    Real.exp (-nguyenInterfaceDetLoss I ρ * (n : ℝ)) ≤
        ∏ k ∈ Finset.Icc 1 n,
          (nguyenInterfaceNormalizedProductBase I *
            Real.exp (-nguyenInterfaceA I * (n : ℝ) /
              ((min k K : ℕ) : ℝ) ^ 2) *
            (((min k K : ℕ) : ℝ) / (n : ℝ))) := by
      simpa [nguyenInterfaceDetLoss] using
        exp_productLoss_le_product (nguyenInterfaceA I)
          (nguyenInterfaceNormalizedProductBase I) ρ
          ha hB hρ n K hn hK1 hKn hKsq hρK
    _ = ∏ j ∈ Finset.range n,
          (nguyenInterfaceNormalizedProductBase I *
            Real.exp (-nguyenInterfaceA I * (n : ℝ) /
              ((min (n - j) K : ℕ) : ℝ) ^ 2) *
            (((min (n - j) K : ℕ) : ℝ) / (n : ℝ))) := by
      exact (prod_range_reverse (fun k ↦
        nguyenInterfaceNormalizedProductBase I *
          Real.exp (-nguyenInterfaceA I * (n : ℝ) /
            ((min k K : ℕ) : ℝ) ^ 2) *
          (((min k K : ℕ) : ℝ) / (n : ℝ))) n).symm
    _ ≤ ∏ j ∈ Finset.range n,
        (nguyenInterfaceSpectrumFloor I n (nguyenInterfaceA I)
            (nguyenInterfaceEpsilon0 I) K j /
          Real.sqrt (3 * (n : ℝ))) := by
      gcongr with j hj
      exact normalizedSpectrumFloor_lower I n K j hn hK1
        (Finset.mem_range.mp hj)

/-- Determinant scaling for the paper's normalized iid square
`(3n)⁻¹ᐟ² G`. -/
lemma norm_det_invSqrtThreeN_smul {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖((((Real.sqrt (3 * (n : ℝ)))⁻¹ : ℝ) : ℂ) • A).det‖ =
      ‖A.det‖ / (Real.sqrt (3 * (n : ℝ))) ^ n := by
  rw [Matrix.det_smul, norm_mul, norm_pow]
  have hs : 0 < Real.sqrt (3 * (n : ℝ)) := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hs]
  rw [inv_pow, inv_mul_eq_div]
  simp

/-- On the spliced Nguyen good event, the normalized iid-square determinant
has the promised `exp (-C n)` lower bound. -/
theorem exp_neg_detLoss_le_norm_det_normalized_of_good
    { Ω : Type* } [MeasurableSpace Ω] { μ : Measure Ω } { n : ℕ }
    (I : NguyenBottomSingularInput) (S : IidSubgaussianSquare Ω μ n)
    (K : ℕ) (ω : Ω)
    (hn : 0 < n) (hK1 : 1 ≤ K) (hKn : K ≤ n)
    (hKsq : n ≤ K ^ 2) (ρ : ℝ) (hρ : 0 < ρ)
    (hρK : ρ * (n : ℝ) ≤ (K : ℝ))
    (hgood : ω ∉ nguyenInterfaceBadEvent I S (nguyenInterfaceA I)
      (nguyenInterfaceEpsilon0 I) K) :
    Real.exp (-nguyenInterfaceDetLoss I ρ * (n : ℝ)) ≤
      ‖((((Real.sqrt (3 * (n : ℝ)))⁻¹ : ℝ) : ℂ) • S.rawMatrix ω).det‖ := by
  have hfloor := exp_neg_detLoss_le_prod_normalizedSpectrumFloor
    I n K hn hK1 hKn hKsq ρ hρ hρK
  have hraw := prod_spectrumFloor_le_norm_det_of_good I S
    (nguyenInterfaceA I) (nguyenInterfaceEpsilon0 I)
    (nguyenInterfaceEpsilon0_pos I).le K ω hK1 hKn hgood
  have hs : 0 ≤ Real.sqrt (3 * (n : ℝ)) := Real.sqrt_nonneg _
  calc
    Real.exp (-nguyenInterfaceDetLoss I ρ * (n : ℝ))
        ≤ ∏ j ∈ Finset.range n,
          (nguyenInterfaceSpectrumFloor I n (nguyenInterfaceA I)
              (nguyenInterfaceEpsilon0 I) K j /
            Real.sqrt (3 * (n : ℝ))) := hfloor
    _ = (∏ j ∈ Finset.range n,
          nguyenInterfaceSpectrumFloor I n (nguyenInterfaceA I)
            (nguyenInterfaceEpsilon0 I) K j) /
          (Real.sqrt (3 * (n : ℝ))) ^ n := by
      rw [Finset.prod_div_distrib]
      simp
    _ ≤ ‖(S.rawMatrix ω).det‖ /
          (Real.sqrt (3 * (n : ℝ))) ^ n :=
      div_le_div_of_nonneg_right hraw (pow_nonneg hs n)
    _ = ‖((((Real.sqrt (3 * (n : ℝ)))⁻¹ : ℝ) : ℂ) •
          S.rawMatrix ω).det‖ :=
      (norm_det_invSqrtThreeN_smul hn (S.rawMatrix ω)).symm

/-- Canonical-cutoff form of the normalized determinant lower bound. -/
theorem exp_neg_detLoss_le_norm_det_normalized_of_good_atCutoff
    { Ω : Type* } [MeasurableSpace Ω] { μ : Measure Ω } { n : ℕ }
    (I : NguyenBottomSingularInput) (S : IidSubgaussianSquare Ω μ n)
    (ω : Ω) (hn : 0 < n)
    (hcutoffLarge :
      1 ≤ nguyenInterfaceCutoffRho I ^ 2 * (n : ℝ))
    (hgood : ω ∉ nguyenInterfaceBadEvent I S (nguyenInterfaceA I)
      (nguyenInterfaceEpsilon0 I) (nguyenInterfaceCutoff I n)) :
    Real.exp
        (-nguyenInterfaceDetLoss I (nguyenInterfaceCutoffRho I) * (n : ℝ)) ≤
      ‖((((Real.sqrt (3 * (n : ℝ)))⁻¹ : ℝ) : ℂ) • S.rawMatrix ω).det‖ := by
  obtain ⟨hK1, hKn, hKsq, hρK, _hKgamma⟩ :=
    nguyenInterfaceCutoff_spec I n hn hcutoffLarge
  exact exp_neg_detLoss_le_norm_det_normalized_of_good I S
    (nguyenInterfaceCutoff I n) ω hn hK1 hKn hKsq
    (nguyenInterfaceCutoffRho I) (nguyenInterfaceCutoffRho_pos I)
    hρK hgood

lemma nguyenInterfaceThreshold_one (I : NguyenBottomSingularInput)
    (n : ℕ) (hn : 0 < n) :
    nguyenInterfaceThreshold I n (nguyenInterfaceA I)
        (nguyenInterfaceEpsilon0 I) 1 =
      Real.exp (-nguyenInterfaceA I * (n : ℝ)) / Real.sqrt n := by
  have h1sqrt : 1 ≤ n.sqrt := Nat.le_sqrt.mpr (by omega)
  have hmax : 1 ≤ max I.k0 n.sqrt := h1sqrt.trans (le_max_right _ _)
  unfold nguyenInterfaceThreshold nguyenInterfaceEpsilon
  simp [hmax]

/-- Scaling the nonsingular inverse by `(3n)⁻¹ᐟ²` multiplies its norm by
`√(3n)`. -/
lemma norm_invSqrtThreeN_smul_inv {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hunit : IsUnit A.det) :
    ‖((((Real.sqrt (3 * (n : ℝ)))⁻¹ : ℝ) : ℂ) • A)⁻¹‖ =
      Real.sqrt (3 * (n : ℝ)) * ‖A⁻¹‖ := by
  have hs : 0 < Real.sqrt (3 * (n : ℝ)) := by positivity
  let c : ℂ := (((Real.sqrt (3 * (n : ℝ)))⁻¹ : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast inv_ne_zero (ne_of_gt hs)
  letI : Invertible c := invertibleOfNonzero hc
  change ‖(c • A)⁻¹‖ = _
  rw [Matrix.inv_smul (A := A) c hunit, norm_smul]
  change ‖(⅟ c : ℂ)‖ * ‖A⁻¹‖ = _
  rw [invOf_eq_inv]
  dsimp [c]
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hs]
  field_simp

/-- The `k = 1` part of the same good event gives the inverse estimate for
the raw iid square, with no determinant or elimination certificate. -/
theorem norm_rawMatrix_inv_le_of_nguyenGood
    { Ω : Type* } [MeasurableSpace Ω] { μ : Measure Ω } { n : ℕ }
    (I : NguyenBottomSingularInput) (S : IidSubgaussianSquare Ω μ n)
    (a ε₀ : ℝ) (K : ℕ) (ω : Ω)
    (hn : 0 < n) (hK1 : 1 ≤ K)
    (hε₀ : 0 < ε₀)
    (hgood : ω ∉ nguyenInterfaceBadEvent I S a ε₀ K) :
    ‖(S.rawMatrix ω)⁻¹‖ ≤
      (nguyenInterfaceThreshold I n a ε₀ 1)⁻¹ := by
  have hmem : 1 ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨le_rfl, hK1⟩
  have hbottom :=
    nguyenInterfaceThreshold_lt_of_good I S a ε₀ K 1 ω hmem hgood
  have hmin : nguyenInterfaceThreshold I n a ε₀ 1 ≤
      matrixSMin (S.rawMatrix ω) := by
    simpa [matrixSMin, ne_of_gt hn] using hbottom.le
  exact norm_nonsing_inv_le_inv_of_le_matrixSMin hn (S.rawMatrix ω)
    (nguyenInterfaceThreshold_pos I n 1 a ε₀ hn Nat.zero_lt_one hε₀) hmin

/-- Explicit exponential loss for the inverse of the normalized iid square. -/
def nguyenInterfaceInvLoss (I : NguyenBottomSingularInput) : ℝ :=
  nguyenInterfaceA I + 2

/-- The `k=1` Nguyen estimate, together with normalization, gives an
`exp (C n)` inverse bound on the same good event. -/
theorem norm_normalized_inv_le_exp_of_nguyenGood
    { Ω : Type* } [MeasurableSpace Ω] { μ : Measure Ω } { n : ℕ }
    (I : NguyenBottomSingularInput) (S : IidSubgaussianSquare Ω μ n)
    (K : ℕ) (ω : Ω) (hn : 0 < n) (hK1 : 1 ≤ K)
    (hgood : ω ∉ nguyenInterfaceBadEvent I S (nguyenInterfaceA I)
      (nguyenInterfaceEpsilon0 I) K) :
    ‖((((Real.sqrt (3 * (n : ℝ)))⁻¹ : ℝ) : ℂ) • S.rawMatrix ω)⁻¹‖ ≤
      Real.exp (nguyenInterfaceInvLoss I * (n : ℝ)) := by
  have hraw := norm_rawMatrix_inv_le_of_nguyenGood I S
    (nguyenInterfaceA I) (nguyenInterfaceEpsilon0 I) K ω hn hK1
    (nguyenInterfaceEpsilon0_pos I) hgood
  rw [nguyenInterfaceThreshold_one I n hn] at hraw
  have hmem : 1 ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨le_rfl, hK1⟩
  have hbottom := nguyenInterfaceThreshold_lt_of_good I S
    (nguyenInterfaceA I) (nguyenInterfaceEpsilon0 I) K 1 ω hmem hgood
  have hmin :
      nguyenInterfaceThreshold I n (nguyenInterfaceA I)
          (nguyenInterfaceEpsilon0 I) 1 ≤ matrixSMin (S.rawMatrix ω) := by
    simpa [matrixSMin, ne_of_gt hn] using hbottom.le
  have hthresholdPos := nguyenInterfaceThreshold_pos I n 1
    (nguyenInterfaceA I) (nguyenInterfaceEpsilon0 I) hn Nat.zero_lt_one
    (nguyenInterfaceEpsilon0_pos I)
  have hdetNorm : 0 < ‖(S.rawMatrix ω).det‖ :=
    lt_of_lt_of_le (pow_pos hthresholdPos n)
      (pow_le_norm_det_of_le_matrixSMin hn (S.rawMatrix ω)
        hthresholdPos.le hmin)
  have hunit : IsUnit (S.rawMatrix ω).det :=
    isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hdetNorm)
  rw [norm_invSqrtThreeN_smul_inv hn (S.rawMatrix ω) hunit]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hsqrt3n : 0 < Real.sqrt (3 * (n : ℝ)) := by positivity
  have hsqrt3 : Real.sqrt 3 ≤ 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hs0 := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  have hsqrtProduct :
      Real.sqrt (3 * (n : ℝ)) * Real.sqrt n ≤ 2 * (n : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      (Real.sqrt 3 * Real.sqrt n) * Real.sqrt n =
          Real.sqrt 3 * (Real.sqrt n) ^ 2 := by ring
      _ = Real.sqrt 3 * (n : ℝ) := by rw [Real.sq_sqrt hnR.le]
      _ ≤ 2 * (n : ℝ) := mul_le_mul_of_nonneg_right hsqrt3 hnR.le
  have hinvThreshold :
      (Real.exp (-nguyenInterfaceA I * (n : ℝ)) / Real.sqrt n)⁻¹ =
        Real.sqrt n * Real.exp (nguyenInterfaceA I * (n : ℝ)) := by
    rw [inv_div, div_eq_mul_inv]
    have hneg : -nguyenInterfaceA I * (n : ℝ) =
        -(nguyenInterfaceA I * (n : ℝ)) := by ring
    rw [hneg, Real.exp_neg]
    simp
  rw [hinvThreshold] at hraw
  have htwoExp : 2 * (n : ℝ) ≤ Real.exp (2 * (n : ℝ)) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  calc
    Real.sqrt (3 * (n : ℝ)) * ‖(S.rawMatrix ω)⁻¹‖
        ≤ Real.sqrt (3 * (n : ℝ)) *
            (Real.sqrt n * Real.exp (nguyenInterfaceA I * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hraw hsqrt3n.le
    _ = (Real.sqrt (3 * (n : ℝ)) * Real.sqrt n) *
          Real.exp (nguyenInterfaceA I * (n : ℝ)) := by ring
    _ ≤ (2 * (n : ℝ)) *
          Real.exp (nguyenInterfaceA I * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hsqrtProduct (Real.exp_pos _).le
    _ ≤ Real.exp (2 * (n : ℝ)) *
          Real.exp (nguyenInterfaceA I * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right htwoExp (Real.exp_pos _).le
    _ = Real.exp (nguyenInterfaceInvLoss I * (n : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      simp [nguyenInterfaceInvLoss]
      ring

/-- Canonical-cutoff inverse bound. -/
theorem norm_normalized_inv_le_exp_of_nguyenGood_atCutoff
    { Ω : Type* } [MeasurableSpace Ω] { μ : Measure Ω } { n : ℕ }
    (I : NguyenBottomSingularInput) (S : IidSubgaussianSquare Ω μ n)
    (ω : Ω) (hn : 0 < n)
    (hcutoffLarge :
      1 ≤ nguyenInterfaceCutoffRho I ^ 2 * (n : ℝ))
    (hgood : ω ∉ nguyenInterfaceBadEvent I S (nguyenInterfaceA I)
      (nguyenInterfaceEpsilon0 I) (nguyenInterfaceCutoff I n)) :
    ‖((((Real.sqrt (3 * (n : ℝ)))⁻¹ : ℝ) : ℂ) • S.rawMatrix ω)⁻¹‖ ≤
      Real.exp (nguyenInterfaceInvLoss I * (n : ℝ)) := by
  obtain ⟨hK1, _hKn, _hKsq, _hρK, _hKgamma⟩ :=
    nguyenInterfaceCutoff_spec I n hn hcutoffLarge
  exact norm_normalized_inv_le_exp_of_nguyenGood I S
    (nguyenInterfaceCutoff I n) ω hn hK1 hgood

/-- Canonical high-probability package supplied solely by the approved
Nguyen input: one explicit bad event has exponentially small probability,
and off that event both the normalized determinant and inverse satisfy their
exponential interface bounds. -/
theorem nguyenInterfaceCanonicalDetInverseControl
    { Ω : Type u } [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] { n : ℕ }
    (I : NguyenBottomSingularInput.{u, u})
    (S : IidSubgaussianSquare Ω μ n)
    (hS : S.subgaussianParameter ≤ I.subgaussianBound) (hn : 0 < n)
    (hcutoffLarge :
      1 ≤ nguyenInterfaceCutoffRho I ^ 2 * (n : ℝ))
    (hprobLarge : 32 ≤ nguyenInterfaceRate I ^ 2 * (n : ℝ)) :
    μ.real
        (nguyenInterfaceBadEvent I S (nguyenInterfaceA I)
          (nguyenInterfaceEpsilon0 I) (nguyenInterfaceCutoff I n)) ≤
        Real.exp (-(nguyenInterfaceRate I / 2) * (n : ℝ)) ∧
      ∀ ω ∉ nguyenInterfaceBadEvent I S (nguyenInterfaceA I)
          (nguyenInterfaceEpsilon0 I) (nguyenInterfaceCutoff I n),
        Real.exp
            (-nguyenInterfaceDetLoss I (nguyenInterfaceCutoffRho I) *
              (n : ℝ)) ≤
            ‖((((Real.sqrt (3 * (n : ℝ)))⁻¹ : ℝ) : ℂ) •
              S.rawMatrix ω).det‖ ∧
          ‖((((Real.sqrt (3 * (n : ℝ)))⁻¹ : ℝ) : ℂ) •
              S.rawMatrix ω)⁻¹‖ ≤
            Real.exp (nguyenInterfaceInvLoss I * (n : ℝ)) := by
  refine ⟨nguyenInterfaceBadEvent_probability_exp_atCutoff μ I S hS hn
    hcutoffLarge hprobLarge, ?_⟩
  intro ω hgood
  exact ⟨exp_neg_detLoss_le_norm_det_normalized_of_good_atCutoff
      I S ω hn hcutoffLarge hgood,
    norm_normalized_inv_le_exp_of_nguyenGood_atCutoff
      I S ω hn hcutoffLarge hgood⟩

end NguyenSplice

end BernoulliSection9
