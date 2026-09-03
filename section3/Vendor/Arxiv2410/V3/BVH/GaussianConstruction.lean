/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/GaussianConstruction.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.BVH.AtomCovariance
import Vendor.Arxiv2410.V3.BVH.GaussianMoments
import Vendor.Arxiv2410.V3.BVH.ModelMoments
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Canonical Gaussian companion and diagonal circularization

This file constructs, on one explicit finite product probability space, the Gaussian model
used in arXiv:2410.16457v3, Proposition 3.4.  One two-dimensional Gaussian coordinate is used
for every matrix entry, with covariance equal to the corresponding scaled covariance of the
standardized atom.  A second, independent family of two-dimensional circular Gaussian
coordinates replaces the diagonal.

Thus the companion `XG`, its circularization `XGo`, and the diagonal difference `d` are
canonical data derived from `RandomMatrixModelV3`; no comparison theorem is used here.
-/

namespace Arxiv2410V3.BVH

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators NNReal

noncomputable section

/-- A real two-vector, used for the real and imaginary coordinates of one complex Gaussian. -/
abbrev GaussianRealPair := EuclideanSpace ℝ (Fin 2)

/-- Sources in the canonical product space: one source for every companion entry and one
additional source for every circularized diagonal entry. -/
abbrev GaussianSourceIndex (n : ℕ) := (Fin n × Fin n) ⊕ Fin n

/-- The canonical finite product sample space. -/
abbrev CanonicalGaussianSample (n : ℕ) := GaussianSourceIndex n → GaussianRealPair

/-- The real coordinate `0 = re`, `1 = im` of a complex number. -/
def complexRealCoordinate (z : ℂ) (k : Fin 2) : ℝ :=
  if k = 0 then z.re else z.im

@[simp] theorem complexRealCoordinate_zero (z : ℂ) :
    complexRealCoordinate z 0 = z.re := by simp [complexRealCoordinate]

@[simp] theorem complexRealCoordinate_one (z : ℂ) :
    complexRealCoordinate z 1 = z.im := by simp [complexRealCoordinate]

/-- The continuous real-linear coordinate map underlying `realPairToComplex`. -/
def realPairCoordinatesCLM : GaussianRealPair →L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.proj (𝕜 := ℝ) 0).prod (EuclideanSpace.proj (𝕜 := ℝ) 1)

@[simp] theorem realPairCoordinatesCLM_apply (x : GaussianRealPair) :
    realPairCoordinatesCLM x = (x 0, x 1) := by
  rfl

/-- Recover a complex scalar from its two Euclidean real coordinates. -/
def realPairToComplex (x : GaussianRealPair) : ℂ :=
  Complex.equivRealProdCLM.symm (realPairCoordinatesCLM x)

@[simp] theorem realPairToComplex_re (x : GaussianRealPair) :
    (realPairToComplex x).re = x 0 := by
  simp [realPairToComplex]

@[simp] theorem realPairToComplex_im (x : GaussianRealPair) :
    (realPairToComplex x).im = x 1 := by
  simp [realPairToComplex]

theorem measurable_realPairToComplex : Measurable realPairToComplex := by
  exact (Complex.equivRealProdCLM.symm.continuous.comp
    realPairCoordinatesCLM.continuous).measurable

variable {Omega OmegaXi : Type*}
  [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
  {mu : Measure Omega} {nu : Measure OmegaXi}
  [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
  {n : ℕ}

/-- Covariance of the entry source indexed by `(i,j)`: `b_ij² Q`, where `Q` is the
two-dimensional covariance matrix of the standardized atom. -/
def companionEntryCovariance
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  model.profile.coefficient i j ^ 2 • atomSecondMomentMatrix model

/-- A circular complex Gaussian with total variance `b_ii²` has real covariance matrix
`(b_ii²/2) I₂`. -/
def circularDiagonalCovariance
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i : Fin n) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (model.profile.coefficient i i ^ 2 / 2) • 1

/-- The covariance attached to one source in the common product sample space. -/
def canonicalSourceCovariance
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    GaussianSourceIndex n → Matrix (Fin 2) (Fin 2) ℝ
  | Sum.inl ij => companionEntryCovariance model ij.1 ij.2
  | Sum.inr i => circularDiagonalCovariance model i

theorem companionEntryCovariance_posSemidef
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    (companionEntryCovariance model i j).PosSemidef := by
  exact (atomSecondMomentMatrix_posSemidef model).smul
    (sq_nonneg (model.profile.coefficient i j))

theorem circularDiagonalCovariance_posSemidef
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i : Fin n) :
    (circularDiagonalCovariance model i).PosSemidef := by
  exact Matrix.PosSemidef.one.smul
    (div_nonneg (sq_nonneg (model.profile.coefficient i i)) (by norm_num))

theorem canonicalSourceCovariance_posSemidef
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (a : GaussianSourceIndex n) :
    (canonicalSourceCovariance model a).PosSemidef := by
  rcases a with ij | i
  · exact companionEntryCovariance_posSemidef model ij.1 ij.2
  · exact circularDiagonalCovariance_posSemidef model i

/-- The centered two-dimensional Gaussian law attached to one source. -/
def canonicalSourceMeasure
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (a : GaussianSourceIndex n) :
    Measure GaussianRealPair :=
  multivariateGaussian 0 (canonicalSourceCovariance model a)

instance canonicalSourceMeasure_isProbabilityMeasure
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (a : GaussianSourceIndex n) :
    IsProbabilityMeasure (canonicalSourceMeasure model a) := by
  unfold canonicalSourceMeasure
  infer_instance

instance canonicalSourceMeasure_isGaussian
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (a : GaussianSourceIndex n) :
    IsGaussian (canonicalSourceMeasure model a) := by
  unfold canonicalSourceMeasure
  infer_instance

/-- The explicit finite product measure carrying the companion and its circularization. -/
def canonicalGaussianMeasure
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    Measure (CanonicalGaussianSample n) :=
  Measure.pi (canonicalSourceMeasure model)

instance canonicalGaussianMeasure_isProbabilityMeasure
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    IsProbabilityMeasure (canonicalGaussianMeasure model) := by
  unfold canonicalGaussianMeasure canonicalSourceMeasure
  infer_instance

/-- All raw two-dimensional source coordinates are mutually independent. -/
theorem canonical_source_iIndepFun
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    iIndepFun (fun a (omega : CanonicalGaussianSample n) ↦ omega a)
      (canonicalGaussianMeasure model) := by
  exact iIndepFun_pi (fun _ ↦ aemeasurable_id)

/-- Each source coordinate has its prescribed multivariate Gaussian law. -/
theorem canonical_source_hasLaw
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (a : GaussianSourceIndex n) :
    HasLaw (fun omega : CanonicalGaussianSample n ↦ omega a)
      (canonicalSourceMeasure model a) (canonicalGaussianMeasure model) := by
  exact (measurePreserving_eval (canonicalSourceMeasure model) a).hasLaw

/-- Each source coordinate is jointly Gaussian. -/
theorem canonical_source_hasGaussianLaw
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (a : GaussianSourceIndex n) :
    HasGaussianLaw (fun omega : CanonicalGaussianSample n ↦ omega a)
      (canonicalGaussianMeasure model) :=
  (canonical_source_hasLaw model a).hasGaussianLaw

/-- One real coordinate of a source has the scalar Gaussian law read from its covariance
matrix. -/
theorem canonical_source_eval_hasLaw
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (a : GaussianSourceIndex n) (k : Fin 2) :
    HasLaw (fun omega : CanonicalGaussianSample n ↦ omega a k)
      (gaussianReal 0 ((canonicalSourceCovariance model a k k).toNNReal))
      (canonicalGaussianMeasure model) := by
  have hEval : MeasurePreserving (fun x : GaussianRealPair ↦ x k)
      (multivariateGaussian (0 : GaussianRealPair)
        (canonicalSourceCovariance model a))
      (gaussianReal 0 ((canonicalSourceCovariance model a k k).toNNReal)) :=
    measurePreserving_eval_multivariateGaussian
      (i := k) (canonicalSourceCovariance_posSemidef model a)
  simpa only [canonicalSourceMeasure] using
    hEval.fun_comp_hasLaw (canonical_source_hasLaw model a)

theorem canonical_source_eval_hasGaussianLaw
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (a : GaussianSourceIndex n) (k : Fin 2) :
    HasGaussianLaw (fun omega : CanonicalGaussianSample n ↦ omega a k)
      (canonicalGaussianMeasure model) :=
  (canonical_source_eval_hasLaw model a k).hasGaussianLaw

theorem canonical_source_eval_mean_zero
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (a : GaussianSourceIndex n) (k : Fin 2) :
    (∫ omega : CanonicalGaussianSample n, omega a k
      ∂canonicalGaussianMeasure model) = 0 := by
  simpa using (canonical_source_eval_hasLaw model a k).integral_eq

theorem canonical_source_eval_variance
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (a : GaussianSourceIndex n) (k : Fin 2) :
    Var[fun omega : CanonicalGaussianSample n ↦ omega a k;
      canonicalGaussianMeasure model] = canonicalSourceCovariance model a k k := by
  rw [(canonical_source_eval_hasLaw model a k).variance_eq,
    variance_id_gaussianReal,
    Real.coe_toNNReal _
      ((canonicalSourceCovariance_posSemidef model a).diag_nonneg)]

theorem canonical_source_eval_secondMoment
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (a : GaussianSourceIndex n) (k : Fin 2) :
    (∫ omega : CanonicalGaussianSample n, (omega a k) ^ 2
      ∂canonicalGaussianMeasure model) = canonicalSourceCovariance model a k k := by
  rw [← canonical_source_eval_variance model a k]
  exact (variance_of_integral_eq_zero
    (canonical_source_eval_hasGaussianLaw model a k).aemeasurable
    (canonical_source_eval_mean_zero model a k)).symm

theorem canonical_source_eval_crossMoment
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (a : GaussianSourceIndex n) :
    (∫ omega : CanonicalGaussianSample n, omega a 0 * omega a 1
      ∂canonicalGaussianMeasure model) = canonicalSourceCovariance model a 0 1 := by
  have h0 := (canonical_source_eval_hasGaussianLaw model a 0).memLp_two
  have h1 := (canonical_source_eval_hasGaussianLaw model a 1).memLp_two
  have hcov := (canonical_source_hasLaw model a).covariance_fun_comp
    (f := fun x : GaussianRealPair ↦ x 0)
    (g := fun x : GaussianRealPair ↦ x 1)
    (by fun_prop) (by fun_prop)
  rw [canonicalSourceMeasure,
    covariance_eval_multivariateGaussian
      (canonicalSourceCovariance_posSemidef model a)] at hcov
  rw [covariance_eq_sub h0 h1,
    canonical_source_eval_mean_zero model a 0,
    canonical_source_eval_mean_zero model a 1, mul_zero, sub_zero] at hcov
  exact hcov

/-- The canonical matching Gaussian companion. -/
def canonicalGaussianMatrix
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    CanonicalGaussianSample n → Matrix (Fin n) (Fin n) ℂ :=
  fun omega i j ↦ realPairToComplex (omega (Sum.inl (i, j)))

/-- The independent circular Gaussian used to replace the `i`th diagonal entry. -/
def canonicalCircularDiagonal
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    Fin n → CanonicalGaussianSample n → ℂ :=
  fun i omega ↦ realPairToComplex (omega (Sum.inr i))

/-- The circularized companion: off-diagonal entries are unchanged and each diagonal entry
is replaced by its additional independent circular source. -/
def canonicalCircularizedMatrix
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    CanonicalGaussianSample n → Matrix (Fin n) (Fin n) ℂ :=
  fun omega i j ↦
    if h : i = j then canonicalCircularDiagonal model i omega
    else canonicalGaussianMatrix model omega i j

/-- Diagonal difference `d_i = XG_ii - XGo_ii` from v3 proof step (4). -/
def canonicalDiagonalDifference
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    Fin n → CanonicalGaussianSample n → ℂ :=
  fun i omega ↦
    canonicalGaussianMatrix model omega i i - canonicalCircularDiagonal model i omega

theorem canonicalGaussianMatrix_entry_measurable
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    Measurable (fun omega ↦ canonicalGaussianMatrix model omega i j) := by
  exact measurable_realPairToComplex.comp (measurable_pi_apply (Sum.inl (i, j)))

theorem canonicalCircularDiagonal_measurable
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i : Fin n) :
    Measurable (canonicalCircularDiagonal model i) := by
  exact measurable_realPairToComplex.comp (measurable_pi_apply (Sum.inr i))

theorem canonicalCircularizedMatrix_entry_measurable
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    Measurable (fun omega ↦ canonicalCircularizedMatrix model omega i j) := by
  by_cases hij : i = j
  · subst j
    simpa [canonicalCircularizedMatrix] using
      canonicalCircularDiagonal_measurable model i
  · simp only [canonicalCircularizedMatrix, hij, dite_false]
    exact canonicalGaussianMatrix_entry_measurable model i j

/-- Exact diagonal coupling used in v3 proof step (4). -/
theorem canonicalGaussianMatrix_sub_circularized
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (omega : CanonicalGaussianSample n) :
    canonicalGaussianMatrix model omega - canonicalCircularizedMatrix model omega =
      Matrix.diagonal (fun i ↦ canonicalDiagonalDifference model i omega) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [canonicalCircularizedMatrix, canonicalDiagonalDifference]
  · simp [canonicalCircularizedMatrix, canonicalDiagonalDifference, hij,
      Matrix.diagonal_apply]

/-- Companion entries are mutually independent, inherited from the product coordinates. -/
theorem canonicalGaussianMatrix_entries_independent
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    iIndepFun
      (fun ij : Fin n × Fin n ↦
        fun omega ↦ canonicalGaussianMatrix model omega ij.1 ij.2)
      (canonicalGaussianMeasure model) := by
  have h := (canonical_source_iIndepFun model).precomp
    (g := fun ij : Fin n × Fin n ↦ Sum.inl ij)
    (fun _ _ hEq ↦ Sum.inl.inj hEq)
  exact h.comp
    (fun _ x ↦ realPairToComplex x)
    (fun _ ↦ measurable_realPairToComplex)

/-- Every companion entry has a jointly Gaussian `(re,im)` pair. -/
theorem canonicalGaussianMatrix_entry_jointGaussian
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    HasGaussianLaw
      (fun omega ↦
        ((canonicalGaussianMatrix model omega i j).re,
          (canonicalGaussianMatrix model omega i j).im))
      (canonicalGaussianMeasure model) := by
  simpa [canonicalGaussianMatrix, realPairCoordinatesCLM, Function.comp_def] using
    (canonical_source_hasGaussianLaw model (Sum.inl (i, j))).map
      realPairCoordinatesCLM

/-- Scaling the standardized atom by the real profile coefficient scales either real
coordinate by that coefficient. -/
private theorem complexRealCoordinate_coefficient_mul_atom
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (i j : Fin n) (omegaXi : OmegaXi) (k : Fin 2) :
    complexRealCoordinate
        ((model.profile.coefficient i j : ℂ) * model.atom omegaXi) k =
      model.profile.coefficient i j * atomRealCoordinates model omegaXi k := by
  fin_cases k <;>
    simp [complexRealCoordinate, atomRealCoordinates, Complex.mul_re, Complex.mul_im]

private theorem measurable_complexRealCoordinate (k : Fin 2) :
    Measurable (fun z : ℂ ↦ complexRealCoordinate z k) := by
  fin_cases k
  · simpa [complexRealCoordinate] using Complex.measurable_re
  · simpa [complexRealCoordinate] using Complex.measurable_im

/-- The actual entry's complete real second-moment matrix is `b_ij² Q`. -/
theorem integral_entry_realCoordinates_mul_eq
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (i j : Fin n) (k l : Fin 2) :
    (∫ omega,
        complexRealCoordinate (model.matrix omega i j) k *
          complexRealCoordinate (model.matrix omega i j) l ∂mu) =
      model.profile.coefficient i j ^ 2 * atomSecondMomentMatrix model k l := by
  have hLaw := (model.entry_law i j).comp
    ((measurable_complexRealCoordinate k).mul
      (measurable_complexRealCoordinate l))
  have hIntegral := hLaw.integral_eq
  rw [show (∫ omega,
      complexRealCoordinate (model.matrix omega i j) k *
        complexRealCoordinate (model.matrix omega i j) l ∂mu) =
      ∫ omegaXi,
        complexRealCoordinate
            ((model.profile.coefficient i j : ℂ) * model.atom omegaXi) k *
          complexRealCoordinate
            ((model.profile.coefficient i j : ℂ) * model.atom omegaXi) l ∂nu by
      simpa [Function.comp_def] using hIntegral]
  simp_rw [complexRealCoordinate_coefficient_mul_atom model i j]
  rw [show (fun omegaXi ↦
      (model.profile.coefficient i j * atomRealCoordinates model omegaXi k) *
        (model.profile.coefficient i j * atomRealCoordinates model omegaXi l)) =
      fun omegaXi ↦ model.profile.coefficient i j ^ 2 *
        (atomRealCoordinates model omegaXi k * atomRealCoordinates model omegaXi l) by
          funext omegaXi
          ring]
  rw [integral_const_mul, ← atomSecondMomentMatrix_apply]

theorem canonicalGaussianMatrix_re_mean_match
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    (∫ omega, (canonicalGaussianMatrix model omega i j).re
        ∂canonicalGaussianMeasure model) =
      ∫ omega, (model.matrix omega i j).re ∂mu := by
  rw [show (∫ omega, (canonicalGaussianMatrix model omega i j).re
      ∂canonicalGaussianMeasure model) = 0 by
        simpa [canonicalGaussianMatrix] using
          canonical_source_eval_mean_zero model (Sum.inl (i, j)) 0,
    integral_entry_re_eq_zero model]

theorem canonicalGaussianMatrix_im_mean_match
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    (∫ omega, (canonicalGaussianMatrix model omega i j).im
        ∂canonicalGaussianMeasure model) =
      ∫ omega, (model.matrix omega i j).im ∂mu := by
  rw [show (∫ omega, (canonicalGaussianMatrix model omega i j).im
      ∂canonicalGaussianMeasure model) = 0 by
        simpa [canonicalGaussianMatrix] using
          canonical_source_eval_mean_zero model (Sum.inl (i, j)) 1,
    integral_entry_im_eq_zero model]

theorem canonicalGaussianMatrix_re_second_match
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    (∫ omega, (canonicalGaussianMatrix model omega i j).re ^ 2
        ∂canonicalGaussianMeasure model) =
      ∫ omega, (model.matrix omega i j).re ^ 2 ∂mu := by
  rw [show (∫ omega, (canonicalGaussianMatrix model omega i j).re ^ 2
      ∂canonicalGaussianMeasure model) =
        companionEntryCovariance model i j 0 0 by
      simpa [canonicalGaussianMatrix, canonicalSourceCovariance] using
        canonical_source_eval_secondMoment model (Sum.inl (i, j)) 0]
  calc
    companionEntryCovariance model i j 0 0 =
        model.profile.coefficient i j ^ 2 * atomSecondMomentMatrix model 0 0 := by
      simp [companionEntryCovariance]
    _ = ∫ omega,
        complexRealCoordinate (model.matrix omega i j) 0 *
          complexRealCoordinate (model.matrix omega i j) 0 ∂mu :=
      (integral_entry_realCoordinates_mul_eq model i j 0 0).symm
    _ = ∫ omega, (model.matrix omega i j).re ^ 2 ∂mu := by
      congr 1
      funext omega
      simp [pow_two]

theorem canonicalGaussianMatrix_im_second_match
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    (∫ omega, (canonicalGaussianMatrix model omega i j).im ^ 2
        ∂canonicalGaussianMeasure model) =
      ∫ omega, (model.matrix omega i j).im ^ 2 ∂mu := by
  rw [show (∫ omega, (canonicalGaussianMatrix model omega i j).im ^ 2
      ∂canonicalGaussianMeasure model) =
        companionEntryCovariance model i j 1 1 by
      simpa [canonicalGaussianMatrix, canonicalSourceCovariance] using
        canonical_source_eval_secondMoment model (Sum.inl (i, j)) 1]
  calc
    companionEntryCovariance model i j 1 1 =
        model.profile.coefficient i j ^ 2 * atomSecondMomentMatrix model 1 1 := by
      simp [companionEntryCovariance]
    _ = ∫ omega,
        complexRealCoordinate (model.matrix omega i j) 1 *
          complexRealCoordinate (model.matrix omega i j) 1 ∂mu :=
      (integral_entry_realCoordinates_mul_eq model i j 1 1).symm
    _ = ∫ omega, (model.matrix omega i j).im ^ 2 ∂mu := by
      congr 1
      funext omega
      simp [pow_two]

theorem canonicalGaussianMatrix_re_im_second_match
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i j : Fin n) :
    (∫ omega,
        (canonicalGaussianMatrix model omega i j).re *
          (canonicalGaussianMatrix model omega i j).im
        ∂canonicalGaussianMeasure model) =
      ∫ omega,
        (model.matrix omega i j).re * (model.matrix omega i j).im ∂mu := by
  rw [show (∫ omega,
      (canonicalGaussianMatrix model omega i j).re *
        (canonicalGaussianMatrix model omega i j).im
      ∂canonicalGaussianMeasure model) =
        companionEntryCovariance model i j 0 1 by
      simpa [canonicalGaussianMatrix, canonicalSourceCovariance] using
        canonical_source_eval_crossMoment model (Sum.inl (i, j))]
  calc
    companionEntryCovariance model i j 0 1 =
        model.profile.coefficient i j ^ 2 * atomSecondMomentMatrix model 0 1 := by
      simp [companionEntryCovariance]
    _ = ∫ omega,
        complexRealCoordinate (model.matrix omega i j) 0 *
          complexRealCoordinate (model.matrix omega i j) 1 ∂mu :=
      (integral_entry_realCoordinates_mul_eq model i j 0 1).symm
    _ = ∫ omega,
        (model.matrix omega i j).re * (model.matrix omega i j).im ∂mu := by
      simp

/-- The canonical construction inhabits the full companion-model structure used by the
internally proved BVH comparison. -/
def canonicalGaussianCompanion
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    GaussianCompanionModelV3 n Omega OmegaXi (CanonicalGaussianSample n)
      mu nu (canonicalGaussianMeasure model) model where
  matrix := canonicalGaussianMatrix model
  entry_measurable := canonicalGaussianMatrix_entry_measurable model
  entries_independent := canonicalGaussianMatrix_entries_independent model
  entry_jointGaussian := canonicalGaussianMatrix_entry_jointGaussian model
  re_mean_match := canonicalGaussianMatrix_re_mean_match model
  im_mean_match := canonicalGaussianMatrix_im_mean_match model
  re_second_match := canonicalGaussianMatrix_re_second_match model
  im_second_match := canonicalGaussianMatrix_im_second_match model
  re_im_second_match := canonicalGaussianMatrix_re_im_second_match model

private theorem canonical_companion_circular_eval_indep
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (i : Fin n) (k : Fin 2) :
    IndepFun
      (fun omega : CanonicalGaussianSample n ↦ omega (Sum.inl (i, i)) k)
      (fun omega : CanonicalGaussianSample n ↦ omega (Sum.inr i) k)
      (canonicalGaussianMeasure model) := by
  have hSources := (canonical_source_iIndepFun model).indepFun
    (show (Sum.inl (i, i) : GaussianSourceIndex n) ≠ Sum.inr i by simp)
  simpa [Function.comp_def] using hSources.comp
    (show Measurable (fun x : GaussianRealPair ↦ x k) by fun_prop)
    (show Measurable (fun x : GaussianRealPair ↦ x k) by fun_prop)

/-- Each real coordinate of the diagonal difference is the difference of two independent
Gaussian coordinates, hence Gaussian. -/
theorem canonicalDiagonalDifference_re_hasGaussianLaw
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i : Fin n) :
    HasGaussianLaw
      (fun omega ↦ (canonicalDiagonalDifference model i omega).re)
      (canonicalGaussianMeasure model) := by
  simpa [canonicalDiagonalDifference, canonicalGaussianMatrix,
    canonicalCircularDiagonal] using
    iIndepFun.hasGaussianLaw_fun_sub
      (canonical_source_eval_hasGaussianLaw model (Sum.inl (i, i)) 0)
      (canonical_source_eval_hasGaussianLaw model (Sum.inr i) 0)
      (canonical_companion_circular_eval_indep model i 0)

theorem canonicalDiagonalDifference_im_hasGaussianLaw
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i : Fin n) :
    HasGaussianLaw
      (fun omega ↦ (canonicalDiagonalDifference model i omega).im)
      (canonicalGaussianMeasure model) := by
  simpa [canonicalDiagonalDifference, canonicalGaussianMatrix,
    canonicalCircularDiagonal] using
    iIndepFun.hasGaussianLaw_fun_sub
      (canonical_source_eval_hasGaussianLaw model (Sum.inl (i, i)) 1)
      (canonical_source_eval_hasGaussianLaw model (Sum.inr i) 1)
      (canonical_companion_circular_eval_indep model i 1)

theorem canonicalDiagonalDifference_re_mean_zero
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i : Fin n) :
    (∫ omega, (canonicalDiagonalDifference model i omega).re
      ∂canonicalGaussianMeasure model) = 0 := by
  have hX := (canonical_source_eval_hasGaussianLaw model (Sum.inl (i, i)) 0).integrable
  have hR := (canonical_source_eval_hasGaussianLaw model (Sum.inr i) 0).integrable
  change (∫ omega : CanonicalGaussianSample n,
    omega (Sum.inl (i, i)) 0 - omega (Sum.inr i) 0
      ∂canonicalGaussianMeasure model) = 0
  rw [integral_sub hX hR,
    canonical_source_eval_mean_zero model (Sum.inl (i, i)) 0,
    canonical_source_eval_mean_zero model (Sum.inr i) 0, sub_zero]

theorem canonicalDiagonalDifference_im_mean_zero
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (i : Fin n) :
    (∫ omega, (canonicalDiagonalDifference model i omega).im
      ∂canonicalGaussianMeasure model) = 0 := by
  have hX := (canonical_source_eval_hasGaussianLaw model (Sum.inl (i, i)) 1).integrable
  have hR := (canonical_source_eval_hasGaussianLaw model (Sum.inr i) 1).integrable
  change (∫ omega : CanonicalGaussianSample n,
    omega (Sum.inl (i, i)) 1 - omega (Sum.inr i) 1
      ∂canonicalGaussianMeasure model) = 0
  rw [integral_sub hX hR,
    canonical_source_eval_mean_zero model (Sum.inl (i, i)) 1,
    canonical_source_eval_mean_zero model (Sum.inr i) 1, sub_zero]

private theorem atomSecondMomentMatrix_diag_le_one
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (k : Fin 2) :
    atomSecondMomentMatrix model k k ≤ 1 := by
  calc
    atomSecondMomentMatrix model k k ≤
        ∑ l : Fin 2, atomSecondMomentMatrix model l l :=
      Finset.single_le_sum
        (f := fun l : Fin 2 ↦ atomSecondMomentMatrix model l l)
        (fun l _ ↦ (atomSecondMomentMatrix_posSemidef model).diag_nonneg)
        (Finset.mem_univ k)
    _ = (atomSecondMomentMatrix model).trace := rfl
    _ = 1 := atomSecondMomentMatrix_trace model

private theorem canonical_companion_source_variance_le_coefficient_sq
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (i j : Fin n) (k : Fin 2) :
    Var[fun omega : CanonicalGaussianSample n ↦ omega (Sum.inl (i, j)) k;
        canonicalGaussianMeasure model] ≤ model.profile.coefficient i j ^ 2 := by
  rw [canonical_source_eval_variance, canonicalSourceCovariance,
    companionEntryCovariance, Matrix.smul_apply]
  simpa only [smul_eq_mul, mul_one] using
    mul_le_mul_of_nonneg_left (atomSecondMomentMatrix_diag_le_one model k)
      (sq_nonneg (model.profile.coefficient i j))

private theorem canonical_circular_source_variance
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (i : Fin n) (k : Fin 2) :
    Var[fun omega : CanonicalGaussianSample n ↦ omega (Sum.inr i) k;
        canonicalGaussianMeasure model] = model.profile.coefficient i i ^ 2 / 2 := by
  rw [canonical_source_eval_variance]
  simp [canonicalSourceCovariance, circularDiagonalCovariance]

private theorem canonical_diagonalDifference_coordinate_variance
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (i : Fin n) (k : Fin 2) :
    Var[fun omega : CanonicalGaussianSample n ↦
        omega (Sum.inl (i, i)) k - omega (Sum.inr i) k;
        canonicalGaussianMeasure model] =
      Var[fun omega : CanonicalGaussianSample n ↦ omega (Sum.inl (i, i)) k;
          canonicalGaussianMeasure model] +
        Var[fun omega : CanonicalGaussianSample n ↦ omega (Sum.inr i) k;
          canonicalGaussianMeasure model] := by
  have hX := (canonical_source_eval_hasGaussianLaw model (Sum.inl (i, i)) k).memLp_two
  have hR := (canonical_source_eval_hasGaussianLaw model (Sum.inr i) k).memLp_two
  rw [variance_fun_sub hX hR,
    (canonical_companion_circular_eval_indep model i k).covariance_eq_zero hX hR]
  ring

theorem canonicalDiagonalDifference_re_variance_le_two_div_bandwidth
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    {B : ℝ} (hB : IsBandwidth model.profile B) (i : Fin n) :
    Var[fun omega ↦ (canonicalDiagonalDifference model i omega).re;
      canonicalGaussianMeasure model] ≤ 2 / B := by
  change Var[fun omega : CanonicalGaussianSample n ↦
    omega (Sum.inl (i, i)) 0 - omega (Sum.inr i) 0;
      canonicalGaussianMeasure model] ≤ 2 / B
  rw [canonical_diagonalDifference_coordinate_variance model i 0,
    canonical_circular_source_variance model i 0]
  calc
    Var[fun omega : CanonicalGaussianSample n ↦ omega (Sum.inl (i, i)) 0;
        canonicalGaussianMeasure model] + model.profile.coefficient i i ^ 2 / 2 ≤
        model.profile.coefficient i i ^ 2 + model.profile.coefficient i i ^ 2 / 2 :=
      by
        exact add_le_add
          (canonical_companion_source_variance_le_coefficient_sq model i i 0) le_rfl
    _ ≤ 2 * model.profile.coefficient i i ^ 2 := by
      nlinarith [sq_nonneg (model.profile.coefficient i i)]
    _ ≤ 2 * B⁻¹ :=
      mul_le_mul_of_nonneg_left (hB.sq_le_inv i i) (by norm_num)
    _ = 2 / B := by simp [div_eq_mul_inv]

theorem canonicalDiagonalDifference_im_variance_le_two_div_bandwidth
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    {B : ℝ} (hB : IsBandwidth model.profile B) (i : Fin n) :
    Var[fun omega ↦ (canonicalDiagonalDifference model i omega).im;
      canonicalGaussianMeasure model] ≤ 2 / B := by
  change Var[fun omega : CanonicalGaussianSample n ↦
    omega (Sum.inl (i, i)) 1 - omega (Sum.inr i) 1;
      canonicalGaussianMeasure model] ≤ 2 / B
  rw [canonical_diagonalDifference_coordinate_variance model i 1,
    canonical_circular_source_variance model i 1]
  calc
    Var[fun omega : CanonicalGaussianSample n ↦ omega (Sum.inl (i, i)) 1;
        canonicalGaussianMeasure model] + model.profile.coefficient i i ^ 2 / 2 ≤
        model.profile.coefficient i i ^ 2 + model.profile.coefficient i i ^ 2 / 2 :=
      by
        exact add_le_add
          (canonical_companion_source_variance_le_coefficient_sq model i i 1) le_rfl
    _ ≤ 2 * model.profile.coefficient i i ^ 2 := by
      nlinarith [sq_nonneg (model.profile.coefficient i i)]
    _ ≤ 2 * B⁻¹ :=
      mul_le_mul_of_nonneg_left (hB.sq_le_inv i i) (by norm_num)
    _ = 2 / B := by simp [div_eq_mul_inv]

end

end Arxiv2410V3.BVH

