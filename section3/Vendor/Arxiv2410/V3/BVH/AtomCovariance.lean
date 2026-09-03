/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/AtomCovariance.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.RandomModel
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The real two-coordinate second-moment matrix of the v3 atom

For the Gaussian companion used below v3 Proposition 3.4, the complex atom is viewed as
the real vector `(re ξ, im ξ)`.  This file constructs its raw `2 × 2` second-moment matrix
as an `L²` Gram matrix.  Consequently positive semidefiniteness is proved internally, rather
than requested as realization data from a caller.
-/

namespace Arxiv2410V3.BVH

open MeasureTheory ProbabilityTheory Matrix

noncomputable section

variable {Omega OmegaXi : Type*}
  [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
  {mu : Measure Omega} {nu : Measure OmegaXi}
  [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
  {n : ℕ}

/-- The two real coordinates of the standardized complex atom in v3 Proposition 3.4:
coordinate `0` is the real part and coordinate `1` is the imaginary part. -/
def atomRealCoordinates
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (omegaXi : OmegaXi) (k : Fin 2) : ℝ :=
  if k = 0 then (model.atom omegaXi).re else (model.atom omegaXi).im

@[simp]
theorem atomRealCoordinates_zero
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (omegaXi : OmegaXi) :
    atomRealCoordinates model omegaXi 0 = (model.atom omegaXi).re := by
  simp [atomRealCoordinates]

@[simp]
theorem atomRealCoordinates_one
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (omegaXi : OmegaXi) :
    atomRealCoordinates model omegaXi 1 = (model.atom omegaXi).im := by
  simp [atomRealCoordinates]

/-- Each real coordinate inherits almost-everywhere strong measurability from integrability
of the complex atom. -/
theorem atomRealCoordinates_aestronglyMeasurable
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (k : Fin 2) :
    AEStronglyMeasurable (fun omegaXi ↦ atomRealCoordinates model omegaXi k) nu := by
  fin_cases k
  · simpa using model.atom_integrable.re.aestronglyMeasurable
  · simpa using model.atom_integrable.im.aestronglyMeasurable

/-- The atom's squared norm is integrable; this is the elementary consequence of the finite
third absolute moment used to place both real coordinates in `L²`. -/
theorem integrable_atom_norm_square
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    Integrable (fun omegaXi ↦ ‖model.atom omegaXi‖ ^ 2) nu := by
  exact integrable_norm_pow_of_le model.atom_integrable.aestronglyMeasurable
    (by norm_num) model.atom_third_moment_finite

/-- Each real coordinate has an integrable square. -/
theorem integrable_atomRealCoordinates_sq
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (k : Fin 2) :
    Integrable (fun omegaXi ↦ atomRealCoordinates model omegaXi k ^ 2) nu := by
  refine Integrable.mono' (integrable_atom_norm_square model)
    ((atomRealCoordinates_aestronglyMeasurable model k).pow 2) ?_
  filter_upwards [] with omegaXi
  fin_cases k
  · simpa [Real.norm_eq_abs, sq_abs] using
      (pow_le_pow_left₀ (abs_nonneg (model.atom omegaXi).re)
        (Complex.abs_re_le_norm (model.atom omegaXi)) 2)
  · simpa [Real.norm_eq_abs, sq_abs] using
      (pow_le_pow_left₀ (abs_nonneg (model.atom omegaXi).im)
        (Complex.abs_im_le_norm (model.atom omegaXi)) 2)

/-- Equivalently, each real coordinate belongs to `L²`. -/
theorem atomRealCoordinates_memLp_two
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (k : Fin 2) :
    MemLp (fun omegaXi ↦ atomRealCoordinates model omegaXi k) 2 nu := by
  exact (memLp_two_iff_integrable_sq
    (atomRealCoordinates_aestronglyMeasurable model k)).2
      (integrable_atomRealCoordinates_sq model k)

/-- Products of any two real coordinates are integrable. -/
theorem integrable_atomRealCoordinates_mul
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (a b : Fin 2) :
    Integrable (fun omegaXi ↦
      atomRealCoordinates model omegaXi a * atomRealCoordinates model omegaXi b) nu := by
  change Integrable
    ((fun omegaXi ↦ atomRealCoordinates model omegaXi a) *
      (fun omegaXi ↦ atomRealCoordinates model omegaXi b)) nu
  exact (atomRealCoordinates_memLp_two model a).integrable_mul
    (atomRealCoordinates_memLp_two model b)

/-- The `L²` realization of one real coordinate of the atom. -/
def atomRealCoordinateL2
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (k : Fin 2) :
    OmegaXi →₂[nu] ℝ :=
  (atomRealCoordinates_memLp_two model k).toLp
    (fun omegaXi ↦ atomRealCoordinates model omegaXi k)

/-- The raw real `2 × 2` second-moment matrix
`Qₐᵇ = ∫ (Re ξ, Im ξ)ₐ (Re ξ, Im ξ)ᵇ` used to construct the Gaussian companion. -/
def atomSecondMomentMatrix
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.gram ℝ (fun k ↦ atomRealCoordinateL2 model k)

/-- Every entry of `Q` is exactly the corresponding raw second moment of the atom. -/
theorem atomSecondMomentMatrix_apply
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) (a b : Fin 2) :
    atomSecondMomentMatrix model a b =
      ∫ omegaXi, atomRealCoordinates model omegaXi a *
        atomRealCoordinates model omegaXi b ∂nu := by
  rw [atomSecondMomentMatrix, Matrix.gram_apply, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  apply integral_congr_ae
  filter_upwards [
    MemLp.coeFn_toLp (atomRealCoordinates_memLp_two model a),
    MemLp.coeFn_toLp (atomRealCoordinates_memLp_two model b)] with omegaXi ha hb
  dsimp only [atomRealCoordinateL2]
  rw [ha, hb]
  exact mul_comm _ _

/-- `Q₀₀ = ∫ (Re ξ)²`. -/
@[simp]
theorem atomSecondMomentMatrix_zero_zero
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    atomSecondMomentMatrix model 0 0 =
      ∫ omegaXi, (model.atom omegaXi).re ^ 2 ∂nu := by
  rw [atomSecondMomentMatrix_apply]
  simp [pow_two]

/-- `Q₁₁ = ∫ (Im ξ)²`. -/
@[simp]
theorem atomSecondMomentMatrix_one_one
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    atomSecondMomentMatrix model 1 1 =
      ∫ omegaXi, (model.atom omegaXi).im ^ 2 ∂nu := by
  rw [atomSecondMomentMatrix_apply]
  simp [pow_two]

/-- `Q₀₁ = ∫ (Re ξ)(Im ξ)`. -/
@[simp]
theorem atomSecondMomentMatrix_zero_one
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    atomSecondMomentMatrix model 0 1 =
      ∫ omegaXi, (model.atom omegaXi).re * (model.atom omegaXi).im ∂nu := by
  rw [atomSecondMomentMatrix_apply]
  simp

/-- `Q₁₀ = ∫ (Im ξ)(Re ξ)`. -/
@[simp]
theorem atomSecondMomentMatrix_one_zero
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    atomSecondMomentMatrix model 1 0 =
      ∫ omegaXi, (model.atom omegaXi).im * (model.atom omegaXi).re ∂nu := by
  rw [atomSecondMomentMatrix_apply]
  simp

/-- The raw second-moment matrix is symmetric. -/
theorem atomSecondMomentMatrix_isSymm
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    (atomSecondMomentMatrix model)ᵀ = atomSecondMomentMatrix model := by
  ext a b
  rw [transpose_apply, atomSecondMomentMatrix_apply, atomSecondMomentMatrix_apply]
  apply integral_congr_ae
  filter_upwards [] with omegaXi
  exact mul_comm _ _

/-- The raw second-moment matrix is positive semidefinite, since it is an `L²` Gram matrix. -/
theorem atomSecondMomentMatrix_posSemidef
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    (atomSecondMomentMatrix model).PosSemidef := by
  exact Matrix.posSemidef_gram ℝ _

/-- The two raw coordinate variances sum to one, by the variance-one normalization of the
complex atom in v3 Proposition 3.4. -/
theorem atomSecondMomentMatrix_trace
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu) :
    Matrix.trace (atomSecondMomentMatrix model) = 1 := by
  rw [Matrix.trace_fin_two, atomSecondMomentMatrix_zero_zero,
    atomSecondMomentMatrix_one_one, ← integral_add]
  · convert model.atom_variance_one using 1
    apply integral_congr_ae
    filter_upwards [] with omegaXi
    simpa [Complex.normSq_apply, pow_two] using
      (Complex.normSq_eq_norm_sq (model.atom omegaXi))
  · exact integrable_atomRealCoordinates_sq model 0
  · exact integrable_atomRealCoordinates_sq model 1

end

end Arxiv2410V3.BVH

