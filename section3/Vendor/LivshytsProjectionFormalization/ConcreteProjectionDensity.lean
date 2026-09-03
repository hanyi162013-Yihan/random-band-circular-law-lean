/- Source snapshot: upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/ConcreteProjectionDensity.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.LivshytsProjectionFormalization.ConcreteFiberBL
import Vendor.LivshytsProjectionFormalization.DensityScaling
import Vendor.LivshytsProjectionFormalization.EntropyJacobian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open scoped ENNReal NNReal

open MeasureTheory

namespace LivshytsProjectionFormalization

noncomputable section

/-- Measurable one-coordinate probability densities with a common pointwise bound. -/
structure CoordinateDensityData (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) (K : ℝ) where
  pdf : Fin n → 𝕜 → ℝ≥0∞
  measurable_pdf : ∀ i, Measurable (pdf i)
  integral_pdf : ∀ i, ∫⁻ z, pdf i z = 1
  pdf_le : ∀ i z, pdf i z ≤ ENNReal.ofReal K

/-- Product density of the independent coordinates on the ambient Euclidean space. -/
def coordinateProductDensity {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (f : Fin n → 𝕜 → ℝ≥0∞) (x : CoordinateSpace 𝕜 n) : ℝ≥0∞ :=
  ∏ i, f i (x i)

theorem measurable_coordinateProductDensity
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {f : Fin n → 𝕜 → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) : Measurable (coordinateProductDensity f) := by
  unfold coordinateProductDensity
  exact Finset.measurable_prod Finset.univ fun i _ ↦ (hf i).comp (by fun_prop)

/-- The affine point on the fiber `y + W` in orthonormal coordinates on `W`. -/
def kernelFiberPoint
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    (y : CoordinateSpace 𝕜 n) (x : CoordinateSpace 𝕜 (Module.finrank 𝕜 W)) :
    CoordinateSpace 𝕜 n :=
  y + (kernelCoordinateBasis W).repr.symm x

/-- Candidate density obtained by integrating the product density along the affine fiber `y + W`. -/
def kernelFiberDensity
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    (f : Fin n → 𝕜 → ℝ≥0∞) (y : CoordinateSpace 𝕜 n) : ℝ≥0∞ :=
  ∫⁻ x : CoordinateSpace 𝕜 (Module.finrank 𝕜 W),
    coordinateProductDensity f (kernelFiberPoint W y x)

theorem measurable_kernelFiberDensity
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    {f : Fin n → 𝕜 → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    Measurable (kernelFiberDensity W f) := by
  unfold kernelFiberDensity coordinateProductDensity kernelFiberPoint
  apply Measurable.lintegral_prod_right
  apply Finset.measurable_prod Finset.univ
  intro i hi
  exact (hf i).comp (by fun_prop)

/-- Fiber density on a subspace `E`, integrating in the orthogonal direction `Eᵮ`. -/
def orthogonalProjectionFiberDensity
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (E : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    (f : Fin n → 𝕜 → ℝ≥0∞) (y : E) : ℝ≥0∞ :=
  kernelFiberDensity (Submodule.orthogonal E) f y

theorem measurable_orthogonalProjectionFiberDensity
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (E : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    {f : Fin n → 𝕜 → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    Measurable (orthogonalProjectionFiberDensity E f) :=
  (measurable_kernelFiberDensity (Submodule.orthogonal E) hf).comp (by fun_prop)

/-- Euclidean volume on a subspace, normalized by an orthonormal coordinate basis. -/
def subspaceVolume
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (E : Submodule 𝕜 (CoordinateSpace 𝕜 n)) :
    Measure E :=
  Measure.map (kernelCoordinateBasis E).repr.symm
    (volume : Measure (CoordinateSpace 𝕜 (Module.finrank 𝕜 E)))

/-- Exact finite-dimensional coarea/disintegration statement needed to identify the fiber integral
as the density of the orthogonal projection.  The geometric BL argument does not belong here. -/
def OrthogonalProjectionCoarea
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (E : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    (f : Fin n → 𝕜 → ℝ≥0∞) : Prop :=
  Measure.map E.orthogonalProjectionOnto
      (volume.withDensity (coordinateProductDensity f)) =
    (subspaceVolume E).withDensity (orthogonalProjectionFiberDensity E f)

/-- Interpolation used at each coordinate: if `x ≤ A` and `0 ≤ c ≤ 1`, then
`x ≤ A^(1-c) x^c`. -/
theorem bounded_le_rpow_interpolation
    {x A : ℝ≥0∞} {c : ℝ} (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hx : x ≤ A) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    x ≤ A ^ (1 - c) * x ^ c := by
  have hq : A⁻¹ * x ≤ 1 := by
    calc
      A⁻¹ * x ≤ A⁻¹ * A := mul_le_mul' (le_rfl : A⁻¹ ≤ A⁻¹) hx
      _ = 1 := ENNReal.inv_mul_cancel hA0 hAtop
  have hqpow : A⁻¹ * x ≤ (A⁻¹ * x) ^ c := by
    calc
      A⁻¹ * x = (A⁻¹ * x) ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
      _ ≤ (A⁻¹ * x) ^ c := ENNReal.rpow_le_rpow_of_exponent_ge hq hc1
  calc
    x = A * (A⁻¹ * x) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hA0 hAtop, one_mul]
    _ ≤ A * (A⁻¹ * x) ^ c := mul_le_mul' (le_rfl : A ≤ A) hqpow
    _ = A ^ (1 - c) * x ^ c := by
      rw [ENNReal.mul_rpow_of_nonneg A⁻¹ x hc0, ENNReal.inv_rpow,
        ENNReal.rpow_sub 1 c hA0 hAtop, ENNReal.rpow_one]
      simp only [div_eq_mul_inv, mul_assoc]

/-- Coordinates which vanish identically on the kernel subspace. -/
abbrev InactiveKernelCoordinate
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (W : Submodule 𝕜 (CoordinateSpace 𝕜 n)) :=
  {i : Fin n // ¬ kernelCoordinateVector W i ≠ 0}

/-- The exponent contributed by inactive coordinates and interpolation on active coordinates. -/
def kernelInterpolationExponent
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (W : Submodule 𝕜 (CoordinateSpace 𝕜 n)) : ℝ :=
  Fintype.card (InactiveKernelCoordinate W) +
    ∑ i : ActiveKernelCoordinate W, (1 - kernelCoordinateWeight W i)

theorem kernelInterpolationExponent_eq_codimension
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (W : Submodule 𝕜 (CoordinateSpace 𝕜 n)) :
    kernelInterpolationExponent W = n - Module.finrank 𝕜 W := by
  classical
  have hcard : Fintype.card (InactiveKernelCoordinate W) =
      n - Fintype.card (ActiveKernelCoordinate W) := by
    simpa [InactiveKernelCoordinate, ActiveKernelCoordinate] using
      (Fintype.card_subtype_compl (fun i : Fin n ↦ kernelCoordinateVector W i ≠ 0))
  have hle : Fintype.card (ActiveKernelCoordinate W) ≤ n := by
    simpa using Fintype.card_subtype_le
  unfold kernelInterpolationExponent
  rw [hcard, Nat.cast_sub hle, Finset.sum_sub_distrib,
    sum_kernelCoordinateWeight_eq_finrank]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

theorem prod_rpow_eq_rpow_sum
    {ι : Type*} [Fintype ι] (A : ℝ≥0∞) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (c : ι → ℝ) :
    ∏ i, A ^ c i = A ^ (∑ i, c i) := by
  classical
  let s : Finset ι := Finset.univ
  change (∏ i ∈ s, A ^ c i) = A ^ (∑ i ∈ s, c i)
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih,
        ENNReal.rpow_add _ _ hA0 hAtop]

/-- Total interpolation constant before applying geometric BL. -/
def kernelInterpolationConstant
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    (A : ℝ≥0∞) : ℝ≥0∞ :=
  (∏ i : ActiveKernelCoordinate W, A ^ (1 - kernelCoordinateWeight W i)) *
    ∏ _i : InactiveKernelCoordinate W, A

theorem kernelInterpolationConstant_eq_codimension
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    {A : ℝ≥0∞} (hA0 : A ≠ 0) (hAtop : A ≠ ∞) :
    kernelInterpolationConstant W A = A ^ (n - Module.finrank 𝕜 W : ℝ) := by
  unfold kernelInterpolationConstant
  rw [prod_rpow_eq_rpow_sum A hA0 hAtop]
  simp only [Finset.prod_const, Finset.card_univ]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_add _ _ hA0 hAtop]
  congr 1
  rw [← kernelInterpolationExponent_eq_codimension W]
  simp only [kernelInterpolationExponent]
  ring

/-- The shifted one-coordinate density seen by a normalized kernel coordinate map. -/
def activeShiftedDensity
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    (f : Fin n → 𝕜 → ℝ≥0∞) (y : CoordinateSpace 𝕜 n)
    (i : ActiveKernelCoordinate W) (t : 𝕜) : ℝ≥0∞ :=
  f i (y i + (‖kernelCoordinateVector W i‖ : 𝕜) * t)

theorem measurable_activeShiftedDensity
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    {f : Fin n → 𝕜 → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    (y : CoordinateSpace 𝕜 n) (i : ActiveKernelCoordinate W) :
    Measurable (activeShiftedDensity W f y i) := by
  unfold activeShiftedDensity
  exact (hf i).comp (by fun_prop)

theorem activeKernelCoordinate_norm_pos
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    (i : ActiveKernelCoordinate W) : 0 < ‖kernelCoordinateVector W i‖ :=
  norm_pos_iff.mpr i.property

theorem real_lintegral_activeShiftedDensity
    {n : ℕ} (W : Submodule ℝ (CoordinateSpace ℝ n))
    (D : CoordinateDensityData ℝ n K) (y : CoordinateSpace ℝ n)
    (i : ActiveKernelCoordinate W) :
    ∫⁻ t : ℝ, activeShiftedDensity W D.pdf y i t =
      ENNReal.ofReal ‖kernelCoordinateVector W i‖⁻¹ := by
  simpa [activeShiftedDensity, D.integral_pdf i] using
    (real_lintegral_comp_add_mul_of_pos (D.pdf i) (D.measurable_pdf i)
      (y i) (activeKernelCoordinate_norm_pos W i))

theorem complex_lintegral_activeShiftedDensity
    {n : ℕ} (W : Submodule ℂ (CoordinateSpace ℂ n))
    (D : CoordinateDensityData ℂ n K) (y : CoordinateSpace ℂ n)
    (i : ActiveKernelCoordinate W) :
    ∫⁻ z : ℂ, activeShiftedDensity W D.pdf y i z =
      ENNReal.ofReal (‖kernelCoordinateVector W i‖⁻¹ ^ 2) := by
  simpa [activeShiftedDensity, RCLike.real_smul_eq_coe_mul, D.integral_pdf i] using
    (complex_lintegral_comp_add_real_smul_of_pos (D.pdf i) (D.measurable_pdf i)
      (y i) (activeKernelCoordinate_norm_pos W i))

/-- Product to which geometric BL is applied on the active kernel coordinates. -/
def activeBLIntegrand
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    (f : Fin n → 𝕜 → ℝ≥0∞) (y : CoordinateSpace 𝕜 n)
    (x : CoordinateSpace 𝕜 (Module.finrank 𝕜 W)) : ℝ≥0∞ :=
  ∏ i : ActiveKernelCoordinate W,
    (activeShiftedDensity W f y i ((normalizedKernelCoordinateMap W i) x)) ^
      kernelCoordinateWeight W i

theorem measurable_activeBLIntegrand
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    {f : Fin n → 𝕜 → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    (y : CoordinateSpace 𝕜 n) : Measurable (activeBLIntegrand W f y) := by
  unfold activeBLIntegrand
  apply Finset.measurable_prod Finset.univ
  intro i hi
  exact ENNReal.continuous_rpow_const.measurable.comp
    ((measurable_activeShiftedDensity W hf y i).comp
      (normalizedKernelCoordinateMap W i).continuous.measurable)

theorem active_kernelFiber_coordinate
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    (f : Fin n → 𝕜 → ℝ≥0∞) (y : CoordinateSpace 𝕜 n)
    (x : CoordinateSpace 𝕜 (Module.finrank 𝕜 W))
    (i : ActiveKernelCoordinate W) :
    f i ((kernelFiberPoint W y x) i) =
      activeShiftedDensity W f y i ((normalizedKernelCoordinateMap W i) x) := by
  unfold kernelFiberPoint activeShiftedDensity
  rw [PiLp.add_apply, ← kernelCoordinate_reconstruct W i x]

theorem inactive_kernelFiber_coordinate
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    (x : CoordinateSpace 𝕜 (Module.finrank 𝕜 W))
    (i : InactiveKernelCoordinate W) :
    (((kernelCoordinateBasis W).repr.symm x : W) : CoordinateSpace 𝕜 n) i = 0 := by
  have h := kernelCoordinate_inner_eq_coordinate W i ((kernelCoordinateBasis W).repr.symm x)
  rw [not_ne_iff.mp i.property, inner_zero_left] at h
  exact h.symm

/-- Pointwise reduction of the concrete fiber integrand to the geometric BL integrand. -/
theorem coordinateProductDensity_kernelFiberPoint_le
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    {f : Fin n → 𝕜 → ℝ≥0∞} {A : ℝ≥0∞}
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞) (hf : ∀ i z, f i z ≤ A)
    (y : CoordinateSpace 𝕜 n) (x : CoordinateSpace 𝕜 (Module.finrank 𝕜 W)) :
    coordinateProductDensity f (kernelFiberPoint W y x) ≤
      kernelInterpolationConstant W A * activeBLIntegrand W f y x := by
  classical
  let p : Fin n → Prop := fun i ↦ kernelCoordinateVector W i ≠ 0
  let g : Fin n → ℝ≥0∞ := fun i ↦ f i ((kernelFiberPoint W y x) i)
  have hsplit :
      (∏ i : ActiveKernelCoordinate W, g i) *
          ∏ i : InactiveKernelCoordinate W, g i = ∏ i, g i := by
    simpa [p, g, ActiveKernelCoordinate, InactiveKernelCoordinate] using
      (Fintype.prod_subtype_mul_prod_subtype p g)
  change (∏ i, g i) ≤ kernelInterpolationConstant W A * activeBLIntegrand W f y x
  rw [← hsplit]
  calc
    (∏ i : ActiveKernelCoordinate W, g i) *
        ∏ i : InactiveKernelCoordinate W, g i ≤
      (∏ i : ActiveKernelCoordinate W,
          A ^ (1 - kernelCoordinateWeight W i) *
            (activeShiftedDensity W f y i ((normalizedKernelCoordinateMap W i) x)) ^
              kernelCoordinateWeight W i) *
        ∏ _i : InactiveKernelCoordinate W, A := by
          gcongr
          · have hg : g i =
                activeShiftedDensity W f y i ((normalizedKernelCoordinateMap W i) x) := by
              dsimp only [g]
              exact active_kernelFiber_coordinate W f y x i
            rw [hg]
            exact bounded_le_rpow_interpolation hA0 hAtop (hf i _)
              (kernelCoordinateWeight_nonnegative W i) (kernelCoordinateWeight_le_one W i)
          · exact hf i _
    _ = kernelInterpolationConstant W A * activeBLIntegrand W f y x := by
      simp only [kernelInterpolationConstant, activeBLIntegrand, Finset.prod_mul_distrib]
      ac_rfl

/-- The concrete fiber integral is bounded by the interpolation constant times the BL integral. -/
theorem kernelFiberDensity_le_activeBL
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (W : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    {f : Fin n → 𝕜 → ℝ≥0∞} {A : ℝ≥0∞}
    (hA0 : A ≠ 0) (hAtop : A ≠ ∞) (hfmeas : ∀ i, Measurable (f i))
    (hf : ∀ i z, f i z ≤ A) (y : CoordinateSpace 𝕜 n) :
    kernelFiberDensity W f y ≤ kernelInterpolationConstant W A *
      ∫⁻ x : CoordinateSpace 𝕜 (Module.finrank 𝕜 W), activeBLIntegrand W f y x := by
  unfold kernelFiberDensity
  calc
    (∫⁻ x : CoordinateSpace 𝕜 (Module.finrank 𝕜 W),
        coordinateProductDensity f (kernelFiberPoint W y x)) ≤
      ∫⁻ x : CoordinateSpace 𝕜 (Module.finrank 𝕜 W),
        kernelInterpolationConstant W A * activeBLIntegrand W f y x :=
          lintegral_mono fun x ↦
            coordinateProductDensity_kernelFiberPoint_le W hA0 hAtop hf y x
    _ = kernelInterpolationConstant W A *
        ∫⁻ x : CoordinateSpace 𝕜 (Module.finrank 𝕜 W),
          activeBLIntegrand W f y x :=
      lintegral_const_mul _ (measurable_activeBLIntegrand W hfmeas y)

theorem real_activeBL_lintegral_le
    (hGBL : RealFiniteGeometricBrascampLieb) {n : ℕ}
    (W : Submodule ℝ (CoordinateSpace ℝ n)) (D : CoordinateDensityData ℝ n K)
    (y : CoordinateSpace ℝ n) :
    (∫⁻ x : CoordinateSpace ℝ (Module.finrank ℝ W), activeBLIntegrand W D.pdf y x) ≤
      ∏ i : ActiveKernelCoordinate W,
        (∫⁻ t : ℝ, activeShiftedDensity W D.pdf y i t) ^ kernelCoordinateWeight W i := by
  simpa only [activeBLIntegrand, ENNReal.rpow_eq_pow] using
    real_kernelCoordinate_geometricBL hGBL W (activeShiftedDensity W D.pdf y)
      (measurable_activeShiftedDensity W D.measurable_pdf y)

theorem complex_activeBL_lintegral_le
    (hGBL : ComplexFiniteGeometricBrascampLieb) {n : ℕ}
    (W : Submodule ℂ (CoordinateSpace ℂ n)) (D : CoordinateDensityData ℂ n K)
    (y : CoordinateSpace ℂ n) :
    (∫⁻ x : CoordinateSpace ℂ (Module.finrank ℂ W), activeBLIntegrand W D.pdf y x) ≤
      ∏ i : ActiveKernelCoordinate W,
        (∫⁻ z : ℂ, activeShiftedDensity W D.pdf y i z) ^ kernelCoordinateWeight W i := by
  simpa only [activeBLIntegrand, ENNReal.rpow_eq_pow] using
    complex_kernelCoordinate_geometricBL hGBL W (activeShiftedDensity W D.pdf y)
      (measurable_activeShiftedDensity W D.measurable_pdf y)

theorem real_activeShiftedDensity_integral_product_eq_entropy
    {n : ℕ} (W : Submodule ℝ (CoordinateSpace ℝ n))
    (D : CoordinateDensityData ℝ n K) (y : CoordinateSpace ℝ n) :
    (∏ i : ActiveKernelCoordinate W,
        (∫⁻ t : ℝ, activeShiftedDensity W D.pdf y i t) ^ kernelCoordinateWeight W i) =
      ENNReal.ofReal (Real.exp
        (1 / 2 * ∑ i : ActiveKernelCoordinate W, projectionEntropy (kernelCoordinateWeight W i))) := by
  classical
  calc
    (∏ i : ActiveKernelCoordinate W,
        (∫⁻ t : ℝ, activeShiftedDensity W D.pdf y i t) ^ kernelCoordinateWeight W i) =
      ∏ i : ActiveKernelCoordinate W,
        ENNReal.ofReal (Real.exp (1 / 2 * projectionEntropy (kernelCoordinateWeight W i))) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [real_lintegral_activeShiftedDensity W D y i]
          simpa only [kernelCoordinateWeight, ENNReal.rpow_eq_pow] using
            real_jacobian_rpow_eq_entropy_half (activeKernelCoordinate_norm_pos W i)
    _ = ENNReal.ofReal (Real.exp
        (1 / 2 * ∑ i : ActiveKernelCoordinate W, projectionEntropy (kernelCoordinateWeight W i))) := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ Real.exp_nonneg _),
        ← Real.exp_sum, ← Finset.mul_sum]

theorem complex_activeShiftedDensity_integral_product_eq_entropy
    {n : ℕ} (W : Submodule ℂ (CoordinateSpace ℂ n))
    (D : CoordinateDensityData ℂ n K) (y : CoordinateSpace ℂ n) :
    (∏ i : ActiveKernelCoordinate W,
        (∫⁻ z : ℂ, activeShiftedDensity W D.pdf y i z) ^ kernelCoordinateWeight W i) =
      ENNReal.ofReal (Real.exp
        (∑ i : ActiveKernelCoordinate W, projectionEntropy (kernelCoordinateWeight W i))) := by
  classical
  calc
    (∏ i : ActiveKernelCoordinate W,
        (∫⁻ z : ℂ, activeShiftedDensity W D.pdf y i z) ^ kernelCoordinateWeight W i) =
      ∏ i : ActiveKernelCoordinate W,
        ENNReal.ofReal (Real.exp (projectionEntropy (kernelCoordinateWeight W i))) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [complex_lintegral_activeShiftedDensity W D y i]
          simpa only [kernelCoordinateWeight, ENNReal.rpow_eq_pow] using
            complex_jacobian_rpow_eq_entropy (activeKernelCoordinate_norm_pos W i)
    _ = ENNReal.ofReal (Real.exp
        (∑ i : ActiveKernelCoordinate W, projectionEntropy (kernelCoordinateWeight W i))) := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ Real.exp_nonneg _), ← Real.exp_sum]

/-- Fully verified real fiber-density bound from the concrete kernel frame and geometric BL. -/
theorem real_kernelFiberDensity_le_entropy
    (hGBL : RealFiniteGeometricBrascampLieb) {n : ℕ} {K : ℝ} (hK : 0 < K)
    (W : Submodule ℝ (CoordinateSpace ℝ n)) (D : CoordinateDensityData ℝ n K)
    (y : CoordinateSpace ℝ n) :
    kernelFiberDensity W D.pdf y ≤
      (ENNReal.ofReal K) ^ (n - Module.finrank ℝ W : ℝ) *
        ENNReal.ofReal (Real.exp
          (1 / 2 * ∑ i : ActiveKernelCoordinate W,
            projectionEntropy (kernelCoordinateWeight W i))) := by
  have hA0 : ENNReal.ofReal K ≠ 0 := by positivity
  have hAtop : ENNReal.ofReal K ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    kernelFiberDensity W D.pdf y ≤ kernelInterpolationConstant W (ENNReal.ofReal K) *
        ∫⁻ x : CoordinateSpace ℝ (Module.finrank ℝ W), activeBLIntegrand W D.pdf y x :=
      kernelFiberDensity_le_activeBL W hA0 hAtop D.measurable_pdf D.pdf_le y
    _ ≤ kernelInterpolationConstant W (ENNReal.ofReal K) *
        ∏ i : ActiveKernelCoordinate W,
          (∫⁻ t : ℝ, activeShiftedDensity W D.pdf y i t) ^ kernelCoordinateWeight W i := by
      gcongr
      exact real_activeBL_lintegral_le hGBL W D y
    _ = _ := by
      rw [kernelInterpolationConstant_eq_codimension W hA0 hAtop,
        real_activeShiftedDensity_integral_product_eq_entropy W D y]

/-- Fully verified complex fiber-density bound from the concrete kernel frame and geometric BL. -/
theorem complex_kernelFiberDensity_le_entropy
    (hGBL : ComplexFiniteGeometricBrascampLieb) {n : ℕ} {K : ℝ} (hK : 0 < K)
    (W : Submodule ℂ (CoordinateSpace ℂ n)) (D : CoordinateDensityData ℂ n K)
    (y : CoordinateSpace ℂ n) :
    kernelFiberDensity W D.pdf y ≤
      (ENNReal.ofReal K) ^ (n - Module.finrank ℂ W : ℝ) *
        ENNReal.ofReal (Real.exp
          (∑ i : ActiveKernelCoordinate W, projectionEntropy (kernelCoordinateWeight W i))) := by
  have hA0 : ENNReal.ofReal K ≠ 0 := by positivity
  have hAtop : ENNReal.ofReal K ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    kernelFiberDensity W D.pdf y ≤ kernelInterpolationConstant W (ENNReal.ofReal K) *
        ∫⁻ x : CoordinateSpace ℂ (Module.finrank ℂ W), activeBLIntegrand W D.pdf y x :=
      kernelFiberDensity_le_activeBL W hA0 hAtop D.measurable_pdf D.pdf_le y
    _ ≤ kernelInterpolationConstant W (ENNReal.ofReal K) *
        ∏ i : ActiveKernelCoordinate W,
          (∫⁻ z : ℂ, activeShiftedDensity W D.pdf y i z) ^ kernelCoordinateWeight W i := by
      gcongr
      exact complex_activeBL_lintegral_le hGBL W D y
    _ = _ := by
      rw [kernelInterpolationConstant_eq_codimension W hA0 hAtop,
        complex_activeShiftedDensity_integral_product_eq_entropy W D y]

theorem finrank_coordinateSpace
    {𝕜 : Type*} [RCLike 𝕜] (n : ℕ) : Module.finrank 𝕜 (CoordinateSpace 𝕜 n) = n := by
  simp [CoordinateSpace, Module.finrank_pi_fintype]

theorem orthogonal_codimension_eq_finrank
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (E : Submodule 𝕜 (CoordinateSpace 𝕜 n)) :
    (n : ℝ) - Module.finrank 𝕜 (Submodule.orthogonal E) = Module.finrank 𝕜 E := by
  have h := E.finrank_add_finrank_orthogonal
  rw [finrank_coordinateSpace] at h
  have h' : (Module.finrank 𝕜 E : ℝ) +
      Module.finrank 𝕜 (Submodule.orthogonal E) = n := by
    exact_mod_cast h
  linarith

theorem orthogonal_natCodimension_eq_finrank
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (E : Submodule 𝕜 (CoordinateSpace 𝕜 n)) :
    n - Module.finrank 𝕜 (Submodule.orthogonal E) = Module.finrank 𝕜 E := by
  have h := E.finrank_add_finrank_orthogonal
  rw [finrank_coordinateSpace] at h
  omega

/-- Real orthogonal projection fiber bound in dimension `d`. -/
theorem real_orthogonalProjectionFiberDensity_le
    (hGBL : RealFiniteGeometricBrascampLieb) {n d : ℕ} {K : ℝ} (hK : 0 < K)
    (E : Submodule ℝ (CoordinateSpace ℝ n)) (hE : Module.finrank ℝ E = d)
    (D : CoordinateDensityData ℝ n K) (y : E) :
    orthogonalProjectionFiberDensity E D.pdf y ≤
      ENNReal.ofReal (K ^ d * Real.exp ((d : ℝ) / 2)) := by
  let W := Submodule.orthogonal E
  have hcodim : (n : ℝ) - Module.finrank ℝ W = d := by
    rw [orthogonal_codimension_eq_finrank E, hE]
  have hentropy :
      (∑ i : ActiveKernelCoordinate W, projectionEntropy (kernelCoordinateWeight W i)) ≤ d := by
    calc
      (∑ i : ActiveKernelCoordinate W, projectionEntropy (kernelCoordinateWeight W i)) ≤
          (n - Module.finrank ℝ W : ℕ) :=
        sum_projectionEntropy_kernelCoordinateWeight_le_codimension W
      _ = d := by rw [orthogonal_natCodimension_eq_finrank E, hE]
  calc
    orthogonalProjectionFiberDensity E D.pdf y ≤
        (ENNReal.ofReal K) ^ ((n : ℝ) - Module.finrank ℝ W) *
          ENNReal.ofReal (Real.exp
            (1 / 2 * ∑ i : ActiveKernelCoordinate W,
              projectionEntropy (kernelCoordinateWeight W i))) :=
      real_kernelFiberDensity_le_entropy hGBL hK W D y
    _ ≤ (ENNReal.ofReal K) ^ (d : ℝ) *
        ENNReal.ofReal (Real.exp (1 / 2 * d)) := by
      rw [hcodim]
      gcongr
    _ = ENNReal.ofReal (K ^ d * Real.exp ((d : ℝ) / 2)) := by
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow hK.le,
        ← ENNReal.ofReal_mul (pow_nonneg hK.le d)]
      congr 2
      congr 1
      ring

/-- Complex orthogonal projection fiber bound in complex dimension `d`. -/
theorem complex_orthogonalProjectionFiberDensity_le
    (hGBL : ComplexFiniteGeometricBrascampLieb) {n d : ℕ} {K : ℝ} (hK : 0 < K)
    (E : Submodule ℂ (CoordinateSpace ℂ n)) (hE : Module.finrank ℂ E = d)
    (D : CoordinateDensityData ℂ n K) (y : E) :
    orthogonalProjectionFiberDensity E D.pdf y ≤
      ENNReal.ofReal (K ^ d * Real.exp d) := by
  let W := Submodule.orthogonal E
  have hcodim : (n : ℝ) - Module.finrank ℂ W = d := by
    rw [orthogonal_codimension_eq_finrank E, hE]
  have hentropy :
      (∑ i : ActiveKernelCoordinate W, projectionEntropy (kernelCoordinateWeight W i)) ≤ d := by
    calc
      (∑ i : ActiveKernelCoordinate W, projectionEntropy (kernelCoordinateWeight W i)) ≤
          (n - Module.finrank ℂ W : ℕ) :=
        sum_projectionEntropy_kernelCoordinateWeight_le_codimension W
      _ = d := by rw [orthogonal_natCodimension_eq_finrank E, hE]
  calc
    orthogonalProjectionFiberDensity E D.pdf y ≤
        (ENNReal.ofReal K) ^ ((n : ℝ) - Module.finrank ℂ W) *
          ENNReal.ofReal (Real.exp
            (∑ i : ActiveKernelCoordinate W, projectionEntropy (kernelCoordinateWeight W i))) :=
      complex_kernelFiberDensity_le_entropy hGBL hK W D y
    _ ≤ (ENNReal.ofReal K) ^ (d : ℝ) * ENNReal.ofReal (Real.exp d) := by
      rw [hcodim]
      gcongr
    _ = ENNReal.ofReal (K ^ d * Real.exp d) := by
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow hK.le,
        ← ENNReal.ofReal_mul (pow_nonneg hK.le d)]

/-- Concrete real projection-density theorem, conditional only on geometric BL and the exact
orthogonal coarea identity. -/
def real_orthogonalProjection_hasBoundedDensity
    (hGBL : RealFiniteGeometricBrascampLieb) {n d : ℕ} {K : ℝ} (hK : 0 < K)
    (E : Submodule ℝ (CoordinateSpace ℝ n)) (hE : Module.finrank ℝ E = d)
    (D : CoordinateDensityData ℝ n K) (hcoarea : OrthogonalProjectionCoarea E D.pdf) :
    HasBoundedDensity
      (Measure.map E.orthogonalProjectionOnto
        (volume.withDensity (coordinateProductDensity D.pdf)))
      (subspaceVolume E) (K ^ d * Real.exp ((d : ℝ) / 2)) where
  density := orthogonalProjectionFiberDensity E D.pdf
  measurable_density := measurable_orthogonalProjectionFiberDensity E D.measurable_pdf
  map_eq_withDensity := hcoarea
  density_le := real_orthogonalProjectionFiberDensity_le hGBL hK E hE D

/-- Concrete complex projection-density theorem, conditional only on geometric BL and the exact
orthogonal coarea identity. -/
def complex_orthogonalProjection_hasBoundedDensity
    (hGBL : ComplexFiniteGeometricBrascampLieb) {n d : ℕ} {K : ℝ} (hK : 0 < K)
    (E : Submodule ℂ (CoordinateSpace ℂ n)) (hE : Module.finrank ℂ E = d)
    (D : CoordinateDensityData ℂ n K) (hcoarea : OrthogonalProjectionCoarea E D.pdf) :
    HasBoundedDensity
      (Measure.map E.orthogonalProjectionOnto
        (volume.withDensity (coordinateProductDensity D.pdf)))
      (subspaceVolume E) (K ^ d * Real.exp d) where
  density := orthogonalProjectionFiberDensity E D.pdf
  measurable_density := measurable_orthogonalProjectionFiberDensity E D.measurable_pdf
  map_eq_withDensity := hcoarea
  density_le := complex_orthogonalProjectionFiberDensity_le hGBL hK E hE D

def HasBoundedDensity.mono
    {F : Type*} [MeasurableSpace F] {projected reference : Measure F} {M N : ℝ}
    (h : HasBoundedDensity projected reference M) (hMN : M ≤ N) :
    HasBoundedDensity projected reference N where
  density := h.density
  measurable_density := h.measurable_density
  map_eq_withDensity := h.map_eq_withDensity
  density_le y := (h.density_le y).trans (ENNReal.ofReal_le_ofReal hMN)

/-- Real one-dimensional projection, with the common constant `exp 1`. -/
def real_orthogonalProjection_dimOne
    (hGBL : RealFiniteGeometricBrascampLieb) {n : ℕ} {K : ℝ} (hK : 0 < K)
    (E : Submodule ℝ (CoordinateSpace ℝ n)) (hE : Module.finrank ℝ E = 1)
    (D : CoordinateDensityData ℝ n K) (hcoarea : OrthogonalProjectionCoarea E D.pdf) :
    HasBoundedDensity
      (Measure.map E.orthogonalProjectionOnto
        (volume.withDensity (coordinateProductDensity D.pdf)))
      (subspaceVolume E) (Real.exp 1 * K) := by
  refine (real_orthogonalProjection_hasBoundedDensity hGBL hK E hE D hcoarea).mono ?_
  simp only [pow_one]
  have hexp : Real.exp (1 / 2) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr (by norm_num)
  nlinarith [Real.exp_pos (1 / 2)]

/-- Real two-dimensional projection, with the same common constant `exp 1`. -/
def real_orthogonalProjection_dimTwo
    (hGBL : RealFiniteGeometricBrascampLieb) {n : ℕ} {K : ℝ} (hK : 0 < K)
    (E : Submodule ℝ (CoordinateSpace ℝ n)) (hE : Module.finrank ℝ E = 2)
    (D : CoordinateDensityData ℝ n K) (hcoarea : OrthogonalProjectionCoarea E D.pdf) :
    HasBoundedDensity
      (Measure.map E.orthogonalProjectionOnto
        (volume.withDensity (coordinateProductDensity D.pdf)))
      (subspaceVolume E) (Real.exp 1 * K ^ 2) := by
  simpa [mul_comm] using
    (real_orthogonalProjection_hasBoundedDensity hGBL hK E hE D hcoarea)

/-- Complex one-dimensional projection, with the common constant `exp 2`. -/
def complex_orthogonalProjection_dimOne
    (hGBL : ComplexFiniteGeometricBrascampLieb) {n : ℕ} {K : ℝ} (hK : 0 < K)
    (E : Submodule ℂ (CoordinateSpace ℂ n)) (hE : Module.finrank ℂ E = 1)
    (D : CoordinateDensityData ℂ n K) (hcoarea : OrthogonalProjectionCoarea E D.pdf) :
    HasBoundedDensity
      (Measure.map E.orthogonalProjectionOnto
        (volume.withDensity (coordinateProductDensity D.pdf)))
      (subspaceVolume E) (Real.exp 2 * K) := by
  refine (complex_orthogonalProjection_hasBoundedDensity hGBL hK E hE D hcoarea).mono ?_
  simp only [pow_one]
  have hexp : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
  simpa [mul_comm] using mul_le_mul_of_nonneg_right hexp hK.le

/-- Complex two-dimensional projection, with the same common constant `exp 2`. -/
def complex_orthogonalProjection_dimTwo
    (hGBL : ComplexFiniteGeometricBrascampLieb) {n : ℕ} {K : ℝ} (hK : 0 < K)
    (E : Submodule ℂ (CoordinateSpace ℂ n)) (hE : Module.finrank ℂ E = 2)
    (D : CoordinateDensityData ℂ n K) (hcoarea : OrthogonalProjectionCoarea E D.pdf) :
    HasBoundedDensity
      (Measure.map E.orthogonalProjectionOnto
        (volume.withDensity (coordinateProductDensity D.pdf)))
      (subspaceVolume E) (Real.exp 2 * K ^ 2) := by
  simpa [mul_comm] using
    (complex_orthogonalProjection_hasBoundedDensity hGBL hK E hE D hcoarea)

/-- A bounded density controls every measurable event by density bound times reference volume. -/
theorem HasBoundedDensity.measure_le
    {F : Type*} [MeasurableSpace F] {projected reference : Measure F} {M : ℝ}
    (h : HasBoundedDensity projected reference M) {s : Set F} (hs : MeasurableSet s) :
    projected s ≤ ENNReal.ofReal M * reference s := by
  rw [h.map_eq_withDensity, withDensity_apply _ hs]
  calc
    (∫⁻ x in s, h.density x ∂reference) ≤ ∫⁻ _x in s, ENNReal.ofReal M ∂reference :=
      setLIntegral_mono' hs fun x hx ↦ h.density_le x
    _ = ENNReal.ofReal M * reference s := by
      rw [setLIntegral_const]

/-- In particular, a bounded density gives the standard metric-ball small-probability bound. -/
theorem HasBoundedDensity.ball_le
    {F : Type*} [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F]
    {projected reference : Measure F} {M : ℝ}
    (h : HasBoundedDensity projected reference M) (y : F) (r : ℝ) :
    projected (Metric.ball y r) ≤ ENNReal.ofReal M * reference (Metric.ball y r) :=
  h.measure_le Metric.isOpen_ball.measurableSet

/-- By definition of `subspaceVolume`, subspace balls are standard Euclidean balls in orthonormal
coordinates. -/
theorem subspaceVolume_ball
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (E : Submodule 𝕜 (CoordinateSpace 𝕜 n))
    (y : E) (r : ℝ) :
    subspaceVolume E (Metric.ball y r) =
      volume (Metric.ball ((kernelCoordinateBasis E).repr y) r) := by
  unfold subspaceVolume
  rw [Measure.map_apply_of_aemeasurable
    (kernelCoordinateBasis E).repr.symm.continuous.measurable.aemeasurable
    Metric.isOpen_ball.measurableSet,
    LinearIsometryEquiv.preimage_ball]
  rfl

theorem subspaceVolume_ball_real_dimOne
    {n : ℕ} (E : Submodule ℝ (CoordinateSpace ℝ n)) (hE : Module.finrank ℝ E = 1)
    (y : E) (r : ℝ) :
    subspaceVolume E (Metric.ball y r) = ENNReal.ofReal r * ENNReal.ofReal 2 := by
  rw [subspaceVolume_ball]
  have hdim : Module.finrank ℝ (CoordinateSpace ℝ (Module.finrank ℝ E)) = 2 * 0 + 1 := by
    simp [finrank_coordinateSpace, hE]
  rw [InnerProductSpace.volume_ball_of_dim_odd (k := 0) hdim]
  simp [hdim]

theorem subspaceVolume_ball_real_dimTwo
    {n : ℕ} (E : Submodule ℝ (CoordinateSpace ℝ n)) (hE : Module.finrank ℝ E = 2)
    (y : E) (r : ℝ) :
    subspaceVolume E (Metric.ball y r) = ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi := by
  rw [subspaceVolume_ball]
  have hdim : Module.finrank ℝ (CoordinateSpace ℝ (Module.finrank ℝ E)) = 2 * 1 := by
    simp [finrank_coordinateSpace, hE]
  have hpos : 0 < Module.finrank ℝ (CoordinateSpace ℝ (Module.finrank ℝ E)) := by
    omega
  haveI : Nontrivial (CoordinateSpace ℝ (Module.finrank ℝ E)) :=
    Module.nontrivial_of_finrank_pos hpos
  rw [InnerProductSpace.volume_ball_of_dim_even (k := 1) hdim]
  rw [hE]
  norm_num

theorem subspaceVolume_ball_complex_dimOne
    {n : ℕ} (E : Submodule ℂ (CoordinateSpace ℂ n)) (hE : Module.finrank ℂ E = 1)
    (y : E) (r : ℝ) :
    subspaceVolume E (Metric.ball y r) = ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi := by
  rw [subspaceVolume_ball]
  have hdim : Module.finrank ℝ (CoordinateSpace ℂ (Module.finrank ℂ E)) = 2 * 1 := by
    rw [finrank_real_of_complex, finrank_coordinateSpace, hE]
  have hpos : 0 < Module.finrank ℝ (CoordinateSpace ℂ (Module.finrank ℂ E)) := by
    omega
  haveI : Nontrivial (CoordinateSpace ℂ (Module.finrank ℂ E)) :=
    Module.nontrivial_of_finrank_pos hpos
  rw [InnerProductSpace.volume_ball_of_dim_even (k := 1) hdim]
  rw [hdim]
  norm_num

theorem subspaceVolume_ball_complex_dimTwo
    {n : ℕ} (E : Submodule ℂ (CoordinateSpace ℂ n)) (hE : Module.finrank ℂ E = 2)
    (y : E) (r : ℝ) :
    subspaceVolume E (Metric.ball y r) =
      ENNReal.ofReal r ^ 4 * ENNReal.ofReal (Real.pi ^ 2 / 2) := by
  rw [subspaceVolume_ball]
  have hdim : Module.finrank ℝ (CoordinateSpace ℂ (Module.finrank ℂ E)) = 2 * 2 := by
    rw [finrank_real_of_complex, finrank_coordinateSpace, hE]
  have hpos : 0 < Module.finrank ℝ (CoordinateSpace ℂ (Module.finrank ℂ E)) := by
    omega
  haveI : Nontrivial (CoordinateSpace ℂ (Module.finrank ℂ E)) :=
    Module.nontrivial_of_finrank_pos hpos
  rw [InnerProductSpace.volume_ball_of_dim_even (k := 2) hdim]
  rw [hdim]
  norm_num

theorem real_orthogonalProjection_dimOne_ball_le
    (hGBL : RealFiniteGeometricBrascampLieb) {n : ℕ} {K : ℝ} (hK : 0 < K)
    (E : Submodule ℝ (CoordinateSpace ℝ n)) (hE : Module.finrank ℝ E = 1)
    (D : CoordinateDensityData ℝ n K) (hcoarea : OrthogonalProjectionCoarea E D.pdf)
    (y : E) (r : ℝ) :
    Measure.map E.orthogonalProjectionOnto
        (volume.withDensity (coordinateProductDensity D.pdf)) (Metric.ball y r) ≤
      ENNReal.ofReal (Real.exp 1 * K) * (ENNReal.ofReal r * ENNReal.ofReal 2) := by
  simpa only [subspaceVolume_ball_real_dimOne E hE y r] using
    (real_orthogonalProjection_dimOne hGBL hK E hE D hcoarea).ball_le y r

theorem real_orthogonalProjection_dimTwo_ball_le
    (hGBL : RealFiniteGeometricBrascampLieb) {n : ℕ} {K : ℝ} (hK : 0 < K)
    (E : Submodule ℝ (CoordinateSpace ℝ n)) (hE : Module.finrank ℝ E = 2)
    (D : CoordinateDensityData ℝ n K) (hcoarea : OrthogonalProjectionCoarea E D.pdf)
    (y : E) (r : ℝ) :
    Measure.map E.orthogonalProjectionOnto
        (volume.withDensity (coordinateProductDensity D.pdf)) (Metric.ball y r) ≤
      ENNReal.ofReal (Real.exp 1 * K ^ 2) *
        (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) := by
  simpa only [subspaceVolume_ball_real_dimTwo E hE y r] using
    (real_orthogonalProjection_dimTwo hGBL hK E hE D hcoarea).ball_le y r

theorem complex_orthogonalProjection_dimOne_ball_le
    (hGBL : ComplexFiniteGeometricBrascampLieb) {n : ℕ} {K : ℝ} (hK : 0 < K)
    (E : Submodule ℂ (CoordinateSpace ℂ n)) (hE : Module.finrank ℂ E = 1)
    (D : CoordinateDensityData ℂ n K) (hcoarea : OrthogonalProjectionCoarea E D.pdf)
    (y : E) (r : ℝ) :
    Measure.map E.orthogonalProjectionOnto
        (volume.withDensity (coordinateProductDensity D.pdf)) (Metric.ball y r) ≤
      ENNReal.ofReal (Real.exp 2 * K) *
        (ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi) := by
  simpa only [subspaceVolume_ball_complex_dimOne E hE y r] using
    (complex_orthogonalProjection_dimOne hGBL hK E hE D hcoarea).ball_le y r

theorem complex_orthogonalProjection_dimTwo_ball_le
    (hGBL : ComplexFiniteGeometricBrascampLieb) {n : ℕ} {K : ℝ} (hK : 0 < K)
    (E : Submodule ℂ (CoordinateSpace ℂ n)) (hE : Module.finrank ℂ E = 2)
    (D : CoordinateDensityData ℂ n K) (hcoarea : OrthogonalProjectionCoarea E D.pdf)
    (y : E) (r : ℝ) :
    Measure.map E.orthogonalProjectionOnto
        (volume.withDensity (coordinateProductDensity D.pdf)) (Metric.ball y r) ≤
      ENNReal.ofReal (Real.exp 2 * K ^ 2) *
        (ENNReal.ofReal r ^ 4 * ENNReal.ofReal (Real.pi ^ 2 / 2)) := by
  simpa only [subspaceVolume_ball_complex_dimTwo E hE y r] using
    (complex_orthogonalProjection_dimTwo hGBL hK E hE D hcoarea).ball_le y r

end

end LivshytsProjectionFormalization
