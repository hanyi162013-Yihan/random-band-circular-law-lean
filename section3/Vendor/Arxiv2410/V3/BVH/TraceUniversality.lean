/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/TraceUniversality.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.BVH.EntryLindeberg
import Vendor.Arxiv2410.V3.BVH.ModelMoments

/-!
# Specialized trace universality behind v3 formula (3.12)

This file combines the deterministic one-entry resolvent calculation with the finite-product
Lindeberg theorem.  Independence is used here to prove, rather than assume, that the joint entry
law is the product of its marginals.  The comparison is stated first with the exact sum of the
actual and Gaussian third absolute moments.
-/

namespace Arxiv2410V3.BVH

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- The marginal law of entry coordinate `k` of a random matrix. -/
def entryCoordinateLaw {Omega : Type*} [MeasurableSpace Omega] {n : ℕ}
    (rho : Measure Omega) (X : Omega → Matrix (Fin n) (Fin n) ℂ)
    (k : Fin (n * n)) : Measure ℂ :=
  rho.map (fun omega ↦ matrixCoordinates (X omega) k)

private theorem measurable_entryCoordinate {Omega : Type*} [MeasurableSpace Omega] {n : ℕ}
    {X : Omega → Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i j, Measurable (fun omega ↦ X omega i j)) (k : Fin (n * n)) :
    Measurable (fun omega ↦ matrixCoordinates (X omega) k) := by
  exact (measurable_pi_apply k).comp (measurable_matrixCoordinates hX)

/-- Independent matrix entries imply that the full coordinate-vector law is the product of
the marginal entry laws. -/
theorem map_matrixCoordinates_eq_pi_entryCoordinateLaw
    {Omega : Type*} [MeasurableSpace Omega] {rho : Measure Omega} {n : ℕ}
    {X : Omega → Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i j, Measurable (fun omega ↦ X omega i j))
    (hind : iIndepFun
      (fun ij : Fin n × Fin n ↦ fun omega ↦ X omega ij.1 ij.2) rho) :
    rho.map (fun omega ↦ matrixCoordinates (X omega)) =
      Measure.pi (entryCoordinateLaw rho X) := by
  let _ : IsProbabilityMeasure rho := hind.isProbabilityMeasure
  have hind' : iIndepFun
      (fun k : Fin (n * n) ↦ fun omega ↦ matrixCoordinates (X omega) k) rho := by
    simpa only [matrixCoordinates] using
      hind.precomp finProdFinEquiv.symm.injective
  change rho.map (fun omega k ↦ matrixCoordinates (X omega) k) =
    Measure.pi (fun k ↦
      rho.map (fun omega ↦ matrixCoordinates (X omega) k))
  exact hind'.map_fun_eq_pi_map
    (fun k ↦ (measurable_entryCoordinate hX k).aemeasurable)

/-- Change of variables from a random matrix to its product-distributed entry coordinates. -/
theorem integral_stieltjesTrace_eq_integral_pi_entryCoordinateLaw
    {Omega : Type*} [MeasurableSpace Omega] {rho : Measure Omega} {n : ℕ}
    {X : Omega → Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i j, Measurable (fun omega ↦ X omega i j))
    (hind : iIndepFun
      (fun ij : Fin n × Fin n ↦ fun omega ↦ X omega ij.1 ij.2) rho)
    (z eta : ℂ) :
    (∫ omega, stieltjesTrace (X omega) z eta ∂rho) =
      ∫ x, stieltjesTrace (matrixOfCoordinates x) z eta
        ∂Measure.pi (entryCoordinateLaw rho X) := by
  let f : (Fin (n * n) → ℂ) → ℂ :=
    fun x ↦ stieltjesTrace (matrixOfCoordinates x) z eta
  have hf : StronglyMeasurable f :=
    stronglyMeasurable_stieltjesTrace_matrixOfCoordinates z eta
  have hmap := map_matrixCoordinates_eq_pi_entryCoordinateLaw hX hind
  calc
    (∫ omega, stieltjesTrace (X omega) z eta ∂rho) =
        ∫ omega, f (matrixCoordinates (X omega)) ∂rho := by
      simp only [f, matrixOfCoordinates_matrixCoordinates]
    _ = ∫ x, f x ∂rho.map (fun omega ↦ matrixCoordinates (X omega)) :=
      (integral_map_of_stronglyMeasurable (measurable_matrixCoordinates hX) hf).symm
    _ = ∫ x, f x ∂Measure.pi (entryCoordinateLaw rho X) := by rw [hmap]

private theorem integrable_cube_entryCoordinateLaw_actual
    {Omega OmegaXi : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {n : ℕ} (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (k : Fin (n * n)) :
    Integrable (fun w : ℂ ↦ ‖w‖ ^ 3)
      (entryCoordinateLaw mu model.matrix k) := by
  unfold entryCoordinateLaw
  rw [integrable_map_measure (by fun_prop)
    (measurable_entryCoordinate model.entry_measurable k).aemeasurable]
  let ij := finProdFinEquiv.symm k
  simpa only [Function.comp_def, matrixCoordinates] using
    integrable_entry_norm_cube model ij.1 ij.2

private theorem integral_entryCoordinateLaw_apply
    {Omega : Type*} [MeasurableSpace Omega] {rho : Measure Omega} {n : ℕ}
    {X : Omega → Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i j, Measurable (fun omega ↦ X omega i j))
    (k : Fin (n * n)) (g : ℂ → ℝ) (hg : StronglyMeasurable g) :
    (∫ w, g w ∂entryCoordinateLaw rho X k) =
      ∫ omega, g (matrixCoordinates (X omega) k) ∂rho := by
  exact integral_map_of_stronglyMeasurable
    (measurable_entryCoordinate hX k) hg

/-- Application-specific BVH/Lindeberg comparison with the exact two-sided cubic budget.

The only extra premise, `hGaussianCube`, is an ordinary integrability side condition.  It is
proved from joint Gaussianity in `GaussianModelMoments.lean`; no comparison estimate is an
input here. -/
theorem norm_expected_stieltjesTrace_sub_gaussian_le_coordinate_cubicBudget
    {Omega OmegaXi OmegaG : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXi] [MeasurableSpace OmegaG]
    {mu : Measure Omega} {nu : Measure OmegaXi} {muG : Measure OmegaG}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure muG]
    {n : ℕ} [NeZero n]
    (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (gaussian : GaussianCompanionModelV3 n Omega OmegaXi OmegaG mu nu muG model)
    (hGaussianCube : ∀ i j,
      Integrable (fun omega ↦ ‖gaussian.matrix omega i j‖ ^ 3) muG)
    (z : ℂ) {eta : ℂ} (heta : 0 < eta.im) :
    ‖(∫ omega, stieltjesTrace (model.matrix omega) z eta ∂mu) -
        ∫ omega, stieltjesTrace (gaussian.matrix omega) z eta ∂muG‖ ≤
      ∑ k : Fin (n * n),
        (1 / ((n : ℝ) * eta.im ^ 4)) *
          ((∫ w, ‖w‖ ^ 3 ∂entryCoordinateLaw mu model.matrix k) +
            ∫ w, ‖w‖ ^ 3 ∂entryCoordinateLaw muG gaussian.matrix k) := by
  let P : Fin (n * n) → Measure ℂ := entryCoordinateLaw mu model.matrix
  let Q : Fin (n * n) → Measure ℂ := entryCoordinateLaw muG gaussian.matrix
  letI hP (k : Fin (n * n)) : IsProbabilityMeasure (P k) := by
    exact Measure.isProbabilityMeasure_map
      (measurable_entryCoordinate model.entry_measurable k).aemeasurable
  letI hQ (k : Fin (n * n)) : IsProbabilityMeasure (Q k) := by
    exact Measure.isProbabilityMeasure_map
      (measurable_entryCoordinate gaussian.entry_measurable k).aemeasurable
  let f : (Fin (n * n) → ℂ) → ℂ :=
    fun x ↦ stieltjesTrace (matrixOfCoordinates x) z eta
  have hf : StronglyMeasurable f :=
    stronglyMeasurable_stieltjesTrace_matrixOfCoordinates z eta
  have hbound : ∀ x, ‖f x‖ ≤ eta.im⁻¹ := by
    intro x
    exact norm_stieltjesTrace_le_inv_im (matrixOfCoordinates x) z heta
  have hcubeP : ∀ k, Integrable (fun w : ℂ ↦ ‖w‖ ^ 3) (P k) := by
    intro k
    exact integrable_cube_entryCoordinateLaw_actual model k
  have hcubeQ : ∀ k, Integrable (fun w : ℂ ↦ ‖w‖ ^ 3) (Q k) := by
    intro k
    dsimp only [Q, entryCoordinateLaw]
    rw [integrable_map_measure (by fun_prop)
      (measurable_entryCoordinate gaussian.entry_measurable k).aemeasurable]
    let ij := finProdFinEquiv.symm k
    simpa only [Function.comp_def, matrixCoordinates] using
      hGaussianCube ij.1 ij.2
  have hexpansion : ∀ k x,
      SecondOrderCubicExpansion
        (fun w ↦ f (Function.update x k w)) (P k) (Q k)
        (fun w ↦ ‖w‖ ^ 3) (1 / ((n : ℝ) * eta.im ^ 4)) := by
    intro k x
    let ij := finProdFinEquiv.symm k
    apply stieltjesTrace_coordinate_secondOrderCubicExpansion
      (P k) (Q k) x k z heta (hcubeP k) (hcubeQ k)
    · calc
        (∫ w, w.re ∂P k) =
            ∫ omega, (model.matrix omega ij.1 ij.2).re ∂mu := by
          simpa only [P, ij, matrixCoordinates] using
            integral_entryCoordinateLaw_apply model.entry_measurable k
              (fun w ↦ w.re) (by fun_prop)
        _ = ∫ omega, (gaussian.matrix omega ij.1 ij.2).re ∂muG :=
          (gaussian.re_mean_match ij.1 ij.2).symm
        _ = ∫ w, w.re ∂Q k := by
          symm
          simpa only [Q, ij, matrixCoordinates] using
            integral_entryCoordinateLaw_apply gaussian.entry_measurable k
              (fun w ↦ w.re) (by fun_prop)
    · calc
        (∫ w, w.im ∂P k) =
            ∫ omega, (model.matrix omega ij.1 ij.2).im ∂mu := by
          simpa only [P, ij, matrixCoordinates] using
            integral_entryCoordinateLaw_apply model.entry_measurable k
              (fun w ↦ w.im) (by fun_prop)
        _ = ∫ omega, (gaussian.matrix omega ij.1 ij.2).im ∂muG :=
          (gaussian.im_mean_match ij.1 ij.2).symm
        _ = ∫ w, w.im ∂Q k := by
          symm
          simpa only [Q, ij, matrixCoordinates] using
            integral_entryCoordinateLaw_apply gaussian.entry_measurable k
              (fun w ↦ w.im) (by fun_prop)
    · calc
        (∫ w, w.re * w.re ∂P k) =
            ∫ omega, (model.matrix omega ij.1 ij.2).re ^ 2 ∂mu := by
          simpa only [P, ij, matrixCoordinates, pow_two] using
            integral_entryCoordinateLaw_apply model.entry_measurable k
              (fun w ↦ w.re * w.re) (by fun_prop)
        _ = ∫ omega, (gaussian.matrix omega ij.1 ij.2).re ^ 2 ∂muG :=
          (gaussian.re_second_match ij.1 ij.2).symm
        _ = ∫ w, w.re * w.re ∂Q k := by
          symm
          simpa only [Q, ij, matrixCoordinates, pow_two] using
            integral_entryCoordinateLaw_apply gaussian.entry_measurable k
              (fun w ↦ w.re * w.re) (by fun_prop)
    · calc
        (∫ w, w.re * w.im ∂P k) =
            ∫ omega, (model.matrix omega ij.1 ij.2).re *
              (model.matrix omega ij.1 ij.2).im ∂mu := by
          simpa only [P, ij, matrixCoordinates] using
            integral_entryCoordinateLaw_apply model.entry_measurable k
              (fun w ↦ w.re * w.im) (by fun_prop)
        _ = ∫ omega, (gaussian.matrix omega ij.1 ij.2).re *
              (gaussian.matrix omega ij.1 ij.2).im ∂muG :=
          (gaussian.re_im_second_match ij.1 ij.2).symm
        _ = ∫ w, w.re * w.im ∂Q k := by
          symm
          simpa only [Q, ij, matrixCoordinates] using
            integral_entryCoordinateLaw_apply gaussian.entry_measurable k
              (fun w ↦ w.re * w.im) (by fun_prop)
    · calc
        (∫ w, w.im * w.im ∂P k) =
            ∫ omega, (model.matrix omega ij.1 ij.2).im ^ 2 ∂mu := by
          simpa only [P, ij, matrixCoordinates, pow_two] using
            integral_entryCoordinateLaw_apply model.entry_measurable k
              (fun w ↦ w.im * w.im) (by fun_prop)
        _ = ∫ omega, (gaussian.matrix omega ij.1 ij.2).im ^ 2 ∂muG :=
          (gaussian.im_second_match ij.1 ij.2).symm
        _ = ∫ w, w.im * w.im ∂Q k := by
          symm
          simpa only [Q, ij, matrixCoordinates, pow_two] using
            integral_entryCoordinateLaw_apply gaussian.entry_measurable k
              (fun w ↦ w.im * w.im) (by fun_prop)
  have hproduct := norm_integral_pi_sub_integral_pi_le_of_secondOrderCubic
    P Q f hf hbound (fun _ w ↦ ‖w‖ ^ 3)
      (fun _ ↦ 1 / ((n : ℝ) * eta.im ^ 4)) hcubeP hcubeQ hexpansion
  have hactual := integral_stieltjesTrace_eq_integral_pi_entryCoordinateLaw
    model.entry_measurable model.entries_independent z eta
  have hgaussian := integral_stieltjesTrace_eq_integral_pi_entryCoordinateLaw
    gaussian.entry_measurable gaussian.entries_independent z eta
  simpa only [P, Q, f, hactual, hgaussian] using hproduct

end

end Arxiv2410V3.BVH

