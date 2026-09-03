import Vendor.GinibreLSV.Ginibre
import Ginibre.GaussianEntries
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The planar density and standard-Gaussian conventions agree

BC12 model specification. These are ordinary changes between Cartesian
Gaussian coordinates, not Schur coordinates and not spectral hypotheses.
In particular the factor `1 / sqrt 2` in the earlier small-ball development
is retained explicitly.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace ShortRingAnchor.BC12

/-- Coordinate changes preserving volume transport a density by substitution. -/
theorem map_withDensity_equiv_verified
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {μ : Measure E} {ν : Measure F} (e : E ≃ᵐ F) (he : MeasurePreserving e μ ν)
    (f : E → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = ν.withDensity (fun y => f (e.symm y)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map_equiv]
  calc
    _ = ∫⁻ x, f x * g (e x) ∂μ := by
      simpa only [Function.comp_def, Pi.mul_apply] using
        lintegral_withDensity_eq_lintegral_mul μ hf (hg.comp e.measurable)
    _ = ∫⁻ y, f (e.symm y) * g y ∂ν := by
      simpa only [Pi.mul_apply, MeasurableEquiv.symm_apply_apply] using
        he.lintegral_comp_emb e.measurableEmbedding (fun y => f (e.symm y) * g y)
    _ = _ := by
      simpa only [Pi.mul_apply, Function.comp_def] using
        (lintegral_withDensity_eq_lintegral_mul ν (hf.comp e.symm.measurable) hg).symm

/-- Cartesian density of a circular complex Gaussian, with real variance `v`. -/
theorem gaussian_realPair_density {a : ℝ} (ha : 0 < a)
    {v : ℝ≥0} (hv : 0 < v) (hav : 2 * (v : ℝ) = a⁻¹) (x y : ℝ) :
    gaussianPDFReal 0 v x * gaussianPDFReal 0 v y =
      Ginibre.complexGaussianDensity a (Complex.measurableEquivRealProd.symm (x, y)) := by
  have hv' : 0 < (v : ℝ) := hv
  have hc : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ ^ 2 = a / Real.pi := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
    have he : 2 * Real.pi * (v : ℝ) = Real.pi * a⁻¹ := by rw [← hav]; ring
    rw [he, mul_inv_rev, inv_inv]
    rfl
  have hn : ‖Complex.measurableEquivRealProd.symm (x, y)‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two]
  unfold gaussianPDFReal Ginibre.complexGaussianDensity
  simp only [sub_zero]
  rw [mul_mul_mul_comm, ← pow_two, hc, ← Real.exp_add, hn, hav]
  congr 2
  simp only [div_eq_mul_inv, inv_inv]
  ring

/-- BC12 entry law equals a pair of independent real Gaussians. -/
theorem gaussianEntryLaw_eq_realPair {a : ℝ} (ha : 0 < a)
    {v : ℝ≥0} (hv : 0 < v) (hav : 2 * (v : ℝ) = a⁻¹) :
    Ginibre.gaussianEntryLaw a =
      ((gaussianReal 0 v).prod (gaussianReal 0 v)).map Complex.measurableEquivRealProd.symm := by
  rw [gaussianReal_of_var_ne_zero _ hv.ne', prod_withDensity
    (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _)]
  change Ginibre.gaussianEntryLaw a =
    ((volume : Measure (ℝ × ℝ)).withDensity
      (fun z => gaussianPDF 0 v z.1 * gaussianPDF 0 v z.2)).map Complex.measurableEquivRealProd.symm
  rw [map_withDensity_equiv_verified Complex.measurableEquivRealProd.symm
      Complex.volume_preserving_equiv_real_prod.symm _ (by fun_prop)]
  unfold Ginibre.gaussianEntryLaw
  congr 1
  funext z
  have hd := gaussian_realPair_density ha hv hav z.re z.im
  simpa only [gaussianPDF, Complex.measurableEquivRealProd_apply,
    ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    MeasurableEquiv.symm_symm, Complex.measurableEquivRealProd_symm_apply, Complex.eta] using
      congrArg ENNReal.ofReal hd.symm

/-- A standard Gaussian on the real plane is exactly the independent real pair. -/
theorem stdGaussian_complex_eq_realPair :
    stdGaussian ℂ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      Complex.measurableEquivRealProd.symm := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis Complex.orthonormalBasisOneI,
    ← (measurePreserving_piFinTwo (fun _ : Fin 2 => gaussianReal 0 1)).map_eq,
    Measure.map_map Complex.measurableEquivRealProd.symm.measurable
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).measurable]
  congr 1
  funext x
  simp [Fin.sum_univ_two, Complex.coe_orthonormalBasisOneI,
    MeasurableEquiv.piFinTwo_apply, Function.comp_def, Complex.ext_iff,
    Complex.measurableEquivRealProd_symm_apply]

/-- BC12 entry normalization: scaling the standard real-plane Gaussian
by `r`, with `2 r² = 1/a`, gives density `(a/pi) exp(-a |z|²)`. -/
theorem scaled_stdGaussian_complex_eq_entryLaw {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (har : 2 * r ^ 2 = a⁻¹) :
    (stdGaussian ℂ).map (fun z => (r : ℂ) * z) = Ginibre.gaussianEntryLaw a := by
  let v : ℝ≥0 := ⟨r ^ 2, sq_nonneg _⟩
  have hv : 0 < v := sq_pos_of_pos hr
  have hreal : (gaussianReal 0 1).map (fun x => r * x) = gaussianReal 0 v := by
    have he : NNReal.mk (r ^ 2) (sq_nonneg r) * (1 : ℝ≥0) = v := by
      rw [mul_one]
      rfl
    have hh := (gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) r).map_eq
    rw [he, mul_zero] at hh
    simpa only [id_eq] using hh
  rw [gaussianEntryLaw_eq_realPair ha hv har, stdGaussian_complex_eq_realPair,
    Measure.map_map (by fun_prop) Complex.measurableEquivRealProd.symm.measurable,
    ← hreal, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map Complex.measurableEquivRealProd.symm.measurable (by fun_prop)]
  congr 1
  funext p
  apply Complex.ext <;> simp [Function.comp_def, Complex.measurableEquivRealProd_symm_apply]

/-- Independent complex standard Gaussians are the coordinates of the
standard Gaussian on complex Euclidean space, viewed as a real space. -/
theorem stdGaussian_complexColumn_eq_pi (n : ℕ) :
    stdGaussian (GinibreLSV.ComplexColumn n) =
      (Measure.pi (fun _ : Fin n => stdGaussian ℂ)).map (WithLp.toLp 2) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stdGaussian, charFun_pi]
  simp_rw [charFun_stdGaussian, ← Complex.exp_sum]
  congr 1
  simp_rw [← Complex.ofReal_pow]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, ← Finset.sum_div,
    ← Finset.sum_neg_distrib]

end ShortRingAnchor.BC12
