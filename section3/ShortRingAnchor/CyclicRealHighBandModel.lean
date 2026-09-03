import ShortRingAnchor.CyclicPlanarHighBandModel
import ShortRingAnchor.BoundedDensityRepresentative
import Vendor.RealRandomMatrixModel

/-!
# The actual cyclic array has the copied real-density Theorem 3.1 model law

The source atom may live on any probability space and need only be real
almost surely. Independence is required only of the source atom copies,
not of extra coordinates or of the real and imaginary parts separately.
-/

open MeasureTheory ProbabilityTheory HighBandLSV LivshytsProjectionFormalization
open scoped ENNReal
noncomputable section
namespace ShortRingAnchor

/-- Theorem 3.1 model construction from manuscript (2.2) and (3.1), real branch. -/
def cyclicRealBandModel {M W : ℕ} {c0 C0 rho : ℝ}
    (weights : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ M) (hW : 0 < W)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) (hint : ∫⁻ x, f x = 1)
    (hbound : ∀ x, f x ≤ ENNReal.ofReal rho) : RealBandModel M W (c0 / 3) C0 rho where
  sigma := cyclicVarianceCoefficient weights hfit
  sigma_nonneg := (cyclicVarianceProfile weights hfit).coefficient_nonneg
  local_floor := cyclicVarianceCoefficient_local_floor weights hfit hW
  variance_upper := cyclicVarianceCoefficient_upper weights hfit hW
  row_normalization := (cyclicVarianceProfile weights hfit).row_sq_sum
  density := fun _ => ⟨fun _ => f, fun _ => hf, fun _ => hint, fun _ => hbound⟩

/-- Theorem 3.1 real product construction: all weighted matrix entries are independent. -/
theorem realBandModel_entries_independent {N W : ℕ} {c C rho : ℝ}
    (m : RealBandModel N W c C rho) :
    iIndepFun (fun ij : Fin N × Fin N => fun sample => m.matrix sample ij.1 ij.2) m.law := by
  have hraw : iIndepFun (fun ji : Fin N × Fin N =>
      fun sample : RealBandModel.Sample N => sample ji.1 ji.2) m.law := by
    change iIndepFun (fun ji : Fin N × Fin N =>
      fun sample : RealBandModel.Sample N => sample ji.1 ji.2)
      (Measure.pi (fun j => Measure.pi (m.atomLaw j)))
    simpa only [Measure.infinitePi_eq_pi, id] using
      (iIndepFun_uncurry_infinitePi' (X := fun _ _ => id) m.atomLaw
        (fun _ _ => measurable_id))
  have hswap := hraw.precomp (g := Prod.swap) (Equiv.prodComm (Fin N) (Fin N)).injective
  exact hswap.comp (fun ij x => ((m.sigma ij.1 ij.2 * x : ℝ) : ℂ)) (fun _ => by fun_prop)

/-- Assumption 2.1 real branch: replacing an almost surely real atom by its
real-part embedding does not change its law. -/
theorem identDistrib_realPart_embedding
    {OmegaXi : Type*} [MeasurableSpace OmegaXi] {nu : Measure OmegaXi}
    (atom : OmegaXi → ℂ) (hAtom : Measurable atom) (him : ∀ᵐ x ∂nu, (atom x).im = 0) :
    IdentDistrib (fun x => ((atom x).re : ℂ)) atom nu nu := by
  apply IdentDistrib.of_ae_eq (by fun_prop)
  filter_upwards [him] with x hx
  apply Complex.ext
  · simp
  · simpa using hx.symm

/-- Theorem 3.1 real product construction: the scaled entry has the source atom law. -/
theorem realBandModel_entry_law
    {OmegaXi : Type*} [MeasurableSpace OmegaXi] {nu : Measure OmegaXi}
    {N W : ℕ} {c C rho : ℝ} (m : RealBandModel N W c C rho)
    (atom : OmegaXi → ℂ) (hAtom : Measurable atom) (him : ∀ᵐ x ∂nu, (atom x).im = 0)
    (hlaw : ∀ j i, m.atomLaw j i = Measure.map (fun x => (atom x).re) nu) (i j : Fin N) :
    IdentDistrib (fun sample => m.matrix sample i j)
      (fun x => (m.sigma i j : ℂ) * atom x) m.law nu := by
  have hraw : IdentDistrib (fun sample : RealBandModel.Sample N => sample j i)
      (fun x => (atom x).re) m.law nu := by
    refine ⟨(by fun_prop : Measurable (fun sample : RealBandModel.Sample N => sample j i)).aemeasurable,
      (Complex.measurable_re.comp hAtom).aemeasurable, ?_⟩
    calc
      _ = Measure.map (fun x : RealBandModel.AtomColumn N => x i)
          (Measure.map (fun sample : RealBandModel.Sample N => sample j) m.law) := by
        exact (Measure.map_map (μ := m.law) (measurable_pi_apply i) (measurable_pi_apply j)).symm
      _ = m.atomLaw j i := by
        change Measure.map (Function.eval i)
          (Measure.map (Function.eval j) (Measure.pi m.columnLaw)) = m.atomLaw j i
        rw [(measurePreserving_eval m.columnLaw j).map_eq]
        exact (measurePreserving_eval (m.atomLaw j) i).map_eq
      _ = _ := hlaw j i
  have hcomplex := (hraw.comp Complex.measurable_ofReal).trans
    (identDistrib_realPart_embedding atom hAtom him)
  simpa only [RealBandModel.matrix, Complex.ofReal_mul, Function.comp_def] using
    hcomplex.const_mul (m.sigma i j : ℂ)

/-- Manuscript (3.1) to Theorem 3.1: equality of the actual cyclic matrix law
with the published real product model, even when reality holds only almost surely. -/
theorem cyclicRealBandModel_matrix_identDistrib
    {Omega OmegaXi : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {M W : ℕ} {c0 C0 rho : ℝ}
    (weights : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ M) (hW : 0 < W)
    (entry : Omega → Fin M → BandOffset W → ℂ)
    (atom : OmegaXi → ℂ) (hatom : AtomMomentAssumption21 nu atom)
    (hcopies : IndependentAtomCopies21 mu nu atom
      (fun is : Fin M × BandOffset W => fun sample => entry sample is.1 is.2))
    (him : ∀ᵐ x ∂nu, (atom x).im = 0)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) (hint : ∫⁻ x, f x = 1)
    (hbound : ∀ x, f x ≤ ENNReal.ofReal rho)
    (hlaw : volume.withDensity f = Measure.map (fun x => (atom x).re) nu) :
    let m := cyclicRealBandModel weights hfit hW f hf hint hbound
    IdentDistrib (cyclicShortRingRandomMatrix weights hfit entry) m.matrix mu m.law := by
  let m := cyclicRealBandModel weights hfit hW f hf hint hbound
  let v := cyclicV3Model weights hfit entry atom hatom hcopies
  apply identDistrib_matrix_of_independent_entries _ _ v.entry_measurable
    (fun i j => by unfold RealBandModel.matrix; fun_prop) v.entries_independent
    (realBandModel_entries_independent m)
  intro i j
  exact (v.entry_law i j).trans
    (realBandModel_entry_law m atom hatom.measurable him (fun _ _ => hlaw) i j).symm

end ShortRingAnchor
