import ShortRingAnchor.CyclicHighBandProfile
import ShortRingAnchor.CyclicV3Model
import Vendor.RandomMatrixModel
import Mathlib.Probability.Independence.InfinitePi

/-!
# The actual cyclic array has the copied Theorem 3.1 model law

No independent-column law is imposed on the caller. Entry independence
and equality of the atom laws determine the full finite matrix law,
including all deterministic off-band zero entries.
-/

open MeasureTheory ProbabilityTheory HighBandLSV
open scoped ENNReal
noncomputable section
namespace ShortRingAnchor

/-- Theorem 3.1 model construction from manuscript (2.2) and (3.1), planar branch. -/
def cyclicPlanarBandModel {M W : ℕ} {c0 C0 L : ℝ}
    (weights : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ M) (hW : 0 < W)
    (law : Measure ℂ) [IsProbabilityMeasure law]
    (hd : law ≤ ENNReal.ofReal L • (volume : Measure ℂ)) :
    PlanarBandModel M W (c0 / 3) C0 L where
  sigma := cyclicVarianceCoefficient weights hfit
  sigma_nonneg := (cyclicVarianceProfile weights hfit).coefficient_nonneg
  local_floor := cyclicVarianceCoefficient_local_floor weights hfit hW
  upper := cyclicVarianceCoefficient_upper weights hfit hW
  row_normalization := (cyclicVarianceProfile weights hfit).row_sq_sum
  atomLaw := fun _ _ => law
  atom_probability := fun _ _ => inferInstance
  atom_density := fun _ _ => hd

/-- Theorem 3.1 law adapter: independent matrix entries determine the entire matrix law. -/
theorem identDistrib_matrix_of_independent_entries
    {Omega Omega' : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega']
    {mu : Measure Omega} {mu' : Measure Omega'}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure mu'] {N : ℕ}
    (X : Omega → Matrix (Fin N) (Fin N) ℂ)
    (Y : Omega' → Matrix (Fin N) (Fin N) ℂ)
    (hX : ∀ i j, Measurable (fun sample => X sample i j))
    (hY : ∀ i j, Measurable (fun sample => Y sample i j))
    (hiX : iIndepFun (fun ij : Fin N × Fin N => fun sample => X sample ij.1 ij.2) mu)
    (hiY : iIndepFun (fun ij : Fin N × Fin N => fun sample => Y sample ij.1 ij.2) mu')
    (hlaw : ∀ i j, IdentDistrib (fun sample => X sample i j) (fun sample => Y sample i j) mu mu') :
    IdentDistrib X Y mu mu' := by
  have hflat : IdentDistrib
      (fun sample (ij : Fin N × Fin N) => X sample ij.1 ij.2)
      (fun sample (ij : Fin N × Fin N) => Y sample ij.1 ij.2) mu mu' := by
    refine ⟨(measurable_pi_lambda _ (fun ij : Fin N × Fin N => hX ij.1 ij.2)).aemeasurable,
      (measurable_pi_lambda _ (fun ij : Fin N × Fin N => hY ij.1 ij.2)).aemeasurable, ?_⟩
    rw [iIndepFun.map_fun_eq_pi_map (fun ij : Fin N × Fin N => (hX ij.1 ij.2).aemeasurable) hiX,
      iIndepFun.map_fun_eq_pi_map (fun ij : Fin N × Fin N => (hY ij.1 ij.2).aemeasurable) hiY]
    congr 1
    funext ij
    exact (hlaw ij.1 ij.2).map_eq
  let unflatten : (Fin N × Fin N → ℂ) → Matrix (Fin N) (Fin N) ℂ := fun v i j => v (i, j)
  have hu : Measurable unflatten := by
    apply Continuous.measurable
    unfold unflatten
    fun_prop
  exact hflat.comp hu

/-- Theorem 3.1 product construction: all entries, not only columns, are independent. -/
theorem planarBandModel_entries_independent {N W : ℕ} {c C L : ℝ}
    (m : PlanarBandModel N W c C L) :
    iIndepFun (fun ij : Fin N × Fin N => fun sample => m.matrix sample ij.1 ij.2) m.law := by
  let _ : ∀ j i, IsProbabilityMeasure (m.atomLaw j i) := m.atom_probability
  have hraw : iIndepFun (fun ji : Fin N × Fin N =>
      fun sample : MatrixSample N => sample ji.1 ji.2) m.law := by
    change iIndepFun (fun ji : Fin N × Fin N =>
      fun sample : MatrixSample N => sample ji.1 ji.2)
      (Measure.pi (fun j => Measure.pi (m.atomLaw j)))
    simpa only [Measure.infinitePi_eq_pi, id] using
      (iIndepFun_uncurry_infinitePi' (X := fun _ _ => id) m.atomLaw
        (fun _ _ => measurable_id))
  have hswap := hraw.precomp (g := Prod.swap) (Equiv.prodComm (Fin N) (Fin N)).injective
  exact hswap.comp (fun ij x => (m.sigma ij.1 ij.2 : ℂ) * x)
    (fun _ => measurable_const.mul measurable_id)

/-- Theorem 3.1 product construction: the weighted marginal is exactly the scaled source atom. -/
theorem planarBandModel_entry_law
    {OmegaXi : Type*} [MeasurableSpace OmegaXi] {nu : Measure OmegaXi}
    {N W : ℕ} {c C L : ℝ} (m : PlanarBandModel N W c C L)
    (atom : OmegaXi → ℂ) (hAtom : Measurable atom)
    (hlaw : ∀ j i, m.atomLaw j i = Measure.map atom nu) (i j : Fin N) :
    IdentDistrib (fun sample => m.matrix sample i j)
      (fun x => (m.sigma i j : ℂ) * atom x) m.law nu := by
  have hraw : IdentDistrib (fun sample : MatrixSample N => sample j i) atom m.law nu := by
    refine ⟨(by fun_prop : Measurable (fun sample : MatrixSample N => sample j i)).aemeasurable,
      hAtom.aemeasurable, ?_⟩
    calc
      _ = Measure.map (fun x : AtomColumn N => x i)
          (Measure.map (fun sample : MatrixSample N => sample j) m.law) := by
        exact (Measure.map_map (μ := m.law) (measurable_pi_apply i) (measurable_pi_apply j)).symm
      _ = m.atomLaw j i := by rw [m.column_marginal j, m.atom_marginal j i]
      _ = _ := hlaw j i
  exact hraw.comp (u := fun x : ℂ => (m.sigma i j : ℂ) * x) (by fun_prop)

/-- Manuscript (3.1) to Theorem 3.1: full equality of the actual cyclic matrix law
and the published planar product model, with off-band degeneracy included. -/
theorem cyclicPlanarBandModel_matrix_identDistrib
    {Omega OmegaXi : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {M W : ℕ} {c0 C0 L : ℝ}
    (weights : AdmissibleWeights W c0 C0) (hfit : 2 * W + 1 ≤ M) (hW : 0 < W)
    (entry : Omega → Fin M → BandOffset W → ℂ)
    (atom : OmegaXi → ℂ) (hatom : AtomMomentAssumption21 nu atom)
    (hcopies : IndependentAtomCopies21 mu nu atom
      (fun is : Fin M × BandOffset W => fun sample => entry sample is.1 is.2))
    (hd : Measure.map atom nu ≤ ENNReal.ofReal L • (volume : Measure ℂ)) :
    letI : IsProbabilityMeasure (Measure.map atom nu) := Measure.isProbabilityMeasure_map hatom.measurable.aemeasurable
    let m := cyclicPlanarBandModel weights hfit hW (Measure.map atom nu) hd
    IdentDistrib (cyclicShortRingRandomMatrix weights hfit entry) m.matrix mu m.law := by
  letI : IsProbabilityMeasure (Measure.map atom nu) := Measure.isProbabilityMeasure_map hatom.measurable.aemeasurable
  let m := cyclicPlanarBandModel weights hfit hW (Measure.map atom nu) hd
  change IdentDistrib (cyclicShortRingRandomMatrix weights hfit entry) m.matrix mu m.law
  let v := cyclicV3Model weights hfit entry atom hatom hcopies
  apply identDistrib_matrix_of_independent_entries _ _ v.entry_measurable
    (fun i j => by unfold PlanarBandModel.matrix; fun_prop) v.entries_independent
    (planarBandModel_entries_independent m)
  intro i j
  exact (v.entry_law i j).trans
    (planarBandModel_entry_law m atom hatom.measurable (fun _ _ => rfl) i j).symm

end ShortRingAnchor
