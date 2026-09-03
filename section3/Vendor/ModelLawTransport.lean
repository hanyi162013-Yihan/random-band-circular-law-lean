/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/ModelLawTransport.lean
   Upstream commit d20607307ee57f31d77397b34bdb2910bef30936.
   Local adaptation: import paths prefixed with Vendor. -/
import Vendor.RealModelTheorem
import Vendor.PlanarModelTheorem

/-! Law invariance under independently sampled column representations. -/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace HighBandLSV.ModelLawTransport

theorem independent_product_law
    {Omega I : Type*} {E : I → Type*} [MeasurableSpace Omega] [Fintype I]
    [∀ i, MeasurableSpace (E i)] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (nu : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (nu i)]
    (xi : ∀ i, Omega → E i) (hxi : ∀ i, Measurable (xi i))
    (hind : iIndepFun xi mu) (hmarg : ∀ i, Measure.map (xi i) mu = nu i) :
    Measure.map (fun omega i => xi i omega) mu = Measure.pi nu := by
  simpa only [hmarg] using
    iIndepFun.map_fun_eq_pi_map (fun i => (hxi i).aemeasurable) hind

theorem real_column_joint_law
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    {N W : Nat} {c C rho : Real} (m : RealBandModel N W c C rho)
    (xi : Fin N → Omega → RealBandModel.AtomColumn N) (hxi : ∀ j, Measurable (xi j))
    (hind : iIndepFun xi mu) (hmarg : ∀ j, Measure.map (xi j) mu = m.columnLaw j) :
    Measure.map (fun omega j => xi j omega) mu = m.law := by
  simpa only [RealBandModel.law] using independent_product_law mu m.columnLaw xi hxi hind hmarg

theorem planar_column_joint_law
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    {N W : Nat} {c C L : Real} (m : PlanarBandModel N W c C L)
    (xi : Fin N → Omega → AtomColumn N) (hxi : ∀ j, Measurable (xi j))
    (hind : iIndepFun xi mu) (hmarg : ∀ j, Measure.map (xi j) mu = m.columnLaw j) :
    Measure.map (fun omega j => xi j omega) mu = m.law := by
  simpa only [PlanarBandModel.law] using independent_product_law mu m.columnLaw xi hxi hind hmarg

/-- The distribution of the weighted real matrix does not depend on the
particular probability space carrying the independent raw columns. -/
theorem real_matrix_law
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    {N W : Nat} {c C rho : Real} (m : RealBandModel N W c C rho)
    (xi : Fin N → Omega → RealBandModel.AtomColumn N) (hxi : ∀ j, Measurable (xi j))
    (hind : iIndepFun xi mu) (hmarg : ∀ j, Measure.map (xi j) mu = m.columnLaw j) :
    Measure.map (fun omega => m.matrix (fun j => xi j omega)) mu = Measure.map m.matrix m.law := by
  have hX : Measurable (fun omega j => xi j omega) := measurable_pi_iff.mpr hxi
  have hM : Measurable m.matrix := by
    have hcont : Continuous m.matrix := by unfold RealBandModel.matrix; fun_prop
    exact hcont.measurable
  calc
    _ = Measure.map m.matrix (Measure.map (fun omega j => xi j omega) mu) := by
      simpa only [Function.comp_def] using (Measure.map_map (μ := mu) hM hX).symm
    _ = _ := by rw [real_column_joint_law mu m xi hxi hind hmarg]

theorem planar_matrix_law
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    {N W : Nat} {c C L : Real} (m : PlanarBandModel N W c C L)
    (xi : Fin N → Omega → AtomColumn N) (hxi : ∀ j, Measurable (xi j))
    (hind : iIndepFun xi mu) (hmarg : ∀ j, Measure.map (xi j) mu = m.columnLaw j) :
    Measure.map (fun omega => m.matrix (fun j => xi j omega)) mu = Measure.map m.matrix m.law := by
  have hX : Measurable (fun omega j => xi j omega) := measurable_pi_iff.mpr hxi
  calc
    _ = Measure.map m.matrix (Measure.map (fun omega j => xi j omega) mu) := by
      simpa only [Function.comp_def] using (Measure.map_map (μ := mu) m.measurable_matrix hX).symm
    _ = _ := by rw [planar_column_joint_law mu m xi hxi hind hmarg]

end HighBandLSV.ModelLawTransport

#print axioms HighBandLSV.ModelLawTransport.real_matrix_law
#print axioms HighBandLSV.ModelLawTransport.planar_matrix_law

