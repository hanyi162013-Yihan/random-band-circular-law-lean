import ShortRingAnchor.IndependentAtomCopies

/-! # Assumption 2.1: transport bounded-density alternatives along equality of laws -/

noncomputable section
namespace ShortRingAnchor
open MeasureTheory ProbabilityTheory

/-- Assumption 2.1: the real/complex bounded-density alternative is a property of the law.
Consequently a single source-atom density assumption supplies all dense entry densities. -/
theorem AtomDensityAlternative21.of_identDistrib
    {Omega OmegaXi : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi}
    {entry : Omega → ℂ} {atom : OmegaXi → ℂ}
    (hcopy : IdentDistrib entry atom mu nu)
    (hatom : AtomDensityAlternative21 nu atom) : AtomDensityAlternative21 mu entry := by
  cases hatom with
  | real him hd =>
    refine .real (hcopy.symm.ae_snd
      (isClosed_eq Complex.continuous_im continuous_const).measurableSet him) ?_
    have heq := (hcopy.comp Complex.measurable_re).map_eq
    change HasBoundedDensityWithRespectTo (Measure.map (Complex.re ∘ entry) mu) volume
    rw [heq]
    exact hd
  | complex hd =>
    apply AtomDensityAlternative21.complex
    rw [hcopy.map_eq]
    exact hd

end ShortRingAnchor
