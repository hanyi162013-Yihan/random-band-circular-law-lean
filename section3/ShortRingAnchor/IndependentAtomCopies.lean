import ShortRingAnchor.AtomAssumption21
import Vendor.Arxiv2410.V3.RandomModel

/-!
# Actual i.i.d. atom data for manuscript (3.1) and Assumption 2.1

These are ordinary ensemble assumptions, not external theorem interfaces.
The marginal moment packages used earlier are derived from equality of laws.
No independence between different matrix sizes or between the two ensembles
is required.
-/

noncomputable section
namespace ShortRingAnchor
open MeasureTheory ProbabilityTheory

/-- Manuscript (3.1): measurable independent copies of one fixed atom law. -/
structure IndependentAtomCopies21 {Omega OmegaXi I : Type*}
    [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    (mu : Measure Omega) (nu : Measure OmegaXi)
    (atom : OmegaXi → ℂ) (entry : I → Omega → ℂ) : Prop where
  measurable : ∀ i, Measurable (entry i)
  independent : iIndepFun entry mu
  law : ∀ i, IdentDistrib (entry i) atom mu nu

/-- Assumption 2.1: each measurable copy inherits all atom moments from its law. -/
theorem AtomMomentAssumption21.of_identDistrib
    {Omega OmegaXi : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi}
    {entry : Omega → ℂ} {atom : OmegaXi → ℂ}
    (hcopy : IdentDistrib entry atom mu nu) (hentry : Measurable entry)
    (hatom : AtomMomentAssumption21 nu atom) : AtomMomentAssumption21 mu entry where
  stronglyMeasurable := hentry.stronglyMeasurable
  centered := hcopy.integral_eq.trans hatom.centered
  unitSecondMoment := hcopy.norm.pow.integral_eq.trans hatom.unitSecondMoment
  thirdMomentIntegrable := hcopy.norm.pow.integrable_iff.mpr hatom.thirdMomentIntegrable

/-- Assumption 2.1 / (3.13): i.i.d. ring atoms supply the previous moment-only package. -/
theorem ringEntryMomentCopies21_of_independentAtomCopies
    {Omega OmegaXi : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi} {M W : ℕ → ℕ}
    {atom : OmegaXi → ℂ}
    (entry : ∀ n, Omega → Fin (M n) → BandOffset (W n) → ℂ)
    (hatom : AtomMomentAssumption21 nu atom)
    (hcopies : ∀ n, IndependentAtomCopies21 mu nu atom
      (fun is : Fin (M n) × BandOffset (W n) => fun sample => entry n sample is.1 is.2)) :
    RingEntryMomentCopies21 mu entry where
  atom n i s := AtomMomentAssumption21.of_identDistrib
    ((hcopies n).law (i, s)) ((hcopies n).measurable (i, s)) hatom

/-- Assumption 2.1 / (3.13): i.i.d. dense atoms supply the previous moment-only package. -/
theorem denseAtomMomentCopies21_of_independentAtomCopies
    {Omega OmegaXi : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi} {M : ℕ → ℕ}
    {atom : OmegaXi → ℂ}
    (entry : ∀ n, Omega → Fin (M n) → Fin (M n) → ℂ)
    (hatom : AtomMomentAssumption21 nu atom)
    (hcopies : ∀ n, IndependentAtomCopies21 mu nu atom
      (fun ij : Fin (M n) × Fin (M n) => fun sample => entry n sample ij.1 ij.2)) :
    DenseAtomMomentCopies21 mu entry where
  atom n i j := AtomMomentAssumption21.of_identDistrib
    ((hcopies n).law (i, j)) ((hcopies n).measurable (i, j)) hatom

/-- v3 zero coefficients: deterministic zero has the same law on any two probability spaces. -/
theorem identDistrib_zero_probability
    {Omega OmegaXi : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    (mu : Measure Omega) (nu : Measure OmegaXi)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    IdentDistrib (fun _ : Omega => (0 : ℂ)) (fun _ : OmegaXi => (0 : ℂ)) mu nu where
  aemeasurable_fst := measurable_const.aemeasurable
  aemeasurable_snd := measurable_const.aemeasurable
  map_eq := by simp

end ShortRingAnchor
