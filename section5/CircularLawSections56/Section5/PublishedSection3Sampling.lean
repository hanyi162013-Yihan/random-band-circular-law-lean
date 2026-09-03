import CircularLawSections56.Section5.PublishedSection3Model
import CircularLawSection4.PiRestrictMarginal

/-! # Actual iid samples construct the published Section 3 ensemble data

Independence and equality of atom laws are derived from the finite product
sampling maps. No extra entrywise independence/moment bundle is supplied.
-/

open MeasureTheory ProbabilityTheory ShortRingAnchor
open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace CircularLawSections56.Section5

theorem independentAtomCopies21_of_jointLaw
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω → I → ℂ) (hF : MeasurePreserving F μ (Measure.pi (fun _ : I => ν))) :
    IndependentAtomCopies21 μ ν id (fun i ω => F ω i) := by
  have hc (i : I) : MeasurePreserving (fun ω => F ω i) μ ν :=
    (measurePreserving_eval (fun _ : I => ν) i).comp hF
  refine ⟨fun i => (hc i).measurable, ?_, ?_⟩
  · apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hc i).measurable.aemeasurable)).2
    have hm (i : I) : Measure.map (fun ω => F ω i) μ = ν := (hc i).map_eq
    simpa only [hm] using hF.map_eq
  · intro i
    refine ⟨(hc i).measurable.aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using (hc i).map_eq

def paperSection3Coordinate (k d W : ℕ) (hwidth : d + 2 = 2 * W + 1)
    (is : Fin (k + 1) × BandOffset W) : Fin ((k + 1) * (d + 2)) :=
  paperIndicatorFlatIndex (k + 1) d (ZMod.finEquiv (k + 1) is.1)
    ((finCongr hwidth).symm is.2)

theorem paperSection3Coordinate_injective (k d W : ℕ) (hwidth : d + 2 = 2 * W + 1) :
    Function.Injective (paperSection3Coordinate k d W hwidth) := by
  intro x y h
  have he := congrArg (paperIndicatorIndexEquiv (k + 1) d) h
  simp only [paperSection3Coordinate, paperIndicatorIndexEquiv_flatIndex] at he
  have hi : ZMod.finEquiv (k + 1) x.1 = ZMod.finEquiv (k + 1) y.1 :=
    congrArg (fun p : ZMod (k + 1) × Fin (d + 2) => p.1) he
  have hs : (finCongr hwidth).symm x.2 = (finCongr hwidth).symm y.2 :=
    congrArg (fun p : ZMod (k + 1) × Fin (d + 2) => p.2) he
  apply Prod.ext
  · exact (ZMod.finEquiv (k + 1)).injective hi
  · exact (finCongr hwidth).symm.injective hs

theorem paperSection3Atoms_measurePreserving (k d W : ℕ) (hwidth : d + 2 = 2 * W + 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun ω is => paperSection3Atoms k d W hwidth ω is.1 is.2)
      (iidMeasure ν ((k + 1) * (d + 2)))
      (Measure.pi (fun _ : Fin (k + 1) × BandOffset W => ν)) := by
  rw [iidMeasure_eq_pi]
  exact measurePreserving_pi_restrict_injective (paperSection3Coordinate k d W hwidth)
    (paperSection3Coordinate_injective k d W hwidth) ν

theorem paperSection3Atoms_copies
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ν : Measure ℂ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (k d W : ℕ) (hwidth : d + 2 = 2 * W + 1)
    (samples : Ω → Fin ((k + 1) * (d + 2)) → ℂ)
    (hSamples : MeasurePreserving samples μ (iidMeasure ν ((k + 1) * (d + 2)))) :
    IndependentAtomCopies21 μ ν id
      (fun is : Fin (k + 1) × BandOffset W => fun ω =>
        paperSection3Atoms k d W hwidth (samples ω) is.1 is.2) :=
  independentAtomCopies21_of_jointLaw μ ν _
    ((paperSection3Atoms_measurePreserving k d W hwidth ν).comp hSamples)

def publishedSection3ModelOfSamples
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (νA νG : Measure ℂ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure νA] [IsProbabilityMeasure νG]
    (k d W : ℕ → ℕ) {c₀ C₀ : ℝ}
    (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (hwidth : ∀ n, d n + 2 = 2 * W n + 1) (hfit : ∀ n, 2 * W n + 1 ≤ k n + 1)
    (samples : ∀ n, Ω → Fin ((k n + 1) * (d n + 2)) → ℂ)
    (denseSamples : ∀ n, Ω → Fin (k n + 1) × Fin (k n + 1) → ℂ)
    (hSamples : ∀ n, MeasurePreserving (samples n) μ (iidMeasure νA ((k n + 1) * (d n + 2))))
    (hDense : ∀ n, MeasurePreserving (denseSamples n) μ
      (Measure.pi (fun _ : Fin (k n + 1) × Fin (k n + 1) => νG)))
    (hMomA : AtomMomentAssumption21 νA id) (hMomG : AtomMomentAssumption21 νG id)
    (hDensityG : AtomDensityAlternative21 νG id) :
    PublishedSection3Model μ νA νG (fun n => k n + 1) W c₀ C₀ where
  weights n := paperSection3Weights (profile n) (hwidth n) hc₀
  fit := hfit
  dimension_pos _ := Nat.succ_pos _
  ringEntry n ω := paperSection3Atoms (k n) (d n) (W n) (hwidth n) (samples n ω)
  denseAtom n ω i j := denseSamples n ω (i, j)
  momentsA := hMomA
  momentsG := hMomG
  copiesA n := paperSection3Atoms_copies μ νA (k n) (d n) (W n) (hwidth n) (samples n) (hSamples n)
  copiesG n := independentAtomCopies21_of_jointLaw μ νG (denseSamples n) (hDense n)
  densityG := hDensityG

end CircularLawSections56.Section5
