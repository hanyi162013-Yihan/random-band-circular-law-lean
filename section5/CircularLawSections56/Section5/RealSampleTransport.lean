import CircularLawSections56.Section5.RealAtomLogMoments
import CircularLawSections56.Section5.LiteralCircularLaw

/-! # Return the real-atom conclusions to the original real sample space

The finite and countable product pushforwards are proved explicitly. Pullback
of convergence uses outer-measure inequalities and does not assume unproved
measurability of the eigenvalue enumeration.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace CircularLawSections56.Section5

open CircularLawSection4 Section6 TaoVuReplacement ShortRingAnchor

def realSampleComplexify (m : ℕ) (ω : Fin m → ℝ) : Fin m → ℂ := fun j => ω j

theorem realSampleComplexify_measurePreserving (m : ℕ)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    MeasurePreserving (realSampleComplexify m) (iidMeasure ρ m)
      (iidMeasure (realComplexAtomLaw ρ) m) := by
  simp only [iidMeasure_eq_pi]
  exact measurePreserving_pi _ _ (fun _ => realComplexAtomLaw_measurePreserving ρ)

def realSamplesComplexify (m : ℕ → ℕ) (ω : ∀ n, Fin (m n) → ℝ) :
    ∀ n, Fin (m n) → ℂ := fun n => realSampleComplexify (m n) (ω n)

theorem realSamplesComplexify_measurePreserving (m : ℕ → ℕ)
    (ρ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ρ n)] :
    MeasurePreserving (realSamplesComplexify m)
      (Measure.infinitePi (fun n => iidMeasure (ρ n) (m n)))
      (Measure.infinitePi (fun n => iidMeasure (realComplexAtomLaw (ρ n)) (m n))) := by
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ρ n) (m n)) :=
    fun n => iidMeasure_isProbability (ρ n) _
  have hm : ∀ n, Measurable (realSampleComplexify (m n)) :=
    fun n => (realSampleComplexify_measurePreserving (m n) (ρ n)).measurable
  refine ⟨measurable_pi_lambda _ (fun n => (hm n).comp (measurable_pi_apply n)), ?_⟩
  rw [show realSamplesComplexify m =
    (fun ω n => realSampleComplexify (m n) (ω n)) from rfl,
    Measure.infinitePi_map_pi _ hm]
  congr 1
  funext n
  exact (realSampleComplexify_measurePreserving (m n) (ρ n)).map_eq

theorem tendstoInMeasure_pullback_measurePreserving
    {Ω Ξ E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [EDist E]
    {μ : Measure Ω} {ν : Measure Ξ} {f : Ω → Ξ} (hf : MeasurePreserving f μ ν)
    {X : ι → Ξ → E} {a : Ξ → E} {l : Filter ι}
    (h : TendstoInMeasure ν X l a) :
    TendstoInMeasure μ (fun n ω => X n (f ω)) l (fun ω => a (f ω)) := by
  intro ε hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun _ => zero_le) (fun n => hf.measure_preimage_le {x | ε ≤ edist (X n x) (a x)})

theorem tendstoInProbabilityTri_pullback_measurePreserving
    {Ω Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (μ : ∀ n, Measure (Ω n)) (ν : ∀ n, Measure (Ξ n))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (f : ∀ n, Ω n → Ξ n) (hf : ∀ n, MeasurePreserving (f n) (μ n) (ν n))
    (X : ∀ n, Ξ n → ℝ) (a : ℝ) (h : TendstoInProbabilityTri ν X a) :
    TendstoInProbabilityTri μ (fun n ω => X n (f n ω)) a := by
  intro ε hε
  apply squeeze_zero (fun _ => measureReal_nonneg) _ (h ε hε)
  intro n
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    ((hf n).measure_preimage_le {x | ε ≤ |X n x - a|})

/-- Both Section 5 conclusions transfer to the original real atom arrays. -/
theorem real_section5_original_samples
    (d : ℕ → ℕ) (center : ∀ n, Fin (d n + 1)) (b : ∀ n, Fin (d n + 2) → ℂ)
    (ρ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ρ n)]
    (hLog :
      let : ∀ n, IsProbabilityMeasure (iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2))) :=
        fun _n => iidMeasure_isProbability _ _
      ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri
        (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2)))
        (fun n ω => physicalLogPotential (literalIndicatorMatrix n (d n) (center n) (b n) ω) z)
        (circularLogPotential z))
    (hEsd : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      TendstoInMeasure
        (Measure.infinitePi (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2))))
        (fun n ω => realEsdTest (literalIndicatorMatrix n (d n) (center n) (b n) (ω n)) g)
        atTop (fun _ => ∫ w, g w ∂circularMeasure)) :
    (let : ∀ n, IsProbabilityMeasure (iidMeasure (ρ n) ((n + 1) * (d n + 2))) :=
      fun _n => iidMeasure_isProbability _ _
     ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri
      (fun n => iidMeasure (ρ n) ((n + 1) * (d n + 2)))
      (fun n ω => physicalLogPotential (literalIndicatorMatrix n (d n) (center n) (b n)
        (realSampleComplexify _ ω)) z) (circularLogPotential z)) ∧
    (∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      TendstoInMeasure (Measure.infinitePi (fun n => iidMeasure (ρ n) ((n + 1) * (d n + 2))))
        (fun n ω => realEsdTest (literalIndicatorMatrix n (d n) (center n) (b n)
          (realSampleComplexify _ (ω n))) g)
        atTop (fun _ => ∫ w, g w ∂circularMeasure)) := by
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ρ n) ((n + 1) * (d n + 2))) :=
    fun _n => iidMeasure_isProbability _ _
  let : ∀ n, IsProbabilityMeasure (iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2))) :=
    fun _n => iidMeasure_isProbability _ _
  constructor
  · filter_upwards [hLog] with z hz
    exact tendstoInProbabilityTri_pullback_measurePreserving
      (fun n => iidMeasure (ρ n) ((n + 1) * (d n + 2)))
      (fun n => iidMeasure (realComplexAtomLaw (ρ n)) ((n + 1) * (d n + 2)))
      (fun n => realSampleComplexify ((n + 1) * (d n + 2)))
      (fun n => realSampleComplexify_measurePreserving _ (ρ n))
      (fun n ω => physicalLogPotential (literalIndicatorMatrix n (d n) (center n) (b n) ω) z)
      (circularLogPotential z) hz
  · intro g hg hc
    exact tendstoInMeasure_pullback_measurePreserving
      (X := fun n ω => realEsdTest (literalIndicatorMatrix n (d n) (center n) (b n) (ω n)) g)
      (a := fun _ => ∫ w, g w ∂circularMeasure)
      (realSamplesComplexify_measurePreserving (fun n => (n + 1) * (d n + 2)) ρ) (hEsd g hg hc)

end CircularLawSections56.Section5
