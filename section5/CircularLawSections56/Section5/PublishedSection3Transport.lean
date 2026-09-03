import CircularLawSections56.Section5.PublishedSection3Source
import CircularLawSections56.Section5.RealSection3Transport

/-! # The two Section 5 anchors from the published Section 3 proof

The remaining transport data are finite model identities and exact sample-law
maps. An inactive branch is filled with the target constant, and finitely many
initial indices can be ignored. No convergence conclusion is a field below.
-/

open MeasureTheory Filter Topology ShortRingAnchor
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CircularLawSections56.Section5

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} {νA νG : Measure ℂ}
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure νA] [IsProbabilityMeasure νG]
variable {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]

/-- A concrete source model, its literature premises, and the finite transport
to one masked Section 5 observable. Planar densities do not require GBL. -/
structure PublishedSection3Anchor (μ : Measure Ω) (νA νG : Measure ℂ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure νA] [IsProbabilityMeasure νG]
    (ν : ∀ n, Measure (Ξ n)) (X : ∀ n, Ξ n → ℝ) (z : ℂ) where
  M : ℕ → ℕ
  W : ℕ → ℕ
  c₀ : ℝ
  C₀ : ℝ
  [dimension_nonempty : ∀ n, Nonempty (Fin (M n))]
  model : PublishedSection3Model μ νA νG M W c₀ C₀
  sources : model.Sources z
  density : Nonempty (HasBoundedDensityWithRespectTo (Measure.map id νA) (volume : Measure ℂ)) ∨
    (AtomDensityAlternative21 νA id ∧
      LivshytsProjectionFormalization.RealFiniteGeometricBrascampLieb)
  sample : ∀ n, Ω → Ξ n
  sample_law : ∀ n, MeasurePreserving (sample n) μ (ν n)
  measurable : ∀ n, Measurable (X n)
  active : ℕ → Bool
  observable_eq : ∀ᶠ n in atTop, ∀ ω,
    X n (sample n ω) =
      if active n then normalizedShiftLogDet (model.matrix n ω) z else circularLogPotential z

theorem PublishedSection3Anchor.limit
    {ν : ∀ n, Measure (Ξ n)} [∀ n, IsProbabilityMeasure (ν n)]
    {X : ∀ n, Ξ n → ℝ} {z : ℂ}
    (h : PublishedSection3Anchor μ νA νG ν X z) :
    TendstoInProbabilityTri ν X (circularLogPotential z) := by
  letI := h.dimension_nonempty
  have hlimit : TendstoInProbabilityTri (fun _ => μ)
      (fun n ω => normalizedShiftLogDet (h.model.matrix n ω) z) (circularLogPotential z) := by
    rcases h.density with ⟨hd⟩ | ⟨hd, hGBL⟩
    · exact PublishedSection3Model.Sources.planar_tri h.model z h.sources hd
    · exact PublishedSection3Model.Sources.density_tri h.model z h.sources hd hGBL
  have hconstant : TendstoInProbabilityTri (fun _ => μ)
      (fun _ _ => circularLogPotential z) (circularLogPotential z) :=
    tendstoInProbabilityTri_const (fun _ => μ) _ _ tendsto_const_nhds
  have hmasked := tendstoInProbabilityTri_branchSelected (fun _ => μ) h.active
    (fun n ω => normalizedShiftLogDet (h.model.matrix n ω) z)
    (fun _ _ => circularLogPotential z) (circularLogPotential z) hlimit hconstant
  have hsource : TendstoInProbabilityTri (fun _ => μ)
      (fun n ω => X n (h.sample n ω)) (circularLogPotential z) := by
    intro ε hε
    apply (hmasked ε hε).congr'
    filter_upwards [h.observable_eq] with n hn
    simp only [hn, branchSelectedTri]
  exact tendstoInProbabilityTri_pushforward_measurePreserving (fun _ => μ) ν
    h.sample h.sample_law X h.measurable _ hsource

/-- Source-facing replacement for the old pair of assumed probability limits.
The two rings can have different dimensions, bands, branch masks and sample maps. -/
def PublishedSection3AnchorsTri (μ : Measure Ω) (νA νG : Measure ℂ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure νA] [IsProbabilityMeasure νG]
    (ν : ∀ n, Measure (Ξ n)) (short calibration : ∀ n, Ξ n → ℝ) (z : ℂ) : Prop :=
  Nonempty (PublishedSection3Anchor μ νA νG ν short z ×
    PublishedSection3Anchor μ νA νG ν calibration z)

theorem PublishedSection3AnchorsTri.toAnchors
    {ν : ∀ n, Measure (Ξ n)} [∀ n, IsProbabilityMeasure (ν n)]
    {short calibration : ∀ n, Ξ n → ℝ} {z : ℂ}
    (h : PublishedSection3AnchorsTri μ νA νG ν short calibration z) :
    Section3IndicatorAnchorsTri ν short calibration (circularLogPotential z) := by
  obtain ⟨hs, hc⟩ := h
  exact ⟨hs.limit, hc.limit⟩

end CircularLawSections56.Section5
