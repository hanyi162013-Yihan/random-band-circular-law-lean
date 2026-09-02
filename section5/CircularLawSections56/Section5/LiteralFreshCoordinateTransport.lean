import CircularLawSection4.PaperFreshCoordinateMarginal
import CircularLawSection4.PaperIsolatedFreshMonomial
import CircularLawSections56.Section5.NearEndToEnd

/-!
# Literal transport of the paper's fresh coordinates

This module supplies the concrete probability-space maps needed at the
Section 4/Section 5 boundary.  In addition to the already proved fresh
marginal, it splits the *whole* flat iid sample measurably into the genuine
fresh coordinates and their literal complement.  It also composes the fresh
marginal with the selected/unselected split used by the isolated-monomial
argument, and provides triangular-array `L¹` pullback wrappers for all three
maps.

No independent copy of the random sample is introduced: every coordinate in
the maps below is read from the original flat sample.
-/

open scoped MeasureTheory
open MeasureTheory Set

noncomputable section

namespace CircularLawSection4

universe u

local instance iidMeasureProbabilityFreshTransport
    {K : Type u} [MeasurableSpace K] (nu : Measure K)
    [IsProbabilityMeasure nu] (n : ℕ) :
    IsProbabilityMeasure (iidMeasure nu n) :=
  iidMeasure_isProbability nu n

/-- The flat scalar coordinates outside one genuine paper fresh block. -/
def PaperIndicatorNonfreshCoordinateIndex
    (N d : ℕ) [NeZero N] (start : ZMod N) :=
  {i : Fin (N * (d + 2)) //
    i ∉ Set.range (paperIndicatorFreshCoordinateIndex N d start)}

noncomputable instance paperIndicatorNonfreshCoordinateIndexFintype
    (N d : ℕ) [NeZero N] (start : ZMod N) :
    Fintype (PaperIndicatorNonfreshCoordinateIndex N d start) :=
  Subtype.fintype _

/-- The genuine fresh coordinates together with their complement enumerate
all scalar coordinates of the flat sample. -/
def paperIndicatorFreshNonfreshIndexSumEquiv
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N) :
    FreshAtomIndex (d + 1) ⊕
        PaperIndicatorNonfreshCoordinateIndex N d start ≃
      Fin (N * (d + 2)) :=
  (Equiv.sumCongr
      (Equiv.ofInjective (paperIndicatorFreshCoordinateIndex N d start)
        (paperIndicatorFreshCoordinateIndex_injective N d start hsize))
      (Equiv.refl _)).trans
    (Equiv.sumCompl (fun i : Fin (N * (d + 2)) =>
      i ∈ Set.range (paperIndicatorFreshCoordinateIndex N d start)))

/-- Split a flat sample into `(fresh coordinates, all nonfresh coordinates)`.
This is an actual measurable equivalence, not merely a marginal map. -/
def paperIndicatorFreshNonfreshSplitMeasurableEquiv
    {K : Type u} [MeasurableSpace K]
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N) :
    (Fin (N * (d + 2)) → K) ≃ᵐ
      (FreshAtomIndex (d + 1) → K) ×
        (PaperIndicatorNonfreshCoordinateIndex N d start → K) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (N * (d + 2)) => K)
      (paperIndicatorFreshNonfreshIndexSumEquiv N d start hsize)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : FreshAtomIndex (d + 1) ⊕
        PaperIndicatorNonfreshCoordinateIndex N d start => K))

@[simp]
theorem paperIndicatorFreshNonfreshSplitMeasurableEquiv_fresh
    {K : Type u} [MeasurableSpace K]
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N)
    (omega : Fin (N * (d + 2)) → K) (a : FreshAtomIndex (d + 1)) :
    (paperIndicatorFreshNonfreshSplitMeasurableEquiv
      N d start hsize omega).1 a =
      omega (paperIndicatorFreshCoordinateIndex N d start a) := by
  rfl

@[simp]
theorem paperIndicatorFreshNonfreshSplitMeasurableEquiv_nonfresh
    {K : Type u} [MeasurableSpace K]
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N)
    (omega : Fin (N * (d + 2)) → K)
    (a : PaperIndicatorNonfreshCoordinateIndex N d start) :
    (paperIndicatorFreshNonfreshSplitMeasurableEquiv
      N d start hsize omega).2 a = omega a.1 := by
  rfl

/-- The whole flat iid law becomes the product of the genuine fresh law and
the iid law on every remaining scalar coordinate. -/
theorem paperIndicatorFreshNonfreshSplit_measurePreserving
    {K : Type u} [MeasurableSpace K]
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N)
    (nu : Measure K) [SigmaFinite nu] [IsProbabilityMeasure nu] :
    MeasurePreserving
      (paperIndicatorFreshNonfreshSplitMeasurableEquiv N d start hsize)
      (iidMeasure nu (N * (d + 2)))
      ((Measure.pi (fun _ : FreshAtomIndex (d + 1) => nu)).prod
        (Measure.pi (fun _ :
          PaperIndicatorNonfreshCoordinateIndex N d start => nu))) := by
  have hreindex :=
    (measurePreserving_piCongrLeft
      (fun _ : Fin (N * (d + 2)) => nu)
      (paperIndicatorFreshNonfreshIndexSumEquiv N d start hsize)).symm
  have hsplit := measurePreserving_sumPiEquivProdPi
    (fun _ : FreshAtomIndex (d + 1) ⊕
      PaperIndicatorNonfreshCoordinateIndex N d start => nu)
  rw [iidMeasure_eq_pi]
  simpa only [paperIndicatorFreshNonfreshSplitMeasurableEquiv,
    MeasurableEquiv.coe_trans, Function.comp_def] using hsplit.comp hreindex

/-- The same exact reassembly, in the order `(outside, fresh)` used by the
conditional Section 4 theorems. -/
def paperIndicatorNonfreshFreshSplitMeasurableEquiv
    {K : Type u} [MeasurableSpace K]
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N) :
    (Fin (N * (d + 2)) → K) ≃ᵐ
      (PaperIndicatorNonfreshCoordinateIndex N d start → K) ×
        (FreshAtomIndex (d + 1) → K) :=
  (paperIndicatorFreshNonfreshSplitMeasurableEquiv
    N d start hsize).trans MeasurableEquiv.prodComm

@[simp]
theorem paperIndicatorNonfreshFreshSplitMeasurableEquiv_nonfresh
    {K : Type u} [MeasurableSpace K]
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N)
    (omega : Fin (N * (d + 2)) → K)
    (a : PaperIndicatorNonfreshCoordinateIndex N d start) :
    (paperIndicatorNonfreshFreshSplitMeasurableEquiv
      N d start hsize omega).1 a = omega a.1 := by
  rfl

@[simp]
theorem paperIndicatorNonfreshFreshSplitMeasurableEquiv_fresh
    {K : Type u} [MeasurableSpace K]
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N)
    (omega : Fin (N * (d + 2)) → K) (a : FreshAtomIndex (d + 1)) :
    (paperIndicatorNonfreshFreshSplitMeasurableEquiv
      N d start hsize omega).2 a =
      omega (paperIndicatorFreshCoordinateIndex N d start a) := by
  rfl

theorem paperIndicatorNonfreshFreshSplit_measurePreserving
    {K : Type u} [MeasurableSpace K]
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N)
    (nu : Measure K) [SigmaFinite nu] [IsProbabilityMeasure nu] :
    MeasurePreserving
      (paperIndicatorNonfreshFreshSplitMeasurableEquiv N d start hsize)
      (iidMeasure nu (N * (d + 2)))
      ((Measure.pi (fun _ :
          PaperIndicatorNonfreshCoordinateIndex N d start => nu)).prod
        (Measure.pi (fun _ : FreshAtomIndex (d + 1) => nu))) := by
  exact Measure.measurePreserving_swap.comp
    (paperIndicatorFreshNonfreshSplit_measurePreserving
      N d start hsize nu)

/-- Read the fresh marginal of a flat sample and then split one selected atom
per fresh row from the unselected fresh atoms. -/
def paperIndicatorSelectedFreshSplit
    {K : Type u} [MeasurableSpace K]
    (N d : ℕ) [NeZero N] (start : ZMod N)
    (word : Fin (d + 1) → ResetLabel (d + 1))
    (omega : Fin (N * (d + 2)) → K) :
    (Fin (d + 1) → K) × (UnselectedFreshIndex word → K) :=
  splitFreshAtomMeasurableEquiv word
    (fun a => omega (paperIndicatorFreshCoordinateIndex N d start a))

theorem paperIndicatorSelectedFreshSplit_measurePreserving
    {K : Type u} [MeasurableSpace K]
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N)
    (word : Fin (d + 1) → ResetLabel (d + 1))
    (nu : Measure K) [SigmaFinite nu] [IsProbabilityMeasure nu] :
    MeasurePreserving
      (paperIndicatorSelectedFreshSplit N d start word)
      (iidMeasure nu (N * (d + 2)))
      ((Measure.pi (fun _ : Fin (d + 1) => nu)).prod
        (Measure.pi (fun _ : UnselectedFreshIndex word => nu))) := by
  change MeasurePreserving
    (fun omega => splitFreshAtomMeasurableEquiv word
      (fun a => omega (paperIndicatorFreshCoordinateIndex N d start a)))
    (iidMeasure nu (N * (d + 2)))
    ((Measure.pi (fun _ : Fin (d + 1) => nu)).prod
      (Measure.pi (fun _ : UnselectedFreshIndex word => nu)))
  exact
    (splitFreshAtom_measurePreserving word nu).comp
      (paperIndicatorFreshCoordinates_measurePreserving
        N d start hsize nu)

/-- The fresh component of the exact outside/fresh split is pointwise the
actual atom array read by the paper model. -/
theorem paperIndicatorFreshAtoms_eq_nonfreshFreshSplit_fresh
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N)
    (omega : Fin (N * (d + 2)) → ℂ) :
    paperIndicatorFreshAtoms N d start omega =
      Function.curry (paperIndicatorNonfreshFreshSplitMeasurableEquiv
        N d start hsize omega).2 := by
  rw [paperIndicatorFreshAtoms_eq_coordinateRestriction]
  funext t ell
  exact (paperIndicatorNonfreshFreshSplitMeasurableEquiv_fresh
    N d start hsize omega (t, ell)).symm

/-- Consequently the literal `FreshZ` on a flat paper sample is exactly the
`FreshZ` on the fresh factor of the outside/fresh product space. -/
theorem PaperIndicatorWeights.paperIndicatorFreshZ_eq_comp_nonfreshFreshSplit
    {d : ℕ} {c0 C0 : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (N : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N)
    (center : Fin (d + 1)) (z : ℂ)
    (omega : Fin (N * (d + 2)) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q)
        (ExteriorIndex (d + 1) q) ℂ) :
    profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtoms N d start omega) B =
      profile.paperIndicatorFreshZ center z
        (Function.curry (paperIndicatorNonfreshFreshSplitMeasurableEquiv
          N d start hsize omega).2) B := by
  rw [paperIndicatorFreshAtoms_eq_nonfreshFreshSplit_fresh]

/-- Reassemble one full flat sample from literal nonfresh coordinates and the
fresh marginal of a second full flat sample.  The unused coordinates of the
second sample are deliberately discarded.  This is the concrete map whose
domain is exactly the `Past × FreshFull` shape used by Section 4's joint
closure theorem. -/
def assembleNonfreshWithFreshFull
    {K : Type u} [MeasurableSpace K]
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N) :
    (PaperIndicatorNonfreshCoordinateIndex N d start → K) ×
        (Fin (N * (d + 2)) → K) →
      (Fin (N * (d + 2)) → K) :=
  (paperIndicatorNonfreshFreshSplitMeasurableEquiv
      N d start hsize).symm ∘
    Prod.map id (fun omega a =>
      omega (paperIndicatorFreshCoordinateIndex N d start a))

/-- Splitting an assembled sample recovers the input nonfresh coordinates
and the genuine fresh-coordinate restriction of the `FreshFull` input. -/
@[simp]
theorem paperIndicatorNonfreshFreshSplit_assembleNonfreshWithFreshFull
    {K : Type u} [MeasurableSpace K]
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N)
    (sample :
      (PaperIndicatorNonfreshCoordinateIndex N d start → K) ×
        (Fin (N * (d + 2)) → K)) :
    paperIndicatorNonfreshFreshSplitMeasurableEquiv N d start hsize
        (assembleNonfreshWithFreshFull N d start hsize sample) =
      Prod.map id (fun omega a =>
        omega (paperIndicatorFreshCoordinateIndex N d start a)) sample := by
  exact (paperIndicatorNonfreshFreshSplitMeasurableEquiv
    N d start hsize).apply_symm_apply _

/-- The nonfresh factor of an assembled sample is exactly the supplied
outside sample. -/
@[simp]
theorem paperIndicatorNonfreshFreshSplit_assemble_nonfresh
    {K : Type u} [MeasurableSpace K]
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N)
    (sample :
      (PaperIndicatorNonfreshCoordinateIndex N d start → K) ×
        (Fin (N * (d + 2)) → K)) :
    (paperIndicatorNonfreshFreshSplitMeasurableEquiv N d start hsize
      (assembleNonfreshWithFreshFull N d start hsize sample)).1 = sample.1 := by
  rw [paperIndicatorNonfreshFreshSplit_assembleNonfreshWithFreshFull]
  rfl

/-- Coordinatewise simp form of exact nonfresh recovery. -/
@[simp]
theorem paperIndicatorNonfreshFreshSplit_assemble_nonfresh_apply
    {K : Type u} [MeasurableSpace K]
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N)
    (sample :
      (PaperIndicatorNonfreshCoordinateIndex N d start → K) ×
        (Fin (N * (d + 2)) → K))
    (a : PaperIndicatorNonfreshCoordinateIndex N d start) :
    (paperIndicatorNonfreshFreshSplitMeasurableEquiv N d start hsize
      (assembleNonfreshWithFreshFull N d start hsize sample)).1 a =
      sample.1 a := by
  rw [paperIndicatorNonfreshFreshSplit_assemble_nonfresh]

/-- Reassembling independent nonfresh coordinates with the fresh marginal of
an independent full sample produces exactly one full flat iid sample. -/
theorem assembleNonfreshWithFreshFull_measurePreserving
    {K : Type u} [MeasurableSpace K]
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N)
    (nu : Measure K) [SigmaFinite nu] [IsProbabilityMeasure nu] :
    MeasurePreserving (assembleNonfreshWithFreshFull N d start hsize)
      ((Measure.pi (fun _ :
          PaperIndicatorNonfreshCoordinateIndex N d start => nu)).prod
        (iidMeasure nu (N * (d + 2))))
      (iidMeasure nu (N * (d + 2))) := by
  let muOutside := Measure.pi (fun _ :
    PaperIndicatorNonfreshCoordinateIndex N d start => nu)
  let muFresh := Measure.pi (fun _ : FreshAtomIndex (d + 1) => nu)
  let muFull := iidMeasure nu (N * (d + 2))
  have hmarginal : MeasurePreserving
      (fun omega : Fin (N * (d + 2)) → K => fun a =>
        omega (paperIndicatorFreshCoordinateIndex N d start a))
      muFull muFresh := by
    simpa only [muFull, muFresh] using
      paperIndicatorFreshCoordinates_measurePreserving
        N d start hsize nu
  have hproduct : MeasurePreserving
      (Prod.map id (fun omega : Fin (N * (d + 2)) → K => fun a =>
        omega (paperIndicatorFreshCoordinateIndex N d start a)))
      (muOutside.prod muFull) (muOutside.prod muFresh) :=
    (MeasurePreserving.id muOutside).prod hmarginal
  have hinverse : MeasurePreserving
      (paperIndicatorNonfreshFreshSplitMeasurableEquiv
        N d start hsize).symm
      (muOutside.prod muFresh) muFull := by
    simpa only [muOutside, muFresh, muFull] using
      (paperIndicatorNonfreshFreshSplit_measurePreserving
        N d start hsize nu).symm
          (paperIndicatorNonfreshFreshSplitMeasurableEquiv
            N d start hsize)
  simpa only [assembleNonfreshWithFreshFull] using hinverse.comp hproduct

/-- The fresh atoms in the assembled full sample are exactly the actual
fresh atoms read from the `FreshFull` input. -/
theorem paperIndicatorFreshAtoms_assembleNonfreshWithFreshFull
    (N d : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N)
    (sample :
      (PaperIndicatorNonfreshCoordinateIndex N d start → ℂ) ×
        (Fin (N * (d + 2)) → ℂ)) :
    paperIndicatorFreshAtoms N d start
        (assembleNonfreshWithFreshFull N d start hsize sample) =
      paperIndicatorFreshAtoms N d start sample.2 := by
  have hsplit :
      paperIndicatorNonfreshFreshSplitMeasurableEquiv N d start hsize
          (assembleNonfreshWithFreshFull N d start hsize sample) =
        Prod.map id (fun omega a =>
          omega (paperIndicatorFreshCoordinateIndex N d start a)) sample := by
    simpa only [assembleNonfreshWithFreshFull, Function.comp_apply] using
      (paperIndicatorNonfreshFreshSplitMeasurableEquiv
        N d start hsize).apply_symm_apply
          (Prod.map id (fun omega a =>
            omega (paperIndicatorFreshCoordinateIndex N d start a)) sample)
  rw [paperIndicatorFreshAtoms_eq_coordinateRestriction,
    paperIndicatorFreshAtoms_eq_coordinateRestriction]
  funext t ell
  have hcoord := congrArg (fun p => p.2 (t, ell)) hsplit
  calc
    assembleNonfreshWithFreshFull N d start hsize sample
        (paperIndicatorFreshCoordinateIndex N d start (t, ell)) =
        (Prod.map id (fun omega a =>
          omega (paperIndicatorFreshCoordinateIndex N d start a)) sample).2
          (t, ell) := by
      simpa only [paperIndicatorNonfreshFreshSplitMeasurableEquiv_fresh]
        using hcoord
    _ = sample.2
        (paperIndicatorFreshCoordinateIndex N d start (t, ell)) := rfl

/-- `FreshZ` is therefore unchanged by the concrete `Past × FreshFull`
reassembly map. -/
theorem PaperIndicatorWeights.paperIndicatorFreshZ_assembleNonfreshWithFreshFull
    {d : ℕ} {c0 C0 : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (N : ℕ) [NeZero N] (start : ZMod N) (hsize : d + 1 ≤ N)
    (center : Fin (d + 1)) (z : ℂ)
    (sample :
      (PaperIndicatorNonfreshCoordinateIndex N d start → ℂ) ×
        (Fin (N * (d + 2)) → ℂ))
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q)
        (ExteriorIndex (d + 1) q) ℂ) :
    profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtoms N d start
          (assembleNonfreshWithFreshFull N d start hsize sample)) B =
      profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtoms N d start sample.2) B := by
  rw [paperIndicatorFreshAtoms_assembleNonfreshWithFreshFull]

end CircularLawSection4

namespace CircularLawSections56.Section5

universe u v

open CircularLawSection4

private theorem integral_comp_of_measurePreserving_freshTransport
    {A : Type u} {B : Type v} [MeasurableSpace A] [MeasurableSpace B]
    {mu : Measure A} {nu : Measure B} {e : A → B}
    (he : MeasurePreserving e mu nu) (g : B → ℝ)
    (hg : Integrable g nu) :
    (∫ x, g (e x) ∂mu) = ∫ y, g y ∂nu := by
  have hgMap : AEStronglyMeasurable g (Measure.map e mu) := by
    rw [he.map_eq]
    exact hg.aestronglyMeasurable
  calc
    (∫ x, g (e x) ∂mu) = ∫ y, g y ∂Measure.map e mu :=
      (MeasureTheory.integral_map he.measurable.aemeasurable hgMap).symm
    _ = ∫ y, g y ∂nu := by rw [he.map_eq]

private def pullbackTwoStepL1ApproximationTri
    {Omega : ℕ → Type u} {Omega' : ℕ → Type v}
    [∀ n, MeasurableSpace (Omega n)] [∀ n, MeasurableSpace (Omega' n)]
    {mu : ∀ n, Measure (Omega n)} {mu' : ∀ n, Measure (Omega' n)}
    {observable : ∀ n, Omega n → ℝ} {center : ℕ → ℝ}
    (h : TwoStepL1ApproximationTri mu observable center)
    (e : ∀ n, Omega' n → Omega n)
    (he : ∀ n, MeasurePreserving (e n) (mu' n) (mu n)) :
    TwoStepL1ApproximationTri mu'
      (fun n omega => observable n (e n omega)) center := by
  let pulledIntermediate : ∀ n, Omega' n → ℝ :=
    fun n omega => h.intermediate n (e n omega)
  refine
    { intermediate := pulledIntermediate
      seamError := h.seamError
      fluctuationError := h.fluctuationError
      seamIntegrable := ?_
      seamIntegral_le := ?_
      fluctuationIntegrable := ?_
      fluctuationIntegral_le := ?_
      seamError_tendsto_zero := h.seamError_tendsto_zero
      fluctuationError_tendsto_zero := h.fluctuationError_tendsto_zero }
  · intro n
    simpa only [Function.comp_def, pulledIntermediate] using
      (he n).integrable_comp_of_integrable (h.seamIntegrable n)
  · intro n
    calc
      (∫ omega, |observable n (e n omega) - pulledIntermediate n omega| ∂mu' n) =
          ∫ omega, |observable n omega - h.intermediate n omega| ∂mu n := by
            simpa only [pulledIntermediate] using
              integral_comp_of_measurePreserving_freshTransport (he n)
                (fun omega => |observable n omega - h.intermediate n omega|)
                (h.seamIntegrable n)
      _ ≤ h.seamError n := h.seamIntegral_le n
  · intro n
    simpa only [Function.comp_def, pulledIntermediate] using
      (he n).integrable_comp_of_integrable (h.fluctuationIntegrable n)
  · intro n
    calc
      (∫ omega, |pulledIntermediate n omega - center n| ∂mu' n) =
          ∫ omega, |h.intermediate n omega - center n| ∂mu n := by
            simpa only [pulledIntermediate] using
              integral_comp_of_measurePreserving_freshTransport (he n)
                (fun omega => |h.intermediate n omega - center n|)
                (h.fluctuationIntegrable n)
      _ ≤ h.fluctuationError n := h.fluctuationIntegral_le n

/-- Pull a two-step `L¹` certificate on the genuine fresh-coordinate law
back to the original flat iid paper sample. -/
def TwoStepL1ApproximationTri.compPaperIndicatorFreshCoordinates
    {K : Type u} [MeasurableSpace K]
    (N d : ℕ → ℕ) [∀ n, NeZero (N n)]
    (start : ∀ n, ZMod (N n)) (hsize : ∀ n, d n + 1 ≤ N n)
    (nu : ℕ → Measure K) [∀ n, SigmaFinite (nu n)]
    [∀ n, IsProbabilityMeasure (nu n)]
    {observable : ∀ n, (FreshAtomIndex (d n + 1) → K) → ℝ}
    {center : ℕ → ℝ}
    (h : TwoStepL1ApproximationTri
      (fun n => Measure.pi
        (fun _ : FreshAtomIndex (d n + 1) => nu n)) observable center) :
    TwoStepL1ApproximationTri
      (fun n => iidMeasure (nu n) (N n * (d n + 2)))
      (fun n omega => observable n
        (fun a => omega
          (paperIndicatorFreshCoordinateIndex (N n) (d n) (start n) a)))
      center := by
  refine pullbackTwoStepL1ApproximationTri
    (mu' := fun n => iidMeasure (nu n) (N n * (d n + 2))) h
    (fun n omega a => omega
      (paperIndicatorFreshCoordinateIndex (N n) (d n) (start n) a)) ?_
  intro n
  exact paperIndicatorFreshCoordinates_measurePreserving
    (N n) (d n) (start n) (hsize n) (nu n)

/-- Pull a two-step `L¹` certificate on an exact `(outside, fresh)` product
space back through the literal coordinate reassembly of the flat sample. -/
def TwoStepL1ApproximationTri.compPaperIndicatorNonfreshFreshSplit
    {K : Type u} [MeasurableSpace K]
    (N d : ℕ → ℕ) [∀ n, NeZero (N n)]
    (start : ∀ n, ZMod (N n)) (hsize : ∀ n, d n + 1 ≤ N n)
    (nu : ℕ → Measure K) [∀ n, SigmaFinite (nu n)]
    [∀ n, IsProbabilityMeasure (nu n)]
    {observable : ∀ n,
      (PaperIndicatorNonfreshCoordinateIndex (N n) (d n) (start n) → K) ×
        (FreshAtomIndex (d n + 1) → K) → ℝ}
    {center : ℕ → ℝ}
    (h : TwoStepL1ApproximationTri
      (fun n =>
        (Measure.pi (fun _ : PaperIndicatorNonfreshCoordinateIndex
          (N n) (d n) (start n) => nu n)).prod
        (Measure.pi (fun _ : FreshAtomIndex (d n + 1) => nu n)))
      observable center) :
    TwoStepL1ApproximationTri
      (fun n => iidMeasure (nu n) (N n * (d n + 2)))
      (fun n omega => observable n
        (paperIndicatorNonfreshFreshSplitMeasurableEquiv
          (N n) (d n) (start n) (hsize n) omega)) center := by
  refine pullbackTwoStepL1ApproximationTri
    (mu' := fun n => iidMeasure (nu n) (N n * (d n + 2))) h
    (fun n => paperIndicatorNonfreshFreshSplitMeasurableEquiv
      (N n) (d n) (start n) (hsize n)) ?_
  intro n
  exact paperIndicatorNonfreshFreshSplit_measurePreserving
    (N n) (d n) (start n) (hsize n) (nu n)

/-- Pull a two-step `L¹` certificate on the concrete selected/unselected
fresh product law all the way back to the original flat iid sample. -/
def TwoStepL1ApproximationTri.compPaperIndicatorSelectedFreshSplit
    {K : Type u} [MeasurableSpace K]
    (N d : ℕ → ℕ) [∀ n, NeZero (N n)]
    (start : ∀ n, ZMod (N n)) (hsize : ∀ n, d n + 1 ≤ N n)
    (word : ∀ n, Fin (d n + 1) → ResetLabel (d n + 1))
    (nu : ℕ → Measure K) [∀ n, SigmaFinite (nu n)]
    [∀ n, IsProbabilityMeasure (nu n)]
    {observable : ∀ n,
      (Fin (d n + 1) → K) × (UnselectedFreshIndex (word n) → K) → ℝ}
    {center : ℕ → ℝ}
    (h : TwoStepL1ApproximationTri
      (fun n =>
        (Measure.pi (fun _ : Fin (d n + 1) => nu n)).prod
          (Measure.pi (fun _ : UnselectedFreshIndex (word n) => nu n)))
      observable center) :
    TwoStepL1ApproximationTri
      (fun n => iidMeasure (nu n) (N n * (d n + 2)))
      (fun n omega => observable n
        (paperIndicatorSelectedFreshSplit
          (N n) (d n) (start n) (word n) omega)) center := by
  refine pullbackTwoStepL1ApproximationTri
    (mu' := fun n => iidMeasure (nu n) (N n * (d n + 2))) h
    (fun n => paperIndicatorSelectedFreshSplit
      (N n) (d n) (start n) (word n)) ?_
  intro n
  exact paperIndicatorSelectedFreshSplit_measurePreserving
    (N n) (d n) (start n) (hsize n) (word n) (nu n)

end CircularLawSections56.Section5
