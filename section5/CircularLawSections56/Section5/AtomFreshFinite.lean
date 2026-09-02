import CircularLawSections56.Section5.GenericPhysicalCell
import CircularLawSections56.Section5.RealCenteredFreshCell
import CircularLawSections56.Section5.UniformLogarithmicWeights

/-! # Real and complex instances of the literal physical cell estimates -/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section
set_option autoImplicit false

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

theorem LiteralFreshProjectiveControl.mono
    {d : ℕ} {c₀ C₀ a b : ℝ} {profile : PaperIndicatorWeights (d + 1) c₀ C₀}
    {center : Fin (d + 1)} {z : ℂ} {q : ExteriorDegree (d + 1)} {ν : Measure ℂ}
    (h : LiteralFreshProjectiveControl d profile center z q ν a) (hab : a ≤ b) :
    LiteralFreshProjectiveControl d profile center z q ν b :=
  fun B hB v hv => ⟨(h B hB v hv).1, (h B hB v hv).2.trans hab⟩

theorem LiteralFreshProjectiveControl.real
    (d : ℕ) {c₀ C₀ L : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (z : ℂ) (q : ExteriorDegree (d + 1))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hL : 0 ≤ L)
    (hν : RealIntervalBound ν (ENNReal.ofReal L)) :
    LiteralFreshProjectiveControl d profile center z q (realComplexAtomLaw ν)
      (realLiteralProjectiveCellLoss d c₀ L q) :=
  fun B hB v hv => realComplex_literalPaperExteriorCellWithLeft_deficit
    d profile hc₀ center z q B hB v hv ν hL hν

theorem LiteralFreshProjectiveControl.complex
    (d : ℕ) {c₀ C₀ L : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (z : ℂ) (q : ExteriorDegree (d + 1))
    (f : ℂ → ENNReal) [IsProbabilityMeasure (volume.withDensity f)] (hL : 0 ≤ L)
    (hf : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L) :
    LiteralFreshProjectiveControl d profile center z q (volume.withDensity f)
      (complexLiteralProjectiveCellLoss d c₀ L q) :=
  fun B hB v hv => (complex_literalPaperExteriorCellWithLeft_vector_logDeficit
    profile hc₀ center z q B hB v hv f hL hf).2

/-- A finite analytic package, constructed below from either density hypothesis.
It contains no large-size limit, cell telescope, or pressure conclusion. -/
structure AtomTransferControl (ν : Measure ℂ) (J K : ℝ) : Prop where
  logarithmic : AtomLogControl ν K
  fresh_constant_nonneg : 0 ≤ J
  atom_constant_nonneg : 0 ≤ K
  projective : ∀ (d : ℕ) (c₀ C₀ : ℝ) (profile : PaperIndicatorWeights (d + 1) c₀ C₀),
    0 < c₀ → ∀ (center : Fin (d + 1)) (z : ℂ) (q : ExteriorDegree (d + 1)),
      LiteralFreshProjectiveControl d profile center z q ν
        (paperProjectiveCoefficientLogLoss d c₀ q + J * (d + 1 : ℝ) * dimensionLogScale d)

theorem AtomTransferControl.real
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (L : ℝ) (hL : 0 ≤ L)
    (hν : RealIntervalBound ν (ENNReal.ofReal L))
    (hInt : Integrable (fun u : ℝ => u ^ 2) ν) (hSecond : ∫ u : ℝ, u ^ 2 ∂ν ≤ 1) :
    AtomTransferControl (realComplexAtomLaw ν) (realFreshLogConstant L)
      (Real.log (max 1 (2 * L)) + 1) where
  logarithmic := AtomLogControl.real ν L hL hν hInt hSecond
  fresh_constant_nonneg := realFreshLogConstant_nonneg L
  atom_constant_nonneg := by linarith [Real.log_nonneg (le_max_left 1 (2 * L))]
  projective := by
    intro d c₀ C₀ profile hc₀ center z q
    apply (LiteralFreshProjectiveControl.real d profile hc₀ center z q ν hL hν).mono
    have h := add_le_add_left (realFreshNegativeBound_le_uniform d L)
      (paperProjectiveCoefficientLogLoss d c₀ q)
    simpa only [realLiteralProjectiveCellLoss, realFreshNegativeBound,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_comm] using h

theorem AtomTransferControl.complex
    (f : ℂ → ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L)
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (volume.withDensity f))
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂volume.withDensity f ≤ 1) :
    AtomTransferControl (volume.withDensity f) (uniformFreshNegativeConstant L)
      ((Real.log (max 1 (Real.pi * L)) + 1) / 2) where
  logarithmic := AtomLogControl.complex _ L hL (complexBallBound_withDensity hf) hInt hSecond
  fresh_constant_nonneg := by
    unfold uniformFreshNegativeConstant
    linarith [Real.log_nonneg (le_max_left 1 (Real.pi * L))]
  atom_constant_nonneg := by linarith [Real.log_nonneg (le_max_left 1 (Real.pi * L))]
  projective := by
    intro d c₀ C₀ profile hc₀ center z q
    apply (LiteralFreshProjectiveControl.complex d profile hc₀ center z q f hL hf).mono
    have h := add_le_add_left (complexFreshNegativeBound_le_uniform d L)
      (paperProjectiveCoefficientLogLoss d c₀ q)
    simpa only [complexLiteralProjectiveCellLoss, complexFreshNegativeBound,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_comm] using h

theorem literal_fresh_mean_le_of_atom_log
    (d : ℕ) (ν : Measure ℂ) [IsProbabilityMeasure ν]
    {c₀ C₀ K : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (hcenter : center ≠ 0)
    (z : ℂ) (q : ExteriorDegree (d + 1)) (hν : AtomLogControl ν K) :
    (∫ ω, Real.log ‖literalPaperExteriorCell profile center z q ω‖
      ∂literalPaperExteriorCellMeasure d ν) ≤
      (d + 1 : ℝ) * ((3 * ‖z‖ + 3) * dimensionLogScale d) := by
  classical
  let μ := literalPaperExteriorCellMeasure d ν
  let : IsProbabilityMeasure μ := inferInstanceAs
    (IsProbabilityMeasure (Measure.pi (fun _ : FreshAtomIndex (d + 1) => ν)))
  let : Nonempty (ExteriorIndex (d + 1) q) := exteriorIndex_nonempty_bridge _ _
  let cost := fun (t : Fin (d + 1)) (ω : LiteralPaperCellAtoms d) =>
    positiveLog ‖profile.paperIndicatorOpenExteriorRow center z q (literalPaperCellRows ω t)‖
  have hcost : ∀ t, Integrable (cost t) μ ∧ ∫ ω, cost t ω ∂μ ≤
      (3 * ‖z‖ + 3) * dimensionLogScale d := by
    intro t
    apply positiveLog_paperIndicatorOpenExteriorRow_integrable_and_bound
      μ d profile hc₀ center z q (fun ω => literalPaperCellRows ω t)
    · exact measurable_pi_lambda _ (fun k => measurable_pi_apply _)
    · intro ell
      simp only [paperIndicatorOpenRowAtoms_literalPaperCellRows]
      have hmp := measurePreserving_eval (fun _ : FreshAtomIndex (d + 1) => ν) (t, ell)
      exact ⟨hmp.integrable_comp_of_integrable hν.second_integrable,
        (integral_comp_measurePreserving_eq hmp _ hν.second_integrable).trans_le hν.second_le_one⟩
  have hsum : Integrable (fun ω => ∑ t, cost t ω) μ :=
    integrable_finsetSum _ (fun t _ => (hcost t).1)
  have hcell := (literal_fresh_integrable_of_atom_log d profile hc₀ center hcenter z q ν hν).1
  have hdom : ∀ ω, Real.log ‖literalPaperExteriorCell profile center z q ω‖ ≤ ∑ t, cost t ω := by
    intro ω
    have h := log_norm_chronologicalProduct_le_sum_positiveLog
      (List.ofFn (fun t : Fin (d + 1) =>
        profile.paperIndicatorOpenExteriorRow center z q (literalPaperCellRows ω t)))
    simpa only [literalPaperExteriorCell, paperIndicatorOpenExteriorProduct,
      List.map_ofFn, List.sum_ofFn, Function.comp_apply, cost] using h
  calc
    _ ≤ ∫ ω, ∑ t, cost t ω ∂μ := integral_mono_ae hcell hsum (ae_of_all _ hdom)
    _ = ∑ t, ∫ ω, cost t ω ∂μ := integral_finsetSum _ (fun t _ => (hcost t).1)
    _ ≤ ∑ _t : Fin (d + 1), (3 * ‖z‖ + 3) * dimensionLogScale d :=
      Finset.sum_le_sum (fun t _ => (hcost t).2)
    _ = _ := by simp


end CircularLawSections56.Section5
