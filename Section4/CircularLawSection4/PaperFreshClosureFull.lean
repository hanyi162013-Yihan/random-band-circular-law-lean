import CircularLawSection4.PaperFreshClosurePositive
import CircularLawSection4.FreshAtomProductSplit
import CircularLawSection4.PaperFreshCoordinateMarginal

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory Set

noncomputable section

namespace CircularLawSection4

set_option maxHeartbeats 4000000

namespace PaperIndicatorWeights

variable {d : ℕ} {c₀ C₀ : ℝ}

noncomputable def complexFreshNegativeBound (d : ℕ) (L : ℝ) : ℝ :=
  (Real.log (max 1 ((d + 1 : ℝ) * (Real.pi * L))) + 1) /
    ((2 : ℝ) / (d + 1 : ℝ))

theorem complexFreshNegativeBound_nonneg (d : ℕ) (L : ℝ) :
    0 ≤ complexFreshNegativeBound d L := by
  unfold complexFreshNegativeBound
  apply div_nonneg
  · have hlog : 0 ≤ Real.log (max 1 ((d + 1 : ℝ) * (Real.pi * L))) :=
      Real.log_nonneg (le_max_left _ _)
    linarith
  · positivity

/-- The inverse selected/unselected split is exactly replacement of the
selected atom in every row. -/
theorem splitFreshAtom_symm_eq_replacePaperFreshSelectedAtoms
    {k : ℕ} (word : Fin k → ResetLabel k)
    (x : Fin k → ℂ) (y : UnselectedFreshIndex word → ℂ) :
    (fun t ell =>
      (splitFreshAtomMeasurableEquiv word).symm (x, y) (t, ell)) =
      replacePaperFreshSelectedAtoms
        (fun t ell =>
          (splitFreshAtomMeasurableEquiv word).symm
            ((fun _ => 0), y) (t, ell)) word x := by
  funext t ell
  by_cases hell : ell = word t
  · subst ell
    simp
  · rw [replacePaperFreshSelectedAtoms_unselected _ word x t hell]
    let u : UnselectedFreshIndex word := ⟨(t, ell), hell⟩
    have hx := splitFreshAtomMeasurableEquiv_symm_unselected word x y u
    have hzero := splitFreshAtomMeasurableEquiv_symm_unselected
      word (fun _ : Fin k => (0 : ℂ)) y u
    exact hx.trans hzero.symm

/-- Transport zero-set nullity, deficit integrability, and its integral bound
through a measure-preserving map. -/
theorem logDeficit_transport_of_measurePreserving
    {Omega Omega' : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega']
    {mu : Measure Omega} {mu' : Measure Omega'}
    (T : Omega → Omega') (hT : MeasurePreserving T mu mu')
    (coefficient : ℝ) (radius : Omega → ℝ) (radius' : Omega' → ℝ)
    (hradius' : Measurable radius') (hradiusEq : radius = radius' ∘ T)
    {C : ℝ} (hzero : mu' {omega | radius' omega = 0} = 0)
    (hint : Integrable (fun omega => logDeficit coefficient (radius' omega)) mu')
    (hbound : ∫ omega, logDeficit coefficient (radius' omega) ∂mu' ≤ C) :
    mu {omega | radius omega = 0} = 0 ∧
      Integrable (fun omega => logDeficit coefficient (radius omega)) mu ∧
      ∫ omega, logDeficit coefficient (radius omega) ∂mu ≤ C := by
  let Z : Set Omega' := {omega | radius' omega = 0}
  have hZmeas : MeasurableSet Z := by
    exact measurableSet_eq_fun hradius' measurable_const
  have hpreimage : {omega | radius omega = 0} = T ⁻¹' Z := by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Z, hradiusEq,
      Function.comp_apply]
  have hzero' : mu {omega | radius omega = 0} = 0 := by
    calc
      mu {omega | radius omega = 0} = mu (T ⁻¹' Z) := congrArg mu hpreimage
      _ = Measure.map T mu Z := (Measure.map_apply hT.measurable hZmeas).symm
      _ = mu' Z := congrArg (fun m : Measure Omega' => m Z) hT.map_eq
      _ = 0 := hzero
  have hint' :
      Integrable (fun omega => logDeficit coefficient (radius omega)) mu := by
    simpa only [hradiusEq, Function.comp_def] using
      hT.integrable_comp_of_integrable hint
  have hbound' : ∫ omega, logDeficit coefficient (radius omega) ∂mu ≤ C := by
    have hmapMeas : AEStronglyMeasurable
        (fun omega' : Omega' => logDeficit coefficient (radius' omega'))
        (Measure.map T mu) := by
      rw [hT.map_eq]
      exact hint.aestronglyMeasurable
    have hintegralMap := integral_map hT.measurable.aemeasurable hmapMeas
    have hintegral :
        (∫ omega, (fun omega' : Omega' =>
            logDeficit coefficient (radius' omega')) (T omega) ∂mu) =
          ∫ omega', logDeficit coefficient (radius' omega') ∂mu' := by
      rw [hT.map_eq] at hintegralMap
      exact hintegralMap.symm
    calc
      (∫ omega, logDeficit coefficient (radius omega) ∂mu) =
          ∫ omega, (fun omega' =>
            logDeficit coefficient (radius' omega')) (T omega) ∂mu := by
        simp only [hradiusEq, Function.comp_apply]
      _ = ∫ omega', logDeficit coefficient (radius' omega') ∂mu' :=
        hintegral
      _ ≤ C := hbound
  exact ⟨hzero', hint', hbound'⟩

/-- The isolated polynomial, integrated first in its selected coordinates
and then over all frozen atoms, gives the negative logarithmic half for the
complete actual fresh product.  The witness `r,I,J` is selected once from
`B` and is independent of the outer frozen atoms. -/
theorem exists_complex_paperFreshAtomProduct_logDeficit_withDensity
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (z : ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < exteriorFamilyMaxL2OpNorm B)
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        let zeroAtoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ :=
          fun _ _ => 0
        let p₀ := profile.paperIndicatorFreshPolynomial
          center z zeroAtoms B r I J
        let coefficient := ‖MultiAffine.topCoeff p₀‖
        let radius := fun ω : FreshAtomIndex (d + 1) → ℂ =>
          ‖profile.paperIndicatorFreshZ center z
            (fun t ell => ω (t, ell)) B‖
        let μ := Measure.pi
          (fun _ : FreshAtomIndex (d + 1) => volume.withDensity f)
        μ {ω | radius ω = 0} = 0 ∧
          Real.log (exteriorFamilyMaxL2OpNorm B) - Real.log coefficient ≤
            paperIsolatedCoefficientLoss d c₀ ∧
          Integrable (fun ω => logDeficit coefficient (radius ω)) μ ∧
          ∫ ω, logDeficit coefficient (radius ω) ∂μ ≤
            complexFreshNegativeBound d L := by
  classical
  let ν : Measure ℂ := volume.withDensity f
  let zeroAtoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ := fun _ _ => 0
  obtain ⟨r, I, J, _heval₀, hcoefficient⟩ :=
    profile.exists_paperIndicatorFreshZ_isolatedFullMonomial_exp
      hc₀ center z zeroAtoms B
  refine ⟨r, I, J, ?_⟩
  let word : Fin (d + 1) → ResetLabel (d + 1) := arbitrarySupportWord I J
  let p₀ := profile.paperIndicatorFreshPolynomial center z zeroAtoms B r I J
  let coefficient : ℝ := ‖MultiAffine.topCoeff p₀‖
  let radius := fun ω : FreshAtomIndex (d + 1) → ℂ =>
    ‖profile.paperIndicatorFreshZ center z (fun t ell => ω (t, ell)) B‖
  let μ := Measure.pi (fun _ : FreshAtomIndex (d + 1) => ν)
  let μx := Measure.pi (fun _ : Fin (d + 1) => ν)
  let μy := Measure.pi (fun _ : UnselectedFreshIndex word => ν)
  let e := splitFreshAtomMeasurableEquiv (K := ℂ) word
  have hcoeff : exteriorFamilyMaxL2OpNorm B *
      Real.exp (-paperIsolatedCoefficientLoss d c₀) ≤ coefficient := by
    simpa only [coefficient, p₀] using hcoefficient
  have htop : 0 < coefficient :=
    (mul_pos hB (Real.exp_pos _)).trans_le hcoeff
  have hscale : Real.log (exteriorFamilyMaxL2OpNorm B) -
      Real.log coefficient ≤ paperIsolatedCoefficientLoss d c₀ :=
    log_scale_sub_log_coefficient_le_of_exp_loss hB hcoeff
  let baseAtoms := fun y : UnselectedFreshIndex word → ℂ =>
    fun t ell => e.symm ((fun _ => 0), y) (t, ell)
  let p := fun y : UnselectedFreshIndex word → ℂ =>
    profile.paperIndicatorFreshPolynomial center z (baseAtoms y) B r I J
  have hcoeff_y (y : UnselectedFreshIndex word → ℂ) :
      ‖MultiAffine.topCoeff (p y)‖ = coefficient := by
    simp only [p, p₀, coefficient,
      topCoeff_paperIndicatorFreshPolynomial]
  have htop_y (y : UnselectedFreshIndex word → ℂ) :
      0 < ‖MultiAffine.topCoeff (p y)‖ := by
    rw [hcoeff_y y]
    exact htop
  have heval (x : Fin (d + 1) → ℂ)
      (y : UnselectedFreshIndex word → ℂ) :
      MultiAffine.eval (p y) x =
        profile.paperIndicatorFreshZ center z
          (fun t ell => e.symm (x, y) (t, ell)) B := by
    calc
      MultiAffine.eval (p y) x =
          profile.paperIndicatorFreshZ center z
            (replacePaperFreshSelectedAtoms (baseAtoms y)
              (arbitrarySupportWord I J) x) B := by
        exact profile.eval_paperIndicatorFreshPolynomial_eq_freshZ_replaceSelected
          center z (baseAtoms y) B r I J x
      _ = profile.paperIndicatorFreshZ center z
            (fun t ell => e.symm (x, y) (t, ell)) B := by
        apply congrArg (fun atoms =>
          profile.paperIndicatorFreshZ center z atoms B)
        have hreconstruct :=
          splitFreshAtom_symm_eq_replacePaperFreshSelectedAtoms word x y
        simpa only [word, e, baseAtoms] using hreconstruct.symm
  let F : (Fin (d + 1) → ℂ) ×
      (UnselectedFreshIndex word → ℂ) → ℝ := fun xy =>
    logDeficit coefficient
      ‖profile.paperIndicatorFreshZ center z
        (fun t ell => e.symm xy (t, ell)) B‖
  have hradiusMeas : Measurable radius := by
    dsimp only [radius]
    exact measurable_norm_paperIndicatorFreshZ
      (d := d) (c₀ := c₀) (C₀ := C₀) profile center z
      (fun (ω : FreshAtomIndex (d + 1) → ℂ)
        (t : Fin (d + 1)) (ell : ResetLabel (d + 1)) => ω (t, ell))
      (fun (t : Fin (d + 1)) (ell : ResetLabel (d + 1)) =>
        measurable_pi_apply (t, ell)) B
  have hFmeas : Measurable F := by
    exact (measurable_logDeficit coefficient hradiusMeas).comp e.symm.measurable
  have hsectionEq (y : UnselectedFreshIndex word → ℂ) :
      (fun x => F (x, y)) =
        (fun x => positiveLogLoss ‖MultiAffine.topCoeff (p y)‖
          ‖MultiAffine.eval (p y) x‖) := by
    funext x
    rw [← logDeficit_eq_positiveLogLoss]
    dsimp only [F]
    rw [heval x y]
    rw [hcoeff_y y]
  have hnegative (y : UnselectedFreshIndex word → ℂ) :=
    iid_complex_positiveLogLoss_withDensity f hL hf (p y) (htop_y y)
  have hsectionInt (y : UnselectedFreshIndex word → ℂ) :
      Integrable (fun x => F (x, y)) μx := by
    rw [hsectionEq y]
    simpa only [μx, ν, iidMeasure_eq_pi] using (hnegative y).2.2.1
  have hsectionBound (y : UnselectedFreshIndex word → ℂ) :
      ∫ x, F (x, y) ∂μx ≤ complexFreshNegativeBound d L := by
    rw [hsectionEq y]
    simpa only [μx, ν, complexFreshNegativeBound,
      iidMeasure_eq_pi, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      (hnegative y).2.2.2
  letI : IsProbabilityMeasure μx := by
    dsimp only [μx]
    infer_instance
  letI : IsProbabilityMeasure μy := by
    dsimp only [μy]
    infer_instance
  obtain ⟨hFint, hFbound⟩ :=
    integrable_prod_and_integral_le_of_forall_integrable_integral_le
      μx μy F hFmeas (fun xy => logDeficit_nonneg _ _)
      (complexFreshNegativeBound d L)
      (complexFreshNegativeBound_nonneg d L) hsectionInt hsectionBound
  have hmp : MeasurePreserving e μ (μx.prod μy) := by
    simpa only [e, μ, μx, μy, ν] using
      splitFreshAtom_measurePreserving word ν
  have hGint : Integrable (fun ω => logDeficit coefficient (radius ω)) μ := by
    have hcomp := (hmp.integrable_comp_emb e.measurableEmbedding).2 hFint
    simpa only [F, radius, Function.comp_def,
      MeasurableEquiv.symm_apply_apply] using hcomp
  have hGbound : ∫ ω, logDeficit coefficient (radius ω) ∂μ ≤
      complexFreshNegativeBound d L := by
    calc
      (∫ ω, logDeficit coefficient (radius ω) ∂μ) =
          ∫ ω, F (e ω) ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        simp only [F, radius, MeasurableEquiv.symm_apply_apply]
      _ = ∫ xy, F xy ∂(μx.prod μy) := hmp.integral_comp' F
      _ ≤ complexFreshNegativeBound d L := hFbound
  let ZF : Set ((Fin (d + 1) → ℂ) ×
      (UnselectedFreshIndex word → ℂ)) :=
    {xy | radius (e.symm xy) = 0}
  have hZFmeas : MeasurableSet ZF := by
    exact measurableSet_eq_fun
      (hradiusMeas.comp e.symm.measurable) measurable_const
  have hzeroSection (y : UnselectedFreshIndex word → ℂ) :
      μx {x | radius (e.symm (x, y)) = 0} = 0 := by
    have hset : {x | radius (e.symm (x, y)) = 0} =
        {x | ‖MultiAffine.eval (p y) x‖ = 0} := by
      ext x
      simp only [Set.mem_setOf_eq, radius]
      rw [heval x y]
    rw [hset]
    simpa only [μx, ν, iidMeasure_eq_pi] using (hnegative y).1
  have hzeroProd : (μx.prod μy) ZF = 0 := by
    rw [Measure.prod_apply_symm hZFmeas]
    have hsections : (fun y => μx ((fun x => (x, y)) ⁻¹' ZF)) =
        (fun _ => 0) := by
      funext y
      simpa only [ZF, Set.preimage_setOf_eq] using hzeroSection y
    rw [hsections]
    simp
  have hzero : μ {ω | radius ω = 0} = 0 := by
    have hpreimage : {ω | radius ω = 0} = e ⁻¹' ZF := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, ZF,
        MeasurableEquiv.symm_apply_apply]
    calc
      μ {ω | radius ω = 0} = μ (e ⁻¹' ZF) := congrArg μ hpreimage
      _ = Measure.map e μ ZF :=
        (Measure.map_apply e.measurable hZFmeas).symm
      _ = (μx.prod μy) ZF :=
        congrArg (fun m : Measure _ => m ZF) hmp.map_eq
      _ = 0 := hzeroProd
  exact ⟨hzero, hscale, hGint, hGbound⟩

noncomputable def realFreshNegativeBound (d : ℕ) (L : ℝ) : ℝ :=
  (Real.log (max 1 ((d + 1 : ℝ) * (4 * L))) + 1) /
    ((1 : ℝ) / (d + 1 : ℝ))

theorem realFreshNegativeBound_nonneg (d : ℕ) (L : ℝ) :
    0 ≤ realFreshNegativeBound d L := by
  unfold realFreshNegativeBound
  apply div_nonneg
  · have hlog : 0 ≤ Real.log (max 1 ((d + 1 : ℝ) * (4 * L))) :=
      Real.log_nonneg (le_max_left _ _)
    linarith
  · positivity

/-- Real selected coordinates, embedded in `ℂ`, reconstruct the same fresh
atom array after the selected/unselected product split. -/
theorem splitFreshAtom_symm_realCast_eq_replacePaperFreshSelectedAtoms
    {k : ℕ} (word : Fin k → ResetLabel k)
    (x : Fin k → ℝ) (y : UnselectedFreshIndex word → ℝ) :
    (fun t ell =>
      ((splitFreshAtomMeasurableEquiv (K := ℝ) word).symm
        (x, y) (t, ell) : ℂ)) =
      replacePaperFreshSelectedAtoms
        (fun t ell =>
          ((splitFreshAtomMeasurableEquiv (K := ℝ) word).symm
            ((fun _ => 0), y) (t, ell) : ℂ)) word
        (fun t => (x t : ℂ)) := by
  funext t ell
  by_cases hell : ell = word t
  · subst ell
    simp
  · rw [replacePaperFreshSelectedAtoms_unselected _ word _ t hell]
    let u : UnselectedFreshIndex word := ⟨(t, ell), hell⟩
    have hx := splitFreshAtomMeasurableEquiv_symm_unselected word x y u
    have hzero := splitFreshAtomMeasurableEquiv_symm_unselected
      word (fun _ : Fin k => (0 : ℝ)) y u
    exact congrArg ((↑) : ℝ → ℂ) (hx.trans hzero.symm)

/-- Pointwise identification of the actual real flat fresh atoms with the
generic coordinate restriction, followed by the canonical embedding in
`ℂ`. -/
theorem paperIndicatorFreshAtomsOfReal_eq_coordinateRestriction
    (N d : ℕ) [NeZero N] (start : ZMod N)
    (omega : Fin (N * (d + 2)) → ℝ) :
    paperIndicatorFreshAtomsOfReal N d start omega =
      fun t ell =>
        (omega (paperIndicatorFreshCoordinateIndex N d start (t, ell)) : ℂ) := by
  funext t ell
  cases ell with
  | none =>
      rfl
  | some j =>
      simp [paperIndicatorFreshAtomsOfReal,
        paperIndicatorFreshCoordinateIndex, paperFreshLabelSlot,
        paperOperatorAffineLabelEquiv]

/-- Real bounded-density counterpart of the complete fresh-product negative
logarithmic half. -/
theorem exists_real_paperFreshAtomProduct_logDeficit_withDensity
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (z : ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < exteriorFamilyMaxL2OpNorm B)
    (f : ℝ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ x ∂(volume : Measure ℝ), f x ≤ ENNReal.ofReal L) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        let zeroAtoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ :=
          fun _ _ => 0
        let p₀ := profile.paperIndicatorFreshPolynomial
          center z zeroAtoms B r I J
        let coefficient := ‖MultiAffine.topCoeff p₀‖
        let radius := fun ω : FreshAtomIndex (d + 1) → ℝ =>
          ‖profile.paperIndicatorFreshZ center z
            (fun t ell => (ω (t, ell) : ℂ)) B‖
        let μ := Measure.pi
          (fun _ : FreshAtomIndex (d + 1) => volume.withDensity f)
        μ {ω | radius ω = 0} = 0 ∧
          Real.log (exteriorFamilyMaxL2OpNorm B) - Real.log coefficient ≤
            paperIsolatedCoefficientLoss d c₀ ∧
          Integrable (fun ω => logDeficit coefficient (radius ω)) μ ∧
          ∫ ω, logDeficit coefficient (radius ω) ∂μ ≤
            realFreshNegativeBound d L := by
  classical
  let ν : Measure ℝ := volume.withDensity f
  let zeroAtoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ := fun _ _ => 0
  obtain ⟨r, I, J, _heval₀, hcoefficient⟩ :=
    profile.exists_paperIndicatorFreshZ_isolatedFullMonomial_exp
      hc₀ center z zeroAtoms B
  refine ⟨r, I, J, ?_⟩
  let word : Fin (d + 1) → ResetLabel (d + 1) := arbitrarySupportWord I J
  let p₀ := profile.paperIndicatorFreshPolynomial center z zeroAtoms B r I J
  let coefficient : ℝ := ‖MultiAffine.topCoeff p₀‖
  let radius := fun ω : FreshAtomIndex (d + 1) → ℝ =>
    ‖profile.paperIndicatorFreshZ center z
      (fun t ell => (ω (t, ell) : ℂ)) B‖
  let μ := Measure.pi (fun _ : FreshAtomIndex (d + 1) => ν)
  let μx := Measure.pi (fun _ : Fin (d + 1) => ν)
  let μy := Measure.pi (fun _ : UnselectedFreshIndex word => ν)
  let e := splitFreshAtomMeasurableEquiv (K := ℝ) word
  have hcoeff : exteriorFamilyMaxL2OpNorm B *
      Real.exp (-paperIsolatedCoefficientLoss d c₀) ≤ coefficient := by
    simpa only [coefficient, p₀] using hcoefficient
  have htop : 0 < coefficient :=
    (mul_pos hB (Real.exp_pos _)).trans_le hcoeff
  have hscale : Real.log (exteriorFamilyMaxL2OpNorm B) -
      Real.log coefficient ≤ paperIsolatedCoefficientLoss d c₀ :=
    log_scale_sub_log_coefficient_le_of_exp_loss hB hcoeff
  let baseAtoms := fun y : UnselectedFreshIndex word → ℝ =>
    fun t ell => (e.symm ((fun _ => 0), y) (t, ell) : ℂ)
  let p := fun y : UnselectedFreshIndex word → ℝ =>
    profile.paperIndicatorFreshPolynomial center z (baseAtoms y) B r I J
  have hcoeff_y (y : UnselectedFreshIndex word → ℝ) :
      ‖MultiAffine.topCoeff (p y)‖ = coefficient := by
    simp only [p, p₀, coefficient,
      topCoeff_paperIndicatorFreshPolynomial]
  have htop_y (y : UnselectedFreshIndex word → ℝ) :
      0 < ‖MultiAffine.topCoeff (p y)‖ := by
    rw [hcoeff_y y]
    exact htop
  have heval (x : Fin (d + 1) → ℝ)
      (y : UnselectedFreshIndex word → ℝ) :
      realInputEval (p y) x =
        profile.paperIndicatorFreshZ center z
          (fun t ell => (e.symm (x, y) (t, ell) : ℂ)) B := by
    calc
      realInputEval (p y) x = MultiAffine.eval (p y) (fun t => (x t : ℂ)) := rfl
      _ = profile.paperIndicatorFreshZ center z
            (replacePaperFreshSelectedAtoms (baseAtoms y)
              (arbitrarySupportWord I J) (fun t => (x t : ℂ))) B := by
        exact profile.eval_paperIndicatorFreshPolynomial_eq_freshZ_replaceSelected
          center z (baseAtoms y) B r I J (fun t => (x t : ℂ))
      _ = profile.paperIndicatorFreshZ center z
            (fun t ell => (e.symm (x, y) (t, ell) : ℂ)) B := by
        apply congrArg (fun atoms =>
          profile.paperIndicatorFreshZ center z atoms B)
        have hreconstruct :=
          splitFreshAtom_symm_realCast_eq_replacePaperFreshSelectedAtoms
            word x y
        simpa only [word, e, baseAtoms] using hreconstruct.symm
  let F : (Fin (d + 1) → ℝ) ×
      (UnselectedFreshIndex word → ℝ) → ℝ := fun xy =>
    logDeficit coefficient
      ‖profile.paperIndicatorFreshZ center z
        (fun t ell => (e.symm xy (t, ell) : ℂ)) B‖
  have hradiusMeas : Measurable radius := by
    dsimp only [radius]
    exact measurable_norm_paperIndicatorFreshZ
      (d := d) (c₀ := c₀) (C₀ := C₀) profile center z
      (fun (ω : FreshAtomIndex (d + 1) → ℝ)
        (t : Fin (d + 1)) (ell : ResetLabel (d + 1)) => (ω (t, ell) : ℂ))
      (fun (t : Fin (d + 1)) (ell : ResetLabel (d + 1)) =>
        Complex.continuous_ofReal.measurable.comp (measurable_pi_apply (t, ell))) B
  have hFmeas : Measurable F := by
    exact (measurable_logDeficit coefficient hradiusMeas).comp e.symm.measurable
  have hsectionEq (y : UnselectedFreshIndex word → ℝ) :
      (fun x => F (x, y)) =
        (fun x => positiveLogLoss ‖MultiAffine.topCoeff (p y)‖
          ‖realInputEval (p y) x‖) := by
    funext x
    rw [← logDeficit_eq_positiveLogLoss]
    dsimp only [F]
    rw [heval x y]
    rw [hcoeff_y y]
  have hnegative (y : UnselectedFreshIndex word → ℝ) :=
    iid_realInput_complex_positiveLogLoss_withDensity f hL hf (p y) (htop_y y)
  have hsectionInt (y : UnselectedFreshIndex word → ℝ) :
      Integrable (fun x => F (x, y)) μx := by
    rw [hsectionEq y]
    simpa only [μx, ν, iidMeasure_eq_pi] using (hnegative y).2.2.1
  have hsectionBound (y : UnselectedFreshIndex word → ℝ) :
      ∫ x, F (x, y) ∂μx ≤ realFreshNegativeBound d L := by
    rw [hsectionEq y]
    simpa only [μx, ν, realFreshNegativeBound, iidMeasure_eq_pi,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using (hnegative y).2.2.2
  letI : IsProbabilityMeasure μx := by
    dsimp only [μx]
    infer_instance
  letI : IsProbabilityMeasure μy := by
    dsimp only [μy]
    infer_instance
  obtain ⟨hFint, hFbound⟩ :=
    integrable_prod_and_integral_le_of_forall_integrable_integral_le
      μx μy F hFmeas (fun xy => logDeficit_nonneg _ _)
      (realFreshNegativeBound d L)
      (realFreshNegativeBound_nonneg d L) hsectionInt hsectionBound
  have hmp : MeasurePreserving e μ (μx.prod μy) := by
    simpa only [e, μ, μx, μy, ν] using
      splitFreshAtom_measurePreserving word ν
  have hGint : Integrable (fun ω => logDeficit coefficient (radius ω)) μ := by
    have hcomp := (hmp.integrable_comp_emb e.measurableEmbedding).2 hFint
    simpa only [F, radius, Function.comp_def,
      MeasurableEquiv.symm_apply_apply] using hcomp
  have hGbound : ∫ ω, logDeficit coefficient (radius ω) ∂μ ≤
      realFreshNegativeBound d L := by
    calc
      (∫ ω, logDeficit coefficient (radius ω) ∂μ) =
          ∫ ω, F (e ω) ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        simp only [F, radius, MeasurableEquiv.symm_apply_apply]
      _ = ∫ xy, F xy ∂(μx.prod μy) := hmp.integral_comp' F
      _ ≤ realFreshNegativeBound d L := hFbound
  let ZF : Set ((Fin (d + 1) → ℝ) ×
      (UnselectedFreshIndex word → ℝ)) :=
    {xy | radius (e.symm xy) = 0}
  have hZFmeas : MeasurableSet ZF := by
    exact measurableSet_eq_fun
      (hradiusMeas.comp e.symm.measurable) measurable_const
  have hzeroSection (y : UnselectedFreshIndex word → ℝ) :
      μx {x | radius (e.symm (x, y)) = 0} = 0 := by
    have hset : {x | radius (e.symm (x, y)) = 0} =
        {x | ‖realInputEval (p y) x‖ = 0} := by
      ext x
      simp only [Set.mem_setOf_eq, radius]
      rw [heval x y]
    rw [hset]
    simpa only [μx, ν, iidMeasure_eq_pi] using (hnegative y).1
  have hzeroProd : (μx.prod μy) ZF = 0 := by
    rw [Measure.prod_apply_symm hZFmeas]
    have hsections : (fun y => μx ((fun x => (x, y)) ⁻¹' ZF)) =
        (fun _ => 0) := by
      funext y
      simpa only [ZF, Set.preimage_setOf_eq] using hzeroSection y
    rw [hsections]
    simp
  have hzero : μ {ω | radius ω = 0} = 0 := by
    have hpreimage : {ω | radius ω = 0} = e ⁻¹' ZF := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, ZF,
        MeasurableEquiv.symm_apply_apply]
    calc
      μ {ω | radius ω = 0} = μ (e ⁻¹' ZF) := congrArg μ hpreimage
      _ = Measure.map e μ ZF :=
        (Measure.map_apply e.measurable hZFmeas).symm
      _ = (μx.prod μy) ZF :=
        congrArg (fun m : Measure _ => m ZF) hmp.map_eq
      _ = 0 := hzeroProd
  exact ⟨hzero, hscale, hGint, hGbound⟩

/-- The negative logarithmic half transported all the way to the actual
complex flat sample. -/
theorem exists_complex_paperIndicatorFlatFreshZ_logDeficit_withDensity
    (N d : ℕ) [NeZero N] (hsize : d + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (z : ℂ) (start : ZMod N)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < exteriorFamilyMaxL2OpNorm B)
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        let zeroAtoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ :=
          fun _ _ => 0
        let p₀ := profile.paperIndicatorFreshPolynomial
          center z zeroAtoms B r I J
        let coefficient := ‖MultiAffine.topCoeff p₀‖
        let radius := fun omega : Fin (N * (d + 2)) → ℂ =>
          ‖profile.paperIndicatorFreshZ center z
            (paperIndicatorFreshAtoms N d start omega) B‖
        let mu := paperIndicatorSampleMeasure N d (volume.withDensity f)
        mu {omega | radius omega = 0} = 0 ∧
          Real.log (exteriorFamilyMaxL2OpNorm B) - Real.log coefficient ≤
            paperIsolatedCoefficientLoss d c₀ ∧
          Integrable (fun omega => logDeficit coefficient (radius omega)) mu ∧
          ∫ omega, logDeficit coefficient (radius omega) ∂mu ≤
            complexFreshNegativeBound d L := by
  classical
  let nu : Measure ℂ := volume.withDensity f
  obtain ⟨r, I, J, hzeroFull, hscale, hintFull, hboundFull⟩ :=
    profile.exists_complex_paperFreshAtomProduct_logDeficit_withDensity
      hc₀ center z B hB f hL hf
  refine ⟨r, I, J, ?_⟩
  let zeroAtoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ := fun _ _ => 0
  let p₀ := profile.paperIndicatorFreshPolynomial center z zeroAtoms B r I J
  let coefficient : ℝ := ‖MultiAffine.topCoeff p₀‖
  let radiusFull := fun omega : FreshAtomIndex (d + 1) → ℂ =>
    ‖profile.paperIndicatorFreshZ center z (fun t ell => omega (t, ell)) B‖
  let radiusFlat := fun omega : Fin (N * (d + 2)) → ℂ =>
    ‖profile.paperIndicatorFreshZ center z
      (paperIndicatorFreshAtoms N d start omega) B‖
  let muFull := Measure.pi (fun _ : FreshAtomIndex (d + 1) => nu)
  let muFlat := paperIndicatorSampleMeasure N d nu
  let T := fun omega : Fin (N * (d + 2)) → ℂ =>
    fun u => omega (paperIndicatorFreshCoordinateIndex N d start u)
  have hT : MeasurePreserving T muFlat muFull := by
    simpa only [T, muFlat, muFull, paperIndicatorSampleMeasure] using
      paperIndicatorFreshCoordinates_measurePreserving
        N d start hsize nu
  have hradiusFull : Measurable radiusFull := by
    dsimp only [radiusFull]
    exact measurable_norm_paperIndicatorFreshZ
      (d := d) (c₀ := c₀) (C₀ := C₀) profile center z
      (fun (omega : FreshAtomIndex (d + 1) → ℂ)
        (t : Fin (d + 1)) (ell : ResetLabel (d + 1)) => omega (t, ell))
      (fun (t : Fin (d + 1)) (ell : ResetLabel (d + 1)) =>
        measurable_pi_apply (t, ell)) B
  have hradiusEq : radiusFlat = radiusFull ∘ T := by
    funext omega
    dsimp only [radiusFlat, radiusFull, T, Function.comp_apply]
    rw [paperIndicatorFreshAtoms_eq_coordinateRestriction]
  obtain ⟨hzeroFlat, hintFlat, hboundFlat⟩ :=
    logDeficit_transport_of_measurePreserving T hT coefficient
      radiusFlat radiusFull hradiusFull hradiusEq
      (by simpa only [muFull, nu, radiusFull, coefficient, p₀, zeroAtoms]
        using hzeroFull)
      (by simpa only [muFull, nu, radiusFull, coefficient, p₀, zeroAtoms]
        using hintFull)
      (by simpa only [muFull, nu, radiusFull, coefficient, p₀, zeroAtoms]
        using hboundFull)
  exact ⟨hzeroFlat, hscale, hintFlat, hboundFlat⟩

/-- The negative logarithmic half transported all the way to the actual real
flat sample. -/
theorem exists_real_paperIndicatorFlatFreshZ_logDeficit_withDensity
    (N d : ℕ) [NeZero N] (hsize : d + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (z : ℂ) (start : ZMod N)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < exteriorFamilyMaxL2OpNorm B)
    (f : ℝ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ x ∂(volume : Measure ℝ), f x ≤ ENNReal.ofReal L) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        let zeroAtoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ :=
          fun _ _ => 0
        let p₀ := profile.paperIndicatorFreshPolynomial
          center z zeroAtoms B r I J
        let coefficient := ‖MultiAffine.topCoeff p₀‖
        let radius := fun omega : Fin (N * (d + 2)) → ℝ =>
          ‖profile.paperIndicatorFreshZ center z
            (paperIndicatorFreshAtomsOfReal N d start omega) B‖
        let mu := paperIndicatorRealSampleMeasure N d (volume.withDensity f)
        mu {omega | radius omega = 0} = 0 ∧
          Real.log (exteriorFamilyMaxL2OpNorm B) - Real.log coefficient ≤
            paperIsolatedCoefficientLoss d c₀ ∧
          Integrable (fun omega => logDeficit coefficient (radius omega)) mu ∧
          ∫ omega, logDeficit coefficient (radius omega) ∂mu ≤
            realFreshNegativeBound d L := by
  classical
  let nu : Measure ℝ := volume.withDensity f
  obtain ⟨r, I, J, hzeroFull, hscale, hintFull, hboundFull⟩ :=
    profile.exists_real_paperFreshAtomProduct_logDeficit_withDensity
      hc₀ center z B hB f hL hf
  refine ⟨r, I, J, ?_⟩
  let zeroAtoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ := fun _ _ => 0
  let p₀ := profile.paperIndicatorFreshPolynomial center z zeroAtoms B r I J
  let coefficient : ℝ := ‖MultiAffine.topCoeff p₀‖
  let radiusFull := fun omega : FreshAtomIndex (d + 1) → ℝ =>
    ‖profile.paperIndicatorFreshZ center z
      (fun t ell => (omega (t, ell) : ℂ)) B‖
  let radiusFlat := fun omega : Fin (N * (d + 2)) → ℝ =>
    ‖profile.paperIndicatorFreshZ center z
      (paperIndicatorFreshAtomsOfReal N d start omega) B‖
  let muFull := Measure.pi (fun _ : FreshAtomIndex (d + 1) => nu)
  let muFlat := paperIndicatorRealSampleMeasure N d nu
  let T := fun omega : Fin (N * (d + 2)) → ℝ =>
    fun u => omega (paperIndicatorFreshCoordinateIndex N d start u)
  have hT : MeasurePreserving T muFlat muFull := by
    simpa only [T, muFlat, muFull, paperIndicatorRealSampleMeasure] using
      paperIndicatorFreshCoordinates_measurePreserving
        N d start hsize nu
  have hradiusFull : Measurable radiusFull := by
    dsimp only [radiusFull]
    exact measurable_norm_paperIndicatorFreshZ
      (d := d) (c₀ := c₀) (C₀ := C₀) profile center z
      (fun (omega : FreshAtomIndex (d + 1) → ℝ)
        (t : Fin (d + 1)) (ell : ResetLabel (d + 1)) => (omega (t, ell) : ℂ))
      (fun (t : Fin (d + 1)) (ell : ResetLabel (d + 1)) =>
        Complex.continuous_ofReal.measurable.comp (measurable_pi_apply (t, ell))) B
  have hradiusEq : radiusFlat = radiusFull ∘ T := by
    funext omega
    dsimp only [radiusFlat, radiusFull, T, Function.comp_apply]
    rw [paperIndicatorFreshAtomsOfReal_eq_coordinateRestriction]
  obtain ⟨hzeroFlat, hintFlat, hboundFlat⟩ :=
    logDeficit_transport_of_measurePreserving T hT coefficient
      radiusFlat radiusFull hradiusFull hradiusEq
      (by simpa only [muFull, nu, radiusFull, coefficient, p₀, zeroAtoms]
        using hzeroFull)
      (by simpa only [muFull, nu, radiusFull, coefficient, p₀, zeroAtoms]
        using hintFull)
      (by simpa only [muFull, nu, radiusFull, coefficient, p₀, zeroAtoms]
        using hboundFull)
  exact ⟨hzeroFlat, hscale, hintFlat, hboundFlat⟩

/-- Explicit positive-logarithmic contribution coming from the actual trace
and fresh-row norm majorant. -/
noncomputable def paperFreshPositiveBound (d : ℕ) (z : ℂ) : ℝ :=
  Real.posLog (paperFreshTraceFactor d) +
    (d + 1 : ℝ) * Real.sqrt
      (3 * (Real.log (d + 2 : ℝ)) ^ 2 + 3 + 3 * ‖z‖ ^ 2)

/-- End-to-end one-fresh-block `L¹` closure for the actual complex flat IID
sample.  Zero-set nullity is proved internally from the isolated full
monomial; no external positivity or excess assumption remains. -/
theorem complex_paperIndicatorFlatFreshZ_absLog_L1_withDensity
    (N d : ℕ) [NeZero N] (hsize : d + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1)) (z : ℂ) (start : ZMod N)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < exteriorFamilyMaxL2OpNorm B)
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2)
      (volume.withDensity f))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(volume.withDensity f) ≤ 1) :
    let radius := fun omega : Fin (N * (d + 2)) → ℂ =>
      ‖profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtoms N d start omega) B‖
    let scale := exteriorFamilyMaxL2OpNorm B
    let mu := paperIndicatorSampleMeasure N d (volume.withDensity f)
    mu {omega | radius omega = 0} = 0 ∧
      Integrable (fun omega =>
        |Real.log (radius omega) - Real.log scale|) mu ∧
      ∫ omega, |Real.log (radius omega) - Real.log scale| ∂mu ≤
        paperIsolatedCoefficientLoss d c₀ +
          complexFreshNegativeBound d L + paperFreshPositiveBound d z := by
  classical
  obtain ⟨r, I, J, hzero, hscale, hnegativeInt, hnegative⟩ :=
    profile.exists_complex_paperIndicatorFlatFreshZ_logDeficit_withDensity
      N d hsize hc₀ center z start B hB f hL hf
  let zeroAtoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ := fun _ _ => 0
  let p₀ := profile.paperIndicatorFreshPolynomial center z zeroAtoms B r I J
  let coefficient : ℝ := ‖MultiAffine.topCoeff p₀‖
  let radius := fun omega : Fin (N * (d + 2)) → ℂ =>
    ‖profile.paperIndicatorFreshZ center z
      (paperIndicatorFreshAtoms N d start omega) B‖
  let scale := exteriorFamilyMaxL2OpNorm B
  let mu := paperIndicatorSampleMeasure N d (volume.withDensity f)
  have hradius : Measurable radius := by
    dsimp only [radius]
    exact measurable_norm_paperIndicatorFreshZ
      (d := d) (c₀ := c₀) (C₀ := C₀) profile center z
      (fun omega => paperIndicatorFreshAtoms N d start omega)
      (fun t ell => measurable_paperIndicatorFreshAtoms N d start t ell) B
  have hradiusPos : ∀ᵐ omega ∂mu, 0 < radius omega := by
    have hnotMem := measure_eq_zero_iff_ae_notMem.mp
      (by simpa only [mu, radius] using hzero)
    filter_upwards [hnotMem] with omega homega
    have hne : radius omega ≠ 0 := by
      simpa only [Set.mem_setOf_eq] using homega
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  obtain ⟨hpositiveInt, hpositive⟩ :=
    complex_paperIndicatorFlatFreshZ_logExcess_le
      N d profile hc₀ center z start B hB (volume.withDensity f)
      hsecondInt hsecond
      (by simpa only [mu, radius] using hradiusPos)
  letI : IsProbabilityMeasure mu := by
    simpa only [mu, paperIndicatorSampleMeasure] using
      iidMeasure_isProbability (volume.withDensity f) (N * (d + 2))
  have hclosure := freshClosure_L1_of_isolatedCoefficient
    mu coefficient scale (paperIsolatedCoefficientLoss d c₀)
    hradius (paperIsolatedCoefficientLoss_nonneg hc₀ hsqrt)
    (by simpa only [scale, coefficient, p₀, zeroAtoms] using hscale)
    (by simpa only [mu, radius, coefficient, p₀, zeroAtoms] using hnegativeInt)
    (by simpa only [mu, radius, scale] using hpositiveInt)
    (by simpa only [mu, radius, coefficient, p₀, zeroAtoms] using hnegative)
    (by simpa only [mu, radius, scale, paperFreshPositiveBound] using hpositive)
  exact ⟨by simpa only [mu, radius] using hzero,
    by simpa only [mu, radius, scale] using hclosure.1,
    by simpa only [mu, radius, scale, paperFreshPositiveBound,
      Nat.cast_add, Nat.cast_one] using hclosure.2⟩

/-- End-to-end one-fresh-block `L¹` closure for the actual real flat IID
sample after canonical embedding into `ℂ`. -/
theorem real_paperIndicatorFlatFreshZ_absLog_L1_withDensity
    (N d : ℕ) [NeZero N] (hsize : d + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1)) (z : ℂ) (start : ZMod N)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < exteriorFamilyMaxL2OpNorm B)
    (f : ℝ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ x ∂(volume : Measure ℝ), f x ≤ ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : ℝ => u ^ 2)
      (volume.withDensity f))
    (hsecond : ∫ u : ℝ, u ^ 2 ∂(volume.withDensity f) ≤ 1) :
    let radius := fun omega : Fin (N * (d + 2)) → ℝ =>
      ‖profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtomsOfReal N d start omega) B‖
    let scale := exteriorFamilyMaxL2OpNorm B
    let mu := paperIndicatorRealSampleMeasure N d (volume.withDensity f)
    mu {omega | radius omega = 0} = 0 ∧
      Integrable (fun omega =>
        |Real.log (radius omega) - Real.log scale|) mu ∧
      ∫ omega, |Real.log (radius omega) - Real.log scale| ∂mu ≤
        paperIsolatedCoefficientLoss d c₀ +
          realFreshNegativeBound d L + paperFreshPositiveBound d z := by
  classical
  obtain ⟨r, I, J, hzero, hscale, hnegativeInt, hnegative⟩ :=
    profile.exists_real_paperIndicatorFlatFreshZ_logDeficit_withDensity
      N d hsize hc₀ center z start B hB f hL hf
  let zeroAtoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ := fun _ _ => 0
  let p₀ := profile.paperIndicatorFreshPolynomial center z zeroAtoms B r I J
  let coefficient : ℝ := ‖MultiAffine.topCoeff p₀‖
  let radius := fun omega : Fin (N * (d + 2)) → ℝ =>
    ‖profile.paperIndicatorFreshZ center z
      (paperIndicatorFreshAtomsOfReal N d start omega) B‖
  let scale := exteriorFamilyMaxL2OpNorm B
  let mu := paperIndicatorRealSampleMeasure N d (volume.withDensity f)
  have hradius : Measurable radius := by
    dsimp only [radius]
    exact measurable_norm_paperIndicatorFreshZ
      (d := d) (c₀ := c₀) (C₀ := C₀) profile center z
      (fun omega => paperIndicatorFreshAtomsOfReal N d start omega)
      (fun t ell => measurable_paperIndicatorFreshAtomsOfReal N d start t ell) B
  have hradiusPos : ∀ᵐ omega ∂mu, 0 < radius omega := by
    have hnotMem := measure_eq_zero_iff_ae_notMem.mp
      (by simpa only [mu, radius] using hzero)
    filter_upwards [hnotMem] with omega homega
    have hne : radius omega ≠ 0 := by
      simpa only [Set.mem_setOf_eq] using homega
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  obtain ⟨hpositiveInt, hpositive⟩ :=
    real_paperIndicatorFlatFreshZ_logExcess_le
      N d profile hc₀ center z start B hB (volume.withDensity f)
      hsecondInt hsecond
      (by simpa only [mu, radius] using hradiusPos)
  letI : IsProbabilityMeasure mu := by
    simpa only [mu, paperIndicatorRealSampleMeasure] using
      iidMeasure_isProbability (volume.withDensity f) (N * (d + 2))
  have hclosure := freshClosure_L1_of_isolatedCoefficient
    mu coefficient scale (paperIsolatedCoefficientLoss d c₀)
    hradius (paperIsolatedCoefficientLoss_nonneg hc₀ hsqrt)
    (by simpa only [scale, coefficient, p₀, zeroAtoms] using hscale)
    (by simpa only [mu, radius, coefficient, p₀, zeroAtoms] using hnegativeInt)
    (by simpa only [mu, radius, scale] using hpositiveInt)
    (by simpa only [mu, radius, coefficient, p₀, zeroAtoms] using hnegative)
    (by simpa only [mu, radius, scale, paperFreshPositiveBound] using hpositive)
  exact ⟨by simpa only [mu, radius] using hzero,
    by simpa only [mu, radius, scale] using hclosure.1,
    by simpa only [mu, radius, scale, paperFreshPositiveBound,
      Nat.cast_add, Nat.cast_one] using hclosure.2⟩

end PaperIndicatorWeights

end CircularLawSection4
