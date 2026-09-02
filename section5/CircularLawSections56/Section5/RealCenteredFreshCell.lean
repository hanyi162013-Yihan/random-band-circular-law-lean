import CircularLawSections56.Section5.LiteralRealCellPackage
import CircularLawSections56.Section5.LiteralCenteredMatrixCellAdapter
import CircularLawSections56.Section5.RealAtomLogMoments
import CircularLawSections56.Section5.LiteralFreshMeanBound

/-! # Real-atom projective deficit with the outside matrix retained

The previously available real theorem used the identity outside matrix.  Here
`B` is arbitrary, the deficit is centered at `log ‖B‖`, and the result is
transported to the complexified IID law used by the physical model.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1200000

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights Matrix

theorem real_fresh_complexify_measurePreserving (d : ℕ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun ω : LiteralRealPaperCellAtoms d => fun i => (ω i : ℂ))
      (literalRealPaperExteriorCellMeasure d ν)
      (literalPaperExteriorCellMeasure d (realComplexAtomLaw ν)) := by
  refine ⟨measurable_pi_lambda _ (fun i => Complex.continuous_ofReal.measurable.comp
    (measurable_pi_apply i)), ?_⟩
  exact Measure.pi_map_pi (fun _ => Complex.continuous_ofReal.measurable.aemeasurable)

theorem real_literalPaperExteriorCellWithLeft_deficit
    (d : ℕ) {c₀ C₀ L : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (z : ℂ) (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ) (hB : 0 < ‖B‖)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q)) (hv : ‖v‖ = 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hL : 0 ≤ L)
    (hν : RealIntervalBound ν (ENNReal.ofReal L)) :
    let radius := fun ω : LiteralRealPaperCellAtoms d =>
      ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) ℂ).symm
        ((literalPaperExteriorCellWithLeft profile center z q B (fun i => (ω i : ℂ))).mulVec
          (fun j => v j))‖
    Integrable (fun ω => logDeficit ‖B‖ (radius ω)) (literalRealPaperExteriorCellMeasure d ν) ∧
      (∫ ω, logDeficit ‖B‖ (radius ω) ∂literalRealPaperExteriorCellMeasure d ν) ≤
        realLiteralProjectiveCellLoss d c₀ L q := by
  classical
  let : Nonempty (ExteriorIndex (d + 1) q) := exteriorIndex_nonempty_bridge _ _
  obtain ⟨o, I, J, hcoef⟩ :=
    exists_uniform_paperProjectiveFreshPolynomial_topCoeff_lower profile center z q B v hv
  let word := arbitrarySupportWord I J
  let e := splitFreshAtomMeasurableEquiv (K := ℝ) word
  let μx := Measure.pi (fun _ : Fin (d + 1) => ν)
  let μy := Measure.pi (fun _ : UnselectedFreshIndex word => ν)
  let μ := literalRealPaperExteriorCellMeasure d ν
  let atoms := fun y : UnselectedFreshIndex word → ℝ =>
    fun t ell => ((e.symm ((fun _ => 0), y) (t, ell) : ℝ) : ℂ)
  let radius := fun ω : LiteralRealPaperCellAtoms d =>
    ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) ℂ).symm
      ((literalPaperExteriorCellWithLeft profile center z q B (fun i => (ω i : ℂ))).mulVec
        (fun j => v j))‖
  have hm : Measurable radius :=
    (measurable_literalPaperExteriorCellWithLeft_vectorNorm profile center z q B v).comp
      (real_fresh_complexify_measurePreserving d ν).measurable
  have heval (x : Fin (d + 1) → ℝ) (y : UnselectedFreshIndex word → ℝ) :
      ‖profile.paperProjectiveFreshVectorOfReal center z (atoms y) q B v I J x‖ =
        radius (e.symm (x, y)) := by
    rw [paperProjectiveFreshVectorOfReal,
      paperProjectiveFreshVector_eq_literalPaperExteriorCellWithLeft_action]
    apply congrArg (fun ω : LiteralPaperCellAtoms d =>
      ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) ℂ).symm
        ((literalPaperExteriorCellWithLeft profile center z q B ω).mulVec (fun j => v j))‖)
    funext u
    rcases u with ⟨t, ell⟩
    have h := congrFun (congrFun
      (splitFreshAtom_symm_realCast_eq_replacePaperFreshSelectedAtoms word x y) t) ell
    simpa only [atoms, e, Function.uncurry, replaceSelectedFreshAtoms,
      replacePaperFreshSelectedAtoms] using h.symm
  let F := fun xy : (Fin (d + 1) → ℝ) × (UnselectedFreshIndex word → ℝ) =>
    logDeficit ‖B‖ (radius (e.symm xy))
  have hFm : Measurable F := (measurable_logDeficit ‖B‖ hm).comp e.symm.measurable
  have hfiber (y : UnselectedFreshIndex word → ℝ) :=
    paperProjectiveFreshVector_real_logDeficit_of_topCoeff profile hc₀ center z (atoms y) q B hB
      v o I J (hcoef (atoms y)) ν hL hν
  let : IsProbabilityMeasure μx := by dsimp only [μx]; infer_instance
  let : IsProbabilityMeasure μy := by dsimp only [μy]; infer_instance
  obtain ⟨hFi, hFb⟩ := integrable_prod_and_integral_le_of_forall_integrable_integral_le
    μx μy F hFm (fun _ => logDeficit_nonneg _ _) (realLiteralProjectiveCellLoss d c₀ L q)
    (realLiteralProjectiveCellLoss_nonneg d c₀ L q)
    (fun y => by simpa only [F, heval, μx, iidMeasure_eq_pi] using (hfiber y).2.1)
    (fun y => by simpa only [F, heval, μx, iidMeasure_eq_pi] using (hfiber y).2.2)
  have hmp : MeasurePreserving e μ (μx.prod μy) :=
    splitFreshAtom_measurePreserving word ν
  have hi : Integrable (fun ω => logDeficit ‖B‖ (radius ω)) μ := by
    have h := (hmp.integrable_comp_emb e.measurableEmbedding).2 hFi
    simpa only [F, Function.comp_def, MeasurableEquiv.symm_apply_apply] using h
  refine ⟨hi, ?_⟩
  calc
    _ = ∫ xy, F xy ∂μx.prod μy := by
      rw [← hmp.integral_comp' F]
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => by simp only [F, MeasurableEquiv.symm_apply_apply]; rfl)
    _ ≤ _ := hFb

theorem realComplex_literalPaperExteriorCellWithLeft_deficit
    (d : ℕ) {c₀ C₀ L : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (z : ℂ) (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ) (hB : 0 < ‖B‖)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q)) (hv : ‖v‖ = 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hL : 0 ≤ L)
    (hν : RealIntervalBound ν (ENNReal.ofReal L)) :
    let radius := fun ω : LiteralPaperCellAtoms d =>
      ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) ℂ).symm
        ((literalPaperExteriorCellWithLeft profile center z q B ω).mulVec (fun j => v j))‖
    Integrable (fun ω => logDeficit ‖B‖ (radius ω))
        (literalPaperExteriorCellMeasure d (realComplexAtomLaw ν)) ∧
      (∫ ω, logDeficit ‖B‖ (radius ω) ∂literalPaperExteriorCellMeasure d (realComplexAtomLaw ν)) ≤
        realLiteralProjectiveCellLoss d c₀ L q := by
  have hmp := real_fresh_complexify_measurePreserving d ν
  let radius := fun ω : LiteralPaperCellAtoms d =>
    ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) ℂ).symm
      ((literalPaperExteriorCellWithLeft profile center z q B ω).mulVec (fun j => v j))‖
  let G := fun ω => logDeficit ‖B‖ (radius ω)
  have hm : Measurable G := measurable_logDeficit ‖B‖
    (measurable_literalPaperExteriorCellWithLeft_vectorNorm profile center z q B v)
  have h := real_literalPaperExteriorCellWithLeft_deficit d profile hc₀ center z q B hB v hv ν hL hν
  have hi : Integrable G (literalPaperExteriorCellMeasure d (realComplexAtomLaw ν)) :=
    (hmp.integrable_comp hm.aestronglyMeasurable).1 h.1
  exact ⟨hi, (integral_comp_measurePreserving_eq hmp G hi).symm.trans_le h.2⟩

end CircularLawSections56.Section5
