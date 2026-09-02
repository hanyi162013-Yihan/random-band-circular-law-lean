import CircularLawSections56.Section5.LiteralAtomPressure
import CircularLawSections56.Section5.GenericCenteredFreshCell
import CircularLawSections56.Section5.LiteralPhysicalMesoscopicCellAdapter

/-! # Actual physical cells under an atom logarithmic moment bound

No cell or global integrability is assumed.  The only additional analytic input
is the finite-dimensional fresh projective deficit, instantiated separately for
real and complex atoms.  All pressure conclusions concern the actual IID rows.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1200000

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

local instance genericPhysicalRowProbability (d : ℕ) (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (paperIndicatorRowMeasure d ν) := iidMeasure_isProbability ν _

local instance genericPhysicalRowsProbability (n d : ℕ) (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (paperIndicatorOpenRowSampleMeasure n d ν) :=
  iidMeasure_isProbability (paperIndicatorRowMeasure d ν) _

local instance freshProbability (d : ℕ) (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (literalPaperExteriorCellMeasure d ν) := by
  unfold literalPaperExteriorCellMeasure
  infer_instance

/-- The finite projective statement, with no asymptotic or pressure premise. -/
def LiteralFreshProjectiveControl (d : ℕ) {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀) (center : Fin (d + 1))
    (z : ℂ) (q : ExteriorDegree (d + 1)) (ν : Measure ℂ) (loss : ℝ) : Prop :=
  ∀ B : Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ,
    0 < ‖B‖ → ∀ v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q), ‖v‖ = 1 →
    Integrable (fun ω => logDeficit ‖B‖
      ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) ℂ).symm
        ((literalPaperExteriorCellWithLeft profile center z q B ω).mulVec (fun j => v j))‖)
      (literalPaperExteriorCellMeasure d ν) ∧
    (∫ ω, logDeficit ‖B‖
      ‖(EuclideanSpace.equiv (ExteriorIndex (d + 1) q) ℂ).symm
        ((literalPaperExteriorCellWithLeft profile center z q B ω).mulVec (fun j => v j))‖
      ∂literalPaperExteriorCellMeasure d ν) ≤ loss

theorem literal_fresh_integrable_of_atom_log
    (d : ℕ) {c₀ C₀ K : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (hcenter : center ≠ 0)
    (z : ℂ) (q : ExteriorDegree (d + 1)) (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hν : AtomLogControl ν K) :
    Integrable (fun ω => Real.log ‖literalPaperExteriorCell profile center z q ω‖)
        (literalPaperExteriorCellMeasure d ν) ∧
      ∀ᵐ ω ∂literalPaperExteriorCellMeasure d ν,
        IsUnit (literalPaperExteriorCell profile center z q ω) := by
  have hall := literal_iid_open_product_integrable_of_atom_log
    (d + 1) d profile hc₀ center hcenter z q ν hν
  have hmp := literalPaperCellRows_measurePreserving d ν
  exact ⟨hmp.integrable_comp_of_integrable hall.1, hmp.quasiMeasurePreserving.ae hall.2⟩

theorem literal_physical_cell_integrable_of_atom_log
    (ell d : ℕ) {c₀ C₀ K : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (hcenter : center ≠ 0)
    (z : ℂ) (q : ExteriorDegree (d + 1)) (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hν : AtomLogControl ν K) :
    Integrable
      (fun sample : LiteralPhysicalOutsideRows ell d × LiteralPaperCellAtoms d =>
        Real.log ‖literalPhysicalMesoscopicCell profile center z q sample‖)
      (literalPhysicalMesoscopicCellMeasure ell d ν) := by
  have hrows := (literal_iid_open_product_integrable_of_atom_log
    ((d + 1) + ell) d profile hc₀ center hcenter z q ν hν).1
  have hpull := (literalPhysicalCellRows_measurePreserving ell d ν).integrable_comp_of_integrable hrows
  have hfun : (profile.paperIndicatorOpenPressure center z q) ∘
      (literalPhysicalCellRowsMeasurableEquiv ell d) =
      (fun sample => Real.log ‖literalPhysicalMesoscopicCell profile center z q sample‖) := by
    funext sample
    simp only [Function.comp_def, paperIndicatorOpenPressure,
      literalPhysicalMesoscopicCell_eq_openProduct]
  rwa [hfun] at hpull

theorem literal_physical_global_integrable_of_atom_log
    (ell d : ℕ) {c₀ C₀ K : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (hcenter : center ≠ 0)
    (z : ℂ) (q : ExteriorDegree (d + 1)) (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hν : AtomLogControl ν K) (n : ℕ) :
    Integrable (iidMatrixCellLogPotential (literalPhysicalMesoscopicCell profile center z q))
      (iidMeasure (literalPhysicalMesoscopicCellMeasure ell d ν) n) := by
  have hrows := (literal_iid_open_product_integrable_of_atom_log
    (n * ((d + 1) + ell)) d profile hc₀ center hcenter z q ν hν).1
  have hpull := (literalPhysicalIidCellRows_measurePreserving n ell d ν).integrable_comp_of_integrable hrows
  have hfun : (profile.paperIndicatorOpenPressure center z q) ∘
      (literalPhysicalIidCellRowsMeasurableEquiv n ell d) =
      iidMatrixCellLogPotential (literalPhysicalMesoscopicCell profile center z q) := by
    funext sample
    simp only [Function.comp_def, paperIndicatorOpenPressure, iidMatrixCellLogPotential,
      iidMatrixCellProduct_literalPhysicalMesoscopicCell_eq_openProduct]
  rwa [hfun] at hpull

/-- Centered telescope for the literal chronological rows, for any atom law
with the proved finite projective input and logarithmic atom control. -/
theorem literal_physical_telescope_of_atom_log
    (ell cellCount d : ℕ) {c₀ C₀ K : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (hcenter : center ≠ 0)
    (z : ℂ) (q : ExteriorDegree (d + 1)) (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hν : AtomLogControl ν K) (loss : ℝ)
    (hProjective : LiteralFreshProjectiveControl d profile center z q ν loss) :
    let base := literalOpenMeanPressure d ell ν profile center z q
    let error := max loss (∫ ω, Real.log ‖literalPaperExteriorCell profile center z q ω‖
      ∂literalPaperExteriorCellMeasure d ν)
    (cellCount : ℝ) * (base - error) ≤
        literalOpenMeanPressure d (cellCount * ((d + 1) + ell)) ν profile center z q ∧
      literalOpenMeanPressure d (cellCount * ((d + 1) + ell)) ν profile center z q ≤
        (cellCount : ℝ) * (base + error) := by
  let B := literalPhysicalOutsideExteriorProduct (ell := ell) profile center z q
  let μ := paperIndicatorOpenRowSampleMeasure ell d ν
  let μfresh := literalPaperExteriorCellMeasure d ν
  let : Nonempty (ExteriorIndex (d + 1) q) := exteriorIndex_nonempty_bridge _ _
  have hBcont : Continuous B :=
    profile.continuous_paperIndicatorOpenExteriorProduct center z q ell
  have hBmeas : ∀ i j, Measurable (fun outside => B outside i j) :=
    fun i j => ((continuous_apply j).comp ((continuous_apply i).comp hBcont)).measurable
  have hBnorm : Measurable (fun outside => ‖B outside‖) := hBcont.norm.measurable
  have hOutside := literal_iid_open_product_integrable_of_atom_log
    ell d profile hc₀ center hcenter z q ν hν
  have hFresh := literal_fresh_integrable_of_atom_log d profile hc₀ center hcenter z q ν hν
  have hFactors : ∀ᵐ sample ∂μ.prod μfresh,
      IsUnit (B sample.1) ∧ IsUnit (literalPaperExteriorCell profile center z q sample.2) := by
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hOutside.2,
      measurePreserving_snd.quasiMeasurePreserving.ae hFresh.2] with sample hb hq
    exact ⟨hb, hq⟩
  have hCell := literal_physical_cell_integrable_of_atom_log
    ell d profile hc₀ center hcenter z q ν hν
  have hGlobal := literal_physical_global_integrable_of_atom_log
    ell d profile hc₀ center hcenter z q ν hν
  have hOne := literalRandomOutsideExteriorCell_oneCellInputs_of_projective
    μ profile center z q B hBmeas hBnorm hOutside.2 hOutside.1
    ν loss hFresh.1 hProjective hFactors hCell
  have hTel := iidMatrixCellProduct_expectedLog_telescope_autoDirection_ae
    (μ.prod μfresh) (literalRandomOutsideExteriorCell profile center z q B) cellCount
    (literalOpenMeanPressure d ell ν profile center z q)
    (max loss (∫ ω, Real.log ‖literalPaperExteriorCell profile center z q ω‖ ∂μfresh))
    hOne.1 hOne.2.1 hOne.2.2 (fun n _ => hGlobal n)
  have hPressure := literalPhysicalMesoscopicCell_expectedLog_eq_openPressure
    cellCount ell ν profile center z q
  change (∫ sample, iidMatrixCellLogPotential
    (literalRandomOutsideExteriorCell profile center z q B) sample
    ∂iidMeasure (μ.prod μfresh) cellCount) = _ at hPressure
  simpa only [hPressure, literalOpenMeanPressure, μfresh] using hTel

end CircularLawSections56.Section5
