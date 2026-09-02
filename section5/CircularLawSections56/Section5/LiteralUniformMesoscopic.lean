import CircularLawSections56.Section5.CompletedMesoscopicCalibration
import CircularLawSections56.Section5.GenericLiteralModel

/-! # Uniform mesoscopic calibration of the actual open-row mean pressures

All admissible auxiliary rings are realized as restrictions of one finite IID
array with enough rows. Their coordinate means are proved to be the literal
open-product pressures; this is not an additional identification premise.
-/

open Filter MeasureTheory Topology
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option autoImplicit false

namespace CircularLawSections56.Section5
open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

def mesoscopicCalibrationAmbient (δ : ℝ) (W : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * paperMesoscopicCellLength δ W n

def literalMesoscopicMean
    (d : ℕ → ℕ) (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)]
    {c₀ C₀ : ℕ → ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n))
    (center : ∀ n, Fin (d n + 1)) (z : ℂ) (n m : ℕ) : ℝ :=
  finiteSignedMax Finset.univ Finset.univ_nonempty
    (fun r => literalOpenMeanPressure (d n) (m - (d n + 1)) (ν n) (profile n) (center n) z r) /
      (m : ℝ)

theorem literal_uniform_mesoscopic_calibration
    (d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ : ℕ → ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n))
    (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)]
    (δ C K target : ℝ) (z : ℂ)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hW : Tendsto W atTop atTop) (hWpos : ∀ n, 0 < W n)
    (hc₀ : ∀ n, 0 < c₀ n) (hcenter : ∀ n, center n ≠ 0)
    (hAtom : ∀ n, AtomLogControl (ν n) K)
    (h4 : ∀ m : ℕ → ℕ,
      (∀ n, paperMesoscopicCellLength δ W n ≤ m n ∧ m n ≤ 2 * paperMesoscopicCellLength δ W n) →
      CompletedSection4PressureInput
        (fun n => iidMeasure (ν n) ((mesoscopicCalibrationAmbient δ W n + 1) * (d n + 2)))
        (fun _ => true)
        (fun n => literalModelCalibrationRaw (mesoscopicCalibrationAmbient δ W n)
          (d n) (m n) (center n) (profile n).b z)
        (fun n => literalModelPressure (mesoscopicCalibrationAmbient δ W n)
          (d n) (m n) (profile n) (center n) z) m W C)
    (h3 :
      let : ∀ n, IsProbabilityMeasure
          (iidMeasure (ν n) ((mesoscopicCalibrationAmbient δ W n + 1) * (d n + 2))) :=
        fun n => iidMeasure_isProbability (ν n) _
      ∀ m : ℕ → ℕ,
      (∀ n, paperMesoscopicCellLength δ W n ≤ m n ∧ m n ≤ 2 * paperMesoscopicCellLength δ W n) →
      TendstoInProbabilityTri
        (fun n => iidMeasure (ν n) ((mesoscopicCalibrationAmbient δ W n + 1) * (d n + 2)))
        (fun n ω => literalModelCalibrationRaw (mesoscopicCalibrationAmbient δ W n)
          (d n) (m n) (center n) (profile n).b z ω / (m n : ℝ)) target) :
    Tendsto (fun n => finiteSignedMax
      (Finset.Icc (paperMesoscopicCellLength δ W n) (2 * paperMesoscopicCellLength δ W n))
      (mesoscopic_interval_nonempty _)
      (fun m => |literalMesoscopicMean d ν profile center z n m - target|)) atTop (𝓝 0) := by
  let : ∀ n, IsProbabilityMeasure
      (iidMeasure (ν n) ((mesoscopicCalibrationAmbient δ W n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability (ν n) _
  apply mesoscopic_supremum_zero_of_all_length_calibrations (paperMesoscopicCellLength δ W)
    (literalMesoscopicMean d ν profile center z) target
  intro m hm
  have hmAmbient (n : ℕ) : m n ≤ mesoscopicCalibrationAmbient δ W n + 1 :=
    (hm n).2.trans (Nat.le_succ _)
  have hcal := completedSection4_mesoscopic_calibration
    (fun n => iidMeasure (ν n) ((mesoscopicCalibrationAmbient δ W n + 1) * (d n + 2)))
    (fun n => literalModelCalibrationRaw (mesoscopicCalibrationAmbient δ W n)
      (d n) (m n) (center n) (profile n).b z)
    (fun n => literalModelPressure (mesoscopicCalibrationAmbient δ W n)
      (d n) (m n) (profile n) (center n) z)
    m W δ C target hδ hC hW hWpos (fun n => (hm n).1) (h4 m hm) (h3 m hm)
  have hmean (n : ℕ) (r : ExteriorDegree (d n + 1)) :=
    literalModelPressure_mean_of_atom_log (mesoscopicCalibrationAmbient δ W n) (d n) (m n)
      (hmAmbient n) (profile n) (hc₀ n) (center n) (hcenter n) z r (ν n) (hAtom n)
  simpa only [coordinateMeanFiniteSignedMaxTri, literalMesoscopicMean, hmean] using hcal

end CircularLawSections56.Section5
