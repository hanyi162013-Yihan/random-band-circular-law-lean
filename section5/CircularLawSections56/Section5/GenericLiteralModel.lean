import CircularLawSections56.Section5.UniformAtomPressure
import CircularLawSections56.Section6.LiteralModelIdentification

/-! # Completed finite ledger for real atoms and polynomial taper

The profile lower parameter may vary with the matrix size.  A fixed logarithmic
weight constant, not a fixed positive lower weight, is what the transfer uses.
Only the two finite Section 4 pressure inputs remain external.
-/

open Filter MeasureTheory Topology
open scoped BigOperators ENNReal

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1800000

namespace CircularLawSections56.Section5

open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

def logarithmicModelLiftedPressure (d q m : ℕ → ℕ) (ν : ℕ → Measure ℂ)
    [∀ n, IsProbabilityMeasure (ν n)]
    {c₀ C₀ : ℕ → ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n))
    (center : ∀ n, Fin (d n + 1)) (z : ℂ) : ∀ n, ExteriorDegree (d n + 1) → ℝ :=
  fun n r => literalOpenMeanPressure (d n) (q n * m n) (ν n) (profile n) (center n) z r

theorem literalModelPressure_mean_of_atom_log
    (k d m : ℕ) (hm : m ≤ k + 1)
    {c₀ C₀ K : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (hcenter : center ≠ 0)
    (z : ℂ) (r : ExteriorDegree (d + 1))
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hν : AtomLogControl ν K) :
    (∫ ω, literalModelPressure k d m profile center z r ω
      ∂iidMeasure ν ((k + 1) * (d + 2))) =
      literalOpenMeanPressure d (m - (d + 1)) ν profile center z r :=
  integral_comp_measurePreserving_eq (literalCalibrationRows_measurePreserving k d m hm ν)
    (profile.paperIndicatorOpenPressure center z r)
    (literal_iid_open_product_integrable_of_atom_log
      (m - (d + 1)) d profile hc₀ center hcenter z r ν hν).1

/-- Cells, pressure transport, every terminal row, and both terminal endpoints
are constructed. No Section 5 pressure limit is a hypothesis. -/
def literalModel_completedSection4Data_of_atom_log
    (active : ℕ → Bool) (d q m W : ℕ → ℕ)
    {c₀ C₀ : ℕ → ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n))
    (center : ∀ n, Fin (d n + 1)) (z : ℂ) (δ A J K C : ℝ)
    (hC : atomTransferConstant A J K z ≤ C)
    (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)]
    (hc₀ : ∀ n, 0 < c₀ n) (hA : 0 ≤ A) (hJ : 0 ≤ J) (hK : 0 ≤ K)
    (hProfile : ∀ n, active n = true → |Real.log (c₀ n)| ≤ A * dimensionLogScale (d n))
    (hAtom : ∀ n, active n = true → AtomTransferControl (ν n) J K)
    (hW : ∀ n, active n = true → 0 < W n)
    (hd : ∀ n, active n = true → d n + 1 = 2 * W n)
    (hm0 : ∀ n, active n = true → 0 < paperMesoscopicCellLength δ W n)
    (hReserve : ∀ n, active n = true → 2 * W n ≤ n + 1)
    (hFit : ∀ n, active n = true → 2 * paperMesoscopicCellLength δ W n ≤ n + 1 - 2 * W n)
    (hCount : ∀ n, active n = true →
      q n = balancedCellCount (n + 1 - 2 * W n) (paperMesoscopicCellLength δ W n))
    (hLength : ∀ n, active n = true →
      m n = balancedCellLength (n + 1 - 2 * W n) (paperMesoscopicCellLength δ W n))
    (hWidth : ∀ n, active n = true → d n + 1 ≤ m n)
    (hmN : ∀ n, active n = true → m n ≤ n + 1)
    (hcenter : ∀ n, active n = true → center n ≠ 0)
    (hCalibration : CompletedSection4PressureInput
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2))) active
      (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (m n) (profile n) (center n) z)
      m W C)
    (hFinal : CompletedSection4PressureInput
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2))) active
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (fun n => n + 1) W C) :
    CompletedSection4LongBranchData
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2))) active
      (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (m n) (profile n) (center n) z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (logarithmicModelLiftedPressure d q m ν profile center z)
      q m (fun n => n + 1) W δ C where
  constant_nonneg := (atomTransferConstant_nonneg A J K z hA hJ hK).trans hC
  bandwidth_pos := hW
  base_length_pos := hm0
  reserve := hReserve
  fit := hFit
  count_eq := hCount
  length_eq := hLength
  calibration := hCalibration
  final := hFinal
  cells := by
    intro n hn r
    have ht := literal_physical_telescope_uniform_atom (m n - (d n + 1)) (q n) (d n) (W n)
      (hW n hn) (hd n hn) (profile n) (hc₀ n) hA (hProfile n hn)
      (center n) (hcenter n hn) z r (ν n) (hAtom n hn)
    have hMean := literalModelPressure_mean_of_atom_log n (d n) (m n) (hmN n hn)
      (profile n) (hc₀ n) (center n) (hcenter n hn) z r (ν n) (hAtom n hn).logarithmic
    have hlen : d n + 1 + (m n - (d n + 1)) = m n := Nat.add_sub_of_le (hWidth n hn)
    dsimp only at ht
    rw [hlen] at ht
    have hLog : 0 ≤ paperLogEW W n :=
      zero_le_one.trans (one_le_paperLogEW_of_bandwidth_pos W n (hW n hn))
    have he := mul_le_mul_of_nonneg_right hC (mul_nonneg (Nat.cast_nonneg (W n)) hLog)
    simp only [literalCoordinateMeanPressure, hMean, logarithmicModelLiftedPressure]
    exact ⟨(mul_le_mul_of_nonneg_left (sub_le_sub_left he _) (Nat.cast_nonneg (q n))).trans ht.1,
      ht.2.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl he) (Nat.cast_nonneg (q n)))⟩
  terminalPressure := fun n r j => literalOpenMeanPressure (d n) (q n * m n + j)
    (ν n) (profile n) (center n) z r
  terminal_start := by intros; simp only [Nat.add_zero, logarithmicModelLiftedPressure]
  terminal_end := by
    intro n hn r
    have hparts := balanced_cells_add_remainder (n + 1 - 2 * W n)
      (paperMesoscopicCellLength δ W n)
    have hlen : q n * m n + balancedCellRemainder (n + 1 - 2 * W n)
        (paperMesoscopicCellLength δ W n) = n + 1 - (d n + 1) := by
      rw [hCount n hn, hLength n hn, hd n hn]
      exact hparts
    rw [hlen]
    exact (literalModelPressure_mean_of_atom_log n (d n) (n + 1) le_rfl
      (profile n) (hc₀ n) (center n) (hcenter n hn) z r (ν n) (hAtom n hn).logarithmic).symm
  row_increment := by
    intro n hn r j _
    have h := literal_row_increment_uniform_atom (d n) (W n) (q n * m n + j)
      (hW n hn) (hd n hn) (profile n) (hc₀ n) hA (hProfile n hn)
      (center n) (hcenter n hn) z r (ν n) (hAtom n hn)
    exact h.trans (mul_le_mul_of_nonneg_right hC
      (zero_le_one.trans (one_le_paperLogEW_of_bandwidth_pos W n (hW n hn))))

end CircularLawSections56.Section5
