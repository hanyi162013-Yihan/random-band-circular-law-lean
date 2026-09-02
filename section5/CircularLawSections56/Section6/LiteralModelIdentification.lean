import CircularLawSections56.Section5.LiteralTerminalPressure
import CircularLawSections56.Section6.LiteralIndicatorModel
import CircularLawSections56.Section6.CompletedSection4Endpoint

/-! # Concrete band-model identification and the completed Section 4 endpoint

The final observable is the actual cyclic log determinant. Calibration outside
rows are the suffix of the first `m` physical rows; final outside rows are the
suffix of the whole matrix. Both restrictions have their exact IID laws.
-/

open Filter MeasureTheory Topology
open scoped BigOperators ENNReal

noncomputable section

namespace CircularLawSections56.Section6

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights
open CircularLawSections56.Section5 TaoVuReplacement

def literalCalibrationRowIndex (k d m : ℕ) (hm : m ≤ k + 1)
    (j : Fin (m - (d + 1))) : Fin (k + 1) :=
  ⟨d + 1 + j.val, by omega⟩

theorem literalCalibrationRowIndex_injective (k d m : ℕ) (hm : m ≤ k + 1) :
    Function.Injective (literalCalibrationRowIndex k d m hm) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [literalCalibrationRowIndex] at hv
  omega

/-- Concrete calibration restriction; the unused indices have a zero-row filler. -/
def literalCalibrationRows (k d m : ℕ) (ω : Fin ((k + 1) * (d + 2)) → ℂ) :
    LiteralPhysicalOutsideRows (m - (d + 1)) d :=
  if hm : m ≤ k + 1 then
    fun j => paperIndicatorFlatRowsEquiv (k + 1) d ω (literalCalibrationRowIndex k d m hm j)
  else fun _ _ => 0

theorem literalCalibrationRows_measurePreserving (k d m : ℕ) (hm : m ≤ k + 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    MeasurePreserving (literalCalibrationRows k d m)
      (iidMeasure ν ((k + 1) * (d + 2)))
      (paperIndicatorOpenRowSampleMeasure (m - (d + 1)) d ν) := by
  let ρ := paperIndicatorRowMeasure d ν
  let : IsProbabilityMeasure ρ := iidMeasure_isProbability ν _
  have h := measurePreserving_pi_restrict_injective
    (literalCalibrationRowIndex k d m hm) (literalCalibrationRowIndex_injective k d m hm) ρ
  have hrows : MeasurePreserving
      (fun rows : Fin (k + 1) → PaperIndicatorAtomRow d =>
        fun j => rows (literalCalibrationRowIndex k d m hm j))
      (paperIndicatorOpenRowSampleMeasure (k + 1) d ν)
      (paperIndicatorOpenRowSampleMeasure (m - (d + 1)) d ν) := by
    simpa only [paperIndicatorOpenRowSampleMeasure, iidMeasure_eq_pi, ρ] using h
  have heq : literalCalibrationRows k d m =
      fun ω j => paperIndicatorFlatRowsEquiv (k + 1) d ω (literalCalibrationRowIndex k d m hm j) := by
    funext ω
    simp only [literalCalibrationRows, dif_pos hm]
  rw [heq]
  exact hrows.comp (paperIndicatorFlatRows_measurePreserving (k + 1) d ν)

def literalModelPressure (k d m : ℕ)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ) (q : ExteriorDegree (d + 1))
    (ω : Fin ((k + 1) * (d + 2)) → ℂ) : ℝ :=
  profile.paperIndicatorOpenPressure center z q (literalCalibrationRows k d m ω)

theorem literalModelPressure_mean (k d m : ℕ) (hm : m ≤ k + 1)
    {c₀ C₀ L : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1)) (z : ℂ) (q : ExteriorDegree (d + 1))
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hL : 0 ≤ L) (hν : ComplexBallBound ν (ENNReal.ofReal L))
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    (∫ ω, literalModelPressure k d m profile center z q ω
      ∂iidMeasure ν ((k + 1) * (d + 2))) =
      literalOpenMeanPressure d (m - (d + 1)) ν profile center z q :=
  integral_comp_measurePreserving_eq (literalCalibrationRows_measurePreserving k d m hm ν)
    (profile.paperIndicatorOpenPressure center z q)
    (complex_literalPhysicalOpenPressure_integrable _ ν hν hL profile hc₀ hsqrt
      center z q hInt hSecond)

/-- At the full matrix size the chosen rows coincide with the previously proved
literal Section 4 suffix, not just with an equal-in-law substitute. -/
theorem literalCalibrationRows_full_eq_suffix (k d : ℕ) (hd : d + 1 ≤ k + 1)
    (ω : Fin ((k + 1) * (d + 2)) → ℂ) :
    literalCalibrationRows k d (k + 1) ω = paperIndicatorSuffixRowsZero (k + 1) d hd ω := by
  funext j
  simp only [literalCalibrationRows, le_refl, dif_pos, paperIndicatorSuffixRowsZero]
  congr 1

def literalModelRawDeterminant (k d : ℕ) (center : Fin (d + 1))
    (b : Fin (d + 2) → ℂ) (z : ℂ) (ω : Fin ((k + 1) * (d + 2)) → ℂ) : ℝ :=
  Real.log ‖(paperIndicatorXSubZI (k + 1) d center b ω z).det‖

/-- The calibration ring uses exactly the first `m` rows of the same atom sample. -/
def literalModelCalibrationRaw (k d m : ℕ) (center : Fin (d + 1))
    (b : Fin (d + 2) → ℂ) (z : ℂ) (ω : Fin ((k + 1) * (d + 2)) → ℂ) : ℝ :=
  if hm : 0 < m ∧ m ≤ k + 1 then
    let : NeZero m := ⟨Nat.ne_of_gt hm.1⟩
    Real.log ‖(paperIndicatorXSubZI m d center b
      (fun j => ω (Fin.castLE (Nat.mul_le_mul_right (d + 2) hm.2) j)) z).det‖
  else 0

def literalModelLiftedPressure (d q m : ℕ → ℕ) (ν : ℕ → Measure ℂ)
    [∀ n, IsProbabilityMeasure (ν n)]
    {c₀ C₀ : ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀)
    (center : ∀ n, Fin (d n + 1)) (z : ℂ) : ∀ n, ExteriorDegree (d n + 1) → ℝ :=
  fun n r => literalOpenMeanPressure (d n) (q n * m n) (ν n) (profile n) (center n) z r

/-- Construct the entire finite ledger from the two completed Section 4 pressure
estimates for the concrete model. Cell bounds, the terminal path and its endpoints,
and inverse-row increments are all proved, not ledger inputs. -/
def literalModel_completedSection4Data
    (active : ℕ → Bool) (d q m W : ℕ → ℕ)
    {c₀ C₀ L : ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀)
    (center : ∀ n, Fin (d n + 1)) (z : ℂ) (δ : ℝ)
    (f : ℕ → ℂ → ℝ≥0∞) [∀ n, IsProbabilityMeasure (volume.withDensity (f n))]
    (hc₀ : 0 < c₀) (hL : 0 ≤ L)
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
    (hsqrt : ∀ n, active n = true → Real.sqrt (c₀ / (d n + 2 : ℝ)) ≤ 1)
    (hcenter : ∀ n, active n = true → center n ≠ 0)
    (hf : ∀ n, active n = true → ∀ᵐ w ∂(volume : Measure ℂ), f n w ≤ ENNReal.ofReal L)
    (hInt : ∀ n, Integrable (fun u : ℂ => ‖u‖ ^ 2) (volume.withDensity (f n)))
    (hSecond : ∀ n, ∫ u : ℂ, ‖u‖ ^ 2 ∂volume.withDensity (f n) ≤ 1)
    (hCalibration : CompletedSection4PressureInput
      (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * (d n + 2))) active
      (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (m n) (profile n) (center n) z)
      m W (completedLiteralConstant c₀ L z))
    (hFinal : CompletedSection4PressureInput
      (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * (d n + 2))) active
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (fun n => n + 1) W (completedLiteralConstant c₀ L z)) :
    CompletedSection4LongBranchData
      (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * (d n + 2))) active
      (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (m n) (profile n) (center n) z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (literalModelLiftedPressure d q m (fun n => volume.withDensity (f n)) profile center z)
      q m (fun n => n + 1) W δ (completedLiteralConstant c₀ L z) where
  constant_nonneg := (completedLiteralConstant_bounds c₀ L z).1
  bandwidth_pos := hW
  base_length_pos := hm0
  reserve := hReserve
  fit := hFit
  count_eq := hCount
  length_eq := hLength
  calibration := hCalibration
  final := hFinal
  cells := by
    have hc := completedLiteral_physical_cell_bounds
      (fun n => iidMeasure (volume.withDensity (f n)) ((n + 1) * (d n + 2))) active
      d (fun n => m n - (d n + 1)) q W profile center z L f
      (fun n => literalCalibrationRows n (d n) (m n))
      (fun n => literalModelPressure n (d n) (m n) (profile n) (center n) z)
      (fun n hn => literalCalibrationRows_measurePreserving n (d n) (m n) (hmN n hn) _)
      (fun _ _ _ => Filter.EventuallyEq.rfl) hc₀ hL hW hd hsqrt hcenter hf
      (fun n _ => hInt n) (fun n _ => hSecond n)
    intro n hn r
    have heq : literalPhysicalLiftedMeanSequence d (fun n => m n - (d n + 1)) q
        (fun n => volume.withDensity (f n)) profile center (fun _ => z) n r =
        literalModelLiftedPressure d q m (fun n => volume.withDensity (f n)) profile center z n r :=
      literalPhysicalLiftedMeanSequence_eq_fullLength active d (fun n => m n - (d n + 1)) q m
        (fun n => volume.withDensity (f n)) profile center (fun _ => z)
        (fun n hn => Nat.add_sub_of_le (hWidth n hn)) n hn r
    have hcell := hc n hn r
    rw [heq] at hcell
    exact hcell
  terminalPressure := fun n r j => literalOpenMeanPressure (d n) (q n * m n + j)
    (volume.withDensity (f n)) (profile n) (center n) z r
  terminal_start := by intros; simp only [Nat.add_zero, literalModelLiftedPressure]
  terminal_end := by
    intro n hn r
    have hparts := balanced_cells_add_remainder (n + 1 - 2 * W n)
      (paperMesoscopicCellLength δ W n)
    have hlen : q n * m n + balancedCellRemainder (n + 1 - 2 * W n)
        (paperMesoscopicCellLength δ W n) = n + 1 - (d n + 1) := by
      rw [hCount n hn, hLength n hn, hd n hn]
      exact hparts
    rw [hlen]
    exact (literalModelPressure_mean n (d n) (n + 1) le_rfl (profile n) hc₀ (hsqrt n hn)
      (center n) z r (volume.withDensity (f n)) hL (complexBallBound_withDensity (hf n hn))
      (hInt n) (hSecond n)).symm
  row_increment := by
    intro n hn r j _
    have h := literal_open_mean_pressure_succ (d n) (W n) (q n * m n + j)
      (hW n hn) (hd n hn) (profile n) hc₀ (hsqrt n hn) (center n) (hcenter n hn) z r
      (f n) hL (hf n hn) (hInt n) (hSecond n)
    apply h.trans
    exact mul_le_mul_of_nonneg_right (completedLiteralConstant_bounds c₀ L z).2.2.2
      (zero_le_one.trans (one_le_paperLogEW_of_bandwidth_pos W n (hW n hn)))

/-- Exact short/long selection for the physical matrix.  No model-identification
premise is passed to the replacement endpoint. -/
theorem literalModel_logPotential_branch
    (d : ℕ → ℕ) (center : ∀ k, Fin (d k + 1)) (b : ∀ k, Fin (d k + 2) → ℂ)
    (shortBranch : ℕ → Bool) (target : ℝ) (z : ℂ)
    (hsize : ∀ k, literalLongActive shortBranch k = true → d k + 2 ≤ k + 1) :
    ∀ k ω, physicalLogPotential (filledLiteralIndicatorMatrix k (d k) (center k) (b k) ω) z =
      branchSelectedTri shortBranch
        (fun k ω => physicalLogPotential
          (filledLiteralIndicatorMatrix k (d k) (center k) (b k) ω) z)
        (literalActiveNormalizedObservable (literalLongActive shortBranch)
          (fun k => literalModelRawDeterminant k (d k) (center k) (b k) z)
          (fun k => k + 1) target) k ω := by
  intro k ω
  cases hb : shortBranch k with
  | true => simp [branchSelectedTri, hb]
  | false =>
      have ha : literalLongActive shortBranch k = true := by simp [literalLongActive, hb]
      simp only [branchSelectedTri, hb, Bool.false_eq_true, ↓reduceIte,
        literalActiveNormalizedObservable, ha,
        filledLiteralIndicatorMatrix, if_pos (hsize k ha), literalIndicatorMatrix_logPotential,
        literalModelRawDeterminant, Nat.cast_add, Nat.cast_one]

/-- Replacement for the actual band matrix, with the Section 4 ledger constructed
by `literalModel_completedSection4Data`. There is no abstract `X`, no `hActual`,
no band-energy assumption, and no user-supplied Section 5 certificate. -/
theorem literal_indicator_replacement_of_identifiedSection4
    (d q m W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ L : ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)]
    (hInt : ∀ n, Integrable (fun u : ℂ => ‖u‖ ^ 2) (ν n))
    (hSecond : ∀ n, ∫ u : ℂ, ‖u‖ ^ 2 ∂ν n ≤ 1)
    (Y : ∀ n, (Fin ((n + 1) * (d n + 2)) → ℂ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hY : ∀ n i j, Measurable fun ω => Y n ω i j)
    (comparisonEnergyBound : ℝ) (hComparisonEnergyBound : 0 ≤ comparisonEnergyBound)
    (hYEnergyInt : ∀ n, Integrable (fun ω => physicalEnergy (Y n ω))
      (iidMeasure (ν n) ((n + 1) * (d n + 2))))
    (hYEnergy : ∀ n, ∫ ω, physicalEnergy (Y n ω)
      ∂iidMeasure (ν n) ((n + 1) * (d n + 2)) ≤ comparisonEnergyBound)
    (shortBranch : ℕ → Bool) (target : ℂ → ℝ) (δ γ : ℝ)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8) (hW : Tendsto W atTop atTop)
    (hLong : ∀ᶠ n in atTop, literalLongActive shortBranch n = true →
      (W n : ℝ) ^ (1 + γ) < (n + 1 : ℝ))
    (hsize : ∀ n, literalLongActive shortBranch n = true → d n + 2 ≤ n + 1)
    (h4 : ∀ᵐ z ∂(volume : Measure ℂ), Nonempty (CompletedSection4LongBranchData
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2))) (literalLongActive shortBranch)
      (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
      (fun n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
      (fun n => literalModelPressure n (d n) (m n) (profile n) (center n) z)
      (fun n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
      (literalModelLiftedPressure d q m ν profile center z) q m (fun n => n + 1) W δ
      (completedLiteralConstant c₀ L z)))
    (h3 :
      let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
        fun n => iidMeasure_isProbability (ν n) _
      ∀ᵐ z ∂(volume : Measure ℂ), Section3IndicatorAnchorsTri
      (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
      (fun n ω => physicalLogPotential
        (filledLiteralIndicatorMatrix n (d n) (center n) (profile n).b ω) z)
      (literalActiveNormalizedObservable (literalLongActive shortBranch)
        (fun n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
        m (target z)) (target z))
    (hLogY :
      let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
        fun n => iidMeasure_isProbability (ν n) _
      ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri
        (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
        (fun n ω => physicalLogPotential (Y n ω) z) (target z)) :
    ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      TendstoInMeasure (Measure.infinitePi (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2))))
        (fun n ω => esdDifference
          (filledLiteralIndicatorMatrix n (d n) (center n) (profile n).b (ω n)) (Y n (ω n)) g)
        atTop 0 := by
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability (ν n) _
  have hXEnergy := fun n => filledLiteralIndicatorMatrix_energy_integrable_and_le_one
    n (d n) (center n) (profile n) hc₀ (ν n) (hInt n) (hSecond n)
  apply replacement_of_completedSection4
    (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
    (fun n ω => filledLiteralIndicatorMatrix n (d n) (center n) (profile n).b ω) Y
    (fun n => filledLiteralIndicatorMatrix_measurable n (d n) (center n) (profile n).b) hY
    (1 + comparisonEnergyBound) (by positivity)
    (fun n => (hXEnergy n).1.add (hYEnergyInt n)) ?_ shortBranch
    (fun z n ω => physicalLogPotential
      (filledLiteralIndicatorMatrix n (d n) (center n) (profile n).b ω) z)
    (fun z n => literalModelCalibrationRaw n (d n) (m n) (center n) (profile n).b z)
    (fun z n => literalModelRawDeterminant n (d n) (center n) (profile n).b z)
    (fun z n => literalModelPressure n (d n) (m n) (profile n) (center n) z)
    (fun z n => literalModelPressure n (d n) (n + 1) (profile n) (center n) z)
    (fun z => literalModelLiftedPressure d q m ν profile center z) q m W target
    (completedLiteralConstant c₀ L) δ γ hδ hδγ hγ hW hLong h4 h3 ?_ hLogY
  · intro n
    rw [integral_add (hXEnergy n).1 (hYEnergyInt n)]
    exact add_le_add (hXEnergy n).2 (hYEnergy n)
  · exact ae_of_all _ fun z =>
      literalModel_logPotential_branch d center (fun n => (profile n).b) shortBranch (target z) z hsize

/-- Finite-index fillers have no effect on the limit of the original, unfilled
paper matrix once the band eventually fits in the circle. -/
theorem literal_indicator_remove_filler
    (d : ℕ → ℕ) (center : ∀ n, Fin (d n + 1)) (b : ∀ n, Fin (d n + 2) → ℂ)
    (μ : Measure (∀ n, Fin ((n + 1) * (d n + 2)) → ℂ))
    (Y : ∀ n, (Fin ((n + 1) * (d n + 2)) → ℂ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (g : ℂ → ℝ) (hsize : ∀ᶠ n in atTop, d n + 2 ≤ n + 1)
    (h : TendstoInMeasure μ
      (fun n ω => esdDifference
        (filledLiteralIndicatorMatrix n (d n) (center n) (b n) (ω n)) (Y n (ω n)) g) atTop 0) :
    TendstoInMeasure μ
      (fun n ω => esdDifference
        (literalIndicatorMatrix n (d n) (center n) (b n) (ω n)) (Y n (ω n)) g) atTop 0 := by
  apply h.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hsize] with n hn
  exact ae_of_all _ fun ω => by simp only [filledLiteralIndicatorMatrix, if_pos hn]

end CircularLawSections56.Section6
