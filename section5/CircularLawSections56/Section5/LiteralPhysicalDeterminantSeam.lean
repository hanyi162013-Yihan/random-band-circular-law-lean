import CircularLawSections56.Section5.LiteralAERawSeamAdapter
import CircularLawSections56.Section5.LiteralPhysicalMesoscopicCellAdapter
import CircularLawSections56.Section5.LiteralOutsidePressureBridge
import CircularLawSections56.Section5.LiteralCyclicStartAdapter

/-!
# Absolute L1 seam for the actual cyclic determinant

The outside block is an actual independent IID row product.  Reassembling it
with the fresh coordinates preserves the full flat sample law.  The Section 4
absolute-log estimate therefore applies to the literal cyclic determinant,
with no pointwise positive filler and no additional integrability input.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

set_option maxHeartbeats 1800000

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

variable {d ell : ℕ} {c₀ C₀ : ℝ}

/-- The actual shifted cyclic matrix depends continuously on its atom sample. -/
theorem continuous_paperIndicatorXSubZI
    (N d : ℕ) [NeZero N] (center : Fin (d + 1))
    (b : Fin (d + 2) → ℂ) (z : ℂ) :
    Continuous (fun omega : Fin (N * (d + 2)) → ℂ =>
      paperIndicatorXSubZI N d center b omega z) := by
  classical
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun omega : Fin (N * (d + 2)) → ℂ =>
    (∑ k : Fin (d + 2),
      if j = i - (center.val : ZMod N) + (k.val : ZMod N)
        then b k * omega (paperIndicatorFlatIndex N d i k) else 0) -
      (z • (1 : Matrix (ZMod N) (ZMod N) ℂ)) i j)
  apply Continuous.sub _ continuous_const
  apply continuous_finsetSum
  intro k _
  split_ifs
  · exact continuous_const.mul (continuous_apply _)
  · exact continuous_const

/-- Measurability of the physical raw log determinant, including singular samples. -/
theorem measurable_log_norm_paperIndicatorXSubZI_det
    (N d : ℕ) [NeZero N] (center : Fin (d + 1))
    (b : Fin (d + 2) → ℂ) (z : ℂ) :
    Measurable (fun omega : Fin (N * (d + 2)) → ℂ =>
      Real.log ‖(paperIndicatorXSubZI N d center b omega z).det‖) :=
  Real.measurable_log.comp
    (continuous_paperIndicatorXSubZI N d center b z).matrix_det.norm.measurable

local instance physicalSeamSizeNeZero (ell d : ℕ) : NeZero ((d + 1) + ell) :=
  ⟨by omega⟩

/-- Replace the fresh prefix of a ring by an independent fresh sample, retaining
the independent physical outside rows as the suffix. -/
def literalPhysicalRingSample (ell d : ℕ)
    (sample : LiteralPhysicalOutsideRows ell d ×
      (Fin (((d + 1) + ell) * (d + 2)) → ℂ)) :
    Fin (((d + 1) + ell) * (d + 2)) → ℂ :=
  (paperIndicatorFlatRowsEquiv ((d + 1) + ell) d).symm
    (literalPhysicalCellRowsMeasurableEquiv ell d
      (sample.1, paperIndicatorCyclicStartCellAtoms ((d + 1) + ell) d 0 sample.2))

/-- Physical reassembly gives exactly the full IID ring law. -/
theorem literalPhysicalRingSample_measurePreserving
    (ell d : ℕ) (nu : Measure ℂ) [SigmaFinite nu] [IsProbabilityMeasure nu] :
    MeasurePreserving (literalPhysicalRingSample ell d)
      ((paperIndicatorOpenRowSampleMeasure ell d nu).prod
        (paperIndicatorSampleMeasure ((d + 1) + ell) d nu))
      (paperIndicatorSampleMeasure ((d + 1) + ell) d nu) := by
  let : IsProbabilityMeasure (paperIndicatorRowMeasure d nu) :=
    iidMeasure_isProbability nu (d + 2)
  let : IsProbabilityMeasure (paperIndicatorOpenRowSampleMeasure ell d nu) :=
    iidMeasure_isProbability (paperIndicatorRowMeasure d nu) ell
  let : IsProbabilityMeasure (literalPaperExteriorCellMeasure d nu) := by
    unfold literalPaperExteriorCellMeasure
    infer_instance
  let : IsProbabilityMeasure (paperIndicatorSampleMeasure ((d + 1) + ell) d nu) :=
    iidMeasure_isProbability nu (((d + 1) + ell) * (d + 2))
  have hExtract := (MeasurePreserving.id
    (paperIndicatorOpenRowSampleMeasure ell d nu)).prod
      (paperIndicatorCyclicStartCellAtoms_measurePreserving
        ((d + 1) + ell) d 0 (by omega) nu)
  have hJoin := literalPhysicalCellRows_measurePreserving ell d nu
  have hFlat := (paperIndicatorFlatRows_measurePreserving ((d + 1) + ell) d nu).symm
  exact hFlat.comp (hJoin.comp hExtract)

@[simp]
theorem literalPhysicalRingSample_flatRows
    (sample : LiteralPhysicalOutsideRows ell d ×
      (Fin (((d + 1) + ell) * (d + 2)) → ℂ)) :
    paperIndicatorFlatRowsEquiv ((d + 1) + ell) d
        (literalPhysicalRingSample ell d sample) =
      literalPhysicalCellRowsMeasurableEquiv ell d
        (sample.1, paperIndicatorCyclicStartCellAtoms ((d + 1) + ell) d 0 sample.2) := by
  exact (paperIndicatorFlatRowsEquiv ((d + 1) + ell) d).apply_symm_apply _

/-- The reassembled ring has exactly the intended fresh atoms. -/
theorem literalPhysicalRingSample_freshAtoms
    (sample : LiteralPhysicalOutsideRows ell d ×
      (Fin (((d + 1) + ell) * (d + 2)) → ℂ)) :
    paperIndicatorFreshAtoms ((d + 1) + ell) d 0
        (literalPhysicalRingSample ell d sample) =
      paperIndicatorFreshAtoms ((d + 1) + ell) d 0 sample.2 := by
  rw [paperIndicatorFreshAtoms_eq_coordinateRestriction,
    paperIndicatorFreshAtoms_eq_coordinateRestriction]
  funext t label
  change paperIndicatorXi ((d + 1) + ell) d (literalPhysicalRingSample ell d sample)
      (paperIndicatorFreshRowSite ((d + 1) + ell) d 0 t) (paperFreshLabelSlot d label) = _
  rw [← zmod_finEquiv_castLE_eq_paperIndicatorFreshRowSite_zero
    ((d + 1) + ell) d (by omega)]
  rw [← paperIndicatorFlatRowsEquiv_apply_eq_Xi, literalPhysicalRingSample_flatRows]
  have ht : Fin.castLE (show d + 1 ≤ (d + 1) + ell by omega) t =
      Fin.castAdd ell t := Fin.ext rfl
  rw [ht, literalPhysicalCellRowsMeasurableEquiv_castAdd]
  simp only [literalPaperCellRows, paperFreshLabelSlot, Equiv.apply_symm_apply]
  rfl

/-- The physical outside rows are exactly the suffix, up to the unavoidable
equality of the two finite row-count presentations. -/
theorem literalPhysicalRingSample_suffixRows
    (hsize : d + 1 ≤ (d + 1) + ell)
    (sample : LiteralPhysicalOutsideRows ell d ×
      (Fin (((d + 1) + ell) * (d + 2)) → ℂ)) :
    paperIndicatorSuffixRowsZero ((d + 1) + ell) d hsize
        (literalPhysicalRingSample ell d sample) =
      fun j => sample.1 (Fin.cast (Nat.add_sub_cancel_left (d + 1) ell) j) := by
  funext j
  unfold paperIndicatorSuffixRowsZero
  rw [literalPhysicalRingSample_flatRows]
  have hj : paperIndicatorSuffixRowIndexZero ((d + 1) + ell) d hsize j =
      Fin.natAdd (d + 1) (Fin.cast (Nat.add_sub_cancel_left (d + 1) ell) j) :=
    Fin.ext rfl
  rw [hj, literalPhysicalCellRowsMeasurableEquiv_natAdd]

/-- Changing only the proof-level finite length does not change an open product. -/
theorem paperIndicatorOpenExteriorProduct_comp_finCast
    {n m : ℕ} (h : n = m) (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ) (q : ExteriorDegree (d + 1))
    (rows : Fin m → PaperIndicatorAtomRow d) :
    profile.paperIndicatorOpenExteriorProduct center z q
        (fun j : Fin n => rows (Fin.cast h j)) =
      profile.paperIndicatorOpenExteriorProduct center z q rows := by
  subst m
  rfl

/-- The actual maximum of open exterior pressures on the suffix of a flat ring. -/
def literalPhysicalSuffixPressureMaximum
    (N d : ℕ) [NeZero N] (hsize : d + 1 ≤ N)
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (omega : Fin (N * (d + 2)) → ℂ) : ℝ :=
  finiteSignedMax Finset.univ Finset.univ_nonempty
    (fun q : ExteriorDegree (d + 1) =>
      profile.paperIndicatorOpenPressure center z q
        (paperIndicatorSuffixRowsZero N d hsize omega))

theorem measurable_literalPhysicalSuffixPressureMaximum
    (N d : ℕ) [NeZero N] (hsize : d + 1 ≤ N)
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ) :
    Measurable (literalPhysicalSuffixPressureMaximum N d hsize profile center z) := by
  classical
  have hRows : Measurable (paperIndicatorSuffixRowsZero N d hsize) := by
    apply measurable_pi_lambda
    intro j
    exact (measurable_pi_apply _).comp (paperIndicatorFlatRowsEquiv N d).measurable
  have hq (q : ExteriorDegree (d + 1)) : Measurable (fun omega =>
      profile.paperIndicatorOpenPressure center z q
        (paperIndicatorSuffixRowsZero N d hsize omega)) :=
    (profile.measurable_paperIndicatorOpenPressure center z q _).comp hRows
  unfold literalPhysicalSuffixPressureMaximum finiteSignedMax
  have heq : (fun omega => Finset.univ.sup' Finset.univ_nonempty
      (fun q : ExteriorDegree (d + 1) => profile.paperIndicatorOpenPressure center z q
        (paperIndicatorSuffixRowsZero N d hsize omega))) =
      Finset.univ.sup' Finset.univ_nonempty
        (fun q : ExteriorDegree (d + 1) => fun omega =>
          profile.paperIndicatorOpenPressure center z q
            (paperIndicatorSuffixRowsZero N d hsize omega)) := by
    funext omega
    exact (Finset.sup'_apply Finset.univ_nonempty
      (fun q : ExteriorDegree (d + 1) => fun omega =>
        profile.paperIndicatorOpenPressure center z q
          (paperIndicatorSuffixRowsZero N d hsize omega)) omega).symm
  rw [heq]
  exact Finset.measurable_sup' Finset.univ_nonempty (fun q _ => hq q)

/-- On the genuine nonvanishing event, the frozen family after physical
reassembly is exactly the independent outside open product. -/
theorem literalPhysicalRingSample_outsideFamily
    (hsize : d + 1 ≤ (d + 1) + ell)
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (sample : LiteralPhysicalOutsideRows ell d ×
      (Fin (((d + 1) + ell) * (d + 2)) → ℂ))
    (hbeta : ∀ j : Fin (((d + 1) + ell) - (d + 1)),
      profile.paperIndicatorOpenBeta
        (paperIndicatorSuffixRowsZero ((d + 1) + ell) d hsize
          (literalPhysicalRingSample ell d sample) j) ≠ 0) :
    paperIndicatorOutsideClearedProductZero ((d + 1) + ell) d profile center z
        (literalPhysicalRingSample ell d sample) =
      fun q => literalPhysicalOutsideExteriorProduct profile center z q sample.1 := by
  funext q
  rw [profile.paperIndicatorOutsideClearedProductZero_eq_suffixOpenExteriorProduct
    ((d + 1) + ell) d hsize center z _ q hbeta,
    literalPhysicalRingSample_suffixRows,
    paperIndicatorOpenExteriorProduct_comp_finCast]
  rfl

/-- The actual full-flat cyclic determinant satisfies the absolute Section 4 seam
against the actual suffix pressure maximum.  All integrability is derived from the
bounded atom density and second moment, not assumed for the physical observable. -/
theorem complex_literalPhysicalDeterminant_absLog_seam_withDensity
    (ell d : ℕ)
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (volume.withDensity f))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(volume.withDensity f) ≤ 1) :
    let N := (d + 1) + ell
    let mu := paperIndicatorSampleMeasure N d (volume.withDensity f)
    let gap := fun omega : Fin (N * (d + 2)) → ℂ =>
      |Real.log ‖(paperIndicatorXSubZI N d center profile.b omega z).det‖ -
        literalPhysicalSuffixPressureMaximum N d (by omega) profile center z omega|
    Integrable gap mu ∧
      (∫ omega, gap omega ∂mu) ≤
        paperIsolatedCoefficientLoss d c₀ + complexFreshNegativeBound d L +
          paperFreshPositiveBound d z := by
  classical
  let N := (d + 1) + ell
  have hsize : d + 1 ≤ N := by dsimp [N]; omega
  let nu : Measure ℂ := volume.withDensity f
  let mu := paperIndicatorSampleMeasure N d nu
  let muPast := paperIndicatorOpenRowSampleMeasure ell d nu
  let : IsProbabilityMeasure (paperIndicatorRowMeasure d nu) :=
    iidMeasure_isProbability nu (d + 2)
  let : IsProbabilityMeasure muPast :=
    iidMeasure_isProbability (paperIndicatorRowMeasure d nu) ell
  let B := fun outside : LiteralPhysicalOutsideRows ell d =>
    fun q : ExteriorDegree (d + 1) =>
      literalPhysicalOutsideExteriorProduct profile center z q outside
  have hBcont (q : ExteriorDegree (d + 1)) : Continuous (fun outside => B outside q) :=
    profile.continuous_paperIndicatorOpenExteriorProduct center z q ell
  have hBmeas : ∀ q i j, Measurable (fun outside => B outside q i j) :=
    fun q i j => ((continuous_apply j).comp ((continuous_apply i).comp (hBcont q))).measurable
  have hBnorm : ∀ q, Measurable (fun outside => ‖B outside q‖) :=
    fun q => (hBcont q).norm.measurable
  have hBpos : ∀ᵐ outside ∂muPast, 0 < exteriorFamilyMaxL2OpNorm (B outside) := by
    let q : ExteriorDegree (d + 1) := 0
    let : Nonempty (ExteriorIndex (d + 1) q) := exteriorIndex_nonempty_bridge _ q
    filter_upwards [ae_literalPhysicalOutsideExteriorProduct_isUnit_complex_withDensity
      ell profile hc₀ center hcenter z q hf] with outside hunit
    apply lt_of_lt_of_le (norm_pos_iff.mpr hunit.ne_zero)
    exact Finset.le_sup' (fun r => ‖B outside r‖) (Finset.mem_univ q)
  have hJoint := complex_paperIndicatorFlatFreshZ_rawJointClosure_ae_withDensity
    muPast N d hsize profile hc₀ hsqrt center z 0 B hBpos hBmeas hBnorm
    f hL hf hsecondInt hsecond
  let sourceGap := fun sample : LiteralPhysicalOutsideRows ell d ×
      (Fin (N * (d + 2)) → ℂ) =>
    |Real.log ‖profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtoms N d 0 sample.2) (B sample.1)‖ -
      Real.log (exteriorFamilyMaxL2OpNorm (B sample.1))|
  change Integrable sourceGap (muPast.prod mu) ∧
    (∫ sample, sourceGap sample ∂(muPast.prod mu)) ≤ _ at hJoint
  let gap := fun omega : Fin (N * (d + 2)) → ℂ =>
    |Real.log ‖(paperIndicatorXSubZI N d center profile.b omega z).det‖ -
      literalPhysicalSuffixPressureMaximum N d hsize profile center z omega|
  have hGapMeas : Measurable gap := by
    change Measurable (fun omega => ‖Real.log
      ‖(paperIndicatorXSubZI N d center profile.b omega z).det‖ -
      literalPhysicalSuffixPressureMaximum N d hsize profile center z omega‖)
    exact ((measurable_log_norm_paperIndicatorXSubZI_det N d center profile.b z).sub
      (measurable_literalPhysicalSuffixPressureMaximum N d hsize profile center z)).norm
  have hReassemble : MeasurePreserving (literalPhysicalRingSample ell d)
      (muPast.prod mu) mu := literalPhysicalRingSample_measurePreserving ell d nu
  have hBeta : ∀ᵐ omega ∂mu, ∀ i : ZMod N,
      profile.b (Fin.last (d + 1)) *
        paperIndicatorXi N d omega i (Fin.last (d + 1)) ≠ 0 :=
    ae_paperIndicator_rightEdge_ne_zero_complex_withDensity N d profile.b
      (profile.b_ne_zero hc₀ (Fin.last (d + 1))) hf
  have hSuffix := profile.ae_suffixOpenBeta_ne_zero_and_outsideClearedProductZero_norm_pos_complex_withDensity
    N d hsize hc₀ center hcenter z hf
  have hEq : (gap ∘ literalPhysicalRingSample ell d) =ᵐ[muPast.prod mu] sourceGap := by
    filter_upwards [hReassemble.quasiMeasurePreserving.ae hBeta,
      hReassemble.quasiMeasurePreserving.ae hSuffix] with sample hbeta hsuffix
    dsimp only [Function.comp_def, gap, sourceGap]
    rw [profile.log_norm_paperIndicatorXSubZI_det_eq_log_norm_freshZ_zero
      N d hsize center z _ hbeta]
    rw [show literalPhysicalSuffixPressureMaximum N d hsize profile center z
        (literalPhysicalRingSample ell d sample) =
        Real.log (exteriorFamilyMaxL2OpNorm
          (paperIndicatorOutsideClearedProductZero N d profile center z
            (literalPhysicalRingSample ell d sample))) from
      (profile.log_exteriorFamilyMaxL2OpNorm_outsideZero_eq_finiteSignedMax_suffixOpenPressure
        N d hsize center z _ hsuffix.1 hsuffix.2).symm]
    rw [literalPhysicalRingSample_freshAtoms,
      literalPhysicalRingSample_outsideFamily hsize profile center z sample hsuffix.1]
  have hGapInt : Integrable gap mu :=
    (hReassemble.integrable_comp hGapMeas.aestronglyMeasurable).mp
      (hJoint.1.congr hEq.symm)
  refine ⟨hGapInt, ?_⟩
  calc
    (∫ omega, gap omega ∂mu) =
        ∫ sample, gap (literalPhysicalRingSample ell d sample) ∂(muPast.prod mu) :=
      (integral_comp_of_measurePreserving hReassemble gap hGapInt).symm
    _ = ∫ sample, sourceGap sample ∂(muPast.prod mu) := integral_congr_ae hEq
    _ ≤ _ := hJoint.2

/-- Arbitrary-size form of the physical seam, directly usable at a calibration
length or at the final matrix size. -/
theorem complex_paperIndicatorXSubZI_det_suffixPressure_absLog_seam_withDensity
    (N d : ℕ) [NeZero N] (hsize : d + 1 ≤ N)
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (volume.withDensity f))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(volume.withDensity f) ≤ 1) :
    let mu := paperIndicatorSampleMeasure N d (volume.withDensity f)
    let gap := fun omega : Fin (N * (d + 2)) → ℂ =>
      |Real.log ‖(paperIndicatorXSubZI N d center profile.b omega z).det‖ -
        literalPhysicalSuffixPressureMaximum N d hsize profile center z omega|
    Integrable gap mu ∧
      (∫ omega, gap omega ∂mu) ≤
        paperIsolatedCoefficientLoss d c₀ + complexFreshNegativeBound d L +
          paperFreshPositiveBound d z := by
  obtain ⟨ell, rfl⟩ := Nat.exists_eq_add_of_le hsize
  exact complex_literalPhysicalDeterminant_absLog_seam_withDensity ell d
    profile hc₀ hsqrt center hcenter z f hL hf hsecondInt hsecond

end CircularLawSections56.Section5
