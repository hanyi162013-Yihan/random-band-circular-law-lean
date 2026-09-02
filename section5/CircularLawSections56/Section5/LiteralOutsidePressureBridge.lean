import CircularLawSections56.Section5.LiteralDeterminantFreshAdapter
import CircularLawSections56.Section5.LiteralPressureAdapter
import CircularLawSection4.PaperCompanionInvertibility
import CircularLawSection4.PiRestrictMarginal

/-!
# Literal start-zero outside/open-pressure bridge

This file identifies the frozen exterior family left after removing the first `m + 1`
rows of the closed start-zero trace with the literal open exterior product on the suffix
rows of the same flat sample.  The pointwise identity is stated on the genuine
right-edge-nonzero event: the closed cleared-step representation uses totalized division,
whereas the open row-linear representation is its polynomial extension across the null
right-edge-zero set.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

/-- A chronological product of invertible matrices is invertible.  This small list
lemma lets the pointwise transfer-matrix certificate from Section 4 pass directly to
the literal suffix product. -/
theorem chronologicalProduct_isUnit_of_forall_mem
    {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n]
    (xs : List (Matrix n n R))
    (hxs : ∀ A ∈ xs, IsUnit A) :
    IsUnit (chronologicalProduct xs) := by
  induction xs with
  | nil => simp
  | cons A xs ih =>
      rw [chronologicalProduct_cons]
      exact (ih (fun B hB ↦ hxs B (List.mem_cons_of_mem A hB))).mul
        (hxs A (List.mem_cons_self))

/-- Every exterior degree occurring in the finite family has at least one coordinate. -/
theorem exteriorIndex_nonempty_bridge (D : ℕ) (q : ExteriorDegree D) :
    Nonempty (ExteriorIndex D q) := by
  have hq : q.val ≤ D := Nat.le_of_lt_succ q.isLt
  obtain ⟨s, hs⟩ :
      ((Finset.univ : Finset (Fin D)).powersetCard q.val).Nonempty :=
    Finset.powersetCard_nonempty.2 (by simpa using hq)
  exact ⟨⟨s, (Finset.mem_powersetCard.1 hs).2⟩⟩

/-- Number of rows remaining after the start-zero fresh prefix. -/
def paperIndicatorSuffixRowCountZero (N m : ℕ) : ℕ := N - (m + 1)

/-- The `j`th row after the start-zero fresh prefix, viewed in the original `Fin N`
indexing. -/
def paperIndicatorSuffixRowIndexZero (N m : ℕ) (hsize : m + 1 ≤ N)
    (j : Fin (N - (m + 1))) : Fin N :=
  ⟨m + 1 + j.val, by
    have hj := j.isLt
    omega⟩

@[simp] theorem paperIndicatorSuffixRowIndexZero_val
    (N m : ℕ) (hsize : m + 1 ≤ N)
    (j : Fin (N - (m + 1))) :
    (paperIndicatorSuffixRowIndexZero N m hsize j).val = m + 1 + j.val := rfl

theorem paperIndicatorSuffixRowIndexZero_injective
    (N m : ℕ) (hsize : m + 1 ≤ N) :
    Function.Injective (paperIndicatorSuffixRowIndexZero N m hsize) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [paperIndicatorSuffixRowIndexZero_val] at hval
  omega

/-- Literal complete rows in the suffix following the start-zero fresh prefix. -/
def paperIndicatorSuffixRowsZero
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    (omega : Fin (N * (m + 2)) → ℂ) :
    Fin (N - (m + 1)) →
      PaperIndicatorWeights.PaperIndicatorAtomRow m :=
  fun j => paperIndicatorFlatRowsEquiv N m omega
    (paperIndicatorSuffixRowIndexZero N m hsize j)

@[simp] theorem paperIndicatorSuffixRowsZero_apply
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    (omega : Fin (N * (m + 2)) → ℂ)
    (j : Fin (N - (m + 1))) (k : Fin (m + 2)) :
    paperIndicatorSuffixRowsZero N m hsize omega j k =
      paperIndicatorXi N m omega
        (ZMod.finEquiv N (paperIndicatorSuffixRowIndexZero N m hsize j)) k := by
  exact paperIndicatorFlatRowsEquiv_apply_eq_Xi N m omega
    (paperIndicatorSuffixRowIndexZero N m hsize j) k

/-- Under the full flat IID atom law, suffix-row extraction has exactly the IID
complete-row law of the shorter sample. -/
theorem paperIndicatorSuffixRowsZero_measurePreserving
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    (nu : Measure ℂ) [SigmaFinite nu] [IsProbabilityMeasure nu] :
    MeasurePreserving (paperIndicatorSuffixRowsZero N m hsize)
      (paperIndicatorSampleMeasure N m nu)
      (PaperIndicatorWeights.paperIndicatorOpenRowSampleMeasure
        (N - (m + 1)) m nu) := by
  let muRow := PaperIndicatorWeights.paperIndicatorRowMeasure m nu
  let _ : IsProbabilityMeasure muRow := iidMeasure_isProbability nu (m + 2)
  have hRestrict := measurePreserving_pi_restrict_injective
    (paperIndicatorSuffixRowIndexZero N m hsize)
    (paperIndicatorSuffixRowIndexZero_injective N m hsize) muRow
  have hRestrict' : MeasurePreserving
      (fun rows : Fin N → PaperIndicatorWeights.PaperIndicatorAtomRow m =>
        fun j => rows (paperIndicatorSuffixRowIndexZero N m hsize j))
      (PaperIndicatorWeights.paperIndicatorOpenRowSampleMeasure N m nu)
      (PaperIndicatorWeights.paperIndicatorOpenRowSampleMeasure
        (N - (m + 1)) m nu) := by
    simpa only [PaperIndicatorWeights.paperIndicatorOpenRowSampleMeasure,
      iidMeasure_eq_pi, muRow] using hRestrict
  change MeasurePreserving
    (fun omega => fun j => paperIndicatorFlatRowsEquiv N m omega
      (paperIndicatorSuffixRowIndexZero N m hsize j))
    (paperIndicatorSampleMeasure N m nu)
    (PaperIndicatorWeights.paperIndicatorOpenRowSampleMeasure
      (N - (m + 1)) m nu)
  exact hRestrict'.comp (paperIndicatorFlatRows_measurePreserving N m nu)

/-- Flat presentation of the same suffix sample, obtained by rejoining the extracted
complete rows. -/
def paperIndicatorSuffixFlatSampleZero
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    (omega : Fin (N * (m + 2)) → ℂ) :
    Fin ((N - (m + 1)) * (m + 2)) → ℂ :=
  (paperIndicatorFlatRowsEquiv (N - (m + 1)) m).symm
    (paperIndicatorSuffixRowsZero N m hsize omega)

@[simp] theorem paperIndicatorFlatRowsEquiv_suffixFlatSampleZero
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    (omega : Fin (N * (m + 2)) → ℂ) :
    paperIndicatorFlatRowsEquiv (N - (m + 1)) m
        (paperIndicatorSuffixFlatSampleZero N m hsize omega) =
      paperIndicatorSuffixRowsZero N m hsize omega := by
  exact (paperIndicatorFlatRowsEquiv (N - (m + 1)) m).apply_symm_apply _

/-- When the suffix is nonempty, its rejoined flat presentation has the literal shorter
flat IID atom law used by Section 4's flat `_auto` concentration theorem. -/
theorem paperIndicatorSuffixFlatSampleZero_measurePreserving
    (N m : ℕ) [NeZero N] [NeZero (N - (m + 1))]
    (hsize : m + 1 ≤ N)
    (nu : Measure ℂ) [SigmaFinite nu] [IsProbabilityMeasure nu] :
    MeasurePreserving (paperIndicatorSuffixFlatSampleZero N m hsize)
      (paperIndicatorSampleMeasure N m nu)
      (paperIndicatorSampleMeasure (N - (m + 1)) m nu) := by
  have hRows := paperIndicatorSuffixRowsZero_measurePreserving N m hsize nu
  have hUnflatten := MeasurePreserving.symm
    (paperIndicatorFlatRowsEquiv (N - (m + 1)) m)
    (paperIndicatorFlatRows_measurePreserving (N - (m + 1)) m nu)
  change MeasurePreserving
    (fun omega => (paperIndicatorFlatRowsEquiv (N - (m + 1)) m).symm
      (paperIndicatorSuffixRowsZero N m hsize omega))
    (paperIndicatorSampleMeasure N m nu)
    (paperIndicatorSampleMeasure (N - (m + 1)) m nu)
  exact hUnflatten.comp hRows

/-- Dropping the fresh prefix from a finite `ofFn` list is exactly `ofFn` on the
arithmetic suffix reindexing. -/
theorem drop_ofFn_eq_ofFn_suffix
    {α : Type*} (N k : ℕ) (h : k ≤ N) (f : Fin N → α) :
    (List.ofFn f).drop k =
      List.ofFn (fun j : Fin (N - k) => f ⟨k + j.val, by omega⟩) := by
  apply List.ext_getElem
  · simp [List.length_drop]
  · intro i hi₁ hi₂
    rw [List.getElem_drop, List.getElem_ofFn, List.getElem_ofFn]

namespace PaperIndicatorWeights

@[simp] theorem paperIndicatorFlatOpenPressure_suffixFlatSampleZero
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (omega : Fin (N * (m + 2)) → ℂ) :
    profile.paperIndicatorFlatOpenPressure center z q
        (paperIndicatorSuffixFlatSampleZero N m hsize omega) =
      profile.paperIndicatorOpenPressure center z q
        (paperIndicatorSuffixRowsZero N m hsize omega) := by
  unfold paperIndicatorFlatOpenPressure
  rw [paperIndicatorFlatRowsEquiv_suffixFlatSampleZero]

@[simp] theorem paperIndicatorOpenBeta_suffixRowsZero
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (omega : Fin (N * (m + 2)) → ℂ)
    (j : Fin (N - (m + 1))) :
    profile.paperIndicatorOpenBeta
        (paperIndicatorSuffixRowsZero N m hsize omega j) =
      paperIndicatorBetaRaw N m profile omega
        (ZMod.finEquiv N (paperIndicatorSuffixRowIndexZero N m hsize j)) := by
  simp only [paperIndicatorOpenBeta, paperIndicatorBetaRaw_apply,
    paperIndicatorSuffixRowsZero_apply]

theorem paperIndicatorOpenTransfer_suffixRowsZero
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (omega : Fin (N * (m + 2)) → ℂ)
    (j : Fin (N - (m + 1))) :
    profile.paperIndicatorOpenTransfer center z
        (paperIndicatorSuffixRowsZero N m hsize omega j) =
      paperCyclicTransferMatrix N m
        (paperIndicatorBetaRaw N m profile omega)
        (paperIndicatorShiftedInterior N m profile center z omega)
        (ZMod.finEquiv N (paperIndicatorSuffixRowIndexZero N m hsize j)) := by
  rw [paperCyclicTransferMatrix_eq_rowCompanion]
  unfold paperIndicatorOpenTransfer
  congr 1
  · exact profile.paperIndicatorOpenBeta_suffixRowsZero N m hsize omega j
  · funext i
    simp only [paperIndicatorOpenShiftedInterior,
      paperIndicatorShiftedInterior_apply, paperIndicatorSuffixRowsZero_apply]

/-- Section 4's full-sample right-edge event restricts to every literal suffix row.
No independence argument is repeated here: this is just the deterministic suffix
reindexing of the existing almost-sure event. -/
theorem ae_paperIndicatorOpenBeta_suffixRowsZero_ne_zero_of_complexBallBound
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (ν : Measure ℂ) [SFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ≥0∞} (hν : ComplexBallBound ν L) :
    ∀ᵐ ω ∂paperIndicatorSampleMeasure N m ν,
      ∀ j : Fin (N - (m + 1)),
        profile.paperIndicatorOpenBeta
          (paperIndicatorSuffixRowsZero N m hsize ω j) ≠ 0 := by
  filter_upwards [
    ae_paperIndicatorWeights_rightEdge_ne_zero_of_complexBallBound
      N m profile hc₀ ν hν] with ω hβ
  intro j
  rw [profile.paperIndicatorOpenBeta_suffixRowsZero N m hsize ω j]
  exact hβ _

/-- Complex-ball anti-concentration already makes every flat atom nonzero almost
surely.  The deterministic Section 4 companion certificate therefore yields the same
simultaneous transfer/compound/cleared-compound invertibility package as its
bounded-density specialization, now under the exact hypotheses of the `_auto`
pressure theorem. -/
theorem ae_paperIndicatorTransferMatrix_all_isUnit_of_complexBallBound
    (N m : ℕ) [NeZero N]
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (m + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (ν : Measure ℂ) [SFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ≥0∞} (hν : ComplexBallBound ν L) :
    ∀ᵐ ω ∂paperIndicatorSampleMeasure N m ν,
      ∀ i : ZMod N,
        IsUnit (paperIndicatorTransferMatrix N m center profile.b ω z i) ∧
          ∀ k : ℕ,
            IsUnit (compound k
              (paperIndicatorTransferMatrix N m center profile.b ω z i)) ∧
            IsUnit ((profile.b (Fin.last (m + 1)) *
                paperIndicatorXi N m ω i (Fin.last (m + 1))) •
              compound k
                (paperIndicatorTransferMatrix N m center profile.b ω z i)) := by
  filter_upwards [iidMeasure_ae_all_ne_zero_of_complexBallBound
    ν hν (N * (m + 2))] with ω hω
  intro i
  let x : ZMod N → Fin (m + 2) → ℂ :=
    fun row k ↦ profile.b k * paperIndicatorXi N m ω row k
  have hβ : paperRightEdgeCoefficient m x i ≠ 0 :=
    mul_ne_zero (profile.b_ne_zero hc₀ (Fin.last (m + 1)))
      (hω (paperIndicatorFlatIndex N m i (Fin.last (m + 1))))
  have hα : paperShiftedInteriorCoefficient m center x z i 0 ≠ 0 := by
    simp only [paperShiftedInteriorCoefficient]
    rw [if_neg]
    · simpa [x] using
        (mul_ne_zero (profile.b_ne_zero hc₀ 0)
          (hω (paperIndicatorFlatIndex N m i 0)))
    · exact fun h ↦ hcenter h.symm
  simpa only [paperIndicatorTransferMatrix, x,
    paperRightEdgeCoefficient] using
    (paperShiftedScalarTransfer_all_isUnit N m center x z i hβ hα)

/-- If each cleared exterior suffix row is invertible, so is their literal open
chronological product. -/
theorem paperIndicatorOpenExteriorProduct_suffixRowsZero_isUnit
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (ω : Fin (N * (m + 2)) → ℂ)
    (q : ExteriorDegree (m + 1))
    (hβ : ∀ j : Fin (N - (m + 1)),
      profile.paperIndicatorOpenBeta
        (paperIndicatorSuffixRowsZero N m hsize ω j) ≠ 0)
    (hunit : ∀ j : Fin (N - (m + 1)),
      IsUnit (profile.paperIndicatorOpenBeta
          (paperIndicatorSuffixRowsZero N m hsize ω j) •
        compound q.val (profile.paperIndicatorOpenTransfer center z
          (paperIndicatorSuffixRowsZero N m hsize ω j)))) :
    IsUnit (profile.paperIndicatorOpenExteriorProduct center z q
      (paperIndicatorSuffixRowsZero N m hsize ω)) := by
  rw [profile.paperIndicatorOpenExteriorProduct_eq_clearedCompounds
    center z q (paperIndicatorSuffixRowsZero N m hsize ω) hβ]
  apply chronologicalProduct_isUnit_of_forall_mem
  intro A hA
  simp only [List.mem_ofFn] at hA
  obtain ⟨j, rfl⟩ := hA
  exact hunit j

/-- The mapped cleared steps in the literal suffix are exactly the row-linear open
exterior rows, on the genuine right-edge-nonzero event. -/
theorem paperIndicatorClearedSteps_drop_map_eq_suffixOpenRows
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (omega : Fin (N * (m + 2)) → ℂ)
    (q : ExteriorDegree (m + 1))
    (hβ : ∀ j : Fin (N - (m + 1)),
      profile.paperIndicatorOpenBeta
        (paperIndicatorSuffixRowsZero N m hsize omega j) ≠ 0) :
    ((paperIndicatorClearedSteps N m center profile.b omega z).drop (m + 1)).map
        (fun step => clearedCompound q.val step.1 step.2) =
      List.ofFn (fun j => profile.paperIndicatorOpenExteriorRow center z q
        (paperIndicatorSuffixRowsZero N m hsize omega j)) := by
  unfold paperIndicatorClearedSteps paperShiftedScalarClearedSteps
    paperCyclicClearedSteps
  rw [List.map_drop, List.map_ofFn]
  rw [drop_ofFn_eq_ofFn_suffix N (m + 1) hsize]
  apply List.ofFn_inj.2
  funext j
  change clearedCompound q.val
      (paperIndicatorBetaRaw N m profile omega
        (ZMod.finEquiv N (paperIndicatorSuffixRowIndexZero N m hsize j)))
      (paperCyclicTransferMatrix N m
        (paperIndicatorBetaRaw N m profile omega)
        (paperIndicatorShiftedInterior N m profile center z omega)
        (ZMod.finEquiv N (paperIndicatorSuffixRowIndexZero N m hsize j))) = _
  rw [← profile.paperIndicatorOpenBeta_suffixRowsZero N m hsize omega j,
    ← profile.paperIndicatorOpenTransfer_suffixRowsZero
      N m hsize center z omega j]
  simpa only [clearedCompound] using
    (profile.paperIndicatorOpenExteriorRow_eq_clearedCompound
      center z q (paperIndicatorSuffixRowsZero N m hsize omega j) (hβ j)).symm

/-- The start-zero frozen family is literally the open exterior product on all suffix
rows. -/
theorem paperIndicatorOutsideClearedProductZero_eq_suffixOpenExteriorProduct
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (omega : Fin (N * (m + 2)) → ℂ)
    (q : ExteriorDegree (m + 1))
    (hβ : ∀ j : Fin (N - (m + 1)),
      profile.paperIndicatorOpenBeta
        (paperIndicatorSuffixRowsZero N m hsize omega j) ≠ 0) :
    paperIndicatorOutsideClearedProductZero N m profile center z omega q =
      profile.paperIndicatorOpenExteriorProduct center z q
        (paperIndicatorSuffixRowsZero N m hsize omega) := by
  unfold paperIndicatorOutsideClearedProductZero
    paperIndicatorOpenExteriorProduct
  rw [clearedCompoundProduct_eq_chronologicalProduct_map]
  rw [profile.paperIndicatorClearedSteps_drop_map_eq_suffixOpenRows
    N m hsize center z omega q hβ]

/-- Pointwise positivity of every outside degree from the invertibility of the
corresponding cleared suffix rows. -/
theorem norm_paperIndicatorOutsideClearedProductZero_pos_of_suffix_isUnit
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (ω : Fin (N * (m + 2)) → ℂ)
    (q : ExteriorDegree (m + 1))
    (hβ : ∀ j : Fin (N - (m + 1)),
      profile.paperIndicatorOpenBeta
        (paperIndicatorSuffixRowsZero N m hsize ω j) ≠ 0)
    (hunit : ∀ j : Fin (N - (m + 1)),
      IsUnit (profile.paperIndicatorOpenBeta
          (paperIndicatorSuffixRowsZero N m hsize ω j) •
        compound q.val (profile.paperIndicatorOpenTransfer center z
          (paperIndicatorSuffixRowsZero N m hsize ω j)))) :
    0 < ‖paperIndicatorOutsideClearedProductZero
      N m profile center z ω q‖ := by
  let _ : Nonempty (ExteriorIndex (m + 1) q) :=
    exteriorIndex_nonempty_bridge (m + 1) q
  rw [profile.paperIndicatorOutsideClearedProductZero_eq_suffixOpenExteriorProduct
    N m hsize center z ω q hβ]
  exact norm_pos_iff.mpr
    (profile.paperIndicatorOpenExteriorProduct_suffixRowsZero_isUnit
      N m hsize center z ω q hβ hunit).ne_zero

/-- Under the bounded planar-density hypotheses used by Section 4, the full IID law
simultaneously supplies the genuine suffix `beta != 0` event and positivity of every
degree of the literal outside product. -/
theorem ae_suffixOpenBeta_ne_zero_and_outsideClearedProductZero_norm_pos_complex_withDensity
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (m + 1)) (hcenter : center ≠ 0) (z : ℂ)
    {f : ℂ → ℝ≥0∞} {L : ℝ≥0∞}
    [IsProbabilityMeasure ((volume : Measure ℂ).withDensity f)]
    (hf : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ L) :
    ∀ᵐ ω ∂paperIndicatorSampleMeasure N m
        ((volume : Measure ℂ).withDensity f),
      (∀ j : Fin (N - (m + 1)),
        profile.paperIndicatorOpenBeta
          (paperIndicatorSuffixRowsZero N m hsize ω j) ≠ 0) ∧
      ∀ q : ExteriorDegree (m + 1),
        0 < ‖paperIndicatorOutsideClearedProductZero
          N m profile center z ω q‖ := by
  change ∀ᵐ ω ∂iidMeasure ((volume : Measure ℂ).withDensity f)
      (N * (m + 2)), _
  filter_upwards [
    ae_paperIndicator_rightEdge_ne_zero_complex_withDensity
      N m profile.b (profile.b_ne_zero hc₀ (Fin.last (m + 1))) hf,
    ae_paperIndicatorTransferMatrix_all_isUnit_complex_withDensity
      N m center hcenter profile.b (profile.b_ne_zero hc₀ 0)
        (profile.b_ne_zero hc₀ (Fin.last (m + 1))) z hf] with ω hβall hall
  have hβ : ∀ j : Fin (N - (m + 1)),
      profile.paperIndicatorOpenBeta
        (paperIndicatorSuffixRowsZero N m hsize ω j) ≠ 0 := by
    intro j
    rw [profile.paperIndicatorOpenBeta_suffixRowsZero N m hsize ω j]
    exact hβall _
  refine ⟨hβ, ?_⟩
  intro q
  apply profile.norm_paperIndicatorOutsideClearedProductZero_pos_of_suffix_isUnit
    N m hsize center z ω q hβ
  intro j
  have hj := (hall
    (ZMod.finEquiv N (paperIndicatorSuffixRowIndexZero N m hsize j))).2 q.val |>.2
  rw [profile.paperIndicatorOpenBeta_suffixRowsZero N m hsize ω j,
    profile.paperIndicatorOpenTransfer_suffixRowsZero
      N m hsize center z ω j]
  exact hj

/-- Degreewise form of the literal bridge, now stated in the exact flat-pressure
presentation consumed by Section 4. -/
theorem log_norm_paperIndicatorOutsideClearedProductZero_eq_suffixFlatOpenPressure
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (omega : Fin (N * (m + 2)) → ℂ)
    (q : ExteriorDegree (m + 1))
    (hβ : ∀ j : Fin (N - (m + 1)),
      profile.paperIndicatorOpenBeta
        (paperIndicatorSuffixRowsZero N m hsize omega j) ≠ 0) :
    Real.log ‖paperIndicatorOutsideClearedProductZero
        N m profile center z omega q‖ =
      profile.paperIndicatorFlatOpenPressure center z q
        (paperIndicatorSuffixFlatSampleZero N m hsize omega) := by
  rw [profile.paperIndicatorFlatOpenPressure_suffixFlatSampleZero
    N m hsize center z q omega]
  unfold paperIndicatorOpenPressure
  rw [profile.paperIndicatorOutsideClearedProductZero_eq_suffixOpenExteriorProduct
    N m hsize center z omega q hβ]

/-- Consequently, the logarithm of the maximal frozen-family norm is exactly the
Section 5 finite signed maximum of the literal open pressures of the suffix rows.
Positivity of every family norm remains explicit: it is not implied merely by the
right-edge-nonzero event. -/
theorem log_exteriorFamilyMaxL2OpNorm_outsideZero_eq_finiteSignedMax_suffixOpenPressure
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (omega : Fin (N * (m + 2)) → ℂ)
    (hβ : ∀ j : Fin (N - (m + 1)),
      profile.paperIndicatorOpenBeta
        (paperIndicatorSuffixRowsZero N m hsize omega j) ≠ 0)
    (hpos : ∀ q : ExteriorDegree (m + 1),
      0 < ‖paperIndicatorOutsideClearedProductZero
        N m profile center z omega q‖) :
    Real.log (exteriorFamilyMaxL2OpNorm
        (paperIndicatorOutsideClearedProductZero
          N m profile center z omega)) =
      CircularLawSections56.Section5.finiteSignedMax
        Finset.univ Finset.univ_nonempty
        (fun q : ExteriorDegree (m + 1) =>
          profile.paperIndicatorOpenPressure center z q
            (paperIndicatorSuffixRowsZero N m hsize omega)) := by
  calc
    Real.log (exteriorFamilyMaxL2OpNorm
        (paperIndicatorOutsideClearedProductZero
          N m profile center z omega)) =
        CircularLawSections56.Section5.finiteSignedMax
          Finset.univ Finset.univ_nonempty
          (fun q : ExteriorDegree (m + 1) =>
            Real.log ‖paperIndicatorOutsideClearedProductZero
              N m profile center z omega q‖) :=
      CircularLawSections56.Section5.log_exteriorFamilyMaxL2OpNorm_eq_finiteSignedMax_log_norm
          (paperIndicatorOutsideClearedProductZero
            N m profile center z omega) hpos
    _ = CircularLawSections56.Section5.finiteSignedMax
          Finset.univ Finset.univ_nonempty
          (fun q : ExteriorDegree (m + 1) =>
            profile.paperIndicatorOpenPressure center z q
              (paperIndicatorSuffixRowsZero N m hsize omega)) := by
      congr 1
      funext q
      unfold paperIndicatorOpenPressure
      rw [profile.paperIndicatorOutsideClearedProductZero_eq_suffixOpenExteriorProduct
        N m hsize center z omega q hβ]

/-- Flat-coordinate version of the preceding family equality.  Its observable and
measure now match the input of Section 4's flat `_auto` concentration theorem exactly. -/
theorem log_exteriorFamilyMaxL2OpNorm_outsideZero_eq_finiteSignedMax_suffixFlatOpenPressure
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (omega : Fin (N * (m + 2)) → ℂ)
    (hβ : ∀ j : Fin (N - (m + 1)),
      profile.paperIndicatorOpenBeta
        (paperIndicatorSuffixRowsZero N m hsize omega j) ≠ 0)
    (hpos : ∀ q : ExteriorDegree (m + 1),
      0 < ‖paperIndicatorOutsideClearedProductZero
        N m profile center z omega q‖) :
    Real.log (exteriorFamilyMaxL2OpNorm
        (paperIndicatorOutsideClearedProductZero
          N m profile center z omega)) =
      CircularLawSections56.Section5.finiteSignedMax
        Finset.univ Finset.univ_nonempty
        (fun q : ExteriorDegree (m + 1) =>
          profile.paperIndicatorFlatOpenPressure center z q
            (paperIndicatorSuffixFlatSampleZero N m hsize omega)) := by
  calc
    Real.log (exteriorFamilyMaxL2OpNorm
        (paperIndicatorOutsideClearedProductZero
          N m profile center z omega)) =
        CircularLawSections56.Section5.finiteSignedMax
          Finset.univ Finset.univ_nonempty
          (fun q : ExteriorDegree (m + 1) =>
            Real.log ‖paperIndicatorOutsideClearedProductZero
              N m profile center z omega q‖) :=
      CircularLawSections56.Section5.log_exteriorFamilyMaxL2OpNorm_eq_finiteSignedMax_log_norm
        (paperIndicatorOutsideClearedProductZero
          N m profile center z omega) hpos
    _ = CircularLawSections56.Section5.finiteSignedMax
          Finset.univ Finset.univ_nonempty
          (fun q : ExteriorDegree (m + 1) =>
            profile.paperIndicatorFlatOpenPressure center z q
              (paperIndicatorSuffixFlatSampleZero N m hsize omega)) := by
      congr 1
      funext q
      exact profile.log_norm_paperIndicatorOutsideClearedProductZero_eq_suffixFlatOpenPressure
        N m hsize center z omega q hβ

/-- Almost-sure literal outside-scale identification on the full IID sample.  This
packages the null-set denominator issue and degreewise norm positivity, leaving exactly
the flat suffix finite maximum consumed by the Section 4 `_auto` fluctuation theorem. -/
theorem ae_log_exteriorFamilyMaxL2OpNorm_outsideZero_eq_finiteSignedMax_suffixFlatOpenPressure_complex_withDensity
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (m + 1)) (hcenter : center ≠ 0) (z : ℂ)
    {f : ℂ → ℝ≥0∞} {L : ℝ≥0∞}
    [IsProbabilityMeasure ((volume : Measure ℂ).withDensity f)]
    (hf : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ L) :
    ∀ᵐ ω ∂paperIndicatorSampleMeasure N m
        ((volume : Measure ℂ).withDensity f),
      Real.log (exteriorFamilyMaxL2OpNorm
          (paperIndicatorOutsideClearedProductZero
            N m profile center z ω)) =
        CircularLawSections56.Section5.finiteSignedMax
          Finset.univ Finset.univ_nonempty
          (fun q : ExteriorDegree (m + 1) ↦
            profile.paperIndicatorFlatOpenPressure center z q
              (paperIndicatorSuffixFlatSampleZero N m hsize ω)) := by
  filter_upwards [
    profile.ae_suffixOpenBeta_ne_zero_and_outsideClearedProductZero_norm_pos_complex_withDensity
      N m hsize hc₀ center hcenter z hf] with ω h
  exact profile.log_exteriorFamilyMaxL2OpNorm_outsideZero_eq_finiteSignedMax_suffixFlatOpenPressure
    N m hsize center z ω h.1 h.2

end PaperIndicatorWeights

end CircularLawSection4
