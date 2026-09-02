import CircularLawSections56.Section5.LiteralDeterminantFreshAdapter
import CircularLawSections56.Section5.LiteralIidCellTelescopeAdapter
import Mathlib.Data.List.Rotate

/-!
# Literal cyclic-start adapter

This file removes the arbitrary-start block-split premise left visible in
`LiteralDeterminantFreshAdapter`.  The full cleared-step list is rotated left
by the canonical representative `start.val`.  At each exterior degree the
alternating trace is invariant under this rotation because the two resulting
block products differ by `AB` versus `BA`.  The first `m + 1` rotated rows are
then exactly the genuine fresh rows beginning at `start`; the remaining rows
define the literal cyclic-start outside product.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

/-- The finite index reached after rotating by `start.val` represents
`start + j` in the cyclic group. -/
theorem zmod_finEquiv_rotateIndex_eq_add
    (N : ℕ) [NeZero N] (start : ZMod N) (j : ℕ) :
    ZMod.finEquiv N
        ⟨(j + start.val) % N, Nat.mod_lt _ (NeZero.pos N)⟩ =
      start + (j : ZMod N) := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N =>
      apply ZMod.val_injective
      change (j + start.val) % (N + 1) =
        (start + (j : ZMod (N + 1))).val
      rw [ZMod.val_add, ZMod.val_natCast]
      rw [Nat.add_comm j start.val]
      rw [Nat.add_mod, Nat.mod_eq_of_lt (ZMod.val_lt start)]

/-- Moving a prefix of cleared steps to the end leaves the signed compound
trace unchanged.  Chronological order reverses concatenation, and matrix
trace exchanges the resulting two factors. -/
theorem clearedSignedCompoundTrace_append_comm
    (D : ℕ)
    (xs ys : List (ℂ × Matrix (Fin D) (Fin D) ℂ)) :
    clearedSignedCompoundTrace (xs ++ ys) =
      clearedSignedCompoundTrace (ys ++ xs) := by
  rw [clearedSignedCompoundTrace_eq_sum_trace,
    clearedSignedCompoundTrace_eq_sum_trace]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [clearedCompoundProduct_append, clearedCompoundProduct_append]
  rw [Matrix.trace_mul_comm]

/-- The signed compound trace is invariant under every cyclic list
rotation. -/
theorem clearedSignedCompoundTrace_rotate
    (D : ℕ) (xs : List (ℂ × Matrix (Fin D) (Fin D) ℂ))
    (r : ℕ) :
    clearedSignedCompoundTrace (xs.rotate r) =
      clearedSignedCompoundTrace xs := by
  let k := r % xs.length
  calc
    clearedSignedCompoundTrace (xs.rotate r) =
        clearedSignedCompoundTrace (xs.drop k ++ xs.take k) := by
      rw [List.rotate_eq_drop_append_take_mod]
    _ = clearedSignedCompoundTrace (xs.take k ++ xs.drop k) :=
      clearedSignedCompoundTrace_append_comm D _ _
    _ = clearedSignedCompoundTrace xs := by
      rw [List.take_append_drop]

/-- The literal full cleared-step list, rotated so that its first row is the
cyclic site `start`. -/
def paperIndicatorCyclicRotatedClearedSteps
    (N m : ℕ) [NeZero N]
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ) (start : ZMod N)
    (omega : Fin (N * (m + 2)) → ℂ) :
    List (ℂ × Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :=
  (paperIndicatorClearedSteps N m center profile.b omega z).rotate start.val

@[simp] theorem length_paperIndicatorCyclicRotatedClearedSteps
    (N m : ℕ) [NeZero N]
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ) (start : ZMod N)
    (omega : Fin (N * (m + 2)) → ℂ) :
    (paperIndicatorCyclicRotatedClearedSteps
      N m profile center z start omega).length = N := by
  simp [paperIndicatorCyclicRotatedClearedSteps,
    paperIndicatorClearedSteps, paperShiftedScalarClearedSteps,
    paperCyclicClearedSteps]

/-- Entrywise spelling of the rotated cleared list. -/
theorem getElem_paperIndicatorCyclicRotatedClearedSteps
    (N m : ℕ) [NeZero N]
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ) (start : ZMod N)
    (omega : Fin (N * (m + 2)) → ℂ) (t : Fin N) :
    (paperIndicatorCyclicRotatedClearedSteps
        N m profile center z start omega)[t.val]'(by simp) =
      (paperIndicatorBetaRaw N m profile omega
          (start + (t.val : ZMod N)),
        paperCyclicTransferMatrix N m
          (paperIndicatorBetaRaw N m profile omega)
          (paperIndicatorShiftedInterior N m profile center z omega)
          (start + (t.val : ZMod N))) := by
  unfold paperIndicatorCyclicRotatedClearedSteps
  rw [List.getElem_rotate]
  simp only [paperIndicatorClearedSteps, paperShiftedScalarClearedSteps,
    paperCyclicClearedSteps, List.length_ofFn, List.getElem_ofFn]
  rw [zmod_finEquiv_rotateIndex_eq_add]
  rfl

/-- The rotated list is the canonical finite enumeration of cyclic rows
starting at `start`. -/
theorem paperIndicatorCyclicRotatedClearedSteps_eq_ofFn
    (N m : ℕ) [NeZero N]
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ) (start : ZMod N)
    (omega : Fin (N * (m + 2)) → ℂ) :
    paperIndicatorCyclicRotatedClearedSteps
        N m profile center z start omega =
      List.ofFn (fun t : Fin N =>
        (paperIndicatorBetaRaw N m profile omega
            (start + (t.val : ZMod N)),
          paperCyclicTransferMatrix N m
            (paperIndicatorBetaRaw N m profile omega)
            (paperIndicatorShiftedInterior N m profile center z omega)
            (start + (t.val : ZMod N)))) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    let t : Fin N := ⟨i, by simpa using hright⟩
    simpa only [t, List.getElem_ofFn] using
      (getElem_paperIndicatorCyclicRotatedClearedSteps
        N m profile center z start omega t)

/-- The first `m + 1` rows of the rotated list are exactly Section 4's
genuine fresh exterior rows at the chosen cyclic start. -/
theorem paperIndicatorCyclicRotatedClearedSteps_take_map_eq_freshRows
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ) (start : ZMod N)
    (omega : Fin (N * (m + 2)) → ℂ)
    (q : ExteriorDegree (m + 1)) :
    ((paperIndicatorCyclicRotatedClearedSteps
        N m profile center z start omega).take (m + 1)).map
        (fun step ↦ clearedCompound q.val step.1 step.2) =
      paperIndicatorFreshClearedExteriorRows
        N m profile center z start omega q := by
  rw [paperIndicatorCyclicRotatedClearedSteps_eq_ofFn]
  rw [← Fin.ofFn_take_eq_take_ofFn hsize]
  simp only [List.map_ofFn]
  unfold paperIndicatorFreshClearedExteriorRows
  apply List.ofFn_inj.2
  funext t
  simp only [Function.comp_apply, Fin.take_apply, clearedCompound,
    paperIndicatorFreshRowSite]
  congr 3

/-- The literal outside family complementary to the fresh block beginning at
an arbitrary cyclic start. -/
def paperIndicatorOutsideClearedProductCyclicStart
    (N m : ℕ) [NeZero N]
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ) (start : ZMod N)
    (omega : Fin (N * (m + 2)) → ℂ)
    (q : ExteriorDegree (m + 1)) :
    Matrix (ExteriorIndex (m + 1) q) (ExteriorIndex (m + 1) q) ℂ :=
  clearedCompoundProduct q.val
    ((paperIndicatorCyclicRotatedClearedSteps
      N m profile center z start omega).drop (m + 1))

/-- Full literal block split at an arbitrary cyclic start.  This is the
compatibility premise formerly required by the public arbitrary-start
determinant/FreshZ wrapper. -/
theorem paperIndicator_clearedSignedCompoundTrace_eq_freshBlock_cyclicStart
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ) (start : ZMod N)
    (omega : Fin (N * (m + 2)) → ℂ) :
    clearedSignedCompoundTrace
        (paperIndicatorClearedSteps N m center profile.b omega z) =
      paperIndicatorFreshBlockAlternatingTrace
        N m profile center z start omega
          (paperIndicatorOutsideClearedProductCyclicStart
            N m profile center z start omega) := by
  let rotated := paperIndicatorCyclicRotatedClearedSteps
    N m profile center z start omega
  calc
    clearedSignedCompoundTrace
        (paperIndicatorClearedSteps N m center profile.b omega z) =
        clearedSignedCompoundTrace rotated := by
      exact (clearedSignedCompoundTrace_rotate (m + 1)
        (paperIndicatorClearedSteps N m center profile.b omega z)
        start.val).symm
    _ = paperIndicatorFreshBlockAlternatingTrace
        N m profile center z start omega
          (paperIndicatorOutsideClearedProductCyclicStart
            N m profile center z start omega) := by
      rw [← List.take_append_drop (m + 1) rotated]
      rw [clearedSignedCompoundTrace_append_eq_sum_trace]
      unfold paperIndicatorFreshBlockAlternatingTrace
      apply Finset.sum_congr rfl
      intro q _hq
      unfold paperIndicatorOutsideClearedProductCyclicStart
      rw [show paperIndicatorCyclicRotatedClearedSteps
          N m profile center z start omega = rotated by rfl]
      rw [clearedCompoundProduct_eq_chronologicalProduct_map
        q.val (rotated.take (m + 1))]
      rw [show rotated.take (m + 1) =
          (paperIndicatorCyclicRotatedClearedSteps
            N m profile center z start omega).take (m + 1) by rfl]
      rw [paperIndicatorCyclicRotatedClearedSteps_take_map_eq_freshRows
        N m hsize profile center z start omega q]

namespace PaperIndicatorWeights

/-- Literal determinant-to-FreshZ identity for every cyclic start, with no
external block-split premise. -/
theorem paperIndicatorXSubZI_det_eq_sign_mul_freshZ_cyclicStart
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ) (start : ZMod N)
    (omega : Fin (N * (m + 2)) → ℂ)
    (hβ : ∀ i : ZMod N,
      profile.b (Fin.last (m + 1)) *
        paperIndicatorXi N m omega i (Fin.last (m + 1)) ≠ 0) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      (paperIndicatorXSubZI N m center profile.b omega z).det =
        σ * profile.paperIndicatorFreshZ center z
          (paperIndicatorFreshAtoms N m start omega)
          (paperIndicatorOutsideClearedProductCyclicStart
            N m profile center z start omega) := by
  apply profile.paperIndicatorXSubZI_det_eq_sign_mul_freshZ_of_blockSplit
    N m center z start omega
      (paperIndicatorOutsideClearedProductCyclicStart
        N m profile center z start omega) hβ
  exact paperIndicator_clearedSignedCompoundTrace_eq_freshBlock_cyclicStart
    N m hsize profile center z start omega

/-- Log-norm form of the arbitrary-start determinant/FreshZ identity. -/
theorem log_norm_paperIndicatorXSubZI_det_eq_log_norm_freshZ_cyclicStart
    (N m : ℕ) [NeZero N] (hsize : m + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ) (start : ZMod N)
    (omega : Fin (N * (m + 2)) → ℂ)
    (hβ : ∀ i : ZMod N,
      profile.b (Fin.last (m + 1)) *
        paperIndicatorXi N m omega i (Fin.last (m + 1)) ≠ 0) :
    Real.log ‖(paperIndicatorXSubZI N m center profile.b omega z).det‖ =
      Real.log ‖profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtoms N m start omega)
        (paperIndicatorOutsideClearedProductCyclicStart
          N m profile center z start omega)‖ := by
  obtain ⟨σ, hσ, hdet⟩ :=
    profile.paperIndicatorXSubZI_det_eq_sign_mul_freshZ_cyclicStart
      N m hsize center z start omega hβ
  have hnorm : ‖σ‖ = (1 : ℝ) := by
    rcases hσ with rfl | rfl <;> simp
  rw [hdet, norm_mul, hnorm, one_mul]

end PaperIndicatorWeights

end CircularLawSection4

/-!
## IID transport from a full sample at an arbitrary cyclic start

The coordinate restriction below extracts precisely the fresh atoms beginning
at `start`.  Its law is the literal cell product measure, so both the one-cell
pressure and the terminal chronological-product potential can be transported
to the already proved literal-cell telescope without an analytic side
condition.
-/

open scoped ENNReal MeasureTheory Matrix.Norms.L2Operator
open MeasureTheory

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights Matrix

variable {d : Nat} {c0 C0 : Real}

local instance paperIndicatorSampleMeasureProbabilityCyclicStart
    (N d : Nat) [NeZero N] (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (paperIndicatorSampleMeasure N d nu) := by
  unfold paperIndicatorSampleMeasure
  exact iidMeasure_isProbability nu (N * (d + 2))

local instance paperIndicatorSampleMeasureSigmaFiniteCyclicStart
    (N d : Nat) [NeZero N] (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    SigmaFinite (paperIndicatorSampleMeasure N d nu) := by
  infer_instance

local instance literalCellMeasureSigmaFiniteCyclicStart
    (d : Nat) (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    SigmaFinite (literalPaperExteriorCellMeasure d nu) := by
  unfold literalPaperExteriorCellMeasure
  infer_instance

local instance literalCellMeasureProbabilityCyclicStart
    (d : Nat) (nu : Measure Complex)
    [SigmaFinite nu] [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (literalPaperExteriorCellMeasure d nu) := by
  unfold literalPaperExteriorCellMeasure
  infer_instance

/-- Fresh literal atoms extracted from a full paper-indicator sample, starting
at an arbitrary cyclic site. -/
def paperIndicatorCyclicStartCellAtoms
    (N d : Nat) [NeZero N] (start : ZMod N)
    (omega : Fin (N * (d + 2)) -> Complex) : LiteralPaperCellAtoms d :=
  fun u => omega (paperIndicatorFreshCoordinateIndex N d start u)

/-- The literal exterior cell at an arbitrary cyclic start, viewed directly
as a function of the full flat sample. -/
def paperIndicatorCyclicStartExteriorCell
    (N d : Nat) [NeZero N]
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex) (start : ZMod N)
    (q : ExteriorDegree (d + 1))
    (omega : Fin (N * (d + 2)) -> Complex) :=
  literalPaperExteriorCell profile center z q
    (paperIndicatorCyclicStartCellAtoms N d start omega)

/-- At every cyclic start, restriction to the fresh coordinates transports
the full flat iid law to the literal one-cell atom law. -/
theorem paperIndicatorCyclicStartCellAtoms_measurePreserving
    (N d : Nat) [NeZero N] (start : ZMod N) (hsize : d + 1 <= N)
    (nu : Measure Complex) [SigmaFinite nu] [IsProbabilityMeasure nu] :
    MeasurePreserving (paperIndicatorCyclicStartCellAtoms N d start)
      (paperIndicatorSampleMeasure N d nu)
      (literalPaperExteriorCellMeasure d nu) := by
  change MeasurePreserving
    (fun omega : Fin (N * (d + 2)) -> Complex =>
      fun u => omega (paperIndicatorFreshCoordinateIndex N d start u))
    (iidMeasure nu (N * (d + 2)))
    (Measure.pi (fun _ : FreshAtomIndex (d + 1) => nu))
  exact paperIndicatorFreshCoordinates_measurePreserving
    N d start hsize nu

/-- Pointwise identification of the arbitrary-start literal cell with the
genuine fresh cleared-row chronological product. -/
theorem paperIndicatorCyclicStartExteriorCell_eq_freshClearedProduct
    (N d : Nat) [NeZero N]
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (center : Fin (d + 1)) (z : Complex) (start : ZMod N)
    (q : ExteriorDegree (d + 1))
    (omega : Fin (N * (d + 2)) -> Complex)
    (hbeta : ∀ t : Fin (d + 1),
      paperIndicatorBetaRaw N d profile omega
        (paperIndicatorFreshRowSite N d start t) ≠ 0) :
    paperIndicatorCyclicStartExteriorCell
        N d profile center z start q omega =
      chronologicalProduct (paperIndicatorFreshClearedExteriorRows
        N d profile center z start omega q) := by
  rw [paperIndicatorCyclicStartExteriorCell,
    literalPaperExteriorCell_eq_freshProduct]
  have hatoms : Function.curry
      (paperIndicatorCyclicStartCellAtoms N d start omega) =
      paperIndicatorFreshAtoms N d start omega := by
    symm
    exact paperIndicatorFreshAtoms_eq_coordinateRestriction
      N d start omega
  rw [hatoms]
  congr 1
  apply List.ofFn_inj.2
  funext t
  exact paperIndicatorFreshExteriorRow_eq_clearedCompound_transfer
    N d profile center z start omega q t (hbeta t)

/-- Measure preservation lifts coordinatewise to a finite iid sequence. -/
theorem measurePreserving_iid_apply_cyclicStart
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) (nu : Measure Y)
    [SFinite mu] [SigmaFinite nu]
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (e : X -> Y) (he : MeasurePreserving e mu nu) (n : Nat) :
    MeasurePreserving (fun omega : Fin n -> X => fun i => e (omega i))
      (iidMeasure mu n) (iidMeasure nu n) := by
  rw [iidMeasure_eq_pi, iidMeasure_eq_pi]
  exact measurePreserving_pi (fun _ : Fin n => mu)
    (fun _ : Fin n => nu) (fun _ => he)

/-- Expected-log telescope for the genuine chronological product of literal
paper-indicator exterior cells extracted at any cyclic start from independent
full flat samples.  The error contains exactly the literal projective loss and
the actual one-cell pressure under the ambient sample law. -/
theorem complex_paperIndicatorCyclicStartExteriorCell_expectedLog_telescope
    (N d : Nat) [NeZero N] (hsize : d + 1 <= N)
    (profile : PaperIndicatorWeights (d + 1) c0 C0)
    (hc0 : 0 < c0)
    (hsqrt : Real.sqrt (c0 / (d + 2 : Real)) <= 1)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : Complex)
    (start : ZMod N) (q : ExteriorDegree (d + 1))
    (f : Complex -> ENNReal) [IsProbabilityMeasure (volume.withDensity f)]
    {L : Real} (hL : 0 <= L)
    (hf : ∀ᵐ w ∂(volume : Measure Complex),
      f w <= ENNReal.ofReal L)
    (hsecondInt : Integrable (fun u : Complex => ‖u‖ ^ 2)
      (volume.withDensity f))
    (hsecond : ∫ u : Complex, ‖u‖ ^ 2 ∂(volume.withDensity f) <= 1)
    (cellCount : Nat) :
    let nu := volume.withDensity f
    let mu := paperIndicatorSampleMeasure N d nu
    let C := paperIndicatorCyclicStartExteriorCell
      N d profile center z start q
    let pressure := ∫ omega, Real.log ‖C omega‖ ∂mu
    let error := max (complexLiteralProjectiveCellLoss d c0 L q) pressure
    (cellCount : Real) * (0 - error) <=
        ∫ omega, iidMatrixCellLogPotential C omega ∂iidMeasure mu cellCount ∧
      (∫ omega, iidMatrixCellLogPotential C omega ∂iidMeasure mu cellCount) <=
        (cellCount : Real) * (0 + error) := by
  classical
  dsimp only
  let nu : Measure Complex := volume.withDensity f
  let muFull := paperIndicatorSampleMeasure N d nu
  let muCell := literalPaperExteriorCellMeasure d nu
  let atoms := paperIndicatorCyclicStartCellAtoms N d start
  let Cstart := paperIndicatorCyclicStartExteriorCell
    N d profile center z start q
  let Cliteral := literalPaperExteriorCell profile center z q
  let _ : SigmaFinite nu := inferInstance
  let _ : IsProbabilityMeasure nu := inferInstance
  let _ : SigmaFinite muFull := inferInstance
  let _ : IsProbabilityMeasure muFull := inferInstance
  let _ : SigmaFinite muCell := inferInstance
  let _ : IsProbabilityMeasure muCell := inferInstance
  let _ : Nonempty (ExteriorIndex (d + 1) q) :=
    exteriorIndex_nonempty (d + 1) q
  have hAtoms : MeasurePreserving atoms muFull muCell := by
    simpa only [atoms, muFull, muCell, nu] using
      (paperIndicatorCyclicStartCellAtoms_measurePreserving
        N d start hsize nu)
  have hIid : MeasurePreserving
      (fun omega : Fin cellCount -> (Fin (N * (d + 2)) -> Complex) =>
        fun i => atoms (omega i))
      (iidMeasure muFull cellCount) (iidMeasure muCell cellCount) :=
    measurePreserving_iid_apply_cyclicStart
      muFull muCell atoms hAtoms cellCount
  have hLiteralLog : Integrable
      (fun omega => Real.log ‖Cliteral omega‖) muCell := by
    simpa only [Cliteral, muCell, nu] using
      (complex_literalPaperExteriorCell_logOpNorm_integrable
        (d := d) (c0 := c0) (C0 := C0) (L := L)
        nu (complexBallBound_withDensity hf) hL profile hc0 hsqrt
        center z q hsecondInt hsecond)
  have hPressure :
      (∫ omega, Real.log ‖Cstart omega‖ ∂muFull) =
        ∫ omega, Real.log ‖Cliteral omega‖ ∂muCell := by
    simpa only [Cstart, Cliteral, atoms,
      paperIndicatorCyclicStartExteriorCell,
      Function.comp_apply] using
      (integral_comp_of_measurePreserving hAtoms
        (fun omega => Real.log ‖Cliteral omega‖) hLiteralLog)
  have hGlobal : ∀ n, Integrable
      (iidMatrixCellLogPotential Cliteral) (iidMeasure muCell n) := by
    simpa only [Cliteral, muCell, nu] using
      (complex_literalPaperExteriorCell_iidMatrixCellLogPotential_integrable
        (d := d) (c0 := c0) (C0 := C0) (L := L)
        nu (complexBallBound_withDensity hf) hL profile hc0 hsqrt
        center z q hsecondInt hsecond)
  have hTerminal :
      (∫ omega, iidMatrixCellLogPotential Cstart omega
          ∂iidMeasure muFull cellCount) =
        ∫ omega, iidMatrixCellLogPotential Cliteral omega
          ∂iidMeasure muCell cellCount := by
    calc
      (∫ omega, iidMatrixCellLogPotential Cstart omega
          ∂iidMeasure muFull cellCount) =
          ∫ omega, iidMatrixCellLogPotential Cliteral
            (fun i => atoms (omega i)) ∂iidMeasure muFull cellCount := by
        congr 1
      _ = ∫ omega, iidMatrixCellLogPotential Cliteral omega
          ∂iidMeasure muCell cellCount := by
        simpa only [Function.comp_apply] using
          (integral_comp_of_measurePreserving hIid
            (iidMatrixCellLogPotential Cliteral) (hGlobal cellCount))
  have hSource := complex_literalPaperExteriorCell_expectedLog_telescope
    (d := d) (c0 := c0) (C0 := C0)
    profile hc0 hsqrt center hcenter z q f hL hf
      hsecondInt hsecond cellCount
  rw [hPressure, hTerminal]
  simpa only [Cliteral, muCell, nu] using hSource

end CircularLawSections56.Section5
