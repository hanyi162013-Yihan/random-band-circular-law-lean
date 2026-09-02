import CircularLawSection4.PaperPeriodicIdentityClosed
import CircularLawSection4.IIDCoordinateFacts
import CircularLawSection4.PaperIndicatorWeights

/-!
# The paper's scalar random band matrix on a finite coordinate sample space

This file specializes the closed periodic determinant identity to the literal
finite coordinate model used by the paper.  A sample

`omega : Fin (N * (m + 2)) -> C`

contains one scalar atom for every cyclic row and every one of the `m + 2`
band coefficients.  The equivalence below makes the flattening convention
explicit.  No probability law is needed for the pointwise determinant
identity; the only remaining pointwise hypothesis is nonvanishing of every
right-edge atom (and of its deterministic weight).
-/

open scoped ENNReal MeasureTheory Matrix
open MeasureTheory

noncomputable section

namespace CircularLawSection4

open Matrix

/-- Explicit flattening of the paper's row/coefficient coordinates into a
single finite sample vector.  The coefficient coordinate varies fastest. -/
def paperIndicatorIndexEquiv (N m : ℕ) [NeZero N] :
    Fin (N * (m + 2)) ≃ ZMod N × Fin (m + 2) :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr (ZMod.finEquiv N).toEquiv (Equiv.refl _))

/-- The flat coordinate carrying the atom in cyclic row `i` and band slot
`k`. -/
def paperIndicatorFlatIndex (N m : ℕ) [NeZero N]
    (i : ZMod N) (k : Fin (m + 2)) : Fin (N * (m + 2)) :=
  (paperIndicatorIndexEquiv N m).symm (i, k)

@[simp] theorem paperIndicatorIndexEquiv_flatIndex
    (N m : ℕ) [NeZero N] (i : ZMod N) (k : Fin (m + 2)) :
    paperIndicatorIndexEquiv N m (paperIndicatorFlatIndex N m i k) = (i, k) :=
  Equiv.apply_symm_apply _ _

/-- The manuscript atom `xi_{i,k}` read from a flat finite sample. -/
def paperIndicatorXi (N m : ℕ) [NeZero N]
    (ω : Fin (N * (m + 2)) → ℂ) : ZMod N → Fin (m + 2) → ℂ :=
  fun i k ↦ ω (paperIndicatorFlatIndex N m i k)

@[simp] theorem paperIndicatorXi_apply
    (N m : ℕ) [NeZero N] (ω : Fin (N * (m + 2)) → ℂ)
    (i : ZMod N) (k : Fin (m + 2)) :
    paperIndicatorXi N m ω i k = ω (paperIndicatorFlatIndex N m i k) := rfl

/-- The paper's unshifted random cyclic band matrix `X_N(omega)`, with
deterministic profile `b_k` and random atoms `xi_{i,k}(omega)`. -/
def paperIndicatorX (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (b : Fin (m + 2) → ℂ) (ω : Fin (N * (m + 2)) → ℂ) :
    Matrix (ZMod N) (ZMod N) ℂ :=
  paperScalarBandMatrix N m center
    (fun i k ↦ b k * paperIndicatorXi N m ω i k)

/-- The literal shifted random matrix `X_N(omega) - z I_N`. -/
def paperIndicatorXSubZI (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (b : Fin (m + 2) → ℂ) (ω : Fin (N * (m + 2)) → ℂ) (z : ℂ) :
    Matrix (ZMod N) (ZMod N) ℂ :=
  paperIndicatorX N m center b ω - z • (1 : Matrix (ZMod N) (ZMod N) ℂ)

/-- The shifted finite-coordinate model is definitionally the generic literal
shifted scalar band matrix after substituting the coordinate projections. -/
theorem paperIndicatorXSubZI_eq_paperShiftedScalarBandMatrix
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (b : Fin (m + 2) → ℂ) (ω : Fin (N * (m + 2)) → ℂ) (z : ℂ) :
    paperIndicatorXSubZI N m center b ω z =
      paperShiftedScalarBandMatrix N m center
        (fun i k ↦ b k * paperIndicatorXi N m ω i k) z := rfl

/-- The denominator-cleared exterior steps associated with the finite sample
`omega`. -/
def paperIndicatorClearedSteps
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (b : Fin (m + 2) → ℂ) (ω : Fin (N * (m + 2)) → ℂ) (z : ℂ) :
    List (ℂ × Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :=
  paperShiftedScalarClearedSteps N m center
    (fun i k ↦ b k * paperIndicatorXi N m ω i k) z

/-- Pointwise closed Section 4 determinant identity for the paper's finite
coordinate random matrix.  All random variables have been replaced by actual
coordinate projections on `omega`; only right-edge nonvanishing is assumed. -/
theorem paperIndicatorXSubZI_det_eq_clearedSignedCompoundTrace
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (b : Fin (m + 2) → ℂ) (ω : Fin (N * (m + 2)) → ℂ) (z : ℂ)
    (hβ : ∀ i : ZMod N,
      b (Fin.last (m + 1)) *
          paperIndicatorXi N m ω i (Fin.last (m + 1)) ≠ 0) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      (paperIndicatorXSubZI N m center b ω z).det =
        σ * clearedSignedCompoundTrace
          (paperIndicatorClearedSteps N m center b ω z) := by
  rw [paperIndicatorXSubZI_eq_paperShiftedScalarBandMatrix]
  exact paperXSubZI_det_eq_clearedSignedCompoundTrace
    N m center b (paperIndicatorXi N m ω) z hβ

/-- The finite product law on all row/coefficient atoms of the paper's
indicator model. -/
noncomputable def paperIndicatorSampleMeasure
    (N m : ℕ) [NeZero N] (ν : Measure ℂ) [SFinite ν] :
    Measure (Fin (N * (m + 2)) → ℂ) :=
  iidMeasure ν (N * (m + 2))

/-- Under the paper's positive deterministic variance profile and an atom law
satisfying the planar small-ball bound, all right-edge coefficients are
simultaneously nonzero almost surely. -/
theorem ae_paperIndicatorWeights_rightEdge_ne_zero_of_complexBallBound
    (N m : ℕ) [NeZero N]
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (ν : Measure ℂ) [SFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ≥0∞} (hν : ComplexBallBound ν L) :
    ∀ᵐ ω ∂paperIndicatorSampleMeasure N m ν,
      ∀ i : ZMod N,
        profile.b (Fin.last (m + 1)) *
            paperIndicatorXi N m ω i (Fin.last (m + 1)) ≠ 0 := by
  filter_upwards [iidMeasure_ae_all_ne_zero_of_complexBallBound
    ν hν (N * (m + 2))] with ω hω
  intro i
  exact mul_ne_zero (profile.b_ne_zero hc₀ (Fin.last (m + 1)))
    (hω (paperIndicatorFlatIndex N m i (Fin.last (m + 1))))

/-- Almost-sure closed determinant/exterior identity for the actual indicator
profile and an arbitrary complex atom law with the required planar small-ball
bound. -/
theorem ae_paperIndicatorWeights_XSubZI_det_eq_clearedSignedCompoundTrace
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (z : ℂ)
    (ν : Measure ℂ) [SFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ≥0∞} (hν : ComplexBallBound ν L) :
    ∀ᵐ ω ∂paperIndicatorSampleMeasure N m ν,
      ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
        (paperIndicatorXSubZI N m center profile.b ω z).det =
          σ * clearedSignedCompoundTrace
            (paperIndicatorClearedSteps N m center profile.b ω z) := by
  filter_upwards [
    ae_paperIndicatorWeights_rightEdge_ne_zero_of_complexBallBound
      N m profile hc₀ ν hν] with ω hβ
  exact paperIndicatorXSubZI_det_eq_clearedSignedCompoundTrace
    N m center profile.b ω z hβ

/-- Under a bounded planar density, every right-edge atom (and hence every
weighted right-edge coefficient with nonzero deterministic weight) is nonzero
simultaneously almost surely. -/
theorem ae_paperIndicator_rightEdge_ne_zero_complex_withDensity
    (N m : ℕ) [NeZero N]
    (b : Fin (m + 2) → ℂ)
    (hb : b (Fin.last (m + 1)) ≠ 0)
    {f : ℂ → ℝ≥0∞} {L : ℝ≥0∞}
    [IsProbabilityMeasure ((volume : Measure ℂ).withDensity f)]
    (hf : ∀ᵐ z ∂(volume : Measure ℂ), f z ≤ L) :
    ∀ᵐ ω ∂iidMeasure ((volume : Measure ℂ).withDensity f) (N * (m + 2)),
      ∀ i : ZMod N,
        b (Fin.last (m + 1)) *
            paperIndicatorXi N m ω i (Fin.last (m + 1)) ≠ 0 := by
  filter_upwards [iidMeasure_ae_all_ne_zero_complex_withDensity
    hf (N * (m + 2))] with ω hω
  intro i
  exact mul_ne_zero hb (hω (paperIndicatorFlatIndex N m i (Fin.last (m + 1))))

/-- Almost-sure form of the closed determinant identity for IID complex atoms
with bounded planar density. -/
theorem ae_paperIndicatorXSubZI_det_eq_clearedSignedCompoundTrace_complex_withDensity
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (b : Fin (m + 2) → ℂ)
    (hb : b (Fin.last (m + 1)) ≠ 0)
    (z : ℂ) {f : ℂ → ℝ≥0∞} {L : ℝ≥0∞}
    [IsProbabilityMeasure ((volume : Measure ℂ).withDensity f)]
    (hf : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ L) :
    ∀ᵐ ω ∂iidMeasure ((volume : Measure ℂ).withDensity f) (N * (m + 2)),
      ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
        (paperIndicatorXSubZI N m center b ω z).det =
          σ * clearedSignedCompoundTrace
            (paperIndicatorClearedSteps N m center b ω z) := by
  filter_upwards [ae_paperIndicator_rightEdge_ne_zero_complex_withDensity
    N m b hb hf] with ω hβ
  exact paperIndicatorXSubZI_det_eq_clearedSignedCompoundTrace
    N m center b ω z hβ

/-- Real IID atoms embedded into `C`, using the same finite flattening as the
complex model. -/
def paperIndicatorXiOfReal (N m : ℕ) [NeZero N]
    (ω : Fin (N * (m + 2)) → ℝ) : ZMod N → Fin (m + 2) → ℂ :=
  fun i k ↦ (ω (paperIndicatorFlatIndex N m i k) : ℂ)

@[simp] theorem paperIndicatorXiOfReal_apply
    (N m : ℕ) [NeZero N] (ω : Fin (N * (m + 2)) → ℝ)
    (i : ZMod N) (k : Fin (m + 2)) :
    paperIndicatorXiOfReal N m ω i k =
      (ω (paperIndicatorFlatIndex N m i k) : ℂ) := rfl

/-- The paper's unshifted matrix when the IID atoms are real and then embedded
canonically in `C`. -/
def paperIndicatorXOfReal (N m : ℕ) [NeZero N]
    (center : Fin (m + 1)) (b : Fin (m + 2) → ℂ)
    (ω : Fin (N * (m + 2)) → ℝ) : Matrix (ZMod N) (ZMod N) ℂ :=
  paperScalarBandMatrix N m center
    (fun i k ↦ b k * paperIndicatorXiOfReal N m ω i k)

/-- The real-atom model's literal `X_N(omega) - z I_N`. -/
def paperIndicatorXSubZIOfReal (N m : ℕ) [NeZero N]
    (center : Fin (m + 1)) (b : Fin (m + 2) → ℂ)
    (ω : Fin (N * (m + 2)) → ℝ) (z : ℂ) :
    Matrix (ZMod N) (ZMod N) ℂ :=
  paperIndicatorXOfReal N m center b ω - z •
    (1 : Matrix (ZMod N) (ZMod N) ℂ)

/-- Cleared companion steps for the real-atom model. -/
def paperIndicatorClearedStepsOfReal
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (b : Fin (m + 2) → ℂ) (ω : Fin (N * (m + 2)) → ℝ) (z : ℂ) :
    List (ℂ × Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :=
  paperShiftedScalarClearedSteps N m center
    (fun i k ↦ b k * paperIndicatorXiOfReal N m ω i k) z

/-- Pointwise closed determinant identity for real atoms embedded in `C`. -/
theorem paperIndicatorXSubZIOfReal_det_eq_clearedSignedCompoundTrace
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    (b : Fin (m + 2) → ℂ) (ω : Fin (N * (m + 2)) → ℝ) (z : ℂ)
    (hβ : ∀ i : ZMod N,
      b (Fin.last (m + 1)) *
          paperIndicatorXiOfReal N m ω i (Fin.last (m + 1)) ≠ 0) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
      (paperIndicatorXSubZIOfReal N m center b ω z).det =
        σ * clearedSignedCompoundTrace
          (paperIndicatorClearedStepsOfReal N m center b ω z) := by
  change ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
    (paperShiftedScalarBandMatrix N m center
      (fun i k ↦ b k * paperIndicatorXiOfReal N m ω i k) z).det =
      σ * clearedSignedCompoundTrace
        (paperShiftedScalarClearedSteps N m center
          (fun i k ↦ b k * paperIndicatorXiOfReal N m ω i k) z)
  exact paperXSubZI_det_eq_clearedSignedCompoundTrace
    N m center b (paperIndicatorXiOfReal N m ω) z hβ

/-- Product law for the flat real atom vector. -/
noncomputable def paperIndicatorRealSampleMeasure
    (N m : ℕ) [NeZero N] (ν : Measure ℝ) [SFinite ν] :
    Measure (Fin (N * (m + 2)) → ℝ) :=
  iidMeasure ν (N * (m + 2))

/-- A real one-coordinate interval bound and the positive indicator profile
make every complexified right-edge coefficient nonzero almost surely. -/
theorem ae_paperIndicatorWeights_rightEdge_ne_zero_of_realIntervalBound
    (N m : ℕ) [NeZero N]
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (ν : Measure ℝ) [SFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ≥0∞} (hν : RealIntervalBound ν L) :
    ∀ᵐ ω ∂paperIndicatorRealSampleMeasure N m ν,
      ∀ i : ZMod N,
        profile.b (Fin.last (m + 1)) *
            paperIndicatorXiOfReal N m ω i (Fin.last (m + 1)) ≠ 0 := by
  filter_upwards [iidMeasure_ae_all_ne_zero_of_realIntervalBound
    ν hν (N * (m + 2))] with ω hω
  intro i
  exact mul_ne_zero (profile.b_ne_zero hc₀ (Fin.last (m + 1))) <|
    Complex.ofReal_ne_zero.mpr
      (hω (paperIndicatorFlatIndex N m i (Fin.last (m + 1))))

/-- Almost-sure determinant/exterior identity for real atoms satisfying the
one-coordinate interval bound. -/
theorem ae_paperIndicatorWeights_XSubZIOfReal_det_eq_clearedSignedCompoundTrace
    (N m : ℕ) [NeZero N] (center : Fin (m + 1))
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (z : ℂ)
    (ν : Measure ℝ) [SFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ≥0∞} (hν : RealIntervalBound ν L) :
    ∀ᵐ ω ∂paperIndicatorRealSampleMeasure N m ν,
      ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧
        (paperIndicatorXSubZIOfReal N m center profile.b ω z).det =
          σ * clearedSignedCompoundTrace
            (paperIndicatorClearedStepsOfReal N m center profile.b ω z) := by
  filter_upwards [
    ae_paperIndicatorWeights_rightEdge_ne_zero_of_realIntervalBound
      N m profile hc₀ ν hν] with ω hβ
  exact paperIndicatorXSubZIOfReal_det_eq_clearedSignedCompoundTrace
    N m center profile.b ω z hβ

/-- A bounded real density likewise makes all complexified right-edge
coefficients nonzero simultaneously almost surely. -/
theorem ae_paperIndicator_rightEdge_ne_zero_real_withDensity
    (N m : ℕ) [NeZero N]
    (b : Fin (m + 2) → ℂ)
    (hb : b (Fin.last (m + 1)) ≠ 0)
    {f : ℝ → ℝ≥0∞} {L : ℝ≥0∞}
    [IsProbabilityMeasure ((volume : Measure ℝ).withDensity f)]
    (hf : ∀ᵐ x ∂(volume : Measure ℝ), f x ≤ L) :
    ∀ᵐ ω ∂iidMeasure ((volume : Measure ℝ).withDensity f) (N * (m + 2)),
      ∀ i : ZMod N,
        b (Fin.last (m + 1)) *
            paperIndicatorXiOfReal N m ω i (Fin.last (m + 1)) ≠ 0 := by
  filter_upwards [iidMeasure_ae_all_ne_zero_real_withDensity
    hf (N * (m + 2))] with ω hω
  intro i
  exact mul_ne_zero hb <| Complex.ofReal_ne_zero.mpr
    (hω (paperIndicatorFlatIndex N m i (Fin.last (m + 1))))

end CircularLawSection4
