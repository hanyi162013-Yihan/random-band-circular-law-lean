import TaoVuReplacement.EmpiricalSpectrum
import TaoVuReplacement.MatrixScaling
import TaoVuReplacement.LogKernelBounds
import TaoVuReplacement.LogKernelGreen
import TaoVuReplacement.LaplacianSupport
import TaoVuReplacement.ProbabilityModes
import TaoVuReplacement.RandomMatrixMeasurability
import TaoVuReplacement.VagueConvergence

/-!
# Tao--Vu's replacement principle (Theorem 2.1)

This file assembles the deterministic spectral identities, the local
logarithmic-potential estimate, Tao--Vu Lemma 3.1, and the Green--Girko
identity into the two modes of Theorem 2.1 of arXiv:0807.4898v5.

The definitions and lemmas in the first section are the algebraic and
measure-theoretic bridges used by both modes.  In particular, the equality
between a logarithmic determinant and the empirical logarithmic potential
is asserted only away from the finite spectrum.  It is then upgraded to a
planar almost-everywhere equality; this keeps Lean's totalized convention
`Real.log 0 = 0` from changing the mathematical statement.
-/

open Filter Set MeasureTheory
open InnerProductSpace Laplacian
open scoped BigOperators ContDiff ENNReal Topology

noncomputable section

namespace TaoVuReplacement

/-! ## Logarithmic-potential bridges -/

/-- The logarithmic potential of the ESD of the normalized matrix
`(k+1)^{-1/2} A`, in the sign convention of Tao--Vu §3.6:

`U_A(z) = (1/(k+1)) sum_i log |lambda_i((k+1)^{-1/2} A) - z|`.
-/
def matrixLogPotential {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (z : ℂ) : ℝ :=
  realEsdTest (normalizedMatrix A) (fun lambda ↦ Real.log ‖lambda - z‖)

/-- Determinant of the shifted normalized matrix.  Naming it separately
keeps the faithful non-singularity guard in Theorem 2.1(ii) readable. -/
def normalizedShiftDet {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (z : ℂ) : ℂ :=
  (normalizedMatrix A -
    z • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)).det

/-- Source-faithful probability semantics for “the two determinants are
nonzero with probability `1-o(1)`” in Theorem 2.1(ii). -/
def DeterminantsEventuallyNonzeroInProbability
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (A B : ∀ k : ℕ,
      Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop :=
  ∀ᵐ z ∂(volume : Measure ℂ),
    Tendsto (fun k ↦ P {omega |
      normalizedShiftDet (A k omega) z = 0 ∨
        normalizedShiftDet (B k omega) z = 0}) atTop (𝓝 0)

/-- Source-faithful almost-sure semantics for “eventually both determinants
are nonzero” in Theorem 2.1(ii). -/
def DeterminantsEventuallyNonzeroAlmostSurely
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (A B : ∀ k : ℕ,
      Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop :=
  ∀ᵐ z ∂(volume : Measure ℂ), ∀ᵐ omega ∂P,
    ∀ᶠ k in atTop,
      normalizedShiftDet (A k omega) z ≠ 0 ∧
        normalizedShiftDet (B k omega) z ≠ 0

/-- A fixed matrix has a nonzero shifted determinant for planar almost every
spectral parameter: the only exceptions are its finitely many eigenvalues. -/
theorem ae_normalizedShiftDet_ne_zero {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    ∀ᵐ z ∂(volume : Measure ℂ), normalizedShiftDet A z ≠ 0 := by
  let s : Set ℂ :=
    ((eigenvalueMultiset (normalizedMatrix A)).toFinset : Set ℂ)
  have hsnull : (volume : Measure ℂ) s = 0 :=
    (eigenvalueMultiset (normalizedMatrix A)).toFinset.finite_toSet.measure_zero
      (volume : Measure ℂ)
  rw [ae_iff]
  apply measure_mono_null (t := s) _ hsnull
  intro z hz
  by_contra hz_not_mem
  apply hz
  unfold normalizedShiftDet
  rw [det_sub_scalar_eq_prod_eigenvalue_sub]
  apply Multiset.prod_ne_zero
  intro hzero
  rcases Multiset.mem_map.mp hzero with ⟨lambda, hlambda, hlambda_sub⟩
  have hlambda_eq : lambda = z := sub_eq_zero.mp hlambda_sub
  subst lambda
  exact hz_not_mem (by simpa [s] using hlambda)

/-- Joint measurability of the shifted normalized determinant. -/
theorem measurable_normalizedShiftDet_joint_of_entrywise
    {Omega : Type*} [MeasurableSpace Omega] {k : ℕ}
    (A : Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ i j, Measurable fun omega ↦ A omega i j) :
    Measurable fun p : ℂ × Omega ↦ normalizedShiftDet (A p.2) p.1 := by
  apply measurable_det_of_entrywise
  intro i j
  change Measurable fun p : ℂ × Omega ↦
    inverseSqrtDimension (Fin (k + 1)) * A p.2 i j -
      p.1 * (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j
  exact ((hA i j).comp measurable_snd).const_mul _ |>.sub
    (measurable_fst.mul_const _)

/-- Fubini upgrades the finite-spectrum fact to random matrices: for almost
every deterministic `z`, the shifted determinant is nonzero almost surely. -/
theorem ae_ae_normalizedShiftDet_ne_zero_of_entrywise
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsFiniteMeasure P]
    {k : ℕ}
    (A : Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ i j, Measurable fun omega ↦ A omega i j) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ᵐ omega ∂P,
      normalizedShiftDet (A omega) z ≠ 0 := by
  have hzero : MeasurableSet {p : ℂ × Omega |
      normalizedShiftDet (A p.2) p.1 = 0} := by
    convert (measurableSet_singleton (0 : ℂ)).preimage
      (measurable_normalizedShiftDet_joint_of_entrywise A hA) using 1 <;>
      ext p <;> simp
  have hmeas : MeasurableSet {p : ℂ × Omega |
      normalizedShiftDet (A p.2) p.1 ≠ 0} := by
    change MeasurableSet ({p : ℂ × Omega |
      normalizedShiftDet (A p.2) p.1 = 0}ᶜ)
    exact hzero.compl
  apply (Measure.ae_ae_comm hmeas).mpr
  exact Filter.Eventually.of_forall fun omega ↦ ae_normalizedShiftDet_ne_zero (A omega)

/-- One common planar full-measure set works for all matrix sizes and both
sequences; on it, every shifted determinant is almost surely nonzero. -/
theorem ae_ae_all_normalizedShiftDets_ne_zero_of_entrywise
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsFiniteMeasure P]
    (A B : ∀ k : ℕ,
      Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ k i j, Measurable fun omega ↦ A k omega i j)
    (hB : ∀ k i j, Measurable fun omega ↦ B k omega i j) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ k : ℕ, ∀ᵐ omega ∂P,
      normalizedShiftDet (A k omega) z ≠ 0 ∧
        normalizedShiftDet (B k omega) z ≠ 0 := by
  filter_upwards [ae_all_iff.mpr fun k ↦
      ae_ae_normalizedShiftDet_ne_zero_of_entrywise P (A k) (hA k),
    ae_all_iff.mpr fun k ↦
      ae_ae_normalizedShiftDet_ne_zero_of_entrywise P (B k) (hB k)]
      with z hzA hzB
  intro k
  filter_upwards [hzA k, hzB k] with omega hAk hBk
  exact ⟨hAk, hBk⟩

/-- Thus the probability non-singularity guard in the paper is automatic
from entrywise measurability (and in fact each bad-event probability is
identically zero on one planar full-measure set). -/
theorem determinantsEventuallyNonzeroInProbability_of_entrywise
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsFiniteMeasure P]
    (A B : ∀ k : ℕ,
      Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ k i j, Measurable fun omega ↦ A k omega i j)
    (hB : ∀ k i j, Measurable fun omega ↦ B k omega i j) :
    DeterminantsEventuallyNonzeroInProbability P A B := by
  filter_upwards [ae_ae_all_normalizedShiftDets_ne_zero_of_entrywise
    P A B hA hB] with z hz
  have hzero : ∀ k, P {omega |
      normalizedShiftDet (A k omega) z = 0 ∨
        normalizedShiftDet (B k omega) z = 0} = 0 := by
    intro k
    have hae : ∀ᵐ omega ∂P, ¬(
        normalizedShiftDet (A k omega) z = 0 ∨
          normalizedShiftDet (B k omega) z = 0) := by
      filter_upwards [hz k] with omega homega
      simp only [not_or]
      exact ⟨homega.1, homega.2⟩
    simpa only [not_not] using (ae_iff.mp hae)
  simpa only [hzero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0∞)) atTop (𝓝 0))

/-- The almost-sure eventual non-singularity guard is automatic as well;
the proof yields the stronger statement that both determinants are nonzero
for every index on a common sample event (after fixing a.e. `z`). -/
theorem determinantsEventuallyNonzeroAlmostSurely_of_entrywise
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsFiniteMeasure P]
    (A B : ∀ k : ℕ,
      Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ k i j, Measurable fun omega ↦ A k omega i j)
    (hB : ∀ k i j, Measurable fun omega ↦ B k omega i j) :
    DeterminantsEventuallyNonzeroAlmostSurely P A B := by
  filter_upwards [ae_ae_all_normalizedShiftDets_ne_zero_of_entrywise
    P A B hA hB] with z hz
  filter_upwards [ae_all_iff.mpr hz] with omega homega
  exact Filter.Eventually.of_forall homega

/-- The same potential written using the normalized multiset-average API of
`LogKernelBounds`. -/
theorem matrixLogPotential_eq_multisetLogPotential {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (z : ℂ) :
    matrixLogPotential A z =
      multisetLogPotential (eigenvalueMultiset (normalizedMatrix A)) z := by
  rw [matrixLogPotential, realEsdTest, realSpectralSum,
    multisetLogPotential, multisetAverage_eq_map_sum_div_card,
    card_eigenvalueMultiset]

/-- The multiset second moment of the normalized spectrum is exactly its ESD
second-moment test. -/
theorem multisetSecondMoment_normalizedSpectrum_eq_realEsdTest {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    multisetSecondMoment (eigenvalueMultiset (normalizedMatrix A)) =
      realEsdTest (normalizedMatrix A) (fun z ↦ ‖z‖ ^ 2) := by
  rw [multisetSecondMoment, multisetAverage_eq_map_sum_div_card,
    realEsdTest, realSpectralSum, card_eigenvalueMultiset]

/-- Weyl's inequality in the exact multiset form needed in the local
logarithmic-potential estimate. -/
theorem multisetSecondMoment_normalizedSpectrum_le {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    multisetSecondMoment (eigenvalueMultiset (normalizedMatrix A)) ≤
      normalizedHilbertSchmidtSq A := by
  rw [multisetSecondMoment_normalizedSpectrum_eq_realEsdTest]
  simpa [normalizedHilbertSchmidtSq] using
    normalizedEsdSecondMoment_le_hilbertSchmidtSq A

/-- Off the spectrum, the normalized determinant in hypothesis (ii) of
Theorem 2.1 is exactly the ESD logarithmic potential. -/
theorem normalizedLogDet_eq_matrixLogPotential_of_det_ne_zero {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (z : ℂ)
    (hdet : (normalizedMatrix A -
      z • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)).det ≠ 0) :
    normalizedLogDet A z = matrixLogPotential A z := by
  simpa [normalizedLogDet, matrixLogPotential] using
    normalized_log_norm_det_sub_scalar_eq_realEsdTest
      (normalizedMatrix A) z hdet

/-- The exceptional set in the determinant/potential identity is the finite
spectrum, hence has planar Lebesgue measure zero.  This is the precise
almost-everywhere form needed before applying Tao--Vu Lemma 3.1. -/
theorem ae_normalizedLogDet_eq_matrixLogPotential {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      normalizedLogDet A z = matrixLogPotential A z := by
  let s : Set ℂ :=
    ((eigenvalueMultiset (normalizedMatrix A)).toFinset : Set ℂ)
  have hsfinite : s.Finite := by
    exact (eigenvalueMultiset (normalizedMatrix A)).toFinset.finite_toSet
  have hsnull : (volume : Measure ℂ) s = 0 :=
    hsfinite.measure_zero (volume : Measure ℂ)
  rw [ae_iff]
  apply measure_mono_null (t := s) _ hsnull
  intro z hz
  by_contra hz_not_mem
  apply hz
  apply normalizedLogDet_eq_matrixLogPotential_of_det_ne_zero A z
  rw [det_sub_scalar_eq_prod_eigenvalue_sub]
  apply Multiset.prod_ne_zero
  intro hzero
  rcases Multiset.mem_map.mp hzero with ⟨lambda, hlambda, hlambda_sub⟩
  have hlambda_eq : lambda = z := sub_eq_zero.mp hlambda_sub
  subst lambda
  exact hz_not_mem (by simpa [s] using hlambda)

/-- The difference version of the preceding a.e. identity. -/
theorem ae_normalizedLogDetDifference_eq_matrixLogPotentialDifference
    {k : ℕ} (A B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      normalizedLogDetDifference A B z =
        matrixLogPotential A z - matrixLogPotential B z := by
  filter_upwards [ae_normalizedLogDet_eq_matrixLogPotential A,
    ae_normalizedLogDet_eq_matrixLogPotential B] with z hA hB
  simp only [normalizedLogDetDifference, hA, hB]

/-! ## The local `L²` moment in hypothesis (i) -/

/-- Sum of the two normalized Hilbert--Schmidt squares in Theorem 2.1(i). -/
def normalizedHilbertSchmidtPairSq {k : ℕ}
    (A B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ℝ :=
  normalizedHilbertSchmidtSq A + normalizedHilbertSchmidtSq B

theorem normalizedHilbertSchmidtSq_nonneg {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    0 ≤ normalizedHilbertSchmidtSq A := by
  unfold normalizedHilbertSchmidtSq
  exact div_nonneg (hilbertSchmidtSq_nonneg A) (sq_nonneg _)

theorem normalizedHilbertSchmidtPairSq_nonneg {k : ℕ}
    (A B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    0 ≤ normalizedHilbertSchmidtPairSq A B := by
  exact add_nonneg (normalizedHilbertSchmidtSq_nonneg A)
    (normalizedHilbertSchmidtSq_nonneg B)

/-- The local squared logarithmic-determinant moment over a fixed closed
ball.  The `lintegral` is used so that finiteness is a genuine conclusion,
not an artefact of the totalized Bochner integral. -/
def localLogDetDifferenceL2Moment (R : ℝ) {k : ℕ}
    (A B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ℝ≥0∞ :=
  ∫⁻ z in Metric.closedBall (0 : ℂ) R,
    ‖normalizedLogDetDifference A B z‖ₑ ^ (2 : ℝ)

private theorem enorm_rpow_two_real (x : ℝ) :
    ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (x ^ 2) := by
  rw [show (2 : ℝ) = (2 : ℕ) by norm_num, ENNReal.rpow_natCast]
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg x)]
  simp [Real.norm_eq_abs, sq_abs]

/-- Equation (27), now for the actual total measurable log-determinant
function used in hypothesis (ii).  The determinant/potential discrepancy is
confined to finitely many spectral points and hence disappears under planar
integration. -/
theorem exists_localLogDetDifferenceL2Moment_le
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ a : ℝ, 0 < a ∧ ∀ {k : ℕ}
      (A B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
      localLogDetDifferenceL2Moment R A B ≤
        ENNReal.ofReal
          (a * (1 + normalizedHilbertSchmidtPairSq A B)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_lintegral_normalizedMatrixLogPotential_sub_sq_closedBall_le R hR
  refine ⟨C + 1, by linarith, fun {k} A B ↦ ?_⟩
  have hae : ∀ᵐ z ∂(volume.restrict (Metric.closedBall (0 : ℂ) R)),
      normalizedLogDetDifference A B z =
        multisetLogPotential (eigenvalueMultiset (normalizedMatrix A)) z -
          multisetLogPotential (eigenvalueMultiset (normalizedMatrix B)) z := by
    filter_upwards [ae_restrict_of_ae
      (ae_normalizedLogDetDifference_eq_matrixLogPotentialDifference A B)]
      with z hz
    simpa [matrixLogPotential_eq_multisetLogPotential] using hz
  calc
    localLogDetDifferenceL2Moment R A B =
        ∫⁻ z in Metric.closedBall (0 : ℂ) R,
          ENNReal.ofReal
            ((multisetLogPotential (eigenvalueMultiset (normalizedMatrix A)) z -
              multisetLogPotential (eigenvalueMultiset (normalizedMatrix B)) z) ^ 2) := by
      unfold localLogDetDifferenceL2Moment
      apply lintegral_congr_ae
      filter_upwards [hae] with z hz
      rw [hz, enorm_rpow_two_real]
    _ ≤ ENNReal.ofReal
        (C * (1 + normalizedHilbertSchmidtSq A +
          normalizedHilbertSchmidtSq B)) := hbound A B
    _ ≤ ENNReal.ofReal
        ((C + 1) * (1 + normalizedHilbertSchmidtPairSq A B)) := by
      apply ENNReal.ofReal_le_ofReal
      have hA := normalizedHilbertSchmidtSq_nonneg A
      have hB := normalizedHilbertSchmidtSq_nonneg B
      unfold normalizedHilbertSchmidtPairSq
      nlinarith

/-! ## Passing real tail bounds to `lintegral` moment bounds -/

/-- A nonnegative extended-real random variable dominated by an affine
function of a nonnegative real random variable bounded in probability is
itself bounded in probability.  This is the tail-bound bridge used after
the deterministic local `L²` estimate (Tao--Vu (27)). -/
theorem ennrealBoundedInProbability_of_affine_le
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (X : ℕ → Omega → ℝ) (Y : ℕ → Omega → ℝ≥0∞)
    (a : ℝ) (ha : 0 < a)
    (hX_nonneg : ∀ n omega, 0 ≤ X n omega)
    (hY : ∀ n omega,
      Y n omega ≤ ENNReal.ofReal (a * (1 + X n omega)))
    (hX : BoundedInProbability P X) :
    ENNRealBoundedInProbability P Y := by
  intro epsilon hepsilon
  obtain ⟨C, hC, htail⟩ := hX epsilon hepsilon
  refine ⟨ENNReal.ofReal (a * (1 + C)), ENNReal.ofReal_ne_top, ?_⟩
  filter_upwards [htail] with n hn
  refine lt_of_le_of_lt (measure_mono ?_) hn
  intro omega homega
  have hstrict :
      ENNReal.ofReal (a * (1 + C)) <
        ENNReal.ofReal (a * (1 + X n omega)) :=
    homega.trans_le (hY n omega)
  have hright_pos : 0 < a * (1 + X n omega) := by
    have : 0 ≤ X n omega := hX_nonneg n omega
    positivity
  have hreal : a * (1 + C) < a * (1 + X n omega) :=
    (ENNReal.ofReal_lt_ofReal_iff hright_pos).mp hstrict
  change C < ‖X n omega‖
  rw [Real.norm_eq_abs, abs_of_nonneg (hX_nonneg n omega)]
  nlinarith

/-- Almost-sure counterpart of `ennrealBoundedInProbability_of_affine_le`.
It turns the source's samplewise normalized Hilbert--Schmidt bound into the
samplewise finite `L²` moment bound required by Lemma 3.1. -/
theorem ennrealAlmostSurelyBounded_of_affine_le
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (X : ℕ → Omega → ℝ) (Y : ℕ → Omega → ℝ≥0∞)
    (a : ℝ) (ha : 0 < a)
    (hX_nonneg : ∀ n omega, 0 ≤ X n omega)
    (hY : ∀ n omega,
      Y n omega ≤ ENNReal.ofReal (a * (1 + X n omega)))
    (hX : AlmostSurelyBounded P X) :
    ENNRealAlmostSurelyBounded P Y := by
  filter_upwards [hX] with omega homega
  obtain ⟨C, hC⟩ := homega
  let C' : ℝ := max C 0
  refine ⟨ENNReal.ofReal (a * (1 + C')), ENNReal.ofReal_ne_top, fun n ↦ ?_⟩
  refine (hY n omega).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hXC : X n omega ≤ C := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hX_nonneg n omega)] using hC n
  nlinarith [hXC, le_max_left C 0]

/-- Multiplication by a deterministic real scalar preserves convergence in
measure to zero.  We use this pointwise in the spectral parameter with the
scalar `Delta f(z)`. -/
theorem tendstoInMeasure_const_mul_zero
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    {u : Filter ℕ} (c : ℝ) (X : ℕ → Omega → ℝ)
    (hX : TendstoInMeasure P X u 0) :
    TendstoInMeasure P (fun n omega ↦ c * X n omega) u 0 := by
  rw [tendstoInMeasure_iff_norm] at hX ⊢
  intro epsilon hepsilon
  by_cases hc : c = 0
  · subst c
    simpa [not_le_of_gt hepsilon] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0∞)) u (𝓝 0))
  have hcabs : 0 < |c| := abs_pos.mpr hc
  have hbase := hX (epsilon / |c|) (div_pos hepsilon hcabs)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbase
    (fun _ ↦ zero_le) ?_
  intro n
  apply measure_mono
  intro omega homega
  simp only [Pi.zero_apply, sub_zero, Real.norm_eq_abs] at homega ⊢
  change epsilon ≤ |c * X n omega| at homega
  rw [abs_mul] at homega
  change epsilon / |c| ≤ |X n omega|
  exact (div_le_iff₀ hcabs).2 (by simpa [mul_comm] using homega)

/-! ## Probabilistic form of the local moment estimate -/

/-- Theorem 2.1(i), together with Weyl's inequality and (27), supplies the
exact `L²`-moment boundedness premise of Tao--Vu Lemma 3.1 on every fixed
observation ball. -/
theorem localLogDetDifferenceL2Moment_boundedInProbability
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (A B : ∀ k : ℕ,
      Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (R : ℝ) (hR : 0 ≤ R)
    (hHS : BoundedInProbability P
      (fun k omega ↦ normalizedHilbertSchmidtPairSq (A k omega) (B k omega))) :
    ENNRealBoundedInProbability P
      (fun k omega ↦ localLogDetDifferenceL2Moment R (A k omega) (B k omega)) := by
  obtain ⟨a, ha, hlocal⟩ := exists_localLogDetDifferenceL2Moment_le R hR
  exact ennrealBoundedInProbability_of_affine_le P
    (fun k omega ↦ normalizedHilbertSchmidtPairSq (A k omega) (B k omega))
    (fun k omega ↦ localLogDetDifferenceL2Moment R (A k omega) (B k omega))
    a ha
    (fun k omega ↦ normalizedHilbertSchmidtPairSq_nonneg (A k omega) (B k omega))
    (fun k omega ↦ hlocal (A k omega) (B k omega)) hHS

/-- Almost-sure counterpart of
`localLogDetDifferenceL2Moment_boundedInProbability`. -/
theorem localLogDetDifferenceL2Moment_almostSurelyBounded
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (A B : ∀ k : ℕ,
      Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (R : ℝ) (hR : 0 ≤ R)
    (hHS : AlmostSurelyBounded P
      (fun k omega ↦ normalizedHilbertSchmidtPairSq (A k omega) (B k omega))) :
    ENNRealAlmostSurelyBounded P
      (fun k omega ↦ localLogDetDifferenceL2Moment R (A k omega) (B k omega)) := by
  obtain ⟨a, ha, hlocal⟩ := exists_localLogDetDifferenceL2Moment_le R hR
  exact ennrealAlmostSurelyBounded_of_affine_le P
    (fun k omega ↦ normalizedHilbertSchmidtPairSq (A k omega) (B k omega))
    (fun k omega ↦ localLogDetDifferenceL2Moment R (A k omega) (B k omega))
    a ha
    (fun k omega ↦ normalizedHilbertSchmidtPairSq_nonneg (A k omega) (B k omega))
    (fun k omega ↦ hlocal (A k omega) (B k omega)) hHS

/-! ## Lemma 3.1 applied on a closed ball -/

/-- On a fixed observation ball, assumptions (i) and (ii) imply convergence
in probability of the integrated log-determinant difference.  This is the
unweighted core of the smooth-test argument. -/
theorem integral_logDetDifference_closedBall_tendstoInProbability
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (A B : ∀ k : ℕ,
      Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ k i j, Measurable fun omega ↦ A k omega i j)
    (hB : ∀ k i j, Measurable fun omega ↦ B k omega i j)
    (R : ℝ) (hR : 0 ≤ R)
    (hHS : BoundedInProbability P
      (fun k omega ↦ normalizedHilbertSchmidtPairSq (A k omega) (B k omega)))
    (hlog : ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInMeasure P
        (fun k omega ↦ normalizedLogDetDifference (A k omega) (B k omega) z)
        atTop 0) :
    TendstoInMeasure P
      (fun k omega ↦ ∫ z in Metric.closedBall (0 : ℂ) R,
        normalizedLogDetDifference (A k omega) (B k omega) z) atTop 0 := by
  let nu : Measure ℂ :=
    (volume : Measure ℂ).restrict (Metric.closedBall (0 : ℂ) R)
  letI : IsFiniteMeasure nu :=
    ⟨by simpa [nu] using
      (measure_closedBall_lt_top :
        (volume : Measure ℂ) (Metric.closedBall (0 : ℂ) R) < (∞ : ℝ≥0∞))⟩
  have hmeas : ∀ k, Measurable (fun p : ℂ × Omega ↦
      normalizedLogDetDifference (A k p.2) (B k p.2) p.1) := by
    intro k
    exact measurable_normalizedLogDetDifference_joint_of_entrywise
      (A k) (B k) (hA k) (hB k)
  have hmoment : ENNRealBoundedInProbability P
      (fun k omega ↦ ∫⁻ z, ‖normalizedLogDetDifference
        (A k omega) (B k omega) z‖ₑ ^ (2 : ℝ) ∂nu) := by
    simpa [nu, localLogDetDifferenceL2Moment] using
      localLogDetDifferenceL2Moment_boundedInProbability P A B R hR hHS
  have hpoint : ∀ᵐ z ∂nu,
      TendstoInMeasure P
        (fun k omega ↦ normalizedLogDetDifference (A k omega) (B k omega) z)
        atTop 0 := ae_restrict_of_ae hlog
  simpa [nu] using randomDominatedConvergence_inProbability
    nu P
    (fun k z omega ↦ normalizedLogDetDifference (A k omega) (B k omega) z)
    2 (by norm_num) hmeas hmoment hpoint

/-- Weighted probability form of the preceding theorem.  The weight may be
any fixed bounded measurable real function; in the Green--Girko application
it is `Delta f`.  The weighted `L²` premise is derived here from (27), rather
than being added as an external assumption. -/
theorem integral_weighted_logDetDifference_closedBall_tendstoInProbability
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (A B : ∀ k : ℕ,
      Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ k i j, Measurable fun omega ↦ A k omega i j)
    (hB : ∀ k i j, Measurable fun omega ↦ B k omega i j)
    (R : ℝ) (hR : 0 ≤ R)
    (hHS : BoundedInProbability P
      (fun k omega ↦ normalizedHilbertSchmidtPairSq (A k omega) (B k omega)))
    (hlog : ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInMeasure P
        (fun k omega ↦ normalizedLogDetDifference (A k omega) (B k omega) z)
        atTop 0)
    (w : ℂ → ℝ) (hw : Measurable w)
    (hw_bound : ∃ C : ℝ, ∀ z, ‖w z‖ ≤ C) :
    TendstoInMeasure P
      (fun k omega ↦ ∫ z in Metric.closedBall (0 : ℂ) R,
        w z * normalizedLogDetDifference (A k omega) (B k omega) z) atTop 0 := by
  let nu : Measure ℂ :=
    (volume : Measure ℂ).restrict (Metric.closedBall (0 : ℂ) R)
  letI : IsFiniteMeasure nu :=
    ⟨by simpa [nu] using
      (measure_closedBall_lt_top :
        (volume : Measure ℂ) (Metric.closedBall (0 : ℂ) R) < (∞ : ℝ≥0∞))⟩
  obtain ⟨C, hC⟩ := hw_bound
  let D : ℝ := max C 0 + 1
  have hD : 0 < D := by
    dsimp [D]
    linarith [le_max_right C 0]
  have hwD : ∀ z, ‖w z‖ ≤ D := by
    intro z
    exact (hC z).trans (by dsimp [D]; linarith [le_max_left C 0])
  have hmeas : ∀ k, Measurable (fun p : ℂ × Omega ↦
      w p.1 * normalizedLogDetDifference (A k p.2) (B k p.2) p.1) := by
    intro k
    exact (hw.comp measurable_fst).mul
      (measurable_normalizedLogDetDifference_joint_of_entrywise
        (A k) (B k) (hA k) (hB k))
  obtain ⟨a, ha, hlocal⟩ := exists_localLogDetDifferenceL2Moment_le R hR
  have hweightedMomentPointwise : ∀ k omega,
      (∫⁻ z, ‖w z * normalizedLogDetDifference
          (A k omega) (B k omega) z‖ₑ ^ (2 : ℝ) ∂nu) ≤
        ENNReal.ofReal ((D ^ 2 * a) *
          (1 + normalizedHilbertSchmidtPairSq (A k omega) (B k omega))) := by
    intro k omega
    calc
      (∫⁻ z, ‖w z * normalizedLogDetDifference
          (A k omega) (B k omega) z‖ₑ ^ (2 : ℝ) ∂nu) ≤
          ∫⁻ z, (ENNReal.ofReal D) ^ (2 : ℝ) *
            ‖normalizedLogDetDifference
              (A k omega) (B k omega) z‖ₑ ^ (2 : ℝ) ∂nu := by
        apply lintegral_mono
        intro z
        change ‖w z * normalizedLogDetDifference
            (A k omega) (B k omega) z‖ₑ ^ (2 : ℝ) ≤
          (ENNReal.ofReal D) ^ (2 : ℝ) *
            ‖normalizedLogDetDifference
              (A k omega) (B k omega) z‖ₑ ^ (2 : ℝ)
        rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hwD z)
      _ = (ENNReal.ofReal D) ^ (2 : ℝ) *
          localLogDetDifferenceL2Moment R (A k omega) (B k omega) := by
        rw [lintegral_const_mul']
        · rfl
        · finiteness
      _ ≤ (ENNReal.ofReal D) ^ (2 : ℝ) *
          ENNReal.ofReal
            (a * (1 + normalizedHilbertSchmidtPairSq
              (A k omega) (B k omega))) := by
        gcongr
        exact hlocal (A k omega) (B k omega)
      _ = ENNReal.ofReal ((D ^ 2 * a) *
          (1 + normalizedHilbertSchmidtPairSq (A k omega) (B k omega))) := by
        rw [show (2 : ℝ) = (2 : ℕ) by norm_num, ENNReal.rpow_natCast]
        rw [← ENNReal.ofReal_pow hD.le, ← ENNReal.ofReal_mul (sq_nonneg D)]
        congr 1
        ring
  have hmoment : ENNRealBoundedInProbability P
      (fun k omega ↦ ∫⁻ z,
        ‖w z * normalizedLogDetDifference
          (A k omega) (B k omega) z‖ₑ ^ (2 : ℝ) ∂nu) := by
    apply ennrealBoundedInProbability_of_affine_le P
      (fun k omega ↦ normalizedHilbertSchmidtPairSq (A k omega) (B k omega))
      (fun k omega ↦ ∫⁻ z,
        ‖w z * normalizedLogDetDifference
          (A k omega) (B k omega) z‖ₑ ^ (2 : ℝ) ∂nu)
      (D ^ 2 * a)
    · positivity
    · exact fun k omega ↦
        normalizedHilbertSchmidtPairSq_nonneg (A k omega) (B k omega)
    · exact hweightedMomentPointwise
    · exact hHS
  have hpoint : ∀ᵐ z ∂nu,
      TendstoInMeasure P
        (fun k omega ↦ w z * normalizedLogDetDifference
          (A k omega) (B k omega) z) atTop 0 := by
    filter_upwards [ae_restrict_of_ae hlog] with z hz
    exact tendstoInMeasure_const_mul_zero P (w z)
      (fun k omega ↦ normalizedLogDetDifference (A k omega) (B k omega) z) hz
  simpa [nu] using randomDominatedConvergence_inProbability
    nu P
    (fun k z omega ↦ w z *
      normalizedLogDetDifference (A k omega) (B k omega) z)
    2 (by norm_num) hmeas hmoment hpoint

/-- Almost-sure application of Lemma 3.1 on a fixed ball, in the stronger
form where one full-probability event works for every bounded measurable
weight on that ball. -/
theorem integral_logDetDifference_closedBall_tendstoAlmostSurely_all_weights
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (A B : ∀ k : ℕ,
      Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ k i j, Measurable fun omega ↦ A k omega i j)
    (hB : ∀ k i j, Measurable fun omega ↦ B k omega i j)
    (R : ℝ) (hR : 0 ≤ R)
    (hHS : AlmostSurelyBounded P
      (fun k omega ↦ normalizedHilbertSchmidtPairSq (A k omega) (B k omega)))
    (hlog : ∀ᵐ z ∂(volume : Measure ℂ), ∀ᵐ omega ∂P,
      Tendsto
        (fun k ↦ normalizedLogDetDifference (A k omega) (B k omega) z)
        atTop (𝓝 0)) :
    ∀ᵐ omega ∂P, ∀ w : ℂ → ℝ, Measurable w →
      (∃ C : ℝ, ∀ z, ‖w z‖ ≤ C) →
      Tendsto (fun k ↦ ∫ z in Metric.closedBall (0 : ℂ) R,
        w z * normalizedLogDetDifference (A k omega) (B k omega) z)
        atTop (𝓝 0) := by
  let nu : Measure ℂ :=
    (volume : Measure ℂ).restrict (Metric.closedBall (0 : ℂ) R)
  letI : IsFiniteMeasure nu :=
    ⟨by simpa [nu] using
      (measure_closedBall_lt_top :
        (volume : Measure ℂ) (Metric.closedBall (0 : ℂ) R) < (∞ : ℝ≥0∞))⟩
  have hmeas : ∀ k, Measurable (fun p : ℂ × Omega ↦
      normalizedLogDetDifference (A k p.2) (B k p.2) p.1) := by
    intro k
    exact measurable_normalizedLogDetDifference_joint_of_entrywise
      (A k) (B k) (hA k) (hB k)
  have hmoment : ENNRealAlmostSurelyBounded P
      (fun k omega ↦ ∫⁻ z, ‖normalizedLogDetDifference
        (A k omega) (B k omega) z‖ₑ ^ (2 : ℝ) ∂nu) := by
    simpa [nu, localLogDetDifferenceL2Moment] using
      localLogDetDifferenceL2Moment_almostSurelyBounded P A B R hR hHS
  have hpoint : ∀ᵐ z ∂nu, ∀ᵐ omega ∂P,
      Tendsto
        (fun k ↦ normalizedLogDetDifference (A k omega) (B k omega) z)
        atTop (𝓝 0) := ae_restrict_of_ae hlog
  simpa [nu] using randomDominatedConvergence_almostSurely_all_bounded_weights
    nu P
    (fun k z omega ↦ normalizedLogDetDifference (A k omega) (B k omega) z)
    2 (by norm_num) hmeas hmoment hpoint

/-- Countable intersection of the preceding full-measure events over all
integer observation radii.  This is what permits one final event to work for
every compactly supported smooth test function, whose support radius is not
fixed in advance. -/
theorem integral_logDetDifference_all_natBalls_tendstoAlmostSurely_all_weights
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (A B : ∀ k : ℕ,
      Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ k i j, Measurable fun omega ↦ A k omega i j)
    (hB : ∀ k i j, Measurable fun omega ↦ B k omega i j)
    (hHS : AlmostSurelyBounded P
      (fun k omega ↦ normalizedHilbertSchmidtPairSq (A k omega) (B k omega)))
    (hlog : ∀ᵐ z ∂(volume : Measure ℂ), ∀ᵐ omega ∂P,
      Tendsto
        (fun k ↦ normalizedLogDetDifference (A k omega) (B k omega) z)
        atTop (𝓝 0)) :
    ∀ᵐ omega ∂P, ∀ m : ℕ, ∀ w : ℂ → ℝ, Measurable w →
      (∃ C : ℝ, ∀ z, ‖w z‖ ≤ C) →
      Tendsto (fun k ↦ ∫ z in Metric.closedBall (0 : ℂ) (m : ℝ),
        w z * normalizedLogDetDifference (A k omega) (B k omega) z)
        atTop (𝓝 0) := by
  apply ae_all_iff.mpr
  intro m
  exact integral_logDetDifference_closedBall_tendstoAlmostSurely_all_weights
    P A B hA hB (m : ℝ) (Nat.cast_nonneg m) hHS hlog

/-! ## Green--Girko assembly for matrix differences -/

/-- Deterministic Green--Girko identity for a pair of normalized matrices,
with the empirical potentials replaced a.e. by the actual normalized
log-determinants from Theorem 2.1(ii). -/
theorem esdDifference_normalized_eq_integral_laplacian_logDetDifference
    {k : ℕ}
    (A B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    esdDifference (normalizedMatrix A) (normalizedMatrix B) f =
      (1 / (2 * Real.pi)) * ∫ z : ℂ,
        Δ f z * normalizedLogDetDifference A B z := by
  rw [esdDifference,
    green_identity_realEsdTest (normalizedMatrix A) f hf hfc,
    green_identity_realEsdTest (normalizedMatrix B) f hf hfc]
  rw [← mul_sub]
  congr 1
  have hintA := integrable_laplacian_mul_realEsdLogPotential
    (normalizedMatrix A) f hf hfc
  have hintB := integrable_laplacian_mul_realEsdLogPotential
    (normalizedMatrix B) f hf hfc
  rw [← integral_sub hintA hintB]
  apply integral_congr_ae
  filter_upwards [ae_normalizedLogDetDifference_eq_matrixLogPotentialDifference A B]
    with z hz
  change Δ f z * matrixLogPotential A z -
      Δ f z * matrixLogPotential B z =
    Δ f z * normalizedLogDetDifference A B z
  rw [hz]
  ring

/-- The same identity restricted to any ball outside which `Delta f`
vanishes.  This is the exact form consumed by Lemma 3.1. -/
theorem esdDifference_normalized_eq_integral_closedBall_logDetDifference
    {k : ℕ}
    (A B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (R : ℝ) (hout : ∀ z ∉ Metric.closedBall (0 : ℂ) R, Δ f z = 0) :
    esdDifference (normalizedMatrix A) (normalizedMatrix B) f =
      (1 / (2 * Real.pi)) * ∫ z in Metric.closedBall (0 : ℂ) R,
        Δ f z * normalizedLogDetDifference A B z := by
  rw [esdDifference_normalized_eq_integral_laplacian_logDetDifference
    A B f hf hfc]
  rw [integral_laplacian_mul_eq_integral_closedBall f
    (fun z ↦ normalizedLogDetDifference A B z) R hout]

/-! ## Smooth tests -/

/-- Assumptions (i) and (ii) imply convergence in probability for every
smooth compactly supported test.  No probability input beyond the two source
hypotheses remains: local `L²` control was proved above from (i). -/
theorem smoothEsdDifference_tendstoInProbability
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (A B : ∀ k : ℕ,
      Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ k i j, Measurable fun omega ↦ A k omega i j)
    (hB : ∀ k i j, Measurable fun omega ↦ B k omega i j)
    (hHS : BoundedInProbability P
      (fun k omega ↦ normalizedHilbertSchmidtPairSq (A k omega) (B k omega)))
    (hlog : ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInMeasure P
        (fun k omega ↦ normalizedLogDetDifference (A k omega) (B k omega) z)
        atTop 0) :
    ∀ g : ℂ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      TendstoInMeasure P
        (fun k omega ↦ esdDifference
          (normalizedMatrix (A k omega)) (normalizedMatrix (B k omega)) g)
        atTop 0 := by
  intro g hg hgc
  have hg2 : ContDiff ℝ 2 g :=
    hg.of_le (WithTop.coe_le_coe.mpr
      (show (2 : ℕ∞) ≤ ⊤ from le_top))
  obtain ⟨R, hR, hout⟩ := exists_laplacian_zero_outside_closedBall hgc
  have hint := integral_weighted_logDetDifference_closedBall_tendstoInProbability
    P A B hA hB R hR hHS hlog (Δ g)
      (continuous_laplacian hg2).measurable
      (exists_norm_laplacian_le hg2 hgc)
  have hscaled := tendstoInMeasure_const_mul_zero P (1 / (2 * Real.pi))
    (fun k omega ↦ ∫ z in Metric.closedBall (0 : ℂ) R,
      Δ g z * normalizedLogDetDifference (A k omega) (B k omega) z) hint
  apply TendstoInMeasure.congr_left _ hscaled
  intro k
  filter_upwards with omega
  exact (esdDifference_normalized_eq_integral_closedBall_logDetDifference
    (A k omega) (B k omega) g hg2 hgc R hout).symm

/-- Almost-sure smooth-test conclusion on one common full-probability event.
The countable family of integer balls is what makes the event independent of
the later choice of smooth compactly supported test. -/
theorem smoothEsdDifference_tendstoAlmostSurely
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (A B : ∀ k : ℕ,
      Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ k i j, Measurable fun omega ↦ A k omega i j)
    (hB : ∀ k i j, Measurable fun omega ↦ B k omega i j)
    (hHS : AlmostSurelyBounded P
      (fun k omega ↦ normalizedHilbertSchmidtPairSq (A k omega) (B k omega)))
    (hlog : ∀ᵐ z ∂(volume : Measure ℂ), ∀ᵐ omega ∂P,
      Tendsto
        (fun k ↦ normalizedLogDetDifference (A k omega) (B k omega) z)
        atTop (𝓝 0)) :
    ∀ᵐ omega ∂P, ∀ g : ℂ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      Tendsto (fun k ↦ esdDifference
        (normalizedMatrix (A k omega)) (normalizedMatrix (B k omega)) g)
        atTop (𝓝 0) := by
  have hall :=
    integral_logDetDifference_all_natBalls_tendstoAlmostSurely_all_weights
      P A B hA hB hHS hlog
  filter_upwards [hall] with omega homega
  intro g hg hgc
  have hg2 : ContDiff ℝ 2 g :=
    hg.of_le (WithTop.coe_le_coe.mpr
      (show (2 : ℕ∞) ≤ ⊤ from le_top))
  obtain ⟨R, _hR, hout⟩ := exists_laplacian_zero_outside_closedBall hgc
  obtain ⟨m, hm⟩ := exists_nat_ge R
  have houtm : ∀ z ∉ Metric.closedBall (0 : ℂ) (m : ℝ), Δ g z = 0 := by
    intro z hzm
    apply hout z
    intro hzR
    exact hzm (Metric.closedBall_subset_closedBall hm hzR)
  have hint := homega m (Δ g) (continuous_laplacian hg2).measurable
    (exists_norm_laplacian_le hg2 hgc)
  have hscaled : Tendsto
      (fun k ↦ (1 / (2 * Real.pi)) *
        ∫ z in Metric.closedBall (0 : ℂ) (m : ℝ),
          Δ g z * normalizedLogDetDifference (A k omega) (B k omega) z)
      atTop (𝓝 0) := by
    simpa using hint.const_mul (1 / (2 * Real.pi))
  have hfun :
      (fun k ↦ esdDifference
        (normalizedMatrix (A k omega)) (normalizedMatrix (B k omega)) g) =
      (fun k ↦ (1 / (2 * Real.pi)) *
        ∫ z in Metric.closedBall (0 : ℂ) (m : ℝ),
          Δ g z * normalizedLogDetDifference (A k omega) (B k omega) z) := by
    funext k
    exact esdDifference_normalized_eq_integral_closedBall_logDetDifference
      (A k omega) (B k omega) g hg2 hgc (m : ℝ) houtm
  rw [hfun]
  exact hscaled

/-! ## Tao--Vu, Theorem 2.1 -/

/-- **Tao--Vu replacement principle, Theorem 2.1 (convergence in
probability).**

For entrywise-measurable random matrices `A_k,B_k` of size `k+1`, assume:

* (i) `((k+1)⁻²)(‖A_k‖_HS² + ‖B_k‖_HS²)` is bounded in probability;
* (ii) for planar-a.e. fixed `z`,
  `(k+1)⁻¹ log |det((k+1)⁻¹ᐟ² A_k-zI)|` minus the analogous expression for
  `B_k` converges to zero in probability.

Then the ESD difference of `(k+1)⁻¹ᐟ² A_k` and `(k+1)⁻¹ᐟ² B_k` converges
vaguely to zero in probability, expressed against every continuous compactly
supported real test function.  No independence hypothesis is present.

The paper's non-singularity semantics for (ii) is not an extra premise:
`determinantsEventuallyNonzeroInProbability_of_entrywise` proves it from
entrywise measurability by the finite-spectrum/Fubini argument above. -/
theorem taoVuReplacementPrinciple_inProbability
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (A B : ∀ k : ℕ,
      Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ k i j, Measurable fun omega ↦ A k omega i j)
    (hB : ∀ k i j, Measurable fun omega ↦ B k omega i j)
    (hHS : BoundedInProbability P
      (fun k omega ↦ normalizedHilbertSchmidtPairSq (A k omega) (B k omega)))
    (hlog : ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInMeasure P
        (fun k omega ↦ normalizedLogDetDifference (A k omega) (B k omega) z)
        atTop 0) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure P
        (fun k omega ↦ esdDifference
          (normalizedMatrix (A k omega)) (normalizedMatrix (B k omega)) f)
        atTop 0 := by
  have _hdeterminants : DeterminantsEventuallyNonzeroInProbability P A B :=
    determinantsEventuallyNonzeroInProbability_of_entrywise P A B hA hB
  exact vague_inProbability_of_smooth P
    (fun k omega ↦ normalizedMatrix (A k omega))
    (fun k omega ↦ normalizedMatrix (B k omega))
    (smoothEsdDifference_tendstoInProbability P A B hA hB hHS hlog)

/-- **Tao--Vu replacement principle, Theorem 2.1 (almost-sure mode).**

Under the almost-sure versions of (i) and (ii), one common
full-probability event supports vague convergence against **every** continuous
compactly supported real test.  The common event is obtained before the test
function is chosen.  As in the probability theorem, eventual
non-singularity is automatic from entrywise measurability and is formally
proved by `determinantsEventuallyNonzeroAlmostSurely_of_entrywise`. -/
theorem taoVuReplacementPrinciple_almostSurely
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (A B : ∀ k : ℕ,
      Omega → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hA : ∀ k i j, Measurable fun omega ↦ A k omega i j)
    (hB : ∀ k i j, Measurable fun omega ↦ B k omega i j)
    (hHS : AlmostSurelyBounded P
      (fun k omega ↦ normalizedHilbertSchmidtPairSq (A k omega) (B k omega)))
    (hlog : ∀ᵐ z ∂(volume : Measure ℂ), ∀ᵐ omega ∂P,
      Tendsto
        (fun k ↦ normalizedLogDetDifference (A k omega) (B k omega) z)
        atTop (𝓝 0)) :
    ∀ᵐ omega ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k ↦ esdDifference
        (normalizedMatrix (A k omega)) (normalizedMatrix (B k omega)) f)
        atTop (𝓝 0) := by
  have _hdeterminants : DeterminantsEventuallyNonzeroAlmostSurely P A B :=
    determinantsEventuallyNonzeroAlmostSurely_of_entrywise P A B hA hB
  exact vague_almostSurely_of_smooth P
    (fun k omega ↦ normalizedMatrix (A k omega))
    (fun k omega ↦ normalizedMatrix (B k omega))
    (smoothEsdDifference_tendstoAlmostSurely P A B hA hB hHS hlog)

end TaoVuReplacement

