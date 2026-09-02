import TaoVuReplacement.ReplacementPrinciple

/-!
# The proved replacement principle for arbitrary positive dimension sequences

This is the dimension-uniform part of the user's TaoVuReplacement proof,
adapted from commit 2f96f5460eea0965956f69d787ebc722f1392078.
The pointwise Green identity, logarithmic-kernel estimate, probability
dominated convergence, and smooth approximation are imported unchanged.
Only the sequence index and matrix dimension are separated here. No
dimension-adaptation certificate or new replacement assumption is used.
-/

open Filter Set MeasureTheory
open InnerProductSpace Laplacian
open scoped BigOperators ContDiff ENNReal Topology

noncomputable section

namespace BernoulliSection10.DimensionReplacement

open TaoVuReplacement

variable {d : ℕ → ℕ}

theorem integral_weighted_logDetDifference_closedBall_sequence
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (A B : ∀ k : ℕ,
      Omega → Matrix (Fin (d k + 1)) (Fin (d k + 1)) ℂ)
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

theorem smoothEsdDifference_sequence
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (A B : ∀ k : ℕ,
      Omega → Matrix (Fin (d k + 1)) (Fin (d k + 1)) ℂ)
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
  have hint := integral_weighted_logDetDifference_closedBall_sequence
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

theorem vague_sequence_of_smooth
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B : ∀ k : ℕ, Ω → Matrix (Fin (d k + 1)) (Fin (d k + 1)) ℂ)
    (hsmooth : ∀ g : (ℂ → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      TendstoInMeasure P
        (fun k sample ↦ esdDifference (A k sample) (B k sample) g) atTop 0) :
    ∀ f : (ℂ → ℝ), Continuous f → HasCompactSupport f →
      TendstoInMeasure P
        (fun k sample ↦ esdDifference (A k sample) (B k sample) f) atTop 0 := by
  intro f hf hfc
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  obtain ⟨g, hg_smooth, hg_compact, hgf⟩ :=
    exists_contDiff_hasCompactSupport_dist_lt f hf hfc (show 0 < ε / 8 by positivity)
  have hfg : ∀ z, |f z - g z| ≤ ε / 8 := by
    intro z
    have := (hgf z).le
    simpa only [Real.dist_eq, abs_sub_comm] using this
  have hG := tendstoInMeasure_iff_norm.mp (hsmooth g hg_smooth hg_compact)
    (ε / 2) (half_pos hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hG
    (fun _ ↦ zero_le) ?_
  intro k
  apply measure_mono
  intro sample hsample
  simp only [Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hsample ⊢
  change ε ≤ |esdDifference (A k sample) (B k sample) f| at hsample
  have hclose :
      |esdDifference (A k sample) (B k sample) f -
        esdDifference (A k sample) (B k sample) g| ≤ ε / 4 := by
    have h := abs_esdDifference_sub_le_of_forall
      (A k sample) (B k sample) f g (by positivity) hfg
    calc
      |esdDifference (A k sample) (B k sample) f -
          esdDifference (A k sample) (B k sample) g| ≤
          2 * (ε / 8) := by simpa only [esdDifference] using h
      _ = ε / 4 := by ring
  have htri :
      |esdDifference (A k sample) (B k sample) f| ≤
        |esdDifference (A k sample) (B k sample) f -
          esdDifference (A k sample) (B k sample) g| +
        |esdDifference (A k sample) (B k sample) g| := by
    calc
      |esdDifference (A k sample) (B k sample) f| =
          |(esdDifference (A k sample) (B k sample) f -
            esdDifference (A k sample) (B k sample) g) +
            esdDifference (A k sample) (B k sample) g| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  change ε / 2 ≤ |esdDifference (A k sample) (B k sample) g|
  linarith

/-- Tao--Vu for an arbitrary positive dimension sequence; dimension growth
is not needed for this replacement implication itself. -/
theorem taoVuReplacementPrinciple_sequence
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ∀ k, Ω → Matrix (Fin (d k + 1)) (Fin (d k + 1)) ℂ)
    (hA : ∀ k i j, Measurable fun sample => A k sample i j)
    (hB : ∀ k i j, Measurable fun sample => B k sample i j)
    (hHS : BoundedInProbability P
      (fun k sample => normalizedHilbertSchmidtPairSq (A k sample) (B k sample)))
    (hlog : ∀ᵐ z ∂(volume : Measure ℂ), TendstoInMeasure P
      (fun k sample => normalizedLogDetDifference (A k sample) (B k sample) z) atTop 0) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure P
        (fun k sample => esdDifference
          (normalizedMatrix (A k sample)) (normalizedMatrix (B k sample)) f) atTop 0 := by
  exact vague_sequence_of_smooth P
    (fun k sample => normalizedMatrix (A k sample))
    (fun k sample => normalizedMatrix (B k sample))
    (smoothEsdDifference_sequence P A B hA hB hHS hlog)

end BernoulliSection10.DimensionReplacement
