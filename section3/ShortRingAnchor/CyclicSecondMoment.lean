import ShortRingAnchor.ShortRingModel
import ShortRingAnchor.SecondMoment

/-!
# The cyclic short-ring second moment

This file discharges the elementary Hilbert--Schmidt input for the genuine
cyclic short-ring matrix (3.1).  It uses only the centered unit-second-moment
assumptions on the supplied atom copies and the normalization
`AdmissibleWeights.sum_q`; no independence assumption is needed.
-/

open scoped BigOperators

noncomputable section

namespace ShortRingAnchor

open MeasureTheory

/-! ## The cyclic placement has no collisions within one row -/

/-- Under `2W+1 <= M`, two distinct band offsets cannot occupy the same
cyclic column in a fixed row.  This is the deterministic injectivity hidden
in formula (3.1). -/
theorem cyclicColumn_injective {M W : Nat} (hfit : 2 * W + 1 <= M)
    (i : Fin M) : Function.Injective (cyclicColumn hfit i) := by
  intro s t hst
  apply Fin.eq_of_val_eq
  have hmod :
      (i.val + s.val + M - W) ≡ (i.val + t.val + M - W) [MOD M] := by
    exact congrArg Fin.val hst
  have hs_rearrange :
      i.val + s.val + M - W = (i.val + M - W) + s.val := by
    omega
  have ht_rearrange :
      i.val + t.val + M - W = (i.val + M - W) + t.val := by
    omega
  rw [hs_rearrange, ht_rearrange] at hmod
  have hoffset : s.val ≡ t.val [MOD M] :=
    (Nat.ModEq.refl (i.val + M - W)).add_left_cancel hmod
  exact Nat.ModEq.eq_of_lt_of_lt hoffset
    (lt_of_lt_of_le s.isLt hfit) (lt_of_lt_of_le t.isLt hfit)

/-! ## Pointwise square and row-sum identities -/

/-- Pointwise squared-norm expansion of one entry of (3.1).  Injectivity of
the cyclic placement removes all cross terms. -/
theorem norm_sq_cyclicShortRingMatrix_apply
    {M W : Nat} {c0 C0 : Real}
    (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 <= M)
    (entry : Fin M -> BandOffset W -> Complex)
    (i j : Fin M) :
    ‖cyclicShortRingMatrix weights hfit entry i j‖ ^ 2 =
      ∑ s : BandOffset W,
        if cyclicColumn hfit i s = j then
          weights.q s * ‖entry i s‖ ^ 2
        else 0 := by
  classical
  by_cases hex : ∃ s : BandOffset W, cyclicColumn hfit i s = j
  · obtain ⟨s, hs⟩ := hex
    have hsingle : ∀ t : BandOffset W,
        cyclicColumn hfit i t = j -> t = s := by
      intro t ht
      exact cyclicColumn_injective hfit i (ht.trans hs.symm)
    rw [cyclicShortRingMatrix_apply]
    rw [Finset.sum_eq_single s]
    · simp only [hs, if_true, norm_mul]
      rw [mul_pow]
      have hq : 0 <= weights.q s := weights.q_nonneg s
      simp [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt hq]
      symm
      have hsum :
          (∑ t : BandOffset W,
            if cyclicColumn hfit i t = j then
              weights.q t * ‖entry i t‖ ^ 2
            else 0) =
            (if cyclicColumn hfit i s = j then
              weights.q s * ‖entry i s‖ ^ 2
            else 0) := by
        apply Finset.sum_eq_single s
        · intro t _ht hts
          have hne : cyclicColumn hfit i t ≠ j := by
            intro ht
            exact hts (hsingle t ht)
          simp [hne]
        · simp
      simpa [hs] using hsum
    · intro t _ht hts
      have hne : cyclicColumn hfit i t ≠ j := by
        intro ht
        exact hts (hsingle t ht)
      simp [hne]
    · simp
  · rw [cyclicShortRingMatrix_apply]
    have hnone : ∀ s : BandOffset W, cyclicColumn hfit i s ≠ j := by
      intro s hs
      exact hex ⟨s, hs⟩
    simp [hnone]

/-- The sum of squared entry norms in one row of (3.1) is exactly the
weighted sum of the squared atom norms in that row. -/
theorem sum_norm_sq_cyclicShortRingMatrix_row
    {M W : Nat} {c0 C0 : Real}
    (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 <= M)
    (entry : Fin M -> BandOffset W -> Complex)
    (i : Fin M) :
    (∑ j : Fin M, ‖cyclicShortRingMatrix weights hfit entry i j‖ ^ 2) =
      ∑ s : BandOffset W, weights.q s * ‖entry i s‖ ^ 2 := by
  classical
  simp_rw [norm_sq_cyclicShortRingMatrix_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _hs
  simp

/-! ## Integrability and centered moments -/

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- First-moment integrability of a cyclic short-ring entry follows from
that of the supplied atom copies. -/
theorem integrable_cyclicShortRingRandomMatrix_entry
    {M W : Nat} {c0 C0 : Real}
    (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 <= M)
    (entry : Omega -> Fin M -> BandOffset W -> Complex)
    (hentry : ∀ i s, Integrable (fun omega => entry omega i s) mu)
    (i j : Fin M) :
    Integrable (fun omega =>
      cyclicShortRingRandomMatrix weights hfit entry omega i j) mu := by
  unfold cyclicShortRingRandomMatrix cyclicShortRingMatrix
  apply integrable_finsetSum Finset.univ
  intro s _hs
  by_cases hsj : cyclicColumn hfit i s = j
  · simp only [hsj, if_true]
    exact (hentry i s).const_mul _
  · simp [hsj]

/-- Second-moment integrability of a cyclic short-ring entry follows from
that of the squared atom norms. -/
theorem integrable_norm_sq_cyclicShortRingRandomMatrix_entry
    {M W : Nat} {c0 C0 : Real}
    (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 <= M)
    (entry : Omega -> Fin M -> BandOffset W -> Complex)
    (hentrySq : ∀ i s,
      Integrable (fun omega => ‖entry omega i s‖ ^ 2) mu)
    (i j : Fin M) :
    Integrable (fun omega =>
      ‖cyclicShortRingRandomMatrix weights hfit entry omega i j‖ ^ 2) mu := by
  have hsum : Integrable (fun omega =>
      ∑ s : BandOffset W,
        if cyclicColumn hfit i s = j then
          weights.q s * ‖entry omega i s‖ ^ 2
        else 0) mu := by
    apply integrable_finsetSum Finset.univ
    intro s _hs
    by_cases hsj : cyclicColumn hfit i s = j
    · simp only [hsj, if_true]
      exact (hentrySq i s).const_mul _
    · simp [hsj]
  refine hsum.congr ?_
  filter_upwards [] with omega
  exact (norm_sq_cyclicShortRingMatrix_apply weights hfit
    (entry omega) i j).symm

/-- Centered supplied atoms make every matrix entry in (3.1) centered. -/
theorem integral_cyclicShortRingRandomMatrix_entry_eq_zero
    {M W : Nat} {c0 C0 : Real}
    (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 <= M)
    (entry : Omega -> Fin M -> BandOffset W -> Complex)
    (hentry : ∀ i s, Integrable (fun omega => entry omega i s) mu)
    (hcentered : ∀ i s, ∫ omega, entry omega i s ∂mu = 0)
    (i j : Fin M) :
    ∫ omega,
      cyclicShortRingRandomMatrix weights hfit entry omega i j ∂mu = 0 := by
  unfold cyclicShortRingRandomMatrix cyclicShortRingMatrix
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_eq_zero
    intro s _hs
    by_cases hsj : cyclicColumn hfit i s = j
    · simp only [hsj, if_true]
      rw [integral_const_mul, hcentered i s]
      simp
    · simp [hsj]
  · intro s _hs
    by_cases hsj : cyclicColumn hfit i s = j
    · simp only [hsj, if_true]
      exact (hentry i s).const_mul _
    · simp [hsj]

/-- If every supplied atom copy has unit second moment, then one fixed row
of the genuine cyclic matrix has total second moment one.  This is exactly
where the source normalization `sum_s q_s = 1` enters formula (3.13). -/
theorem sum_integral_norm_sq_cyclicShortRingRandomMatrix_row_eq_one
    {M W : Nat} {c0 C0 : Real}
    (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 <= M)
    (entry : Omega -> Fin M -> BandOffset W -> Complex)
    (hentrySq : ∀ i s,
      Integrable (fun omega => ‖entry omega i s‖ ^ 2) mu)
    (hunitVariance : ∀ i s,
      ∫ omega, ‖entry omega i s‖ ^ 2 ∂mu = 1)
    (i : Fin M) :
    ∑ j : Fin M,
        ∫ omega,
          ‖cyclicShortRingRandomMatrix weights hfit entry omega i j‖ ^ 2 ∂mu =
      1 := by
  have hpoint : ∀ j : Fin M,
      ∫ omega,
          ‖cyclicShortRingRandomMatrix weights hfit entry omega i j‖ ^ 2 ∂mu =
        ∑ s : BandOffset W,
          if cyclicColumn hfit i s = j then weights.q s else 0 := by
    intro j
    change
      ∫ omega,
          ‖cyclicShortRingMatrix weights hfit (entry omega) i j‖ ^ 2 ∂mu =
        _
    rw [integral_congr_ae (Filter.Eventually.of_forall fun omega =>
      norm_sq_cyclicShortRingMatrix_apply weights hfit (entry omega) i j)]
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro s _hs
      by_cases hsj : cyclicColumn hfit i s = j
      · simp only [hsj, if_true]
        rw [integral_const_mul, hunitVariance i s]
        simp
      · simp [hsj]
    · intro s _hs
      by_cases hsj : cyclicColumn hfit i s = j
      · simp only [hsj, if_true]
        exact (hentrySq i s).const_mul _
      · simp [hsj]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  simpa using weights.sum_q

/-! ## Constructor for the exact upper-edge input -/

/-- The centered unit-variance atom assumptions construct
`CenteredMatrixRowSecondMomentInputs` for a sequence of genuine cyclic
short-ring matrices.  Independence is deliberately absent: it is not used
by the Hilbert--Schmidt calculation in formula (3.13). -/
theorem centeredMatrixRowSecondMomentInputs_cyclicShortRing
    {M W : Nat -> Nat} {c0 C0 : Real}
    (weights : ∀ n, AdmissibleWeights (W n) c0 C0)
    (hfit : ∀ n, 2 * W n + 1 <= M n)
    (entry : ∀ n, Omega -> Fin (M n) -> BandOffset (W n) -> Complex)
    (hentry : ∀ n i s,
      Integrable (fun omega => entry n omega i s) mu)
    (hentrySq : ∀ n i s,
      Integrable (fun omega => ‖entry n omega i s‖ ^ 2) mu)
    (hcentered : ∀ n i s, ∫ omega, entry n omega i s ∂mu = 0)
    (hunitVariance : ∀ n i s,
      ∫ omega, ‖entry n omega i s‖ ^ 2 ∂mu = 1) :
    CenteredMatrixRowSecondMomentInputs mu
      (fun n omega =>
        cyclicShortRingRandomMatrix (weights n) (hfit n) (entry n) omega)
      1 := by
  constructor
  · norm_num
  · intro n i j
    exact integrable_cyclicShortRingRandomMatrix_entry
      (weights n) (hfit n) (entry n) (hentry n) i j
  · intro n i j
    exact integrable_norm_sq_cyclicShortRingRandomMatrix_entry
      (weights n) (hfit n) (entry n) (hentrySq n) i j
  · intro n i j
    exact integral_cyclicShortRingRandomMatrix_entry_eq_zero
      (weights n) (hfit n) (entry n) (hentry n) (hcentered n) i j
  · intro n i
    exact sum_integral_norm_sq_cyclicShortRingRandomMatrix_row_eq_one
      (weights n) (hfit n) (entry n) (hentrySq n) (hunitVariance n) i

end ShortRingAnchor
