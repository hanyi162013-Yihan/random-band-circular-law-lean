import BernoulliSection8.RademacherIntervalIID
import BernoulliSection8.FiniteSupport
import BernoulliSection8.BandwidthLedger
import BernoulliSection9.InterfaceCanonicalLargeW
import BernoulliSection10.PhysicalProbabilityInstances
import BernoulliSection10.IntervalTransfer

/-!
# Nguyen's interface estimate on the actual Rademacher block coordinates

Every iid-square hypothesis is constructed from the literal physical row
product law. The only probability estimate input is the user-authorized
`NguyenBottomSingularInput`, with its range checked at parameter one.

The good event is finite-dimensional and may have a nonempty exceptional
set. No assertion of almost-sure invertibility is made.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators Matrix Matrix.Norms.L2Operator NNReal

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10 BernoulliLinearAlgebra

theorem normalized_rademacherIntervalSquare_B (W s : ℕ)
    (j : Fin s) (x : IntervalRows W s) (z : ℂ) :
    normalizedInterfaceMatrix (rademacherIntervalSquare W s j 0) x =
      (intervalSiteBlocks z x j).B := by
  ext a c
  simp [normalizedInterfaceMatrix, rademacherIntervalSquare,
    IidSubgaussianFamily.squareRestriction, IidSubgaussianSquare.rawMatrix,
    rademacherIntervalFamily, intervalSquareEntryEmbedding, intervalSiteBlocks,
    intervalPhysicalRow, physicalRowGroupOfAtoms, normalizedPhysicalAtom,
    blockNormalization, Complex.ofReal_mul]

theorem normalized_rademacherIntervalSquare_A (W s : ℕ)
    (j : Fin s) (x : IntervalRows W s) :
    normalizedInterfaceMatrix (rademacherIntervalSquare W s j 1) x =
      (intervalSiteBlocks 0 x j).D := by
  ext a c
  simp [normalizedInterfaceMatrix, rademacherIntervalSquare,
    IidSubgaussianFamily.squareRestriction, IidSubgaussianSquare.rawMatrix,
    rademacherIntervalFamily, intervalSquareEntryEmbedding, intervalSiteBlocks,
    intervalPhysicalRow, physicalRowGroupOfAtoms, normalizedPhysicalAtom,
    blockNormalization, Complex.ofReal_mul]

theorem normalized_rademacherIntervalSquare_C (W s : ℕ)
    (j : Fin s) (x : IntervalRows W s) (z : ℂ) :
    normalizedInterfaceMatrix (rademacherIntervalSquare W s j 2) x =
      (intervalSiteBlocks z x j).C := by
  ext a c
  simp [normalizedInterfaceMatrix, rademacherIntervalSquare,
    IidSubgaussianFamily.squareRestriction, IidSubgaussianSquare.rawMatrix,
    rademacherIntervalFamily, intervalSquareEntryEmbedding, intervalSiteBlocks,
    intervalPhysicalRow, physicalRowGroupOfAtoms, normalizedPhysicalAtom,
    blockNormalization, Complex.ofReal_mul]

/-- The site event controls B,A,C simultaneously. Including a determinant
condition for A is harmless and keeps one literal event family. -/
def rademacherSiteBadEvent (I : NguyenBottomSingularInput)
    (W s : ℕ) (j : Fin s) : Set (IntervalRows W s) :=
  ⋃ b : Fin 3, interfaceCombinedBadEvent I (rademacherIntervalSquare W s j b)

/-- The exceptional set for all block sites in the actual interval/ring. -/
def rademacherInterfaceBadEvent (I : NguyenBottomSingularInput) (W s : ℕ) :
    Set (IntervalRows W s) :=
  ⋃ j : Fin s, rademacherSiteBadEvent I W s j

theorem rademacherSiteBadEvent_probability_le
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (j : Fin s) (hW : interfaceCanonicalLargeWThreshold I ≤ W) :
    (intervalRowsLaw W s rademacherLaw).real (rademacherSiteBadEvent I W s j) ≤
      3 * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
  have hw := interfaceCanonicalLargeWConditions I hW
  apply measureReal_siteUnion_le
  intro b
  exact interfaceCombinedBadEvent_probability_exp
    (intervalRowsLaw W s rademacherLaw) I (rademacherIntervalSquare W s j b)
    (by simpa using hI) hw.1 hw.2.1 hw.2.2

theorem rademacherInterfaceBadEvent_probability_le
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W) :
    (intervalRowsLaw W s rademacherLaw).real (rademacherInterfaceBadEvent I W s) ≤
      3 * (s : ℝ) * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
  have h := measureReal_siteUnion_le (intervalRowsLaw W s rademacherLaw)
    (rademacherSiteBadEvent I W s)
    (3 * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)))
    (fun j => rademacherSiteBadEvent_probability_le I hI W s j hW)
  simpa only [rademacherInterfaceBadEvent, mul_left_comm, mul_assoc] using h

/-- Every actual normalized block has its quantitative interface estimates
outside the explicitly defined finite exceptional event. -/
theorem rademacherInterface_controls
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (x : IntervalRows W s) (hx : x ∉ rademacherInterfaceBadEvent I W s)
    (j : Fin s) (b : Fin 3) :
    let A := normalizedInterfaceMatrix (rademacherIntervalSquare W s j b) x
    ‖A‖ ≤ 40 * Real.sqrt 2 ∧
      Real.exp (-nguyenInterfaceDetLoss I (nguyenInterfaceCutoffRho I) * (W : ℝ)) ≤
        ‖A.det‖ ∧
      ‖A.det‖ ≤ (40 * Real.sqrt 2) ^ W ∧
      ‖A⁻¹‖ ≤ Real.exp (nguyenInterfaceInvLoss I * (W : ℝ)) := by
  have hw := interfaceCanonicalLargeWConditions I hW
  have hxb : x ∉ interfaceCombinedBadEvent I (rademacherIntervalSquare W s j b) := by
    intro h
    apply hx
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨b, h⟩⟩
  have h := (interfaceCanonicalDetUpperLowerInverseControl
    (intervalRowsLaw W s rademacherLaw) I (rademacherIntervalSquare W s j b)
      (by simpa using hI) hw.1 hw.2.1 hw.2.2).2 x hxb
  simpa only [← normalizedInterfaceMatrix, rademacherIntervalSquare_opNormConstant] using h

/-- Invertibility for B and C is a consequence on the good event, not an
almost-sure assertion for the finite Rademacher law. -/
theorem rademacherInterface_dets_isUnit_of_good
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (x : IntervalRows W s) (hx : x ∉ rademacherInterfaceBadEvent I W s)
    (z : ℂ) (j : Fin s) :
    IsUnit (intervalSiteBlocks z x j).B.det ∧
      IsUnit (intervalSiteBlocks z x j).C.det := by
  have hB := (rademacherInterface_controls I hI W s hW x hx j 0).2.1
  have hC := (rademacherInterface_controls I hI W s hW x hx j 2).2.1
  rw [normalized_rademacherIntervalSquare_B W s j x z] at hB
  rw [normalized_rademacherIntervalSquare_C W s j x z] at hC
  exact ⟨isUnit_iff_ne_zero.mpr (norm_pos_iff.mp ((Real.exp_pos _).trans_le hB)),
    isUnit_iff_ne_zero.mpr (norm_pos_iff.mp ((Real.exp_pos _).trans_le hC))⟩

/-- The actual all-interface exceptional probability vanishes under the
Section 8 bandwidth hypothesis. -/
theorem rademacherInterfaceBadEvent_probability_tendsto_zero
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log ((s n * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n => (intervalRowsLaw (W n) (s n) rademacherLaw).real
      (rademacherInterfaceBadEvent I (W n) (s n))) atTop (𝓝 0) := by
  apply tendsto_measureReal_siteUnion_zero s W hW hlog
    (fun n => intervalRowsLaw (W n) (s n) rademacherLaw)
    (fun n => rademacherSiteBadEvent I (W n) (s n)) 3
    (half_pos (interfaceCombinedRate_pos I))
  filter_upwards [hW.eventually
    (eventually_ge_atTop (interfaceCanonicalLargeWThreshold I))] with n hn j
  exact rademacherSiteBadEvent_probability_le I hI (W n) (s n) j hn

/-- The source's original `W / log N → ∞` form for rings with at least
four sites. -/
theorem rademacherInterfaceBadEvent_probability_tendsto_zero_of_bandwidth
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hs : ∀ᶠ n in atTop, 4 ≤ s n)
    (hband : Tendsto (fun n => (W n : ℝ) /
      Real.log ((s n * W n : ℕ) : ℝ)) atTop atTop) :
    Tendsto (fun n => (intervalRowsLaw (W n) (s n) rademacherLaw).real
      (rademacherInterfaceBadEvent I (W n) (s n))) atTop (𝓝 0) := by
  apply rademacherInterfaceBadEvent_probability_tendsto_zero I hI W s hW
  apply (bandwidth_div_log_tendsto_iff (fun n => s n * W n) W hW ?_).mp hband
  filter_upwards [hs] with n hn
  exact Nat.mul_le_mul_right (W n) hn

/-- The physical one-site norm part of (L1), with a fixed explicit constant. -/
theorem rademacherSite_norm_sum_le_of_good
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (x : IntervalRows W s) (hx : x ∉ rademacherInterfaceBadEvent I W s)
    (j : Fin s) :
    ‖(intervalSiteBlocks 0 x j).D‖ + ‖(intervalSiteBlocks 0 x j).B‖ +
      ‖(intervalSiteBlocks 0 x j).C‖ ≤ 120 * Real.sqrt 2 := by
  have hA := (rademacherInterface_controls I hI W s hW x hx j 1).1
  have hB := (rademacherInterface_controls I hI W s hW x hx j 0).1
  have hC := (rademacherInterface_controls I hI W s hW x hx j 2).1
  rw [normalized_rademacherIntervalSquare_A] at hA
  rw [normalized_rademacherIntervalSquare_B W s j x 0] at hB
  rw [normalized_rademacherIntervalSquare_C W s j x 0] at hC
  linarith

/-- The actual shifted middle block gains exactly the deterministic
operator-norm cost of the scalar spectral parameter. -/
theorem rademacherSite_shifted_norm_sum_le_of_good
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (x : IntervalRows W s) (hx : x ∉ rademacherInterfaceBadEvent I W s)
    (j : Fin s) (z : ℂ) :
    ‖(intervalSiteBlocks z x j).D‖ + ‖(intervalSiteBlocks z x j).B‖ +
      ‖(intervalSiteBlocks z x j).C‖ ≤ 120 * Real.sqrt 2 + ‖z‖ := by
  have hWpos := (interfaceCanonicalLargeWConditions I hW).1
  letI : NeZero W := ⟨ne_of_gt hWpos⟩
  have hD : (intervalSiteBlocks z x j).D = (intervalSiteBlocks 0 x j).D - z • 1 := by
    ext a c
    by_cases hac : a = c <;>
      simp [intervalSiteBlocks, intervalPhysicalRow, physicalRowGroupOfAtoms,
        Matrix.one_apply, hac]
  have hnorm : ‖(intervalSiteBlocks z x j).D‖ ≤ ‖(intervalSiteBlocks 0 x j).D‖ + ‖z‖ := by
    rw [hD]
    simpa only [norm_smul, norm_one, mul_one] using
      norm_sub_le ((intervalSiteBlocks 0 x j).D) (z • (1 : Matrix (Fin W) (Fin W) ℂ))
  have hraw := rademacherSite_norm_sum_le_of_good I hI W s hW x hx j
  have hB : (intervalSiteBlocks z x j).B = (intervalSiteBlocks 0 x j).B := rfl
  have hC : (intervalSiteBlocks z x j).C = (intervalSiteBlocks 0 x j).C := rfl
  rw [hB, hC]
  linarith

/-- Endpoint data for any selected packet's physical outer interfaces are
constructed on the same global event. -/
theorem rademacherEndpointGood_of_good
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (x : IntervalRows W s) (hx : x ∉ rademacherInterfaceBadEvent I W s)
    (jL jR : Fin s) (z : ℂ) :
    PaperEndpointGood (intervalSiteBlocks z x jL).C (intervalSiteBlocks z x jR).B
      (40 * Real.sqrt 2) (interfaceDeterminantLowerBound I W) := by
  have hL := rademacherInterface_controls I hI W s hW x hx jL 2
  have hR := rademacherInterface_controls I hI W s hW x hx jR 0
  dsimp only at hL hR
  rw [normalized_rademacherIntervalSquare_C W s jL x z] at hL
  rw [normalized_rademacherIntervalSquare_B W s jR x z] at hR
  exact ⟨hL.1, hR.1, interfaceDeterminantLowerBound_pos I W, hL.2.1, hR.2.1⟩

/-- The cleared products have the actual transfer representation on the
high-probability event; unlike the density API this does not claim the
event has full measure at any finite size. -/
theorem rademacherIntervalTransfer_representation_of_good
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (x : IntervalRows W s) (hx : x ∉ rademacherInterfaceBadEvent I W s)
    (z : ℂ) :
    intervalClearingFactor W s z x ≠ 0 ∧
      IsUnit (intervalTransferProduct W s z x).det ∧
      ∀ r : Fin (2 * W + 1), intervalClearedProduct W s z x r =
        intervalClearingFactor W s z x • compound r.1 (intervalTransferProduct W s z x) := by
  have hdet := rademacherInterface_dets_isUnit_of_good I hI W s hW x hx z
  exact ⟨intervalClearingFactor_ne_zero W s z x (fun j => (hdet j).1),
    intervalTransferProduct_det_isUnit W s z x
      (fun j => (hdet j).1) (fun j => (hdet j).2),
    intervalClearedProduct_eq_clearing_smul_compound W s z x (fun j => (hdet j).1)⟩

/-- A literal measurable good event on this interval's own finite support. -/
def rademacherInterfaceGoodEvent (I : NguyenBottomSingularInput) (W s : ℕ) :
    Set (IntervalRows W s) :=
  rademacherGoodEvent W s (rademacherInterfaceBadEvent I W s)

theorem measurableSet_rademacherInterfaceGoodEvent
    (I : NguyenBottomSingularInput) (W s : ℕ) :
    MeasurableSet (rademacherInterfaceGoodEvent I W s) :=
  measurableSet_rademacherGoodEvent W s _

theorem rademacherInterfaceGoodEvent_spec
    (I : NguyenBottomSingularInput) (W s : ℕ)
    {x : IntervalRows W s} (hx : x ∈ rademacherInterfaceGoodEvent I W s) :
    (∀ i a, x i a = 1 ∨ x i a = -1) ∧
      x ∉ rademacherInterfaceBadEvent I W s :=
  hx

theorem rademacherInterfaceGoodEvent_compl_probability_eq
    (I : NguyenBottomSingularInput) (W s : ℕ) :
    (intervalRowsLaw W s rademacherLaw).real (rademacherInterfaceGoodEvent I W s)ᶜ =
      (intervalRowsLaw W s rademacherLaw).real (rademacherInterfaceBadEvent I W s) :=
  measureReal_rademacherGoodEvent_compl W s _

theorem rademacherInterfaceGoodEvent_compl_probability_le
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W) :
    (intervalRowsLaw W s rademacherLaw).real (rademacherInterfaceGoodEvent I W s)ᶜ ≤
      3 * (s : ℝ) * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
  rw [rademacherInterfaceGoodEvent_compl_probability_eq]
  exact rademacherInterfaceBadEvent_probability_le I hI W s hW

theorem rademacherInterfaceGoodEvent_compl_probability_tendsto_zero
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log ((s n * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n => (intervalRowsLaw (W n) (s n) rademacherLaw).real
      (rademacherInterfaceGoodEvent I (W n) (s n))ᶜ) atTop (𝓝 0) := by
  simp_rw [rademacherInterfaceGoodEvent_compl_probability_eq]
  exact rademacherInterfaceBadEvent_probability_tendsto_zero I hI W s hW hlog

theorem rademacherInterfaceGoodEvent_compl_probability_tendsto_zero_of_bandwidth
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hs : ∀ᶠ n in atTop, 4 ≤ s n)
    (hband : Tendsto (fun n => (W n : ℝ) /
      Real.log ((s n * W n : ℕ) : ℝ)) atTop atTop) :
    Tendsto (fun n => (intervalRowsLaw (W n) (s n) rademacherLaw).real
      (rademacherInterfaceGoodEvent I (W n) (s n))ᶜ) atTop (𝓝 0) := by
  simp_rw [rademacherInterfaceGoodEvent_compl_probability_eq]
  exact rademacherInterfaceBadEvent_probability_tendsto_zero_of_bandwidth I hI W s hW hs hband

/-- A cell/subinterval event is the pullback of the good event built from
that subinterval's own coordinates. This retains its local measurability. -/
def rademacherSubintervalGoodEvent (I : NguyenBottomSingularInput)
    {W s t : ℕ} (e : Fin t ↪ Fin s) : Set (IntervalRows W s) :=
  intervalRestriction e ⁻¹' rademacherInterfaceGoodEvent I W t

theorem measurableSet_rademacherSubintervalGoodEvent
    (I : NguyenBottomSingularInput) {W s t : ℕ} (e : Fin t ↪ Fin s) :
    MeasurableSet (rademacherSubintervalGoodEvent (W := W) I e) := by
  apply (measurableSet_rademacherInterfaceGoodEvent I W t).preimage
  unfold intervalRestriction
  fun_prop

theorem rademacherSubintervalGoodEvent_compl_probability_le
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    {W s t : ℕ} (e : Fin t ↪ Fin s)
    (hW : interfaceCanonicalLargeWThreshold I ≤ W) :
    (intervalRowsLaw W s rademacherLaw).real
      (rademacherSubintervalGoodEvent (W := W) I e)ᶜ ≤
        3 * (t : ℝ) * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
  have hp : MeasurePreserving (intervalRestriction (W := W) e)
      (intervalRowsLaw W s rademacherLaw) (intervalRowsLaw W t rademacherLaw) :=
    measurePreserving_pi_restrict_embedding
      (physicalRowLaw W rademacherLaw) (intervalRowEmbedding e)
  have hmeasure :
      (intervalRowsLaw W s rademacherLaw).real
          (rademacherSubintervalGoodEvent (W := W) I e)ᶜ =
        (intervalRowsLaw W t rademacherLaw).real (rademacherInterfaceGoodEvent I W t)ᶜ := by
    unfold rademacherSubintervalGoodEvent
    simp only [← preimage_compl, measureReal_def]
    rw [← hp.map_eq, Measure.map_apply hp.measurable
      (measurableSet_rademacherInterfaceGoodEvent I W t).compl]
  rw [hmeasure]
  exact rademacherInterfaceGoodEvent_compl_probability_le I hI W t hW

theorem rademacherIntervalSquare_rawMatrix_restriction
    {W s t : ℕ} (e : Fin t ↪ Fin s) (j : Fin t) (b : Fin 3)
    (x : IntervalRows W s) :
    (rademacherIntervalSquare W t j b).rawMatrix (intervalRestriction e x) =
      (rademacherIntervalSquare W s (e j) b).rawMatrix x := by
  ext a c
  simp [IidSubgaussianSquare.rawMatrix, rademacherIntervalSquare,
    IidSubgaussianFamily.squareRestriction, rademacherIntervalFamily,
    intervalSquareEntryEmbedding, intervalRestriction]

theorem rademacherCombinedBadEvent_restriction_iff
    (I : NguyenBottomSingularInput) {W s t : ℕ}
    (e : Fin t ↪ Fin s) (j : Fin t) (b : Fin 3) (x : IntervalRows W s) :
    intervalRestriction e x ∈ interfaceCombinedBadEvent I (rademacherIntervalSquare W t j b) ↔
      x ∈ interfaceCombinedBadEvent I (rademacherIntervalSquare W s (e j) b) := by
  simp only [interfaceCombinedBadEvent, nguyenInterfaceBadEvent,
    nguyenInterfaceBadAt, subgaussianOpNormBadEvent, Set.mem_union,
    Set.mem_iUnion, Set.mem_setOf_eq, rademacherIntervalSquare_rawMatrix_restriction,
    rademacherIntervalSquare_opNormConstant]

/-- One all-site event certifies every selected interval simultaneously;
no union over the collection of intervals is needed. -/
theorem rademacherInterfaceGoodEvent_subset_subinterval
    (I : NguyenBottomSingularInput) {W s t : ℕ} (e : Fin t ↪ Fin s) :
    rademacherInterfaceGoodEvent I W s ⊆ rademacherSubintervalGoodEvent (W := W) I e := by
  intro x hx
  refine ⟨?_, ?_⟩
  · intro i a
    exact hx.1 _ _
  · intro hbad
    rcases mem_iUnion.mp hbad with ⟨j, hj⟩
    rcases mem_iUnion.mp hj with ⟨b, hb⟩
    apply hx.2
    exact mem_iUnion.mpr ⟨e j, mem_iUnion.mpr ⟨b,
      (rademacherCombinedBadEvent_restriction_iff I e j b x).mp hb⟩⟩

end BernoulliSection8
