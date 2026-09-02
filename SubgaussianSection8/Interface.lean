import SubgaussianSection8.IID
import BernoulliSection8.BandwidthLedger
import BernoulliSection9.InterfaceCanonicalLargeW
import BernoulliSection10.PhysicalProbabilityInstances
import BernoulliSection10.IntervalTransfer

/-!
# Nguyen's interface estimate on the actual subgaussian block coordinates

Every IID-square hypothesis is constructed from the physical row product law.
The atom parameter is checked against the explicit Nguyen input range.

The good event is finite-dimensional and may have a nonempty exceptional
set. No assertion of almost-sure invertibility is made.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators Matrix Matrix.Norms.L2Operator NNReal

noncomputable section

namespace SubgaussianSection8

open BernoulliSection8 BernoulliSection9 BernoulliSection10 BernoulliLinearAlgebra

local instance rademacherInterfaceSumOrder (W : ℕ) : LinearOrder (Fin W ⊕ Fin W) :=
  LinearOrder.lift' (fun x : Fin W ⊕ Fin W => (toLex x : Fin W ⊕ₗ Fin W))
    (fun _ _ h => toLex.injective h)

@[simp] theorem subgaussianIntervalSquare_rawMatrix_apply (A : Atom) (W s : ℕ)
    (j : Fin s) (b : Fin 3) (x : IntervalRows W s) (a c : Fin W) :
    ((intervalSquare A) W s j b).rawMatrix x a c =
      (x (intervalRowIndex j a) (physicalAtomIndex b c) : ℂ) := rfl

theorem normalized_subgaussianIntervalSquare_B (A : Atom) (W s : ℕ)
    (j : Fin s) (x : IntervalRows W s) (z : ℂ) :
    normalizedInterfaceMatrix ((intervalSquare A) W s j 0) x =
      (intervalSiteBlocks z x j).B := by
  ext a c
  simp only [normalizedInterfaceMatrix, Matrix.smul_apply, smul_eq_mul,
    (subgaussianIntervalSquare_rawMatrix_apply A), intervalSiteBlocks,
    intervalPhysicalRow, physicalRowGroupOfAtoms, normalizedPhysicalAtom,
    blockNormalization, Complex.ofReal_mul]

theorem normalized_subgaussianIntervalSquare_A (A : Atom) (W s : ℕ)
    (j : Fin s) (x : IntervalRows W s) :
    normalizedInterfaceMatrix ((intervalSquare A) W s j 1) x =
      (intervalSiteBlocks 0 x j).D := by
  ext a c
  simp only [normalizedInterfaceMatrix, Matrix.smul_apply, smul_eq_mul,
    (subgaussianIntervalSquare_rawMatrix_apply A), intervalSiteBlocks,
    intervalPhysicalRow, physicalRowGroupOfAtoms, normalizedPhysicalAtom,
    blockNormalization, Complex.ofReal_mul, ite_self, sub_zero]

theorem normalized_subgaussianIntervalSquare_C (A : Atom) (W s : ℕ)
    (j : Fin s) (x : IntervalRows W s) (z : ℂ) :
    normalizedInterfaceMatrix ((intervalSquare A) W s j 2) x =
      (intervalSiteBlocks z x j).C := by
  ext a c
  simp only [normalizedInterfaceMatrix, Matrix.smul_apply, smul_eq_mul,
    (subgaussianIntervalSquare_rawMatrix_apply A), intervalSiteBlocks,
    intervalPhysicalRow, physicalRowGroupOfAtoms, normalizedPhysicalAtom,
    blockNormalization, Complex.ofReal_mul]

/-- The directly measurable control event for a single actual normalized block. -/
def blockControl (A : Atom) (I : NguyenBottomSingularInput.{0, 0})
    {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ) : Prop :=
  ‖M‖ ≤ opNormConstant A ∧
    Real.exp (-nguyenInterfaceDetLoss I (nguyenInterfaceCutoffRho I) * (W : ℝ)) ≤ ‖M.det‖ ∧
    ‖M.det‖ ≤ opNormConstant A ^ W ∧
    ‖M⁻¹‖ ≤ Real.exp (nguyenInterfaceInvLoss I * (W : ℝ))

def blockBadEvent (A : Atom) (I : NguyenBottomSingularInput.{0, 0})
    (W s : ℕ) (j : Fin s) (b : Fin 3) : Set (IntervalRows W s) :=
  {x | ¬blockControl A I (normalizedInterfaceMatrix (intervalSquare A W s j b) x)}

theorem measurableSet_blockBadEvent (A : Atom) (I : NguyenBottomSingularInput.{0, 0})
    (W s : ℕ) (j : Fin s) (b : Fin 3) :
    MeasurableSet (blockBadEvent A I W s j b) := by
  let T := fun x => normalizedInterfaceMatrix (intervalSquare A W s j b) x
  have hT : Continuous T := by
    apply continuous_pi
    intro a
    apply continuous_pi
    intro c
    dsimp only [T]
    simp only [normalizedInterfaceMatrix, Matrix.smul_apply, smul_eq_mul,
      intervalSquare_rawMatrix_apply]
    fun_prop
  have hInv : Measurable (fun x => (T x)⁻¹) := by
    simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
    exact hT.matrix_det.measurable.inv.smul hT.matrix_adjugate.measurable
  exact ((measurableSet_le hT.norm.measurable measurable_const).inter
    ((measurableSet_le measurable_const hT.matrix_det.norm.measurable).inter
      ((measurableSet_le hT.matrix_det.norm.measurable measurable_const).inter
        (measurableSet_le hInv.norm measurable_const)))).compl

/-- The site event controls the three physical blocks simultaneously. -/
def subgaussianSiteBadEvent (A : Atom) (I : NguyenBottomSingularInput.{0, 0})
    (W s : ℕ) (j : Fin s) : Set (IntervalRows W s) :=
  ⋃ b : Fin 3, blockBadEvent A I W s j b

/-- The exceptional set for all block sites in the actual interval/ring. -/
def subgaussianInterfaceBadEvent (A : Atom) (I : NguyenBottomSingularInput.{0, 0}) (W s : ℕ) :
    Set (IntervalRows W s) :=
  ⋃ j : Fin s, (subgaussianSiteBadEvent A) I W s j

theorem subgaussianSiteBadEvent_probability_le (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : A.parameter ≤ I.subgaussianBound)
    (W s : ℕ) (j : Fin s) (hW : interfaceCanonicalLargeWThreshold I ≤ W) :
    (intervalRowsLaw W s A.law).real ((subgaussianSiteBadEvent A) I W s j) ≤
      3 * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
  have hw := interfaceCanonicalLargeWConditions I hW
  apply measureReal_siteUnion_le
  intro b
  have h := interfaceCanonicalDetUpperLowerInverseControl
    (intervalRowsLaw W s A.law) I (intervalSquare A W s j b)
    (by simpa using hI) hw.1 hw.2.1 hw.2.2
  apply (measureReal_mono (fun x hx => ?_)).trans h.1
  by_contra hnot
  apply hx
  simpa only [blockControl, normalizedInterfaceMatrix, intervalSquare_opNormConstant] using h.2 x hnot

theorem subgaussianInterfaceBadEvent_probability_le (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : A.parameter ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W) :
    (intervalRowsLaw W s A.law).real ((subgaussianInterfaceBadEvent A) I W s) ≤
      3 * (s : ℝ) * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
  have h := measureReal_siteUnion_le (intervalRowsLaw W s A.law)
    ((subgaussianSiteBadEvent A) I W s)
    (3 * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)))
    (fun j => (subgaussianSiteBadEvent_probability_le A) I hI W s j hW)
  simpa only [(subgaussianInterfaceBadEvent A), mul_left_comm, mul_assoc] using h

/-- Every actual normalized block has its quantitative interface estimates
outside the explicitly defined finite exceptional event. -/
theorem subgaussianInterface_controls (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : A.parameter ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (x : IntervalRows W s) (hx : x ∉ (subgaussianInterfaceBadEvent A) I W s)
    (j : Fin s) (b : Fin 3) :
    let M := normalizedInterfaceMatrix (intervalSquare A W s j b) x
    ‖M‖ ≤ opNormConstant A ∧
      Real.exp (-nguyenInterfaceDetLoss I (nguyenInterfaceCutoffRho I) * (W : ℝ)) ≤ ‖M.det‖ ∧
      ‖M.det‖ ≤ opNormConstant A ^ W ∧
      ‖M⁻¹‖ ≤ Real.exp (nguyenInterfaceInvLoss I * (W : ℝ)) := by
  have hxb : x ∉ blockBadEvent A I W s j b := by
    intro h
    apply hx
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨b, h⟩⟩
  exact not_not.mp hxb

/-- Invertibility for B and C is a consequence on the good event, not an
almost-sure assertion for the finite subgaussian law. -/
theorem subgaussianInterface_dets_isUnit_of_good (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : A.parameter ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (x : IntervalRows W s) (hx : x ∉ (subgaussianInterfaceBadEvent A) I W s)
    (z : ℂ) (j : Fin s) :
    IsUnit (intervalSiteBlocks z x j).B.det ∧
      IsUnit (intervalSiteBlocks z x j).C.det := by
  have hB := ((subgaussianInterface_controls A) I hI W s hW x hx j 0).2.1
  have hC := ((subgaussianInterface_controls A) I hI W s hW x hx j 2).2.1
  rw [(normalized_subgaussianIntervalSquare_B A) W s j x z] at hB
  rw [(normalized_subgaussianIntervalSquare_C A) W s j x z] at hC
  exact ⟨isUnit_iff_ne_zero.mpr (norm_pos_iff.mp ((Real.exp_pos _).trans_le hB)),
    isUnit_iff_ne_zero.mpr (norm_pos_iff.mp ((Real.exp_pos _).trans_le hC))⟩

/-- The actual all-interface exceptional probability vanishes under the
Section 8 bandwidth hypothesis. -/
theorem subgaussianInterfaceBadEvent_probability_tendsto_zero (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : A.parameter ≤ I.subgaussianBound)
    (W s : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log ((s n * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n => (intervalRowsLaw (W n) (s n) A.law).real
      ((subgaussianInterfaceBadEvent A) I (W n) (s n))) atTop (𝓝 0) := by
  apply tendsto_measureReal_siteUnion_zero s W hW hlog
    (fun n => intervalRowsLaw (W n) (s n) A.law)
    (fun n => (subgaussianSiteBadEvent A) I (W n) (s n)) 3
    (half_pos (interfaceCombinedRate_pos I))
  filter_upwards [hW.eventually
    (eventually_ge_atTop (interfaceCanonicalLargeWThreshold I))] with n hn j
  exact (subgaussianSiteBadEvent_probability_le A) I hI (W n) (s n) j hn

/-- The source's original `W / log N → ∞` form for rings with at least
four sites. -/
theorem subgaussianInterfaceBadEvent_probability_tendsto_zero_of_bandwidth (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : A.parameter ≤ I.subgaussianBound)
    (W s : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hs : ∀ᶠ n in atTop, 4 ≤ s n)
    (hband : Tendsto (fun n => (W n : ℝ) /
      Real.log ((s n * W n : ℕ) : ℝ)) atTop atTop) :
    Tendsto (fun n => (intervalRowsLaw (W n) (s n) A.law).real
      ((subgaussianInterfaceBadEvent A) I (W n) (s n))) atTop (𝓝 0) := by
  apply (subgaussianInterfaceBadEvent_probability_tendsto_zero A) I hI W s hW
  apply (bandwidth_div_log_tendsto_iff (fun n => s n * W n) W hW ?_).mp hband
  filter_upwards [hs] with n hn
  exact Nat.mul_le_mul_right (W n) hn

/-- The physical one-site norm part of (L1), with a fixed explicit constant. -/
theorem subgaussianSite_norm_sum_le_of_good (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : A.parameter ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (x : IntervalRows W s) (hx : x ∉ (subgaussianInterfaceBadEvent A) I W s)
    (j : Fin s) :
    ‖(intervalSiteBlocks 0 x j).D‖ + ‖(intervalSiteBlocks 0 x j).B‖ +
      ‖(intervalSiteBlocks 0 x j).C‖ ≤ 3 * opNormConstant A := by
  have hA := ((subgaussianInterface_controls A) I hI W s hW x hx j 1).1
  have hB := ((subgaussianInterface_controls A) I hI W s hW x hx j 0).1
  have hC := ((subgaussianInterface_controls A) I hI W s hW x hx j 2).1
  rw [(normalized_subgaussianIntervalSquare_A A)] at hA
  rw [(normalized_subgaussianIntervalSquare_B A) W s j x 0] at hB
  rw [(normalized_subgaussianIntervalSquare_C A) W s j x 0] at hC
  linarith

/-- The actual shifted middle block gains exactly the deterministic
operator-norm cost of the scalar spectral parameter. -/
theorem subgaussianSite_shifted_norm_sum_le_of_good (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : A.parameter ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (x : IntervalRows W s) (hx : x ∉ (subgaussianInterfaceBadEvent A) I W s)
    (j : Fin s) (z : ℂ) :
    ‖(intervalSiteBlocks z x j).D‖ + ‖(intervalSiteBlocks z x j).B‖ +
      ‖(intervalSiteBlocks z x j).C‖ ≤ 3 * opNormConstant A + ‖z‖ := by
  have hWpos := (interfaceCanonicalLargeWConditions I hW).1
  letI : NeZero W := ⟨ne_of_gt hWpos⟩
  have hD : (intervalSiteBlocks z x j).D = (intervalSiteBlocks 0 x j).D - z • 1 := by
    ext a c
    change normalizedPhysicalAtom (x (intervalRowIndex j a)) 1 c -
        (if a = c then z else 0) =
      (normalizedPhysicalAtom (x (intervalRowIndex j a)) 1 c -
        (if a = c then (0 : ℂ) else 0)) - z * (if a = c then 1 else 0)
    by_cases hac : a = c <;> simp [hac]
  have hnorm : ‖(intervalSiteBlocks z x j).D‖ ≤ ‖(intervalSiteBlocks 0 x j).D‖ + ‖z‖ := by
    rw [hD]
    simpa only [norm_smul, norm_one, mul_one] using
      norm_sub_le ((intervalSiteBlocks 0 x j).D) (z • (1 : Matrix (Fin W) (Fin W) ℂ))
  have hraw := (subgaussianSite_norm_sum_le_of_good A) I hI W s hW x hx j
  have hB : (intervalSiteBlocks z x j).B = (intervalSiteBlocks 0 x j).B := rfl
  have hC : (intervalSiteBlocks z x j).C = (intervalSiteBlocks 0 x j).C := rfl
  rw [hB, hC]
  linarith

/-- Endpoint data for any selected packet's physical outer interfaces are
constructed on the same global event. -/
theorem subgaussianEndpointGood_of_good (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : A.parameter ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (x : IntervalRows W s) (hx : x ∉ (subgaussianInterfaceBadEvent A) I W s)
    (jL jR : Fin s) (z : ℂ) :
    PaperEndpointGood (intervalSiteBlocks z x jL).C (intervalSiteBlocks z x jR).B
      (opNormConstant A) (interfaceDeterminantLowerBound I W) := by
  have hL := (subgaussianInterface_controls A) I hI W s hW x hx jL 2
  have hR := (subgaussianInterface_controls A) I hI W s hW x hx jR 0
  dsimp only at hL hR
  rw [(normalized_subgaussianIntervalSquare_C A) W s jL x z] at hL
  rw [(normalized_subgaussianIntervalSquare_B A) W s jR x z] at hR
  exact ⟨hL.1, hR.1, interfaceDeterminantLowerBound_pos I W, hL.2.1, hR.2.1⟩

/-- The cleared products have the actual transfer representation on the
high-probability event; unlike the density API this does not claim the
event has full measure at any finite size. -/
theorem subgaussianIntervalTransfer_representation_of_good (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : A.parameter ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (x : IntervalRows W s) (hx : x ∉ (subgaussianInterfaceBadEvent A) I W s)
    (z : ℂ) :
    intervalClearingFactor W s z x ≠ 0 ∧
      IsUnit (intervalTransferProduct W s z x).det ∧
      ∀ r : Fin (2 * W + 1), intervalClearedProduct W s z x r =
        intervalClearingFactor W s z x • compound r.1 (intervalTransferProduct W s z x) := by
  have hdet := (subgaussianInterface_dets_isUnit_of_good A) I hI W s hW x hx z
  exact ⟨intervalClearingFactor_ne_zero W s z x (fun j => (hdet j).1),
    intervalTransferProduct_det_isUnit W s z x
      (fun j => (hdet j).1) (fun j => (hdet j).2),
    intervalClearedProduct_eq_clearing_smul_compound W s z x (fun j => (hdet j).1)⟩

/-- All physical block controls hold on this measurable event.
It depends only on the interval's own coordinates and is preserved by restriction. -/
def subgaussianInterfaceGoodEvent (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (W s : ℕ) : Set (IntervalRows W s) :=
  (subgaussianInterfaceBadEvent A I W s)ᶜ

theorem measurableSet_subgaussianInterfaceGoodEvent (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (W s : ℕ) :
    MeasurableSet (subgaussianInterfaceGoodEvent A I W s) := by
  apply MeasurableSet.compl
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun b =>
    measurableSet_blockBadEvent A I W s j b

theorem subgaussianInterfaceGoodEvent_spec (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (W s : ℕ) (x : IntervalRows W s)
    (hx : x ∈ subgaussianInterfaceGoodEvent A I W s) :
    x ∉ subgaussianInterfaceBadEvent A I W s := hx

theorem subgaussianInterfaceGoodEvent_compl_probability_eq (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (W s : ℕ) :
    (intervalRowsLaw W s A.law).real (subgaussianInterfaceGoodEvent A I W s)ᶜ =
      (intervalRowsLaw W s A.law).real (subgaussianInterfaceBadEvent A I W s) := by
  simp only [subgaussianInterfaceGoodEvent, compl_compl]

theorem subgaussianInterfaceGoodEvent_compl_probability_le (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : A.parameter ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W) :
    (intervalRowsLaw W s A.law).real ((subgaussianInterfaceGoodEvent A) I W s)ᶜ ≤
      3 * (s : ℝ) * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
  rw [(subgaussianInterfaceGoodEvent_compl_probability_eq A)]
  exact (subgaussianInterfaceBadEvent_probability_le A) I hI W s hW

theorem subgaussianInterfaceGoodEvent_compl_probability_tendsto_zero (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : A.parameter ≤ I.subgaussianBound)
    (W s : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hlog : Tendsto (fun n => Real.log ((s n * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n => (intervalRowsLaw (W n) (s n) A.law).real
      ((subgaussianInterfaceGoodEvent A) I (W n) (s n))ᶜ) atTop (𝓝 0) := by
  simp_rw [(subgaussianInterfaceGoodEvent_compl_probability_eq A)]
  exact (subgaussianInterfaceBadEvent_probability_tendsto_zero A) I hI W s hW hlog

theorem subgaussianInterfaceGoodEvent_compl_probability_tendsto_zero_of_bandwidth (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : A.parameter ≤ I.subgaussianBound)
    (W s : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hs : ∀ᶠ n in atTop, 4 ≤ s n)
    (hband : Tendsto (fun n => (W n : ℝ) /
      Real.log ((s n * W n : ℕ) : ℝ)) atTop atTop) :
    Tendsto (fun n => (intervalRowsLaw (W n) (s n) A.law).real
      ((subgaussianInterfaceGoodEvent A) I (W n) (s n))ᶜ) atTop (𝓝 0) := by
  simp_rw [(subgaussianInterfaceGoodEvent_compl_probability_eq A)]
  exact (subgaussianInterfaceBadEvent_probability_tendsto_zero_of_bandwidth A) I hI W s hW hs hband

/-- A cell/subinterval event is the pullback of the good event built from
that subinterval's own coordinates. This retains its local measurability. -/
def subgaussianSubintervalGoodEvent (A : Atom) (I : NguyenBottomSingularInput.{0, 0})
    {W s t : ℕ} (e : Fin t ↪ Fin s) : Set (IntervalRows W s) :=
  intervalRestriction e ⁻¹' (subgaussianInterfaceGoodEvent A) I W t

theorem measurableSet_subgaussianSubintervalGoodEvent (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) {W s t : ℕ} (e : Fin t ↪ Fin s) :
    MeasurableSet ((subgaussianSubintervalGoodEvent A) (W := W) I e) := by
  apply ((measurableSet_subgaussianInterfaceGoodEvent A) I W t).preimage
  unfold intervalRestriction
  fun_prop

theorem subgaussianSubintervalGoodEvent_compl_probability_le (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) (hI : A.parameter ≤ I.subgaussianBound)
    {W s t : ℕ} (e : Fin t ↪ Fin s)
    (hW : interfaceCanonicalLargeWThreshold I ≤ W) :
    (intervalRowsLaw W s A.law).real
      ((subgaussianSubintervalGoodEvent A) (W := W) I e)ᶜ ≤
        3 * (t : ℝ) * Real.exp (-(interfaceCombinedRate I / 2) * (W : ℝ)) := by
  have hp : MeasurePreserving (intervalRestriction (W := W) e)
      (intervalRowsLaw W s A.law) (intervalRowsLaw W t A.law) :=
    measurePreserving_pi_restrict_embedding
      (physicalRowLaw W A.law) (intervalRowEmbedding e)
  have hmeasure :
      (intervalRowsLaw W s A.law).real
          ((subgaussianSubintervalGoodEvent A) (W := W) I e)ᶜ =
        (intervalRowsLaw W t A.law).real ((subgaussianInterfaceGoodEvent A) I W t)ᶜ := by
    unfold subgaussianSubintervalGoodEvent
    simp only [← preimage_compl, measureReal_def]
    rw [← hp.map_eq, Measure.map_apply hp.measurable
      ((measurableSet_subgaussianInterfaceGoodEvent A) I W t).compl]
  rw [hmeasure]
  exact (subgaussianInterfaceGoodEvent_compl_probability_le A) I hI W t hW

theorem subgaussianIntervalSquare_rawMatrix_restriction (A : Atom)
    {W s t : ℕ} (e : Fin t ↪ Fin s) (j : Fin t) (b : Fin 3)
    (x : IntervalRows W s) :
    ((intervalSquare A) W t j b).rawMatrix (intervalRestriction e x) =
      ((intervalSquare A) W s (e j) b).rawMatrix x := by
  ext a c
  simp only [(subgaussianIntervalSquare_rawMatrix_apply A), intervalRestriction,
    Function.comp_apply, intervalRowEmbedding_rowIndex]

theorem subgaussianCombinedBadEvent_restriction_iff (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) {W s t : ℕ}
    (e : Fin t ↪ Fin s) (j : Fin t) (b : Fin 3) (x : IntervalRows W s) :
    intervalRestriction e x ∈ blockBadEvent A I W t j b ↔
      x ∈ blockBadEvent A I W s (e j) b := by
  simp only [blockBadEvent, Set.mem_setOf_eq, normalizedInterfaceMatrix,
    subgaussianIntervalSquare_rawMatrix_restriction]

/-- One global event certifies every selected interval, without an extra union bound. -/
theorem subgaussianInterfaceGoodEvent_subset_subinterval (A : Atom)
    (I : NguyenBottomSingularInput.{0, 0}) {W s t : ℕ} (e : Fin t ↪ Fin s) :
    subgaussianInterfaceGoodEvent A I W s ⊆ subgaussianSubintervalGoodEvent A (W := W) I e := by
  intro x hx hbad
  rcases mem_iUnion.mp hbad with ⟨j, hj⟩
  rcases mem_iUnion.mp hj with ⟨b, hb⟩
  exact hx (mem_iUnion.mpr ⟨e j, mem_iUnion.mpr ⟨b,
    (subgaussianCombinedBadEvent_restriction_iff A I e j b x).mp hb⟩⟩)

end SubgaussianSection8
