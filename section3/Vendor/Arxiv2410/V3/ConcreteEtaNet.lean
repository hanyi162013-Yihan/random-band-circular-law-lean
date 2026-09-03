/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/ConcreteEtaNet.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.EtaUniformization
import Vendor.Arxiv2410.V3.Proposition34
import Mathlib.Algebra.Order.Floor.Ring

/-!
# An explicit finite net for the spectral domain in v3 Proposition 3.4

The final clause of arXiv:2410.16457v3, Proposition 3.4 uses

`Im eta > 0`, `‖eta‖ <= 5`, and `v0 <= Im eta`,

where `v0 = B^(-1/8) n^(c')`.  This file constructs an actual finite net for this set.
The construction rounds the absolute value of the real coordinate *towards zero* and rounds
the imaginary coordinate *downwards from `v0`*.  Consequently both coordinate magnitudes can
only decrease, so every centre remains in the radius-five disk.  No compactness or net-existence
hypothesis is used.
-/

namespace Arxiv2410V3

open Complex MeasureTheory Set

noncomputable section

/-- The v3 `eta` domain with its lower imaginary cutoff exposed as a parameter. -/
def EtaDomainAtScale (v0 : ℝ) : Set ℂ :=
  {eta | InUpperHalfPlane eta ∧ ‖eta‖ ≤ 5 ∧ v0 ≤ eta.im}

/-- v3 Proposition 3.4: its written domain is `EtaDomainAtScale` at the paper's scale. -/
theorem proposition34EtaDomain_iff_mem_etaDomainAtScale
    (n : ℕ) (B cPrime : ℝ) (eta : ℂ) :
    Proposition34EtaDomain n B cPrime eta ↔
      eta ∈ EtaDomainAtScale
        (Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n cPrime) := by
  rfl

/-- Round a nonnegative real number down to the preceding multiple of `delta`. -/
def roundDown (delta x : ℝ) : ℝ :=
  (Nat.floor (x / delta) : ℝ) * delta

theorem roundDown_nonneg {delta x : ℝ} (hdelta : 0 ≤ delta) :
    0 ≤ roundDown delta x := by
  exact mul_nonneg (Nat.cast_nonneg _) hdelta

theorem roundDown_le {delta x : ℝ} (hdelta : 0 < delta) (hx : 0 ≤ x) :
    roundDown delta x ≤ x := by
  have hratio : 0 ≤ x / delta := div_nonneg hx hdelta.le
  calc
    roundDown delta x = (Nat.floor (x / delta) : ℝ) * delta := rfl
    _ ≤ (x / delta) * delta :=
      mul_le_mul_of_nonneg_right (Nat.floor_le hratio) hdelta.le
    _ = x := div_mul_cancel₀ x hdelta.ne'

theorem sub_roundDown_lt {delta x : ℝ} (hdelta : 0 < delta) :
    x - roundDown delta x < delta := by
  have h := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (x / delta)) hdelta
  rw [div_mul_cancel₀ x hdelta.ne'] at h
  rw [sub_lt_iff_lt_add]
  simpa only [roundDown, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using h

/-- Signed rounding towards zero.  This is the horizontal coordinate of the concrete net. -/
def signedRoundDown (delta x : ℝ) : ℝ :=
  if 0 ≤ x then roundDown delta x else -roundDown delta (-x)

theorem abs_signedRoundDown_le_abs {delta x : ℝ} (hdelta : 0 < delta) :
    |signedRoundDown delta x| ≤ |x| := by
  by_cases hx : 0 ≤ x
  · have hrd0 : 0 ≤ roundDown delta x := roundDown_nonneg hdelta.le
    simp only [signedRoundDown, if_pos hx, abs_of_nonneg hrd0, abs_of_nonneg hx]
    exact roundDown_le hdelta hx
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hnegx : 0 ≤ -x := neg_nonneg.mpr hxneg.le
    have hrd0 : 0 ≤ roundDown delta (-x) := roundDown_nonneg hdelta.le
    simp only [signedRoundDown, if_neg hx, abs_neg, abs_of_nonneg hrd0,
      abs_of_neg hxneg]
    exact roundDown_le hdelta hnegx

theorem abs_sub_signedRoundDown_lt {delta x : ℝ} (hdelta : 0 < delta) :
    |x - signedRoundDown delta x| < delta := by
  by_cases hx : 0 ≤ x
  · have hle := roundDown_le hdelta hx
    have hrem := sub_roundDown_lt (delta := delta) (x := x) hdelta
    rw [signedRoundDown, if_pos hx, abs_of_nonneg (sub_nonneg.mpr hle)]
    exact hrem
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hnegx : 0 ≤ -x := neg_nonneg.mpr hxneg.le
    have hle := roundDown_le hdelta hnegx
    have hrem := sub_roundDown_lt (delta := delta) (x := -x) hdelta
    have hsum : x + roundDown delta (-x) ≤ 0 := by linarith
    rw [signedRoundDown, if_neg hx, sub_neg_eq_add, abs_of_nonpos hsum]
    nlinarith

/-- The point obtained by rounding horizontally towards zero and vertically down from `v0`. -/
def inwardRoundedEta (v0 delta : ℝ) (eta : ℂ) : ℂ :=
  Complex.mk (signedRoundDown delta eta.re)
    (v0 + roundDown delta (eta.im - v0))

/-- Rounding is inward: a point of the v3 domain is sent to another point of the same domain. -/
theorem inwardRoundedEta_mem
    {v0 delta : ℝ} (hv0 : 0 < v0) (hdelta : 0 < delta)
    {eta : ℂ} (heta : eta ∈ EtaDomainAtScale v0) :
    inwardRoundedEta v0 delta eta ∈ EtaDomainAtScale v0 := by
  rcases heta with ⟨hetaPos, hetaNorm, hetaIm⟩
  have himdiff : 0 ≤ eta.im - v0 := sub_nonneg.mpr hetaIm
  have himRound0 : 0 ≤ roundDown delta (eta.im - v0) :=
    roundDown_nonneg hdelta.le
  have himRoundLe : roundDown delta (eta.im - v0) ≤ eta.im - v0 :=
    roundDown_le hdelta himdiff
  have himCenterPos : 0 < v0 + roundDown delta (eta.im - v0) := by linarith
  have himCenterLe : v0 + roundDown delta (eta.im - v0) ≤ eta.im := by linarith
  have himEtaPos : 0 < eta.im := hetaPos
  have hreSq : (signedRoundDown delta eta.re) ^ 2 ≤ eta.re ^ 2 := by
    rw [sq_le_sq]
    exact abs_signedRoundDown_le_abs hdelta
  have himSq : (v0 + roundDown delta (eta.im - v0)) ^ 2 ≤ eta.im ^ 2 := by
    nlinarith
  have hnormSq : Complex.normSq (inwardRoundedEta v0 delta eta) ≤
      Complex.normSq eta := by
    simp only [inwardRoundedEta, Complex.normSq_apply]
    linarith
  have hnorm : ‖inwardRoundedEta v0 delta eta‖ ≤ ‖eta‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    exact Real.sqrt_le_sqrt hnormSq
  exact ⟨by simpa [InUpperHalfPlane, inwardRoundedEta] using himCenterPos,
    hnorm.trans hetaNorm,
    by simp [inwardRoundedEta, himRound0]⟩

/-- Each coordinate moves by less than `delta`, hence the complex distance is less than
`2 * delta`.  The deliberately coarse constant `2` avoids an irrelevant `sqrt 2`. -/
theorem dist_inwardRoundedEta_lt
    {v0 delta : ℝ} (hdelta : 0 < delta)
    {eta : ℂ} (hetaIm : v0 ≤ eta.im) :
    dist eta (inwardRoundedEta v0 delta eta) < 2 * delta := by
  have hre := abs_sub_signedRoundDown_lt (delta := delta) (x := eta.re) hdelta
  have himdiff : 0 ≤ eta.im - v0 := sub_nonneg.mpr hetaIm
  have himle := roundDown_le hdelta himdiff
  have himrem := sub_roundDown_lt (delta := delta) (x := eta.im - v0) hdelta
  have himabs :
      |eta.im - (v0 + roundDown delta (eta.im - v0))| < delta := by
    rw [abs_of_nonneg]
    · linarith
    · linarith
  calc
    dist eta (inwardRoundedEta v0 delta eta) =
        ‖eta - inwardRoundedEta v0 delta eta‖ := dist_eq_norm _ _
    _ ≤ |(eta - inwardRoundedEta v0 delta eta).re| +
          |(eta - inwardRoundedEta v0 delta eta).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ < delta + delta := by
      simp only [Complex.sub_re, Complex.sub_im, inwardRoundedEta]
      linarith
    _ = 2 * delta := by ring

/-- One more than the ceiling of `5 / delta`; both coordinates use this many indices. -/
def etaGridSteps (delta : ℝ) : ℕ := Nat.ceil (5 / delta) + 1

/-- The unfiltered rectangular index family.  The final net is its subtype whose centres lie in
the v3 domain. -/
abbrev EtaGridRawIndex (delta : ℝ) :=
  Bool × Fin (etaGridSteps delta) × Fin (etaGridSteps delta)

def etaGridRawCenter (v0 delta : ℝ) (i : EtaGridRawIndex delta) : ℂ :=
  Complex.mk
    (if i.1 then (i.2.1 : ℕ) * delta else -((i.2.1 : ℕ) * delta))
    (v0 + (i.2.2 : ℕ) * delta)

/-- The concrete finite index type: only the inward centres are retained. -/
abbrev EtaGridIndex (v0 delta : ℝ) :=
  {i : EtaGridRawIndex delta // etaGridRawCenter v0 delta i ∈ EtaDomainAtScale v0}

noncomputable instance etaGridIndexFintype (v0 delta : ℝ) :
    Fintype (EtaGridIndex v0 delta) := Fintype.ofFinite _

theorem floor_div_lt_etaGridSteps
    {delta x : ℝ} (hdelta : 0 < delta) (_hx0 : 0 ≤ x) (hx5 : x ≤ 5) :
    Nat.floor (x / delta) < etaGridSteps delta := by
  apply Nat.lt_succ_of_le
  apply Nat.floor_le_of_le
  exact (div_le_div_iff_of_pos_right hdelta).2 hx5 |>.trans (Nat.le_ceil _)

/-- The rounded point is represented by one of the explicit raw indices. -/
theorem exists_etaGridRawIndex_center_eq_inwardRounded
    {v0 delta : ℝ} (hv0 : 0 < v0) (hdelta : 0 < delta)
    {eta : ℂ} (heta : eta ∈ EtaDomainAtScale v0) :
    ∃ i : EtaGridRawIndex delta,
      etaGridRawCenter v0 delta i = inwardRoundedEta v0 delta eta := by
  rcases heta with ⟨hetaPos, hetaNorm, hetaIm⟩
  have hre5 : |eta.re| ≤ 5 := (Complex.abs_re_le_norm eta).trans hetaNorm
  have him5 : eta.im ≤ 5 := (Complex.im_le_norm eta).trans hetaNorm
  have himdiff0 : 0 ≤ eta.im - v0 := sub_nonneg.mpr hetaIm
  have himdiff5 : eta.im - v0 ≤ 5 := by linarith
  let kre : Fin (etaGridSteps delta) :=
    ⟨Nat.floor (|eta.re| / delta),
      floor_div_lt_etaGridSteps hdelta (abs_nonneg _) hre5⟩
  let kim : Fin (etaGridSteps delta) :=
    ⟨Nat.floor ((eta.im - v0) / delta),
      floor_div_lt_etaGridSteps hdelta himdiff0 himdiff5⟩
  by_cases hre : 0 ≤ eta.re
  · refine ⟨(true, kre, kim), ?_⟩
    apply Complex.ext
    · simp [etaGridRawCenter, inwardRoundedEta, signedRoundDown, roundDown, kre, kim,
        hre, abs_of_nonneg hre]
    · simp [etaGridRawCenter, inwardRoundedEta, signedRoundDown, roundDown, kre, kim,
        hre, abs_of_nonneg hre]
  · have hreNeg : eta.re < 0 := lt_of_not_ge hre
    refine ⟨(false, kre, kim), ?_⟩
    apply Complex.ext
    · simp [etaGridRawCenter, inwardRoundedEta, signedRoundDown, roundDown, kre, kim,
        hre, abs_of_neg hreNeg]
    · simp [etaGridRawCenter, inwardRoundedEta, signedRoundDown, roundDown, kre, kim,
        hre, abs_of_neg hreNeg]

/-- The explicit net for the exact v3 `eta` domain. -/
noncomputable def concreteEtaNet
    (v0 delta : ℝ) (hv0 : 0 < v0) (hdelta : 0 < delta) :
    FiniteEtaNet (EtaGridIndex v0 delta) (EtaDomainAtScale v0) where
  center i := etaGridRawCenter v0 delta i.1
  radius := 2 * delta
  radius_nonneg := by positivity
  center_mem i := i.2
  cover eta heta := by
    obtain ⟨i, hi⟩ :=
      exists_etaGridRawIndex_center_eq_inwardRounded hv0 hdelta heta
    have hiMem : etaGridRawCenter v0 delta i ∈ EtaDomainAtScale v0 := by
      rw [hi]
      exact inwardRoundedEta_mem hv0 hdelta heta
    refine ⟨⟨i, hiMem⟩, ?_⟩
    change dist eta (etaGridRawCenter v0 delta i) ≤ 2 * delta
    rw [hi]
    exact (dist_inwardRoundedEta_lt hdelta heta.2.2).le

/-- Explicit cardinality ledger for the concrete net. -/
theorem etaGridIndex_card_le (v0 delta : ℝ) :
    Fintype.card (EtaGridIndex v0 delta) ≤
      2 * etaGridSteps delta ^ 2 := by
  calc
    Fintype.card (EtaGridIndex v0 delta) ≤ Fintype.card (EtaGridRawIndex delta) :=
      Fintype.card_subtype_le _
    _ = 2 * etaGridSteps delta ^ 2 := by
      simp [EtaGridRawIndex, pow_two]

/-- The net is nonempty whenever `0 < v0 <= 5`: `I v0` is its bottom centre. -/
theorem etaGridIndex_nonempty
    {v0 delta : ℝ} (hv0 : 0 < v0) (hv05 : v0 ≤ 5) :
    Nonempty (EtaGridIndex v0 delta) := by
  have hsteps : 0 < etaGridSteps delta := by
    simp [etaGridSteps]
  let zeroIndex : Fin (etaGridSteps delta) := ⟨0, hsteps⟩
  let raw : EtaGridRawIndex delta := (true, zeroIndex, zeroIndex)
  have hmem : etaGridRawCenter v0 delta raw ∈ EtaDomainAtScale v0 := by
    simp only [etaGridRawCenter, raw, zeroIndex,
      if_true, Nat.cast_zero, zero_mul, neg_zero, add_zero]
    refine ⟨?_, ?_, le_rfl⟩
    · simpa [InUpperHalfPlane] using hv0
    · simpa [Complex.norm_def, Complex.normSq_apply, ← pow_two,
        Real.sqrt_sq_eq_abs, abs_of_pos hv0] using hv05
  exact ⟨⟨raw, hmem⟩⟩

/-- Cardinal division closes the complete finite-union budget internally.  In particular, no
separate `card * pointwiseFailure <= totalFailure` interface is needed. -/
theorem probabilityAtLeast_iInter_of_card_divided_failure
    {kappa Omega : Type*} [Fintype kappa] [Nonempty kappa]
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (good : kappa → Set Omega) (hmeas : ∀ i, MeasurableSet (good i))
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hpoint : ∀ i,
      mu (good i)ᶜ ≤ ENNReal.ofReal (epsilon / Fintype.card kappa)) :
    ProbabilityAtLeast mu (⋂ i, good i) (1 - epsilon) := by
  apply probabilityAtLeast_iInter_of_finite_failure_bounds mu good hmeas
    (ENNReal.ofReal (epsilon / Fintype.card kappa)) hepsilon hpoint
  rw [← ENNReal.ofReal_nsmul]
  have hcard : (Fintype.card kappa : ℝ) ≠ 0 := by positivity
  have heq : Fintype.card kappa •
      (epsilon / Fintype.card kappa) = epsilon := by
    simp only [nsmul_eq_mul]
    field_simp [hcard]
  rw [heq]

/-- Concentration-independent finite-net theorem.

The caller supplies only a measurable good event and an explicit failure estimate at every
listed centre.  The intersection probability, the finite union arithmetic, and the deterministic
continuity passage are all proved here.  In particular this theorem can be fed by either the
row-Doob compatibility route or the direct product McDiarmid route. -/
theorem probabilityAtLeast_uniformEtaGood_of_card_divided_center_failure
    {kappa Omega : Type*} [Fintype kappa] [Nonempty kappa]
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {domain : Set ℂ} (net : FiniteEtaNet kappa domain)
    (trace : Omega → ℂ → ℂ) (good : kappa → Set Omega)
    (hmeas : ∀ i, MeasurableSet (good i))
    {epsilon L margin C : ℝ} (hepsilon : 0 ≤ epsilon)
    (hpoint : ∀ i,
      mu (good i)ᶜ ≤ ENNReal.ofReal (epsilon / Fintype.card kappa))
    (hcenter : ∀ i omega, omega ∈ good i →
      ‖trace omega (net.center i)‖ ≤ C)
    (hL : 0 ≤ L)
    (hcontinuity : ∀ omega eta theta,
      eta ∈ domain → theta ∈ domain →
        ‖trace omega eta - trace omega theta‖ ≤ L * dist eta theta)
    (hmargin : L * net.radius ≤ margin) :
    ProbabilityAtLeast mu (UniformEtaGood domain trace (C + margin))
      (1 - epsilon) := by
  have hcommon := probabilityAtLeast_iInter_of_card_divided_failure
    mu good hmeas hepsilon hpoint
  have hinterGrid : (⋂ i, good i) ⊆ net.gridGood trace C := by
    intro omega homega i
    exact hcenter i omega (Set.mem_iInter.mp homega i)
  have hgridUniform : net.gridGood trace C ⊆
      UniformEtaGood domain trace (C + margin) :=
    finiteEtaNet_gridGood_subset_uniformEtaGood net trace hL hcontinuity hmargin
  exact hcommon.trans (measure_mono (hinterGrid.trans hgridUniform))

/-- The preceding concentration-independent theorem specialized to the explicit v3 net and
the normalized Hermitized resolvent trace.  No probability mechanism appears in the statement. -/
theorem probabilityAtLeast_stieltjesTrace_uniform_of_concrete_center_failure
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {n : ℕ} [NeZero n]
    (matrix : Omega → Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {v0 delta C epsilon : ℝ}
    (hv0 : 0 < v0) (hv05 : v0 ≤ 5) (hdelta : 0 < delta)
    (good : EtaGridIndex v0 delta → Set Omega)
    (hmeas : ∀ i, MeasurableSet (good i))
    (hepsilon : 0 ≤ epsilon)
    (hpoint : ∀ i,
      mu (good i)ᶜ ≤
        ENNReal.ofReal
          (epsilon / Fintype.card (EtaGridIndex v0 delta)))
    (hcenter : ∀ i omega, omega ∈ good i →
      ‖stieltjesTrace (matrix omega) z
        ((concreteEtaNet v0 delta hv0 hdelta).center i)‖ ≤ C) :
    ProbabilityAtLeast mu
      (UniformEtaGood (EtaDomainAtScale v0)
        (fun omega eta ↦ stieltjesTrace (matrix omega) z eta)
        (C + v0⁻¹ ^ 2 * (2 * delta)))
      (1 - epsilon) := by
  let _ : Nonempty (EtaGridIndex v0 delta) := etaGridIndex_nonempty hv0 hv05
  apply probabilityAtLeast_uniformEtaGood_of_card_divided_center_failure
    (epsilon := epsilon) (L := v0⁻¹ ^ 2)
    (margin := v0⁻¹ ^ 2 * (2 * delta)) (C := C)
    mu (concreteEtaNet v0 delta hv0 hdelta)
      (fun omega eta ↦ stieltjesTrace (matrix omega) z eta)
      good hmeas hepsilon hpoint hcenter (by positivity)
  · intro omega eta theta heta htheta
    exact norm_stieltjesTrace_sub_eta_le_of_im_ge
      (matrix omega) z hv0 heta.2.2 htheta.2.2
  · change v0⁻¹ ^ 2 * (2 * delta) ≤ v0⁻¹ ^ 2 * (2 * delta)
    exact le_rfl

end

end Arxiv2410V3

