import Vendor.GinibreLSV.GinibreSmoothed
import ShortRingAnchor.HighBandLSVBridge

/-!
# A proved polynomial lower edge for normalized circular Ginibre

BC12 (4.9), short route: the previously checked distance-to-span argument
already works after **every deterministic shift**. This file supplies the
dimension normalization, Borel-law transport, and vanishing exceptional
probability needed by the negative-moment argument. No BC12 or other
random-matrix estimate is assumed here.

`normalizedGinibreLaw` is a definition of an actual Gaussian matrix law,
not an interface asserting a tail estimate. The deliberately nonoptimal
bound `4 N^3 epsilon` suffices: at `epsilon = N^(-4)` it is `4/N`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace ShortRingAnchor.BC12

local instance (N : ℕ) : MeasurableSpace (Matrix (Fin N) (Fin N) ℂ) := borel _
local instance (N : ℕ) : BorelSpace (Matrix (Fin N) (Fin N) ℂ) := ⟨rfl⟩

/-- BC12's dense normalization: independent standard complex Gaussian
entries divided by `sqrt N`. Each raw real Gaussian coordinate has variance
one, so the additional `sqrt 2` is contained in `normalizedComplexGinibreMatrix`. -/
def normalizedGinibreMatrix (N : ℕ) (C : Fin N → GinibreLSV.ComplexColumn N) :
    Matrix (Fin N) (Fin N) ℂ :=
  ((Real.sqrt (N : ℝ))⁻¹ : ℂ) • GinibreLSV.normalizedComplexGinibreMatrix C

/-- Law transport for the BC12 shortcut: the canonical Gaussian matrix map is continuous. -/
theorem continuous_normalizedGinibreMatrix (N : ℕ) :
    Continuous (normalizedGinibreMatrix N) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun C : Fin N → GinibreLSV.ComplexColumn N =>
    ((Real.sqrt (N : ℝ))⁻¹ : ℂ) * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * C j i))
  exact continuous_const.mul (continuous_const.mul
    ((PiLp.continuous_apply 2 (fun _ : Fin N => ℂ) i).comp (continuous_apply j)))

/-- The concrete normalized circular Ginibre matrix distribution. -/
def normalizedGinibreLaw (N : ℕ) : Measure (Matrix (Fin N) (Fin N) ℂ) :=
  (GinibreLSV.complexGinibreColumns N).map (normalizedGinibreMatrix N)

/-- The Gaussian normalization defines a probability measure, including dimension zero. -/
instance normalizedGinibreLaw_isProbabilityMeasure (N : ℕ) :
    IsProbabilityMeasure (normalizedGinibreLaw N) := by
  letI : IsProbabilityMeasure (GinibreLSV.complexGinibreColumns N) := by
    unfold GinibreLSV.complexGinibreColumns
    infer_instance
  unfold normalizedGinibreLaw
  exact Measure.isProbabilityMeasure_map (continuous_normalizedGinibreMatrix N).measurable.aemeasurable

/-- Exact realization of the Gaussian matrix law; no probabilistic conclusion is postulated. -/
theorem normalizedGinibreMatrix_hasLaw (N : ℕ) :
    HasLaw (normalizedGinibreMatrix N) (normalizedGinibreLaw N)
      (GinibreLSV.complexGinibreColumns N) :=
  ⟨(continuous_normalizedGinibreMatrix N).measurable.aemeasurable, rfl⟩

/-- The shift used in BC12 equals the arbitrary deterministic perturbation
already covered by the elementary Gaussian small-ball theorem. -/
theorem normalizedGinibreMatrix_sub_shift (N : ℕ)
    (C : Fin N → GinibreLSV.ComplexColumn N) (z : ℂ) :
    normalizedGinibreMatrix N C - z • 1 =
      GinibreLSV.normalizedShiftedGinibreMatrix (-z • 1) (Real.sqrt (N : ℝ))⁻¹ C := by
  rw [GinibreLSV.normalizedShiftedGinibreMatrix_eq_add]
  simp only [normalizedGinibreMatrix, Complex.ofReal_inv, neg_smul]
  abel

/-- Elementary Gaussian-density constant used by the BC12 shortcut. -/
theorem gaussianPeak_one_le_one : GinibreLSV.gaussianPeak 1 ≤ 1 := by
  unfold GinibreLSV.gaussianPeak
  apply (ENNReal.ofReal_le_one).2
  have hp : 1 ≤ Real.sqrt (2 * Real.pi * (1 : NNReal)) := by
    norm_num only [NNReal.coe_one, mul_one]
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    nlinarith [Real.one_le_pi_div_two]
  exact inv_le_one_of_one_le₀ hp

/-- BC12 lower-edge arithmetic. We use `sqrt N ≤ N`, deliberately losing
a half power; the resulting polynomial lower edge is still sufficient. -/
theorem gaussian_smallBall_normalization_le {x e : ℝ} (hx : 1 ≤ x) (he : 0 ≤ e) :
    x * (2 * (x * e / (x.sqrt⁻¹ / Real.sqrt 2))) ≤ 4 * x ^ 3 * e := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have ht : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hsle : Real.sqrt x ≤ x := (Real.sqrt_le_iff).2 ⟨hx0.le, by nlinarith⟩
  have htle : Real.sqrt (2 : ℝ) ≤ 2 := by
    apply (Real.sqrt_le_iff).2
    norm_num
  have heq : x * (2 * (x * e / (x.sqrt⁻¹ / Real.sqrt 2))) =
      (2 * x ^ 2 * e) * (Real.sqrt x * Real.sqrt 2) := by
    field_simp
    <;> ring
  rw [heq]
  calc
    _ ≤ (2 * x ^ 2 * e) * (x * 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hsle htle ht.le hx0.le) (by positivity)
    _ = _ := by ring

/-- BC12 (4.9), proved nonoptimal shifted Ginibre lower tail. The constant
is universal and the shift `z` is unrestricted. -/
theorem normalizedGinibre_smallBall {N : ℕ} (hN : 0 < N) (z : ℂ)
    {e : ℝ} (he : 0 ≤ e) :
    GinibreLSV.complexGinibreColumns N
      {C | GinibreLSV.leastSingularValue (normalizedGinibreMatrix N C - z • 1) < e} ≤
      ENNReal.ofReal (4 * (N : ℝ) ^ 3 * e) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hraw := GinibreLSV.normalizedShiftedGinibre_leastSingularValue_lt_le
    (-z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
    (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ e (by positivity) he
  simp_rw [← normalizedGinibreMatrix_sub_shift] at hraw
  refine hraw.trans ?_
  calc
    _ ≤ (n + 1 : ENNReal) * (1 * ENNReal.ofReal
        (2 * (((n + 1 : ℕ) : ℝ) * e / ((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ / Real.sqrt 2)))) :=
      by gcongr; exact gaussianPeak_one_le_one
    _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) *
        (2 * (((n + 1 : ℕ) : ℝ) * e / ((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ / Real.sqrt 2)))) := by
      rw [one_mul, ENNReal.ofReal_mul (Nat.cast_nonneg (n + 1)), ENNReal.ofReal_natCast]
      simp only [Nat.cast_add, Nat.cast_one]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (gaussian_smallBall_normalization_le hn he)

/-- The lower-tail event is Borel. This discharges the measurability needed
to transfer Gaussian estimates to the actual matrix array in later chapters. -/
theorem measurableSet_shifted_leastSingularValue_lt {N : ℕ} (hN : 0 < N) (z : ℂ) (e : ℝ) :
    MeasurableSet {A : Matrix (Fin N) (Fin N) ℂ |
      GinibreLSV.leastSingularValue (A - z • 1) < e} :=
  ((isOpen_leastSingularValue_lt hN e).preimage (continuous_id.sub continuous_const)).measurableSet

/-- BC12 lower tail on any realization with the actual Ginibre law.
`hG` is an ensemble definition (equality of distributions), not a small-ball hypothesis. -/
theorem normalizedGinibre_smallBall_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {N : ℕ} (hN : 0 < N)
    {G : Ω → Matrix (Fin N) (Fin N) ℂ}
    (hG : HasLaw G (normalizedGinibreLaw N) μ) (z : ℂ) {e : ℝ} (he : 0 ≤ e) :
    μ {sample | GinibreLSV.leastSingularValue (G sample - z • 1) < e} ≤
      ENNReal.ofReal (4 * (N : ℝ) ^ 3 * e) := by
  rw [hG.measure_eq (measurableSet_shifted_leastSingularValue_lt hN z e),
    ← (normalizedGinibreMatrix_hasLaw N).measure_eq
      (measurableSet_shifted_leastSingularValue_lt hN z e)]
  exact normalizedGinibre_smallBall hN z he

/-- BC12 shortcut at the explicit polynomial floor `N^(-4)`: failure is at most `4/N`. -/
theorem normalizedGinibre_polynomial_lower_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {N : ℕ} (hN : 0 < N)
    {G : Ω → Matrix (Fin N) (Fin N) ℂ}
    (hG : HasLaw G (normalizedGinibreLaw N) μ) (z : ℂ) :
    μ {sample | GinibreLSV.leastSingularValue (G sample - z • 1) < (N : ℝ) ^ (-(4 : ℝ))} ≤
      ENNReal.ofReal (4 / (N : ℝ)) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h := normalizedGinibre_smallBall_of_hasLaw hN hG z
    (Real.rpow_nonneg (Nat.cast_nonneg N) (-(4 : ℝ)))
  have heq : 4 * (N : ℝ) ^ 3 * (N : ℝ) ^ (-(4 : ℝ)) = 4 / (N : ℝ) := by
    rw [Real.rpow_neg (Nat.cast_nonneg N)]
    norm_num only [Real.rpow_ofNat]
    field_simp
    <;> ring
  rwa [heq] at h

/-- BC12 (4.9), lower-edge good events along arbitrary diverging dimensions.
No independence across matrix sizes is needed. -/
theorem normalizedGinibre_lower_bad_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {N : ℕ → ℕ}
    (hNpos : ∀ k, 0 < N k) (hN : Tendsto N atTop atTop)
    (G : ∀ k, Ω → Matrix (Fin (N k)) (Fin (N k)) ℂ)
    (hG : ∀ k, HasLaw (G k) (normalizedGinibreLaw (N k)) μ) (z : ℂ) :
    Tendsto (fun k => μ {sample |
      GinibreLSV.leastSingularValue (G k sample - z • 1) < (N k : ℝ) ^ (-(4 : ℝ))})
      atTop (nhds 0) := by
  have hlim : Tendsto (fun k => ENNReal.ofReal (4 / (N k : ℝ))) atTop (nhds 0) := by
    have hi : Tendsto (fun k => (N k : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)
    simpa only [div_eq_mul_inv, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (hi.const_mul (4 : ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) (fun k => normalizedGinibre_polynomial_lower_tail (hNpos k) (hG k) z)

end ShortRingAnchor.BC12
