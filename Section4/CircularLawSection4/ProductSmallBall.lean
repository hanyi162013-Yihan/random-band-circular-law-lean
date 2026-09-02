import CircularLawSection4.Multiaffine
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Product-law instances for the Section 4 multiaffine induction

This module constructs an honest recursive IID product law on `Fin n → ℝ`.
It proves the prefix marginal identity and lifts a one-dimensional interval
measure bound through product measure/Fubini to the integrated
`OneCoordinateSmallBall` interface.
-/

open scoped ENNReal
open MeasureTheory Set

namespace CircularLawSection4

universe u

section RecursiveProduct

variable {K : Type u} [MeasurableSpace K]

/-- Append a fresh last coordinate to a finite vector. -/
def joinLast {n : ℕ} (y : (Fin n → K) × K) : Fin (n + 1) → K :=
  Fin.lastCases y.2 y.1

omit [MeasurableSpace K] in
@[simp] theorem joinLast_castSucc {n : ℕ} (y : (Fin n → K) × K) (i : Fin n) :
    joinLast y i.castSucc = y.1 i := by
  simp [joinLast]

omit [MeasurableSpace K] in
@[simp] theorem joinLast_last {n : ℕ} (y : (Fin n → K) × K) :
    joinLast y (Fin.last n) = y.2 := by
  simp [joinLast]

omit [MeasurableSpace K] in
@[simp] theorem dropLast_joinLast {n : ℕ} (y : (Fin n → K) × K) :
    MultiAffine.dropLast (joinLast y) = y.1 := by
  funext i
  simp [MultiAffine.dropLast]

theorem measurable_dropLast {n : ℕ} :
    Measurable (MultiAffine.dropLast : (Fin (n + 1) → K) → (Fin n → K)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply i.castSucc

theorem measurable_joinLast {n : ℕ} :
    Measurable (joinLast : ((Fin n → K) × K) → (Fin (n + 1) → K)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [joinLast_last] using
      (measurable_snd : Measurable (fun y : (Fin n → K) × K => y.2))
  · simp only [joinLast_castSucc]
    exact (measurable_pi_apply j).comp measurable_fst

/-- Recursive IID law: start from the unique empty vector and repeatedly append
one independent coordinate with law `ν`. -/
noncomputable def iidMeasure (ν : Measure K) [SFinite ν] :
    (n : ℕ) → Measure (Fin n → K)
  | 0 => Measure.dirac fun i => Fin.elim0 i
  | n + 1 => Measure.map joinLast ((iidMeasure ν n).prod ν)

theorem iidMeasure_isProbability (ν : Measure K) [SFinite ν]
    [IsProbabilityMeasure ν] : ∀ n, IsProbabilityMeasure (iidMeasure ν n)
  | 0 => by
      simp only [iidMeasure]
      infer_instance
  | n + 1 => by
      let _ := iidMeasure_isProbability ν n
      simp only [iidMeasure]
      exact Measure.isProbabilityMeasure_map measurable_joinLast.aemeasurable

end RecursiveProduct

section RealMeasurability

theorem continuous_dropLast_real {n : ℕ} :
    Continuous
      (MultiAffine.dropLast : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) := by
  apply continuous_pi
  intro i
  exact continuous_apply i.castSucc

theorem MultiAffine.continuous_eval_real :
    ∀ {n : ℕ} (p : MultiAffine ℝ n), Continuous p.eval := by
  intro n p
  induction p with
  | const c =>
      change Continuous (fun _ : Fin 0 → ℝ => c)
      exact continuous_const
  | @affine n p₀ p₁ ih₀ ih₁ =>
      change Continuous (fun x : Fin (n + 1) → ℝ =>
        p₀.eval (MultiAffine.dropLast x) +
          x (Fin.last n) * p₁.eval (MultiAffine.dropLast x))
      exact (ih₀.comp continuous_dropLast_real).add
        ((continuous_apply (Fin.last n)).mul
          (ih₁.comp continuous_dropLast_real))

theorem measurableSet_openSmallBall_real {n : ℕ} (p : MultiAffine ℝ n) (r : ℝ) :
    MeasurableSet (openSmallBall p r) := by
  change MeasurableSet ((fun x => ‖p.eval x‖) ⁻¹' Iio r)
  exact isOpen_Iio.preimage p.continuous_eval_real.norm |>.measurableSet

theorem measurableSet_closedSmallBall_real {n : ℕ} (p : MultiAffine ℝ n) (r : ℝ) :
    MeasurableSet (closedSmallBall p r) := by
  change MeasurableSet ((fun x => ‖p.eval x‖) ⁻¹' Iic r)
  exact isClosed_Iic.preimage p.continuous_eval_real.norm |>.measurableSet

theorem measurableSet_oneCoordinateEvent_real {n : ℕ}
    (p₀ p₁ : MultiAffine ℝ n) (ε ρ : ℝ) :
    MeasurableSet
      {x | ‖(MultiAffine.affine p₀ p₁).eval x‖ ≤ ε * ρ ∧
        ε ≤ ‖p₁.eval (MultiAffine.dropLast x)‖} := by
  apply MeasurableSet.inter
  · exact measurableSet_closedSmallBall_real _ _
  · exact isClosed_Ici.preimage
      (p₁.continuous_eval_real.norm.comp continuous_dropLast_real) |>.measurableSet

end RealMeasurability

section ComplexMeasurability

theorem continuous_dropLast_complex {n : ℕ} :
    Continuous
      (MultiAffine.dropLast : (Fin (n + 1) → ℂ) → (Fin n → ℂ)) := by
  apply continuous_pi
  intro i
  exact continuous_apply i.castSucc

theorem MultiAffine.continuous_eval_complex :
    ∀ {n : ℕ} (p : MultiAffine ℂ n), Continuous p.eval := by
  intro n p
  induction p with
  | const c =>
      change Continuous (fun _ : Fin 0 → ℂ => c)
      exact continuous_const
  | @affine n p₀ p₁ ih₀ ih₁ =>
      change Continuous (fun x : Fin (n + 1) → ℂ =>
        p₀.eval (MultiAffine.dropLast x) +
          x (Fin.last n) * p₁.eval (MultiAffine.dropLast x))
      exact (ih₀.comp continuous_dropLast_complex).add
        ((continuous_apply (Fin.last n)).mul
          (ih₁.comp continuous_dropLast_complex))

theorem measurableSet_openSmallBall_complex {n : ℕ} (p : MultiAffine ℂ n) (r : ℝ) :
    MeasurableSet (openSmallBall p r) := by
  change MeasurableSet ((fun x => ‖p.eval x‖) ⁻¹' Iio r)
  exact isOpen_Iio.preimage p.continuous_eval_complex.norm |>.measurableSet

theorem measurableSet_oneCoordinateEvent_complex {n : ℕ}
    (p₀ p₁ : MultiAffine ℂ n) (ε ρ : ℝ) :
    MeasurableSet
      {x | ‖(MultiAffine.affine p₀ p₁).eval x‖ ≤ ε * ρ ∧
        ε ≤ ‖p₁.eval (MultiAffine.dropLast x)‖} := by
  apply MeasurableSet.inter
  · change MeasurableSet
      ((fun x => ‖(MultiAffine.affine p₀ p₁).eval x‖) ⁻¹' Iic (ε * ρ))
    exact isClosed_Iic.preimage
      (MultiAffine.continuous_eval_complex _).norm |>.measurableSet
  · exact isClosed_Ici.preimage
      (p₁.continuous_eval_complex.norm.comp continuous_dropLast_complex) |>.measurableSet

end ComplexMeasurability

section RealProduct

/-- A density-free formulation of the only one-dimensional analytic fact
needed below: every interval has mass at most `L` times its length. -/
def RealIntervalBound (ν : Measure ℝ) (L : ℝ≥0∞) : Prop :=
  ∀ a b : ℝ, a ≤ b → ν (Icc a b) ≤ L * ENNReal.ofReal (b - a)

/-- Domination by `L` times Lebesgue measure implies the interval bound. -/
theorem realIntervalBound_of_le_smul_volume
    {ν : Measure ℝ} {L : ℝ≥0∞} (hν : ν ≤ L • volume) :
    RealIntervalBound ν L := by
  intro a b hab
  calc
    ν (Icc a b) ≤ (L • volume) (Icc a b) := hν _
    _ = L * ENNReal.ofReal (b - a) := by
      rw [Measure.smul_apply, smul_eq_mul, Real.volume_Icc]

/-- A Lebesgue density bounded by `L` almost everywhere gives the interval
bound used by the product/Fubini argument. -/
theorem realIntervalBound_withDensity
    {f : ℝ → ℝ≥0∞} {L : ℝ≥0∞}
    (hf : ∀ᵐ x ∂(volume : Measure ℝ), f x ≤ L) :
    RealIntervalBound (volume.withDensity f) L := by
  apply realIntervalBound_of_le_smul_volume
  calc
    volume.withDensity f ≤ volume.withDensity (fun _ : ℝ => L) :=
      withDensity_mono hf
    _ = L • volume := withDensity_const _

theorem iidMeasure_prefixSmallBallConsistent (ν : Measure ℝ) [SFinite ν]
    [IsProbabilityMeasure ν] :
    PrefixSmallBallConsistent (iidMeasure ν) := by
  intro n p r
  let _ := iidMeasure_isProbability ν n
  have hs : MeasurableSet (openSmallBall p r) :=
    measurableSet_openSmallBall_real p r
  rw [iidMeasure, Measure.map_apply measurable_joinLast (hs.preimage measurable_dropLast)]
  have hpre :
      joinLast ⁻¹' (MultiAffine.dropLast ⁻¹' openSmallBall p r) =
        Prod.fst ⁻¹' openSmallBall p r := by
    ext y
    simp only [mem_preimage, dropLast_joinLast]
  rw [hpre, ← Measure.map_apply measurable_fst hs, Measure.map_fst_prod]
  simp

theorem real_affine_smallBall_of_intervalBound
    {ν : Measure ℝ} {L : ℝ≥0∞} (hν : RealIntervalBound ν L)
    {a b ε ρ : ℝ} (hρ : 0 ≤ ρ) (hε : 0 < ε) (hslope : ε ≤ |a|) :
    ν {x | |b + x * a| ≤ ε * ρ} ≤
      (2 : ℝ≥0∞) * L * ENNReal.ofReal ρ := by
  have ha : a ≠ 0 := by
    intro ha
    subst a
    simp only [abs_zero] at hslope
    linarith
  have habs : 0 < |a| := abs_pos.mpr ha
  let c : ℝ := -(b / a)
  have hsub : {x | |b + x * a| ≤ ε * ρ} ⊆ Icc (c - ρ) (c + ρ) := by
    intro x hx
    have hfactor : b + x * a = a * (x + b / a) := by
      field_simp [ha]
      ring
    have hdist : |x + b / a| ≤ ρ := by
      apply le_of_mul_le_mul_left _ habs
      calc
        |a| * |x + b / a| = |a * (x + b / a)| := (abs_mul _ _).symm
        _ = |b + x * a| := congrArg abs hfactor.symm
        _ ≤ ε * ρ := hx
        _ ≤ |a| * ρ := mul_le_mul_of_nonneg_right hslope hρ
    have hb := abs_le.mp hdist
    change c - ρ ≤ x ∧ x ≤ c + ρ
    dsimp only [c]
    constructor <;> linarith
  calc
    ν {x | |b + x * a| ≤ ε * ρ} ≤ ν (Icc (c - ρ) (c + ρ)) :=
      measure_mono hsub
    _ ≤ L * ENNReal.ofReal ((c + ρ) - (c - ρ)) := hν _ _ (by linarith)
    _ = (2 : ℝ≥0∞) * L * ENNReal.ofReal ρ := by
      rw [show (c + ρ) - (c - ρ) = (2 : ℝ) * ρ by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
      ac_rfl

/-- Product measure plus the one-dimensional interval bound gives exactly the
integrated real one-coordinate cost used by the multiaffine induction. -/
theorem iidMeasure_oneCoordinateSmallBall_real
    (ν : Measure ℝ) [SFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ≥0∞} (hν : RealIntervalBound ν L) {ρ : ℝ} (hρ : 0 < ρ) :
    OneCoordinateSmallBall (iidMeasure ν) ρ
      ((2 : ℝ≥0∞) * L * ENNReal.ofReal ρ) := by
  intro n p₀ p₁ ε hε
  let _ := iidMeasure_isProbability ν n
  let good : Set (Fin (n + 1) → ℝ) :=
    {x | ‖(MultiAffine.affine p₀ p₁).eval x‖ ≤ ε * ρ ∧
      ε ≤ ‖p₁.eval (MultiAffine.dropLast x)‖}
  have hgood : MeasurableSet good := by
    simpa only [good] using measurableSet_oneCoordinateEvent_real p₀ p₁ ε ρ
  change iidMeasure ν (n + 1) good ≤
    (2 : ℝ≥0∞) * L * ENNReal.ofReal ρ
  rw [iidMeasure, Measure.map_apply measurable_joinLast hgood,
    Measure.prod_apply (hgood.preimage measurable_joinLast)]
  calc
    (∫⁻ y, ν (Prod.mk y ⁻¹' (joinLast ⁻¹' good)) ∂iidMeasure ν n) ≤
        ∫⁻ _y : Fin n → ℝ,
          (2 : ℝ≥0∞) * L * ENNReal.ofReal ρ ∂iidMeasure ν n := by
      apply lintegral_mono
      intro y
      by_cases hslope : ε ≤ |p₁.eval y|
      · simpa [good, MultiAffine.eval_affine, Real.norm_eq_abs, hslope] using
          real_affine_smallBall_of_intervalBound hν hρ.le hε hslope
      · simp [good, MultiAffine.eval_affine, Real.norm_eq_abs, hslope]
    _ = (2 : ℝ≥0∞) * L * ENNReal.ofReal ρ := by simp

/-- Fully instantiated real multiaffine estimate for recursive IID product
laws satisfying the interval density bound. -/
theorem iid_real_multiaffine_bound
    (ν : Measure ℝ) [SFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ≥0∞} (hν : RealIntervalBound ν L)
    {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ} (p : MultiAffine ℝ (n + 1))
    (htop : 0 < ‖p.topCoeff‖) :
    iidMeasure ν (n + 1)
        (closedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) * L) * ENNReal.ofReal ρ := by
  exact closedSmallBall_topCoeff_le_mul_rho_of_oneCoordinate hρ
    (iidMeasure_prefixSmallBallConsistent ν)
    (iidMeasure_oneCoordinateSmallBall_real ν hν hρ) p htop

/-- End-to-end density formulation: an IID real coordinate with probability
density `f ≤ L` yields the manuscript's `2 L k ρ` bound. -/
theorem iid_real_multiaffine_bound_withDensity
    (f : ℝ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ≥0∞} (hf : ∀ᵐ x ∂(volume : Measure ℝ), f x ≤ L)
    {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ} (p : MultiAffine ℝ (n + 1))
    (htop : 0 < ‖p.topCoeff‖) :
    iidMeasure (volume.withDensity f) (n + 1)
        (closedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) * L) * ENNReal.ofReal ρ := by
  exact iid_real_multiaffine_bound (volume.withDensity f)
    (realIntervalBound_withDensity hf) hρ p htop

end RealProduct

section ComplexProduct

/-- Planar one-coordinate input stated geometrically: a closed disk of radius
`r` has mass at most `π L r²`. -/
def ComplexBallBound (ν : Measure ℂ) (L : ℝ≥0∞) : Prop :=
  ∀ c : ℂ, ∀ r : ℝ, 0 ≤ r →
    ν (Metric.closedBall c r) ≤
      ENNReal.ofReal Real.pi * L * ENNReal.ofReal r ^ 2

theorem complex_volume_closedBall (c : ℂ) (r : ℝ) :
    volume (Metric.closedBall c r) =
      ENNReal.ofReal Real.pi * ENNReal.ofReal r ^ 2 := by
  rw [InnerProductSpace.volume_closedBall_of_dim_even (E := ℂ) (k := 1)
    (by norm_num [Complex.finrank_real_complex])]
  simp only [Complex.finrank_real_complex, Nat.factorial_one, Nat.cast_one,
    pow_one, div_one]
  ac_rfl

/-- Domination by `L` times planar Lebesgue measure gives the disk bound. -/
theorem complexBallBound_of_le_smul_volume
    {ν : Measure ℂ} {L : ℝ≥0∞} (hν : ν ≤ L • volume) :
    ComplexBallBound ν L := by
  intro c r hr
  calc
    ν (Metric.closedBall c r) ≤ (L • volume) (Metric.closedBall c r) := hν _
    _ = L * volume (Metric.closedBall c r) := by
      rw [Measure.smul_apply, smul_eq_mul]
    _ = ENNReal.ofReal Real.pi * L * ENNReal.ofReal r ^ 2 := by
      rw [complex_volume_closedBall]
      ac_rfl

/-- A planar Lebesgue density bounded by `L` almost everywhere gives the disk
bound with the sharp area constant `π`. -/
theorem complexBallBound_withDensity
    {f : ℂ → ℝ≥0∞} {L : ℝ≥0∞}
    (hf : ∀ᵐ z ∂(volume : Measure ℂ), f z ≤ L) :
    ComplexBallBound (volume.withDensity f) L := by
  apply complexBallBound_of_le_smul_volume
  calc
    volume.withDensity f ≤ volume.withDensity (fun _ : ℂ => L) :=
      withDensity_mono hf
    _ = L • volume := withDensity_const _

theorem iidMeasure_prefixSmallBallConsistent_complex (ν : Measure ℂ) [SFinite ν]
    [IsProbabilityMeasure ν] :
    PrefixSmallBallConsistent (iidMeasure ν) := by
  intro n p r
  let _ := iidMeasure_isProbability ν n
  have hs : MeasurableSet (openSmallBall p r) :=
    measurableSet_openSmallBall_complex p r
  rw [iidMeasure, Measure.map_apply measurable_joinLast (hs.preimage measurable_dropLast)]
  have hpre :
      joinLast ⁻¹' (MultiAffine.dropLast ⁻¹' openSmallBall p r) =
        Prod.fst ⁻¹' openSmallBall p r := by
    ext y
    simp only [mem_preimage, dropLast_joinLast]
  rw [hpre, ← Measure.map_apply measurable_fst hs, Measure.map_fst_prod]
  simp

theorem complex_affine_smallBall_of_ballBound
    {ν : Measure ℂ} {L : ℝ≥0∞} (hν : ComplexBallBound ν L)
    {a b : ℂ} {ε ρ : ℝ} (hρ : 0 ≤ ρ) (hε : 0 < ε)
    (hslope : ε ≤ ‖a‖) :
    ν {x | ‖b + x * a‖ ≤ ε * ρ} ≤
      ENNReal.ofReal Real.pi * L * ENNReal.ofReal ρ ^ 2 := by
  have ha : a ≠ 0 := by
    intro ha
    subst a
    simp only [norm_zero] at hslope
    linarith
  have habs : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let c : ℂ := -(b / a)
  have hsub : {x | ‖b + x * a‖ ≤ ε * ρ} ⊆ Metric.closedBall c ρ := by
    intro x hx
    have hfactor : b + x * a = a * (x + b / a) := by
      field_simp [ha]
      ring
    have hdist : ‖x + b / a‖ ≤ ρ := by
      apply le_of_mul_le_mul_left _ habs
      calc
        ‖a‖ * ‖x + b / a‖ = ‖a * (x + b / a)‖ := (norm_mul _ _).symm
        _ = ‖b + x * a‖ := congrArg norm hfactor.symm
        _ ≤ ε * ρ := hx
        _ ≤ ‖a‖ * ρ := mul_le_mul_of_nonneg_right hslope hρ
    change dist x c ≤ ρ
    simpa only [c, dist_eq_norm, sub_neg_eq_add] using hdist
  exact (measure_mono hsub).trans (hν c ρ hρ)

theorem iidMeasure_oneCoordinateSmallBall_complex
    (ν : Measure ℂ) [SFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ≥0∞} (hν : ComplexBallBound ν L) {ρ : ℝ} (hρ : 0 < ρ) :
    OneCoordinateSmallBall (iidMeasure ν) ρ
      (ENNReal.ofReal Real.pi * L * ENNReal.ofReal ρ ^ 2) := by
  intro n p₀ p₁ ε hε
  let _ := iidMeasure_isProbability ν n
  let good : Set (Fin (n + 1) → ℂ) :=
    {x | ‖(MultiAffine.affine p₀ p₁).eval x‖ ≤ ε * ρ ∧
      ε ≤ ‖p₁.eval (MultiAffine.dropLast x)‖}
  have hgood : MeasurableSet good := by
    simpa only [good] using measurableSet_oneCoordinateEvent_complex p₀ p₁ ε ρ
  change iidMeasure ν (n + 1) good ≤
    ENNReal.ofReal Real.pi * L * ENNReal.ofReal ρ ^ 2
  rw [iidMeasure, Measure.map_apply measurable_joinLast hgood,
    Measure.prod_apply (hgood.preimage measurable_joinLast)]
  calc
    (∫⁻ y, ν (Prod.mk y ⁻¹' (joinLast ⁻¹' good)) ∂iidMeasure ν n) ≤
        ∫⁻ _y : Fin n → ℂ,
          ENNReal.ofReal Real.pi * L * ENNReal.ofReal ρ ^ 2 ∂iidMeasure ν n := by
      apply lintegral_mono
      intro y
      by_cases hslope : ε ≤ ‖p₁.eval y‖
      · simpa [good, MultiAffine.eval_affine, hslope] using
          complex_affine_smallBall_of_ballBound hν hρ.le hε hslope
      · simp [good, MultiAffine.eval_affine, hslope]
    _ = ENNReal.ofReal Real.pi * L * ENNReal.ofReal ρ ^ 2 := by simp

/-- Fully instantiated complex multiaffine estimate from the planar disk
bound. -/
theorem iid_complex_multiaffine_bound
    (ν : Measure ℂ) [SFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ≥0∞} (hν : ComplexBallBound ν L)
    {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ} (p : MultiAffine ℂ (n + 1))
    (htop : 0 < ‖p.topCoeff‖) :
    iidMeasure ν (n + 1)
        (closedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal Real.pi * L) *
        ENNReal.ofReal ρ ^ 2 := by
  exact closedSmallBall_topCoeff_le_mul_rho_sq_of_oneCoordinate hρ
    (iidMeasure_prefixSmallBallConsistent_complex ν)
    (iidMeasure_oneCoordinateSmallBall_complex ν hν hρ) p htop

/-- End-to-end planar-density formulation: an IID complex coordinate with
probability density `f ≤ L` yields the manuscript's `π L k ρ²` bound. -/
theorem iid_complex_multiaffine_bound_withDensity
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ≥0∞} (hf : ∀ᵐ z ∂(volume : Measure ℂ), f z ≤ L)
    {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ} (p : MultiAffine ℂ (n + 1))
    (htop : 0 < ‖p.topCoeff‖) :
    iidMeasure (volume.withDensity f) (n + 1)
        (closedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal Real.pi * L) *
        ENNReal.ofReal ρ ^ 2 := by
  exact iid_complex_multiaffine_bound (volume.withDensity f)
    (complexBallBound_withDensity hf) hρ p htop

end ComplexProduct

end CircularLawSection4
