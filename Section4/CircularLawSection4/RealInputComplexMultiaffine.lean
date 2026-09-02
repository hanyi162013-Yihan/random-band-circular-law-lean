import CircularLawSection4.MultiaffineUntruncated

/-!
# Complex multiaffine polynomials with real random inputs

The real-atom branch of the manuscript still has complex coefficients because
the spectral parameter is complex.  This module evaluates `MultiAffine ℂ n`
on real vectors via `Complex.ofReal`, proves a real-product small-ball bound,
and derives the corresponding untruncated negative logarithmic moment.

For one affine coordinate we project to either the real or imaginary part of
the complex slope.  One of those parts has size at least half the complex
norm, giving the convenient constant `4 L` in place of the scalar-real
constant `2 L`.
-/

open scoped ENNReal MeasureTheory Topology
open Set MeasureTheory Filter Measure

namespace CircularLawSection4

/-- Evaluate a complex multiaffine polynomial on real inputs. -/
def realInputEval {n : ℕ} (p : MultiAffine ℂ n) (x : Fin n → ℝ) : ℂ :=
  p.eval fun i => (x i : ℂ)

@[simp] theorem realInputEval_const (c : ℂ) (x : Fin 0 → ℝ) :
    realInputEval (.const c) x = c := rfl

@[simp] theorem realInputEval_affine {n : ℕ}
    (p₀ p₁ : MultiAffine ℂ n) (x : Fin (n + 1) → ℝ) :
    realInputEval (.affine p₀ p₁) x =
      realInputEval p₀ (MultiAffine.dropLast x) +
        (x (Fin.last n) : ℂ) *
          realInputEval p₁ (MultiAffine.dropLast x) := rfl

/-- Closed small-ball event for a complex polynomial restricted to real
inputs. -/
def realInputClosedSmallBall {n : ℕ} (p : MultiAffine ℂ n) (r : ℝ) :
    Set (Fin n → ℝ) :=
  {x | ‖realInputEval p x‖ ≤ r}

/-- Open small-ball event for a complex polynomial restricted to real
inputs. -/
def realInputOpenSmallBall {n : ℕ} (p : MultiAffine ℂ n) (r : ℝ) :
    Set (Fin n → ℝ) :=
  {x | ‖realInputEval p x‖ < r}

/-- Real-input evaluation is continuous even though the polynomial and its
value are complex. -/
theorem MultiAffine.continuous_realInputEval : ∀ {n : ℕ}
    (p : MultiAffine ℂ n), Continuous (realInputEval p) := by
  intro n p
  induction p with
  | const c =>
      change Continuous (fun _ : Fin 0 → ℝ => c)
      exact continuous_const
  | @affine n p₀ p₁ ih₀ ih₁ =>
      change Continuous (fun x : Fin (n + 1) → ℝ =>
        realInputEval p₀ (MultiAffine.dropLast x) +
          (x (Fin.last n) : ℂ) *
            realInputEval p₁ (MultiAffine.dropLast x))
      exact (ih₀.comp continuous_dropLast_real).add
        ((Complex.continuous_ofReal.comp (continuous_apply (Fin.last n))).mul
          (ih₁.comp continuous_dropLast_real))

theorem measurableSet_realInputOpenSmallBall {n : ℕ}
    (p : MultiAffine ℂ n) (r : ℝ) :
    MeasurableSet (realInputOpenSmallBall p r) := by
  change MeasurableSet ((fun x => ‖realInputEval p x‖) ⁻¹' Iio r)
  exact isOpen_Iio.preimage p.continuous_realInputEval.norm |>.measurableSet

theorem measurableSet_realInputClosedSmallBall {n : ℕ}
    (p : MultiAffine ℂ n) (r : ℝ) :
    MeasurableSet (realInputClosedSmallBall p r) := by
  change MeasurableSet ((fun x => ‖realInputEval p x‖) ⁻¹' Iic r)
  exact isClosed_Iic.preimage p.continuous_realInputEval.norm |>.measurableSet

theorem measurableSet_realInputOneCoordinateEvent {n : ℕ}
    (p₀ p₁ : MultiAffine ℂ n) (ε ρ : ℝ) :
    MeasurableSet
      {x | ‖realInputEval (.affine p₀ p₁) x‖ ≤ ε * ρ ∧
        ε ≤ ‖realInputEval p₁ (MultiAffine.dropLast x)‖} := by
  apply MeasurableSet.inter
  · exact measurableSet_realInputClosedSmallBall _ _
  · exact isClosed_Ici.preimage
      (p₁.continuous_realInputEval.norm.comp continuous_dropLast_real)
        |>.measurableSet

/-- A complex affine function of one real variable has a small-ball bound
obtained by projecting onto a real or imaginary component of its slope. -/
theorem complexAffine_realInput_smallBall_of_intervalBound
    {ν : Measure ℝ} {L : ℝ≥0∞} (hν : RealIntervalBound ν L)
    {a b : ℂ} {ε ρ : ℝ} (hρ : 0 ≤ ρ) (hε : 0 < ε)
    (hslope : ε ≤ ‖a‖) :
    ν {x : ℝ | ‖b + (x : ℂ) * a‖ ≤ ε * ρ} ≤
      (4 : ℝ≥0∞) * L * ENNReal.ofReal ρ := by
  have hcomponent : ε / 2 ≤ |a.re| ∨ ε / 2 ≤ |a.im| := by
    by_contra h
    push Not at h
    have hnorm := Complex.norm_le_abs_re_add_abs_im a
    linarith
  have hεhalf : 0 < ε / 2 := by positivity
  have htwoρ : 0 ≤ 2 * ρ := mul_nonneg (by norm_num) hρ
  rcases hcomponent with hre | him
  · have hsub :
        {x : ℝ | ‖b + (x : ℂ) * a‖ ≤ ε * ρ} ⊆
          {x : ℝ | |b.re + x * a.re| ≤ (ε / 2) * (2 * ρ)} := by
      intro x hx
      have hpart := Complex.abs_re_le_norm (b + (x : ℂ) * a)
      change |b.re + x * a.re| ≤ (ε / 2) * (2 * ρ)
      calc
        |b.re + x * a.re| ≤ ‖b + (x : ℂ) * a‖ := by simpa using hpart
        _ ≤ ε * ρ := hx
        _ = (ε / 2) * (2 * ρ) := by ring
    calc
      ν {x : ℝ | ‖b + (x : ℂ) * a‖ ≤ ε * ρ} ≤
          ν {x : ℝ | |b.re + x * a.re| ≤ (ε / 2) * (2 * ρ)} :=
        measure_mono hsub
      _ ≤ (2 : ℝ≥0∞) * L * ENNReal.ofReal (2 * ρ) :=
        real_affine_smallBall_of_intervalBound hν htwoρ hεhalf hre
      _ = (4 : ℝ≥0∞) * L * ENNReal.ofReal ρ := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_ofNat]
        ring
  · have hsub :
        {x : ℝ | ‖b + (x : ℂ) * a‖ ≤ ε * ρ} ⊆
          {x : ℝ | |b.im + x * a.im| ≤ (ε / 2) * (2 * ρ)} := by
      intro x hx
      have hpart := Complex.abs_im_le_norm (b + (x : ℂ) * a)
      change |b.im + x * a.im| ≤ (ε / 2) * (2 * ρ)
      calc
        |b.im + x * a.im| ≤ ‖b + (x : ℂ) * a‖ := by simpa using hpart
        _ ≤ ε * ρ := hx
        _ = (ε / 2) * (2 * ρ) := by ring
    calc
      ν {x : ℝ | ‖b + (x : ℂ) * a‖ ≤ ε * ρ} ≤
          ν {x : ℝ | |b.im + x * a.im| ≤ (ε / 2) * (2 * ρ)} :=
        measure_mono hsub
      _ ≤ (2 : ℝ≥0∞) * L * ENNReal.ofReal (2 * ρ) :=
        real_affine_smallBall_of_intervalBound hν htwoρ hεhalf him
      _ = (4 : ℝ≥0∞) * L * ENNReal.ofReal ρ := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_ofNat]
        ring

/-- Exact prefix-marginal input for complex polynomials evaluated on real
vectors. -/
def RealInputPrefixSmallBallConsistent
    (μ : (n : ℕ) → Measure (Fin n → ℝ)) : Prop :=
  ∀ (n : ℕ) (p : MultiAffine ℂ n) (r : ℝ),
    μ (n + 1) (MultiAffine.dropLast ⁻¹' realInputOpenSmallBall p r) =
      μ n (realInputOpenSmallBall p r)

/-- Integrated one-real-coordinate input for a complex-valued multiaffine
polynomial. -/
def RealInputOneCoordinateSmallBall
    (μ : (n : ℕ) → Measure (Fin n → ℝ)) (ρ : ℝ) (δ : ℝ≥0∞) : Prop :=
  ∀ (n : ℕ) (p₀ p₁ : MultiAffine ℂ n) (ε : ℝ),
    0 < ε → μ (n + 1)
      {x | ‖realInputEval (.affine p₀ p₁) x‖ ≤ ε * ρ ∧
        ε ≤ ‖realInputEval p₁ (MultiAffine.dropLast x)‖} ≤ δ

/-- One recursive small-ball step for complex polynomials on real inputs. -/
theorem oneStep_realInputClosedSmallBall
    {μ : (n : ℕ) → Measure (Fin n → ℝ)} {ρ : ℝ} {δ : ℝ≥0∞}
    (hprefix : RealInputPrefixSmallBallConsistent μ)
    (hone : RealInputOneCoordinateSmallBall μ ρ δ)
    {n : ℕ} (p₀ p₁ : MultiAffine ℂ n) (ε : ℝ) (hε : 0 < ε) :
    μ (n + 1)
        (realInputClosedSmallBall (.affine p₀ p₁) (ε * ρ)) ≤
      δ + μ n (realInputOpenSmallBall p₁ ε) := by
  let good : Set (Fin (n + 1) → ℝ) :=
    {x | ‖realInputEval (.affine p₀ p₁) x‖ ≤ ε * ρ ∧
      ε ≤ ‖realInputEval p₁ (MultiAffine.dropLast x)‖}
  let bad : Set (Fin (n + 1) → ℝ) :=
    MultiAffine.dropLast ⁻¹' realInputOpenSmallBall p₁ ε
  have hsub :
      realInputClosedSmallBall (.affine p₀ p₁) (ε * ρ) ⊆ good ∪ bad := by
    intro x hx
    simp only [realInputClosedSmallBall, mem_ofPred_eq] at hx
    simp only [good, bad, mem_union, mem_ofPred_eq, mem_preimage,
      realInputOpenSmallBall]
    by_cases hslope :
        ε ≤ ‖realInputEval p₁ (MultiAffine.dropLast x)‖
    · exact Or.inl ⟨hx, hslope⟩
    · exact Or.inr (lt_of_not_ge hslope)
  have hgood : μ (n + 1) good ≤ δ := by
    simpa only [good] using hone n p₀ p₁ ε hε
  have hbad : μ (n + 1) bad = μ n (realInputOpenSmallBall p₁ ε) := by
    simpa only [bad] using hprefix n p₁ ε
  calc
    μ (n + 1) (realInputClosedSmallBall (.affine p₀ p₁) (ε * ρ)) ≤
        μ (n + 1) (good ∪ bad) := measure_mono hsub
    _ ≤ μ (n + 1) good + μ (n + 1) bad := measure_union_le _ _
    _ ≤ δ + μ n (realInputOpenSmallBall p₁ ε) :=
      add_le_add hgood (le_of_eq hbad)

/-- Recursive open-ball estimate for complex polynomials on real inputs. -/
theorem realInputOpenSmallBall_topCoeff_le
    {μ : (n : ℕ) → Measure (Fin n → ℝ)} {ρ : ℝ} {δ : ℝ≥0∞}
    (hρ : 0 < ρ) (hprefix : RealInputPrefixSmallBallConsistent μ)
    (hone : RealInputOneCoordinateSmallBall μ ρ δ) :
    ∀ {n : ℕ} (p : MultiAffine ℂ n),
      0 < ‖p.topCoeff‖ →
        μ n (realInputOpenSmallBall p (‖p.topCoeff‖ * ρ ^ n)) ≤
          (n : ℝ≥0∞) * δ := by
  intro n p htop
  induction p with
  | const c =>
      simp [realInputOpenSmallBall, realInputEval]
  | @affine n p₀ p₁ ih₀ ih₁ =>
      have htop₁ : 0 < ‖p₁.topCoeff‖ := by simpa using htop
      have hscale : 0 < ‖p₁.topCoeff‖ * ρ ^ n :=
        mul_pos htop₁ (pow_pos hρ n)
      have hsub :
          realInputOpenSmallBall (.affine p₀ p₁)
              (‖p₁.topCoeff‖ * ρ ^ (n + 1)) ⊆
            realInputClosedSmallBall (.affine p₀ p₁)
              ((‖p₁.topCoeff‖ * ρ ^ n) * ρ) := by
        intro x hx
        have hx' :
            ‖realInputEval (.affine p₀ p₁) x‖ <
              ‖p₁.topCoeff‖ * ρ ^ (n + 1) := by
          simpa only [realInputOpenSmallBall, mem_ofPred_eq] using hx
        simpa only [realInputClosedSmallBall, mem_ofPred_eq, pow_succ,
          mul_assoc] using le_of_lt hx'
      calc
        μ (n + 1) (realInputOpenSmallBall (.affine p₀ p₁)
            (‖(MultiAffine.affine p₀ p₁).topCoeff‖ * ρ ^ (n + 1))) ≤
          μ (n + 1) (realInputClosedSmallBall (.affine p₀ p₁)
            ((‖p₁.topCoeff‖ * ρ ^ n) * ρ)) := by
              simpa using measure_mono hsub
        _ ≤ δ + μ n
            (realInputOpenSmallBall p₁ (‖p₁.topCoeff‖ * ρ ^ n)) :=
          oneStep_realInputClosedSmallBall hprefix hone p₀ p₁ _ hscale
        _ ≤ δ + (n : ℝ≥0∞) * δ :=
          add_le_add (le_refl δ) (ih₁ htop₁)
        _ = ((n + 1 : ℕ) : ℝ≥0∞) * δ := by
          simp [add_mul, add_comm]

/-- Closed-ball version for at least one real input variable. -/
theorem realInputClosedSmallBall_topCoeff_le
    {μ : (n : ℕ) → Measure (Fin n → ℝ)} {ρ : ℝ} {δ : ℝ≥0∞}
    (hρ : 0 < ρ) (hprefix : RealInputPrefixSmallBallConsistent μ)
    (hone : RealInputOneCoordinateSmallBall μ ρ δ)
    {n : ℕ} (p : MultiAffine ℂ (n + 1)) (htop : 0 < ‖p.topCoeff‖) :
    μ (n + 1)
        (realInputClosedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) * δ := by
  cases p with
  | affine p₀ p₁ =>
      have htop₁ : 0 < ‖p₁.topCoeff‖ := by simpa using htop
      have hscale : 0 < ‖p₁.topCoeff‖ * ρ ^ n :=
        mul_pos htop₁ (pow_pos hρ n)
      calc
        μ (n + 1) (realInputClosedSmallBall (.affine p₀ p₁)
            (‖(MultiAffine.affine p₀ p₁).topCoeff‖ * ρ ^ (n + 1))) ≤
          δ + μ n
            (realInputOpenSmallBall p₁ (‖p₁.topCoeff‖ * ρ ^ n)) := by
              simpa [pow_succ, mul_assoc] using
                oneStep_realInputClosedSmallBall hprefix hone p₀ p₁
                  (‖p₁.topCoeff‖ * ρ ^ n) hscale
        _ ≤ δ + (n : ℝ≥0∞) * δ :=
          add_le_add (le_refl δ)
            (realInputOpenSmallBall_topCoeff_le hρ hprefix hone p₁ htop₁)
        _ = ((n + 1 : ℕ) : ℝ≥0∞) * δ := by
          simp [add_mul, add_comm]

/-- Recursive IID real product laws have the required prefix marginal for
complex polynomials restricted to real inputs. -/
theorem iidMeasure_realInputPrefixSmallBallConsistent
    (ν : Measure ℝ) [SFinite ν] [IsProbabilityMeasure ν] :
    RealInputPrefixSmallBallConsistent (iidMeasure ν) := by
  intro n p r
  let _ := iidMeasure_isProbability ν n
  have hs : MeasurableSet (realInputOpenSmallBall p r) :=
    measurableSet_realInputOpenSmallBall p r
  rw [iidMeasure,
    Measure.map_apply measurable_joinLast (hs.preimage measurable_dropLast)]
  have hpre :
      joinLast ⁻¹' (MultiAffine.dropLast ⁻¹' realInputOpenSmallBall p r) =
        Prod.fst ⁻¹' realInputOpenSmallBall p r := by
    ext y
    simp only [mem_preimage, dropLast_joinLast]
  rw [hpre, ← Measure.map_apply measurable_fst hs, Measure.map_fst_prod]
  simp

/-- The one-dimensional projection bound lifts through the real IID product
law with cost `4 L ρ`. -/
theorem iidMeasure_oneCoordinateSmallBall_realInputComplex
    (ν : Measure ℝ) [SFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ≥0∞} (hν : RealIntervalBound ν L) {ρ : ℝ} (hρ : 0 < ρ) :
    RealInputOneCoordinateSmallBall (iidMeasure ν) ρ
      ((4 : ℝ≥0∞) * L * ENNReal.ofReal ρ) := by
  intro n p₀ p₁ ε hε
  let _ := iidMeasure_isProbability ν n
  let good : Set (Fin (n + 1) → ℝ) :=
    {x | ‖realInputEval (.affine p₀ p₁) x‖ ≤ ε * ρ ∧
      ε ≤ ‖realInputEval p₁ (MultiAffine.dropLast x)‖}
  have hgood : MeasurableSet good := by
    simpa only [good] using
      measurableSet_realInputOneCoordinateEvent p₀ p₁ ε ρ
  change iidMeasure ν (n + 1) good ≤
    (4 : ℝ≥0∞) * L * ENNReal.ofReal ρ
  rw [iidMeasure, Measure.map_apply measurable_joinLast hgood,
    Measure.prod_apply (hgood.preimage measurable_joinLast)]
  calc
    (∫⁻ y, ν (Prod.mk y ⁻¹' (joinLast ⁻¹' good)) ∂iidMeasure ν n) ≤
        ∫⁻ _y : Fin n → ℝ,
          (4 : ℝ≥0∞) * L * ENNReal.ofReal ρ ∂iidMeasure ν n := by
      apply lintegral_mono
      intro y
      by_cases hslope : ε ≤ ‖realInputEval p₁ y‖
      · simpa [good, realInputEval_affine, hslope] using
          complexAffine_realInput_smallBall_of_intervalBound hν hρ.le hε hslope
      · simp [good, realInputEval_affine, hslope]
    _ = (4 : ℝ≥0∞) * L * ENNReal.ofReal ρ := by simp

/-- Real IID small-ball estimate for a complex-valued multiaffine polynomial
with nonzero complex top coefficient. -/
theorem iid_realInput_complex_multiaffine_bound
    (ν : Measure ℝ) [SFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ≥0∞} (hν : RealIntervalBound ν L)
    {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ} (p : MultiAffine ℂ (n + 1))
    (htop : 0 < ‖p.topCoeff‖) :
    iidMeasure ν (n + 1)
        (realInputClosedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) * ((4 : ℝ≥0∞) * L) * ENNReal.ofReal ρ := by
  calc
    iidMeasure ν (n + 1)
        (realInputClosedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) *
        ((4 : ℝ≥0∞) * L * ENNReal.ofReal ρ) :=
      realInputClosedSmallBall_topCoeff_le hρ
        (iidMeasure_realInputPrefixSmallBallConsistent ν)
        (iidMeasure_oneCoordinateSmallBall_realInputComplex ν hν hρ)
        p htop
    _ = ((n + 1 : ℕ) : ℝ≥0∞) * ((4 : ℝ≥0∞) * L) *
        ENNReal.ofReal ρ := by ring

/-- Density presentation of the real-input/complex-valued small-ball bound. -/
theorem iid_realInput_complex_multiaffine_bound_withDensity
    (f : ℝ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ≥0∞} (hf : ∀ᵐ x ∂(volume : Measure ℝ), f x ≤ L)
    {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ} (p : MultiAffine ℂ (n + 1))
    (htop : 0 < ‖p.topCoeff‖) :
    iidMeasure (volume.withDensity f) (n + 1)
        (realInputClosedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) * ((4 : ℝ≥0∞) * L) * ENNReal.ofReal ρ := by
  exact iid_realInput_complex_multiaffine_bound (volume.withDensity f)
    (realIntervalBound_withDensity hf) hρ p htop

/-- Untruncated negative-log theorem for complex coefficients and IID real
inputs satisfying an interval-density bound.  The scale is the modulus of
the genuinely complex top coefficient. -/
theorem iid_realInput_complex_positiveLogLoss_of_intervalBound
    (ν : Measure ℝ) [SFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ} (hL : 0 ≤ L)
    (hν : RealIntervalBound ν (ENNReal.ofReal L))
    {n : ℕ} (p : MultiAffine ℂ (n + 1))
    (htop : 0 < ‖p.topCoeff‖) :
    iidMeasure ν (n + 1) {x | ‖realInputEval p x‖ = 0} = 0 ∧
      (fun x => positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p x‖) =ᵐ[
        iidMeasure ν (n + 1)]
        (fun x => max 0
          (Real.log (‖p.topCoeff‖ / ‖realInputEval p x‖))) ∧
      Integrable
        (fun x => positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p x‖)
        (iidMeasure ν (n + 1)) ∧
      ∫ x, positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p x‖
          ∂iidMeasure ν (n + 1) ≤
        (Real.log
              (max 1 (((n + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
          (((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  let _ := iidMeasure_isProbability ν (n + 1)
  apply zeroSet_aeLog_and_integrable_positiveLogLoss_of_power_smallBall
    (iidMeasure ν (n + 1))
    (fun x => ‖realInputEval p x‖) p.continuous_realInputEval.norm.measurable
    (fun x => norm_nonneg _)
    ‖p.topCoeff‖ (((n + 1 : ℕ) : ℝ) * (4 * L)) htop
    (n + 1) 1 (Nat.succ_pos n) Nat.one_pos
  intro ρ hρ
  change iidMeasure ν (n + 1)
      (realInputClosedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤ _
  calc
    iidMeasure ν (n + 1)
        (realInputClosedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) *
          ((4 : ℝ≥0∞) * ENNReal.ofReal L) * ENNReal.ofReal ρ :=
      iid_realInput_complex_multiaffine_bound ν hν hρ p htop
    _ = ENNReal.ofReal
        ((((n + 1 : ℕ) : ℝ) * (4 * L)) * ρ ^ 1) := by
      rw [pow_one, ← ENNReal.ofReal_natCast (n + 1),
        ← ENNReal.ofReal_ofNat 4,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
        ← ENNReal.ofReal_mul (Nat.cast_nonneg (n + 1)),
        ← ENNReal.ofReal_mul
          (mul_nonneg (Nat.cast_nonneg (n + 1))
            (mul_nonneg (by norm_num) hL))]

/-- Bounded-density specialization of the untruncated negative-log theorem. -/
theorem iid_realInput_complex_positiveLogLoss_withDensity
    (f : ℝ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ x ∂(volume : Measure ℝ), f x ≤ ENNReal.ofReal L)
    {n : ℕ} (p : MultiAffine ℂ (n + 1))
    (htop : 0 < ‖p.topCoeff‖) :
    iidMeasure (volume.withDensity f) (n + 1)
        {x | ‖realInputEval p x‖ = 0} = 0 ∧
      (fun x => positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p x‖) =ᵐ[
        iidMeasure (volume.withDensity f) (n + 1)]
        (fun x => max 0
          (Real.log (‖p.topCoeff‖ / ‖realInputEval p x‖))) ∧
      Integrable
        (fun x => positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p x‖)
        (iidMeasure (volume.withDensity f) (n + 1)) ∧
      ∫ x, positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p x‖
          ∂iidMeasure (volume.withDensity f) (n + 1) ≤
        (Real.log
              (max 1 (((n + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
          (((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  exact iid_realInput_complex_positiveLogLoss_of_intervalBound
    (volume.withDensity f) hL (realIntervalBound_withDensity hf) p htop

end CircularLawSection4
