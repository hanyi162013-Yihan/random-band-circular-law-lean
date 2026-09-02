import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Probability modes used by the Tao--Vu replacement principle

This file isolates the probabilistic notions in Theorem 2.1 and both the
probability and almost-sure parts of Lemma 3.1 of Tao--Vu,
*Random matrices: Universality of ESDs and the circular law*,
arXiv:0807.4898v5.

The definitions below make the common underlying probability space explicit.
No independence assumption is present.
-/

open Filter Set
open scoped ENNReal Topology

namespace TaoVuReplacement

open MeasureTheory

section Modes

variable {Ω E : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup E]

/-- Tao--Vu Definition 1.2, in its standard tail formulation: `Xₙ` is bounded
in probability when, for every positive error probability, a deterministic
norm bound holds eventually outside an event of at most that probability.

For finite-valued scalar random variables this is equivalent to the paper's
formula
`lim_{C → ∞} liminf_{n → ∞} P (‖Xₙ‖ ≤ C) = 1`.
-/
def BoundedInProbability (ℙ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ℙ {ω | C < ‖X n ω‖} < ε

/-- Tao--Vu Definition 1.2, almost-sure boundedness.  For a real sequence,
this is equivalent to `limsupₙ ‖Xₙ(ω)‖ < ∞`: changing finitely many terms does
not affect existence of a finite bound for the whole sequence. -/
def AlmostSurelyBounded (ℙ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ᵐ ω ∂ℙ, ∃ C : ℝ, ∀ n, ‖X n ω‖ ≤ C

/-- Scalar convergence in probability, expressed using mathlib's convergence
in measure on the underlying probability space. -/
def ConvergesInProbability (ℙ : Measure Ω) (X : ℕ → Ω → E) (Y : Ω → E) : Prop :=
  TendstoInMeasure ℙ X atTop Y

/-- The threshold-event characterization of scalar convergence in
probability. -/
theorem convergesInProbability_iff_norm {ℙ : Measure Ω} [IsFiniteMeasure ℙ]
    {X : ℕ → Ω → E} {Y : Ω → E} :
    ConvergesInProbability ℙ X Y ↔
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n ↦ ℙ.real {ω | ε ≤ ‖X n ω - Y ω‖}) atTop (𝓝 0) := by
  simpa [ConvergesInProbability] using
    (tendstoInMeasure_iff_measureReal_norm (μ := ℙ) (f := X) (g := Y) (l := atTop))

/-- A deterministic uniform bound is, in particular, a bound in
probability. -/
theorem boundedInProbability_of_uniform_bound {ℙ : Measure Ω} [IsFiniteMeasure ℙ]
    {X : ℕ → Ω → E} {C : ℝ} (hC : 0 ≤ C)
    (hX : ∀ n ω, ‖X n ω‖ ≤ C) : BoundedInProbability ℙ X := by
  intro ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [] with n
  have hempty : {ω | C < ‖X n ω‖} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    exact fun ω hω ↦ (not_lt_of_ge (hX n ω)) hω
  rw [hempty, measure_empty]
  exact hε

end Modes

section ExtendedNonnegativeModes

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Tail boundedness in probability for an extended-nonnegative random
variable.  This variant is useful for `lintegral` moments: unlike the Bochner
integral, `lintegral` records non-integrability as `∞` rather than silently
returning zero.  Requiring the cutoff to be finite is essential. -/
def ENNRealBoundedInProbability (ℙ : Measure Ω)
    (X : ℕ → Ω → ℝ≥0∞) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ᶠ n in atTop, ℙ {ω | C < X n ω} < ε

/-- Almost-sure boundedness for extended-nonnegative random variables.
This is the version needed for `lintegral` moments in the almost-sure half of
Tao--Vu Lemma 3.1.  The witness is required to be finite, so the statement
does not become vacuous when a moment is `∞`. -/
def ENNRealAlmostSurelyBounded (ℙ : Measure Ω)
    (X : ℕ → Ω → ℝ≥0∞) : Prop :=
  ∀ᵐ ω ∂ℙ, ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n, X n ω ≤ C

/-- Direct threshold formulation of convergence in probability to zero for
extended-nonnegative random variables.  Only finite thresholds are needed. -/
def ENNRealConvergesInProbabilityToZero (ℙ : Measure Ω)
    (X : ℕ → Ω → ℝ≥0∞) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ε ≠ ∞ →
    Tendsto (fun n ↦ ℙ {ω | ε ≤ X n ω}) atTop (𝓝 0)

end ExtendedNonnegativeModes

section DeterministicMomentBound

variable {S E : Type*} [MeasurableSpace S] [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E]

/-- The deterministic estimate underlying Tao--Vu Lemma 3.1.  It separates
the region where `‖g‖ < κ` and applies Hölder on its complement. -/
theorem lintegral_enorm_le_cutoff_add_moment
    (ν : Measure S) (g : S → E) (hg : Measurable g)
    {p q : ℝ} (hpq : p.HolderConjugate q) (κ : ℝ≥0∞) :
    (∫⁻ x, ‖g x‖ₑ ∂ν) ≤
      κ * ν Set.univ +
        (∫⁻ x, ‖g x‖ₑ ^ p ∂ν) ^ (1 / p) *
          ν {x | κ ≤ ‖g x‖ₑ} ^ (1 / q) := by
  let s : Set S := {x | κ ≤ ‖g x‖ₑ}
  have hs : MeasurableSet s := measurableSet_le measurable_const hg.enorm
  rw [← lintegral_add_compl (μ := ν) (fun x ↦ ‖g x‖ₑ) hs]
  rw [add_comm (κ * ν Set.univ)]
  refine add_le_add ?_ ?_
  · let ind : S → ℝ≥0∞ := s.indicator (fun _ ↦ 1)
    have hind : AEMeasurable ind ν := (measurable_const.indicator hs).aemeasurable
    have hindpow : (∫⁻ x, ind x ^ q ∂ν) = ν s := by
      rw [show (fun x ↦ ind x ^ q) = s.indicator (fun _ ↦ 1) by
        funext x
        by_cases hx : x ∈ s
        · simp [ind, hx]
        · simp [ind, hx, ENNReal.zero_rpow_of_pos hpq.symm.pos]]
      exact lintegral_indicator_one hs
    have hbad_eq :
        (∫⁻ x in s, ‖g x‖ₑ ∂ν) = ∫⁻ x, ‖g x‖ₑ * ind x ∂ν := by
      rw [← lintegral_indicator hs]
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ s <;> simp [ind, hx]
    rw [hbad_eq]
    calc
      (∫⁻ x, ‖g x‖ₑ * ind x ∂ν) ≤
          (∫⁻ x, ‖g x‖ₑ ^ p ∂ν) ^ (1 / p) *
            (∫⁻ x, ind x ^ q ∂ν) ^ (1 / q) := by
        simpa only [Pi.mul_apply] using
          (ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hg.enorm.aemeasurable hind)
      _ = (∫⁻ x, ‖g x‖ₑ ^ p ∂ν) ^ (1 / p) *
          (ν s) ^ (1 / q) := by rw [hindpow]
      _ = (∫⁻ x, ‖g x‖ₑ ^ p ∂ν) ^ (1 / p) *
          ν {x | κ ≤ ‖g x‖ₑ} ^ (1 / q) := by rfl
  · calc
      (∫⁻ x in sᶜ, ‖g x‖ₑ ∂ν) ≤ ∫⁻ _x in sᶜ, κ ∂ν := by
        refine setLIntegral_mono' hs.compl ?_
        intro x hx
        have hx' : ¬κ ≤ ‖g x‖ₑ := by simpa [s] using hx
        exact (lt_of_not_ge hx').le
      _ = κ * ν (sᶜ) := by simp
      _ ≤ κ * ν Set.univ := by
        gcongr
        exact Set.subset_univ _

/-- Deterministic uniform-integrability step behind the almost-sure half of
Tao--Vu Lemma 3.1.  Almost-everywhere convergence to zero, together with one
finite uniform `Lᵖ` bound for `p > 1`, forces the `L¹` norms to tend to zero.

The proof deliberately uses the same cutoff/Hölder estimate as the
probability argument, rather than importing a dominated-convergence premise
that would be stronger than the source hypothesis. -/
theorem tendsto_lintegral_enorm_of_ae_tendsto_zero_of_uniform_rpow_bound
    (ν : Measure S) [IsFiniteMeasure ν] [SecondCountableTopology E]
    (g : ℕ → S → E) (p : ℝ) (hp : 1 < p)
    (hg : ∀ n, Measurable (g n))
    (hpoint : ∀ᵐ x ∂ν, Tendsto (fun n ↦ g n x) atTop (𝓝 0))
    (M : ℝ≥0∞) (hM_top : M ≠ ∞)
    (hmoment : ∀ n, (∫⁻ x, ‖g n x‖ₑ ^ p ∂ν) ≤ M) :
    Tendsto (fun n ↦ ∫⁻ x, ‖g n x‖ₑ ∂ν) atTop (𝓝 0) := by
  let q : ℝ := Real.conjExponent p
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hq_pos : 0 < q := hpq.symm.pos
  have hconv : TendstoInMeasure ν g atTop 0 :=
    tendstoInMeasure_of_tendsto_ae (fun n ↦ (hg n).aestronglyMeasurable) hpoint
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε_half : 0 < ε / 2 := ENNReal.half_pos hε.ne'

  have hν_top : ν Set.univ ≠ ∞ := measure_ne_top ν Set.univ
  have hκ_tendsto :
      Tendsto (fun κ : ℝ≥0∞ ↦ ν Set.univ * κ ^ (1 : ℝ))
        (𝓝 0) (𝓝 0) :=
    ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hν_top one_pos
  have hκ_eventually := hκ_tendsto.eventually (gt_mem_nhds hε_half)
  obtain ⟨κ₀, hκ₀_pos, hκ₀⟩ :=
    ENNReal.nhds_zero_basis_Iic.eventually_iff.mp hκ_eventually
  let κ : ℝ≥0∞ := min κ₀ 1
  have hκ_pos : 0 < κ := by simp [κ, hκ₀_pos]
  have hκ_top : κ ≠ ∞ := by simp [κ]
  have hκ_small : κ * ν Set.univ < ε / 2 := by
    have hmem : min κ₀ 1 ∈ Set.Iic κ₀ := by
      simpa only [Set.mem_Iic] using (min_le_left κ₀ 1)
    have h := hκ₀ hmem
    simpa [κ, ENNReal.rpow_one, mul_comm] using h

  let volume : ℕ → ℝ≥0∞ := fun n ↦ ν {x | κ ≤ ‖g n x‖ₑ}
  have hvolume : Tendsto volume atTop (𝓝 0) := by
    have h := (tendstoInMeasure_iff_enorm.mp hconv) κ hκ_pos hκ_top
    simpa [volume] using h
  let c : ℝ≥0∞ := M ^ (1 / p)
  have hc_top : c ≠ ∞ := by
    exact (ENNReal.rpow_lt_top_of_nonneg (by positivity) hM_top).ne
  have htail :
      Tendsto (fun n ↦ c * volume n ^ (1 / q)) atTop (𝓝 0) := by
    exact (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hc_top
      (one_div_pos.mpr hq_pos)).comp hvolume
  have htail_eventually :=
    (ENNReal.tendsto_nhds_zero.mp htail) (ε / 2) hε_half

  filter_upwards [htail_eventually] with n hn
  have hdet := lintegral_enorm_le_cutoff_add_moment
    ν (g n) (hg n) hpq κ
  calc
    (∫⁻ x, ‖g n x‖ₑ ∂ν) ≤
        κ * ν Set.univ +
          (∫⁻ x, ‖g n x‖ₑ ^ p ∂ν) ^ (1 / p) *
            volume n ^ (1 / q) := by
      simpa [volume] using hdet
    _ ≤ κ * ν Set.univ + c * volume n ^ (1 / q) := by
      dsimp [c]
      gcongr
      exact hmoment n
    _ ≤ ε / 2 + ε / 2 := add_le_add hκ_small.le hn
    _ = ε := ENNReal.add_halves ε

/-- Bochner-integral form of
`tendsto_lintegral_enorm_of_ae_tendsto_zero_of_uniform_rpow_bound`.
It is the deterministic conclusion applied samplewise in the almost-sure
version of Tao--Vu Lemma 3.1. -/
theorem tendsto_integral_of_ae_tendsto_zero_of_uniform_rpow_bound
    (ν : Measure S) [IsFiniteMeasure ν] [SecondCountableTopology E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (g : ℕ → S → E) (p : ℝ) (hp : 1 < p)
    (hg : ∀ n, Measurable (g n))
    (hpoint : ∀ᵐ x ∂ν, Tendsto (fun n ↦ g n x) atTop (𝓝 0))
    (M : ℝ≥0∞) (hM_top : M ≠ ∞)
    (hmoment : ∀ n, (∫⁻ x, ‖g n x‖ₑ ^ p ∂ν) ≤ M) :
    Tendsto (fun n ↦ ∫ x, g n x ∂ν) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_enorm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_lintegral_enorm_of_ae_tendsto_zero_of_uniform_rpow_bound
      ν g p hp hg hpoint M hM_top hmoment) (fun _ ↦ zero_le) ?_
  exact fun n ↦ enorm_integral_le_lintegral_enorm (g n)

end DeterministicMomentBound

section ProductConvergence

variable {S Ω E : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- The Fubini step in Tao--Vu Lemma 3.1: pointwise convergence in probability
for almost every parameter gives convergence in measure on the product space.

This is the genuinely probabilistic analogue of applying dominated
convergence to the probabilities of the threshold events. -/
theorem tendstoInMeasure_prod_of_ae_tendstoInMeasure
    (ν : Measure S) (ℙ : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure ℙ]
    (f : ℕ → S → Ω → E)
    (hf : ∀ n, Measurable (fun p : S × Ω ↦ f n p.1 p.2))
    (hpoint : ∀ᵐ x ∂ν, TendstoInMeasure ℙ (fun n ω ↦ f n x ω) atTop 0) :
    TendstoInMeasure (ν.prod ℙ) (fun n p ↦ f n p.1 p.2) atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let s : ℕ → Set (S × Ω) := fun n ↦ {p | ε ≤ ‖f n p.1 p.2‖}
  have hs : ∀ n, MeasurableSet (s n) := by
    intro n
    exact measurableSet_Ici.preimage (by simpa [s] using (hf n).norm)
  have hmeas : ∀ n, Measurable (fun x ↦ ℙ (Prod.mk x ⁻¹' s n)) := by
    intro n
    exact measurable_measure_prodMk_left (hs n)
  have hlim : ∀ᵐ x ∂ν,
      Tendsto (fun n ↦ ℙ (Prod.mk x ⁻¹' s n)) atTop (𝓝 0) := by
    filter_upwards [hpoint] with x hx
    rw [tendstoInMeasure_iff_norm] at hx
    simpa [s] using hx ε hε
  have hbound : ∀ᶠ n in atTop,
      ∀ᵐ x ∂ν, ℙ (Prod.mk x ⁻¹' s n) ≤ ℙ Set.univ := by
    filter_upwards [] with n
    exact Filter.Eventually.of_forall fun x ↦ measure_mono (Set.subset_univ _)
  have hfin : (∫⁻ _ : S, ℙ Set.univ ∂ν) ≠ ∞ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top (measure_ne_top ℙ Set.univ) (measure_ne_top ν Set.univ)
  have hdc := tendsto_lintegral_filter_of_dominated_convergence
    (μ := ν) (f := fun _ ↦ 0) (fun _ : S ↦ ℙ Set.univ)
    (Eventually.of_forall hmeas) hbound hfin hlim
  simpa [Measure.prod_apply, hs, s] using hdc

/-- A Markov/Fubini consequence used in Tao--Vu Lemma 3.1.  If measurable
sets in a product space have mass tending to zero, then the measure of their
vertical section converges to zero in probability. -/
theorem sectionMeasure_convergesInProbabilityToZero
    (ν : Measure S) (ℙ : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure ℙ]
    (s : ℕ → Set (S × Ω)) (hs : ∀ n, MeasurableSet (s n))
    (hprod : Tendsto (fun n ↦ (ν.prod ℙ) (s n)) atTop (𝓝 0)) :
    ENNRealConvergesInProbabilityToZero ℙ
      (fun n ω ↦ ν ((fun x ↦ (x, ω)) ⁻¹' s n)) := by
  intro a ha ha_top
  let v : ℕ → Ω → ℝ≥0∞ := fun n ω ↦ ν ((fun x ↦ (x, ω)) ⁻¹' s n)
  have hvmeas : ∀ n, Measurable (v n) := by
    intro n
    exact measurable_measure_prodMk_right (hs n)
  have hvint : Tendsto (fun n ↦ ∫⁻ ω, v n ω ∂ℙ) atTop (𝓝 0) := by
    simpa [v, Measure.prod_apply_symm, hs] using hprod
  have hvdiv : Tendsto (fun n ↦ (∫⁻ ω, v n ω ∂ℙ) / a) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.div_const hvint (Or.inr ha.ne')
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvdiv
    (fun _ ↦ zero_le) ?_
  intro n
  exact meas_ge_le_lintegral_div (hvmeas n).aemeasurable ha.ne' ha_top

/-- Fubini exchange for the almost-sure half of Tao--Vu Lemma 3.1.
Joint measurability makes the set of product points at which the whole
sequence converges measurable.  Consequently the full-measure event obtained
after exchanging the two variables is fixed once and for all; it does not
depend on any deterministic weight used in a later integral. -/
theorem ae_tendsto_sections_of_ae_ae_tendsto
    (ν : Measure S) (ℙ : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure ℙ]
    [SecondCountableTopology E]
    (f : ℕ → S → Ω → E)
    (hf : ∀ n, Measurable (fun z : S × Ω ↦ f n z.1 z.2))
    (hpoint : ∀ᵐ x ∂ν, ∀ᵐ ω ∂ℙ,
      Tendsto (fun n ↦ f n x ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂ℙ, ∀ᵐ x ∂ν,
      Tendsto (fun n ↦ f n x ω) atTop (𝓝 0) := by
  have hmeas : MeasurableSet {z : S × Ω |
      Tendsto (fun n ↦ f n z.1 z.2) atTop (𝓝 0)} :=
    measurableSet_tendsto_fun hf measurable_const
  exact (Measure.ae_ae_comm hmeas).mp hpoint

end ProductConvergence

section RandomDominatedConvergence

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

/-- Tao--Vu Lemma 3.1, convergence-in-probability case.

The source writes the exponent as `1 + δ` with `δ > 0`; here it is denoted
by `p`, with the equivalent assumption `1 < p`.  The moment is a `lintegral`
so that a non-integrable section has value `∞`, rather than the default value
zero used by the Bochner integral.

The proof follows the paper's argument: Fubini turns pointwise convergence in
probability into small product-measure level sets, Markov controls the random
size of their vertical sections, and Hölder controls the integral on the
large-value part. -/
theorem randomDominatedConvergence_inProbability
    (ν : Measure S) (ℙ : Measure Ω) [IsFiniteMeasure ν] [IsProbabilityMeasure ℙ]
    (f : ℕ → S → Ω → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : ∀ n, Measurable (fun z : S × Ω ↦ f n z.1 z.2))
    (hmoment : ENNRealBoundedInProbability ℙ
      (fun n ω ↦ ∫⁻ x, ‖f n x ω‖ₑ ^ p ∂ν))
    (hpoint : ∀ᵐ x ∂ν,
      TendstoInMeasure ℙ (fun n ω ↦ f n x ω) atTop 0) :
    TendstoInMeasure ℙ (fun n ω ↦ ∫ x, f n x ω ∂ν) atTop 0 := by
  let F : ℕ → S × Ω → ℝ := fun n z ↦ f n z.1 z.2
  let moment : ℕ → Ω → ℝ≥0∞ :=
    fun n ω ↦ ∫⁻ x, ‖f n x ω‖ₑ ^ p ∂ν
  have hFprod : TendstoInMeasure (ν.prod ℙ) F atTop 0 := by
    exact tendstoInMeasure_prod_of_ae_tendstoInMeasure ν ℙ f hf hpoint
  let q : ℝ := Real.conjExponent p
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hp_pos : 0 < p := hpq.pos
  have hq_pos : 0 < q := hpq.symm.pos
  rw [tendstoInMeasure_iff_enorm]
  intro ε hε hε_top
  rw [ENNReal.tendsto_nhds_zero]
  intro ρ hρ
  have hε_half : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have hρ_half : 0 < ρ / 2 := ENNReal.half_pos hρ.ne'

  obtain ⟨M, hM_top, hmoment_bad⟩ := hmoment (ρ / 2) hρ_half

  have hν_top : ν Set.univ ≠ ∞ := measure_ne_top ν Set.univ
  have hκ_tendsto :
      Tendsto (fun κ : ℝ≥0∞ ↦ ν Set.univ * κ ^ (1 : ℝ))
        (𝓝 0) (𝓝 0) :=
    ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hν_top one_pos
  have hκ_eventually := hκ_tendsto.eventually (gt_mem_nhds hε_half)
  obtain ⟨κ₀, hκ₀_pos, hκ₀⟩ :=
    ENNReal.nhds_zero_basis_Iic.eventually_iff.mp hκ_eventually
  let κ : ℝ≥0∞ := min κ₀ 1
  have hκ_pos : 0 < κ := by simp [κ, hκ₀_pos]
  have hκ_top : κ ≠ ∞ := by simp [κ]
  have hκ_small : κ * ν Set.univ < ε / 2 := by
    have hmem : min κ₀ 1 ∈ Set.Iic κ₀ := by
      simpa only [Set.mem_Iic] using (min_le_left κ₀ 1)
    have h := hκ₀ hmem
    simpa [κ, ENNReal.rpow_one, mul_comm] using h

  let c : ℝ≥0∞ := M ^ (1 / p)
  have hc_top : c ≠ ∞ := by
    exact (ENNReal.rpow_lt_top_of_nonneg (by positivity) hM_top).ne
  have ha_tendsto :
      Tendsto (fun a : ℝ≥0∞ ↦ c * a ^ (1 / q)) (𝓝 0) (𝓝 0) :=
    ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hc_top (by positivity)
  have ha_eventually := ha_tendsto.eventually (gt_mem_nhds hε_half)
  obtain ⟨a₀, ha₀_pos, ha₀⟩ :=
    ENNReal.nhds_zero_basis_Iic.eventually_iff.mp ha_eventually
  let a : ℝ≥0∞ := min a₀ 1
  have ha_pos : 0 < a := by simp [a, ha₀_pos]
  have ha_top : a ≠ ∞ := by simp [a]
  have ha_small : c * a ^ (1 / q) < ε / 2 := by
    have hmem : min a₀ 1 ∈ Set.Iic a₀ := by
      simpa only [Set.mem_Iic] using (min_le_left a₀ 1)
    exact ha₀ hmem

  let s : ℕ → Set (S × Ω) :=
    fun n ↦ {z | κ ≤ ‖F n z‖ₑ}
  have hs : ∀ n, MeasurableSet (s n) := by
    intro n
    exact measurableSet_le measurable_const (hf n).enorm
  have hs_prod_tendsto :
      Tendsto (fun n ↦ (ν.prod ℙ) (s n)) atTop (𝓝 0) := by
    have h := (tendstoInMeasure_iff_enorm.mp hFprod) κ hκ_pos hκ_top
    simpa [s, F] using h
  have hsection :=
    sectionMeasure_convergesInProbabilityToZero ν ℙ s hs hs_prod_tendsto
  have hsection_tendsto := hsection a ha_pos ha_top
  rw [ENNReal.tendsto_nhds_zero] at hsection_tendsto
  have hsection_bad := hsection_tendsto (ρ / 2) hρ_half

  let volume : ℕ → Ω → ℝ≥0∞ :=
    fun n ω ↦ ν {x | κ ≤ ‖f n x ω‖ₑ}
  have hsubset : ∀ n,
      {ω | ε ≤ ‖∫ x, f n x ω ∂ν‖ₑ} ⊆
        {ω | M < moment n ω} ∪ {ω | a ≤ volume n ω} := by
    intro n ω hω
    by_contra hbad
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hbad
    have hmoment_le : moment n ω ≤ M := le_of_not_gt hbad.1
    have hvolume_lt : volume n ω < a := lt_of_not_ge hbad.2
    have hsection_meas : Measurable (fun x ↦ f n x ω) := by
      exact (hf n).comp (measurable_id.prodMk measurable_const)
    have hdet := lintegral_enorm_le_cutoff_add_moment
      ν (fun x ↦ f n x ω) hsection_meas hpq κ
    have hmoment_part :
        moment n ω ^ (1 / p) * volume n ω ^ (1 / q) ≤
          c * a ^ (1 / q) := by
      dsimp [moment, volume, c]
      gcongr
    have hintegral_lt : ‖∫ x, f n x ω ∂ν‖ₑ < ε := by
      calc
        ‖∫ x, f n x ω ∂ν‖ₑ ≤ ∫⁻ x, ‖f n x ω‖ₑ ∂ν :=
          enorm_integral_le_lintegral_enorm _
        _ ≤ κ * ν Set.univ +
            moment n ω ^ (1 / p) * volume n ω ^ (1 / q) := by
          simpa [moment, volume] using hdet
        _ ≤ κ * ν Set.univ + c * a ^ (1 / q) :=
          add_le_add (le_refl _) hmoment_part
        _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hκ_small ha_small
        _ = ε := ENNReal.add_halves ε
    exact (not_lt_of_ge hω) hintegral_lt

  filter_upwards [hmoment_bad, hsection_bad] with n hn_moment hn_section
  have hn_section' :
      ℙ {ω | a ≤ volume n ω} ≤ ρ / 2 := by
    simpa [volume, s, F] using hn_section
  have hn_moment' : ℙ {ω | M < moment n ω} < ρ / 2 := by
    simpa [moment] using hn_moment
  simp only [Pi.zero_apply, sub_zero]
  change ℙ {ω | ε ≤ ‖∫ x, f n x ω ∂ν‖ₑ} ≤ ρ
  have hfinal : ℙ {ω | ε ≤ ‖∫ x, f n x ω ∂ν‖ₑ} < ρ := by
    calc
      ℙ {ω | ε ≤ ‖∫ x, f n x ω ∂ν‖ₑ} ≤
          ℙ ({ω | M < moment n ω} ∪ {ω | a ≤ volume n ω}) :=
        measure_mono (hsubset n)
      _ ≤ ℙ {ω | M < moment n ω} + ℙ {ω | a ≤ volume n ω} :=
        measure_union_le _ _
      _ < ρ / 2 + ρ / 2 := ENNReal.add_lt_add_of_lt_of_le
        (by finiteness) hn_moment' hn_section'
      _ = ρ := ENNReal.add_halves ρ
  exact hfinal.le

/-- Tao--Vu Lemma 3.1 in the paper's `1 + δ` notation, for convergence in
probability.  This is a direct specialization of
`randomDominatedConvergence_inProbability`. -/
theorem randomDominatedConvergence_inProbability_one_add
    (ν : Measure S) (ℙ : Measure Ω) [IsFiniteMeasure ν] [IsProbabilityMeasure ℙ]
    (f : ℕ → S → Ω → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hf : ∀ n, Measurable (fun z : S × Ω ↦ f n z.1 z.2))
    (hmoment : ENNRealBoundedInProbability ℙ
      (fun n ω ↦ ∫⁻ x, ‖f n x ω‖ₑ ^ (1 + δ) ∂ν))
    (hpoint : ∀ᵐ x ∂ν,
      TendstoInMeasure ℙ (fun n ω ↦ f n x ω) atTop 0) :
    TendstoInMeasure ℙ (fun n ω ↦ ∫ x, f n x ω ∂ν) atTop 0 := by
  exact randomDominatedConvergence_inProbability ν ℙ f (1 + δ) (by linarith)
    hf hmoment hpoint

/-- Tao--Vu Lemma 3.1, almost-sure case, with exponent `p > 1`.

The Fubini exchange is performed on the measurable event where the entire
sequence converges.  Intersecting that event with the almost-sure uniform
moment bound leaves, for each sample, precisely the deterministic hypotheses
of `tendsto_integral_of_ae_tendsto_zero_of_uniform_rpow_bound`. -/
theorem randomDominatedConvergence_almostSurely
    (ν : Measure S) (ℙ : Measure Ω) [IsFiniteMeasure ν] [IsProbabilityMeasure ℙ]
    (f : ℕ → S → Ω → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : ∀ n, Measurable (fun z : S × Ω ↦ f n z.1 z.2))
    (hmoment : ENNRealAlmostSurelyBounded ℙ
      (fun n ω ↦ ∫⁻ x, ‖f n x ω‖ₑ ^ p ∂ν))
    (hpoint : ∀ᵐ x ∂ν, ∀ᵐ ω ∂ℙ,
      Tendsto (fun n ↦ f n x ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂ℙ,
      Tendsto (fun n ↦ ∫ x, f n x ω ∂ν) atTop (𝓝 0) := by
  have hpoint_comm : ∀ᵐ ω ∂ℙ, ∀ᵐ x ∂ν,
      Tendsto (fun n ↦ f n x ω) atTop (𝓝 0) :=
    ae_tendsto_sections_of_ae_ae_tendsto ν ℙ f hf hpoint
  filter_upwards [hpoint_comm, hmoment] with ω hpoint_ω hmoment_ω
  obtain ⟨M, hM_top, hM⟩ := hmoment_ω
  exact tendsto_integral_of_ae_tendsto_zero_of_uniform_rpow_bound
    ν (fun n x ↦ f n x ω) p hp
    (fun n ↦ (hf n).comp (measurable_id.prodMk measurable_const))
    hpoint_ω M hM_top hM

/-- A common-event strengthening of the almost-sure part of Tao--Vu Lemma
3.1.  On one full-probability event, convergence holds simultaneously after
multiplication by **every** fixed bounded measurable weight.  The universal
quantifier over `w` occurs inside `∀ᵐ ω`, so this is stronger than taking a
separate null-set exception for each weight.

This is the form needed downstream for deterministic compactly supported test
functions (and their bounded derivatives): no new Fubini exceptional set is
introduced when the weight is chosen. -/
theorem randomDominatedConvergence_almostSurely_all_bounded_weights
    (ν : Measure S) (ℙ : Measure Ω) [IsFiniteMeasure ν] [IsProbabilityMeasure ℙ]
    (f : ℕ → S → Ω → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : ∀ n, Measurable (fun z : S × Ω ↦ f n z.1 z.2))
    (hmoment : ENNRealAlmostSurelyBounded ℙ
      (fun n ω ↦ ∫⁻ x, ‖f n x ω‖ₑ ^ p ∂ν))
    (hpoint : ∀ᵐ x ∂ν, ∀ᵐ ω ∂ℙ,
      Tendsto (fun n ↦ f n x ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂ℙ, ∀ w : S → ℝ, Measurable w →
      (∃ B : ℝ, ∀ x, ‖w x‖ ≤ B) →
      Tendsto (fun n ↦ ∫ x, w x * f n x ω ∂ν) atTop (𝓝 0) := by
  have hpoint_comm : ∀ᵐ ω ∂ℙ, ∀ᵐ x ∂ν,
      Tendsto (fun n ↦ f n x ω) atTop (𝓝 0) :=
    ae_tendsto_sections_of_ae_ae_tendsto ν ℙ f hf hpoint
  filter_upwards [hpoint_comm, hmoment] with ω hpoint_ω hmoment_ω
  intro w hw hw_bounded
  obtain ⟨B, hB⟩ := hw_bounded
  obtain ⟨M, hM_top, hM⟩ := hmoment_ω
  let b : ℝ≥0∞ := ENNReal.ofReal B
  have hb_top : b ≠ ∞ := ENNReal.ofReal_ne_top
  have hwenorm : ∀ x, ‖w x‖ₑ ≤ b := by
    intro x
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hB x)
  have hbpow_top : b ^ p ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg (zero_le_one.trans hp.le) hb_top).ne
  let M' : ℝ≥0∞ := b ^ p * M
  have hM'_top : M' ≠ ∞ := ENNReal.mul_ne_top hbpow_top hM_top
  have hweighted_meas : ∀ n, Measurable (fun x ↦ w x * f n x ω) := by
    intro n
    exact hw.mul ((hf n).comp (measurable_id.prodMk measurable_const))
  have hweighted_point : ∀ᵐ x ∂ν,
      Tendsto (fun n ↦ w x * f n x ω) atTop (𝓝 0) := by
    filter_upwards [hpoint_ω] with x hx
    simpa using tendsto_const_nhds.mul hx
  have hweighted_moment : ∀ n,
      (∫⁻ x, ‖w x * f n x ω‖ₑ ^ p ∂ν) ≤ M' := by
    intro n
    calc
      (∫⁻ x, ‖w x * f n x ω‖ₑ ^ p ∂ν) ≤
          ∫⁻ x, b ^ p * ‖f n x ω‖ₑ ^ p ∂ν := by
        refine lintegral_mono fun x ↦ ?_
        rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (zero_le_one.trans hp.le)]
        gcongr
        exact hwenorm x
      _ = b ^ p * (∫⁻ x, ‖f n x ω‖ₑ ^ p ∂ν) := by
        rw [lintegral_const_mul' _ _ hbpow_top]
      _ ≤ b ^ p * M := by
        gcongr
        exact hM n
      _ = M' := rfl
  exact tendsto_integral_of_ae_tendsto_zero_of_uniform_rpow_bound
    ν (fun n x ↦ w x * f n x ω) p hp hweighted_meas hweighted_point
    M' hM'_top hweighted_moment

/-- Tao--Vu Lemma 3.1 in the paper's `1 + δ` notation, for almost-sure
convergence.  This is a direct specialization of
`randomDominatedConvergence_almostSurely`. -/
theorem randomDominatedConvergence_almostSurely_one_add
    (ν : Measure S) (ℙ : Measure Ω) [IsFiniteMeasure ν] [IsProbabilityMeasure ℙ]
    (f : ℕ → S → Ω → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hf : ∀ n, Measurable (fun z : S × Ω ↦ f n z.1 z.2))
    (hmoment : ENNRealAlmostSurelyBounded ℙ
      (fun n ω ↦ ∫⁻ x, ‖f n x ω‖ₑ ^ (1 + δ) ∂ν))
    (hpoint : ∀ᵐ x ∂ν, ∀ᵐ ω ∂ℙ,
      Tendsto (fun n ↦ f n x ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂ℙ,
      Tendsto (fun n ↦ ∫ x, f n x ω ∂ν) atTop (𝓝 0) := by
  exact randomDominatedConvergence_almostSurely ν ℙ f (1 + δ) (by linarith)
    hf hmoment hpoint

/-- Paper-notation specialization of the common-event strengthening: for
`δ > 0`, one full-probability event works simultaneously for every fixed
bounded measurable weight. -/
theorem randomDominatedConvergence_almostSurely_all_bounded_weights_one_add
    (ν : Measure S) (ℙ : Measure Ω) [IsFiniteMeasure ν] [IsProbabilityMeasure ℙ]
    (f : ℕ → S → Ω → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hf : ∀ n, Measurable (fun z : S × Ω ↦ f n z.1 z.2))
    (hmoment : ENNRealAlmostSurelyBounded ℙ
      (fun n ω ↦ ∫⁻ x, ‖f n x ω‖ₑ ^ (1 + δ) ∂ν))
    (hpoint : ∀ᵐ x ∂ν, ∀ᵐ ω ∂ℙ,
      Tendsto (fun n ↦ f n x ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂ℙ, ∀ w : S → ℝ, Measurable w →
      (∃ B : ℝ, ∀ x, ‖w x‖ ≤ B) →
      Tendsto (fun n ↦ ∫ x, w x * f n x ω ∂ν) atTop (𝓝 0) := by
  exact randomDominatedConvergence_almostSurely_all_bounded_weights
    ν ℙ f (1 + δ) (by linarith) hf hmoment hpoint

end RandomDominatedConvergence

end TaoVuReplacement

