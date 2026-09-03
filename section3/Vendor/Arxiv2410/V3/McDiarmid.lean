/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/McDiarmid.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Mathlib.Probability.Moments.SubGaussian

/-!
# The bounded-differences input in the proof of v3 Proposition 3.4

This file replaces as much as possible of the paper's scalar “by McDiarmid” step by
machine-checked consequences of mathlib's proved Hoeffding lemma and Azuma--Hoeffding theorem.
No declaration below assumes a concentration conclusion.

The only bridge not supplied here is the model-specific construction which turns the resolvent
trace's coordinatewise rank/Lipschitz estimate into bounds for its Doob martingale increments.
That bridge depends on how the independent matrix entries are enumerated and is deliberately kept
out of this generic probability module.
-/

namespace Arxiv2410V3

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

section ConditionalHoeffding

variable {Omega : Type*} {m mOmega : MeasurableSpace Omega}
  [StandardBorelSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]

/-- v3 Proposition 3.4, proof step (3), conditional Hoeffding lemma used inside McDiarmid:
an almost surely `[a,b]`-valued variable whose conditional-kernel mean is zero is conditionally
sub-Gaussian with variance proxy `((b-a)/2)^2`.

This is proved from mathlib's (unconditional) Hoeffding lemma on each conditional probability
measure.  Thus conditional sub-Gaussianity is not an external interface. -/
theorem hasCondSubgaussianMGF_of_mem_Icc_of_kernel_integral_eq_zero
    (hm : m ≤ mOmega) {X : Omega → ℝ} {a b : ℝ}
    (hX : AEMeasurable X mu) (hIcc : ∀ᵐ omega ∂mu, X omega ∈ Icc a b)
    (hzero : ∀ᵐ omega ∂(mu.trim hm),
      ∫ y, X y ∂(condExpKernel mu m omega) = 0) :
    HasCondSubgaussianMGF m hm X ((‖b - a‖₊ / 2) ^ 2) mu := by
  have hXint : Integrable X mu := Integrable.of_mem_Icc a b hX hIcc
  have hkernelInt : ∀ᵐ omega ∂(mu.trim hm),
      Integrable X (condExpKernel mu m omega) := by
    apply Measure.ae_integrable_of_integrable_comp
    simpa only [condExpKernel_comp_trim hm] using hXint
  have hkernelIcc : ∀ᵐ omega ∂(mu.trim hm),
      ∀ᵐ y ∂(condExpKernel mu m omega), X y ∈ Icc a b := by
    apply Measure.ae_ae_of_ae_comp
    simpa only [condExpKernel_comp_trim hm] using hIcc
  refine ⟨?_, ?_⟩
  · intro t
    rw [condExpKernel_comp_trim hm]
    exact integrable_exp_mul_of_mem_Icc hX hIcc
  · filter_upwards [hkernelInt, hkernelIcc, hzero] with omega hInt hBound hMean
    intro t
    exact (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      hInt.aemeasurable hBound hMean).mgf_le t

/-- v3 Proposition 3.4, proof step (3), the form of conditional Hoeffding needed for
McDiarmid's Doob martingale.  The enclosing point `omega` may select an interval
`[lower omega, upper omega]`; only its width is uniformly bounded by `c`.

The exponential-integrability assumption is separate from the interval assertion because the
endpoints are allowed to be unbounded functions of the past.  For bounded-difference Doob
increments it follows from the usual pointwise bound, and it is not a concentration conclusion. -/
theorem hasCondSubgaussianMGF_of_kernel_mem_Icc_of_width_le
    (hm : m ≤ mOmega) {X : Omega → ℝ} {lower upper : Omega → ℝ} {c : ℝ≥0}
    (hExp : ∀ t : ℝ, Integrable (fun omega ↦ exp (t * X omega)) mu)
    (hIcc : ∀ᵐ omega ∂(mu.trim hm), ∀ᵐ y ∂(condExpKernel mu m omega),
      X y ∈ Icc (lower omega) (upper omega))
    (hwidth : ∀ᵐ omega ∂(mu.trim hm),
      ‖upper omega - lower omega‖₊ ≤ c)
    (hzero : ∀ᵐ omega ∂(mu.trim hm),
      ∫ y, X y ∂(condExpKernel mu m omega) = 0) :
    HasCondSubgaussianMGF m hm X ((c / 2) ^ 2) mu := by
  have hkernelExp : ∀ᵐ omega ∂(mu.trim hm),
      Integrable (fun y ↦ exp (X y)) (condExpKernel mu m omega) := by
    apply Measure.ae_integrable_of_integrable_comp
    rw [condExpKernel_comp_trim hm]
    simpa using hExp 1
  refine ⟨?_, ?_⟩
  · intro t
    rw [condExpKernel_comp_trim hm]
    exact hExp t
  · filter_upwards [hkernelExp, hIcc, hwidth, hzero] with omega hInt hBound hWidth hMean
    intro t
    have hMeas : AEMeasurable X (condExpKernel mu m omega) :=
      aemeasurable_of_aemeasurable_exp hInt.aemeasurable
    have hSmall := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      hMeas hBound hMean
    calc
      mgf X (condExpKernel mu m omega) t
          ≤ exp (((‖upper omega - lower omega‖₊ / 2) ^ 2 : ℝ) * t ^ 2 / 2) :=
        hSmall.mgf_le t
      _ ≤ exp ((((c / 2) ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2) := by
        apply exp_le_exp.mpr
        gcongr
        have hProxy : (‖upper omega - lower omega‖₊ / 2) ^ 2 ≤ (c / 2) ^ 2 := by
          gcongr
        exact_mod_cast hProxy

end ConditionalHoeffding

section OneCoordinate

variable {Omega : Type*} [MeasurableSpace Omega]
  {mu : Measure Omega} [IsProbabilityMeasure mu]

/-- v3 Proposition 3.4, proof step (3), the one-coordinate McDiarmid inequality.

For an arbitrary random input and an observable with essential oscillation at most `b-a`, this
gives the sharp bounded-differences exponent `exp (-2 t²/(b-a)²)`.  This is already a genuine
McDiarmid statement (the product has one coordinate), proved without an external probability
interface. -/
theorem mcdiarmid_one_coordinate
    {F : Omega → ℝ} {a b t : ℝ}
    (hF : AEMeasurable F mu) (hIcc : ∀ᵐ omega ∂mu, F omega ∈ Icc a b)
    (ht : 0 ≤ t) :
    mu.real {omega | t ≤ F omega - ∫ x, F x ∂mu}
      ≤ exp (-t ^ 2 / (2 * ((‖b - a‖₊ / 2) ^ 2 : ℝ))) := by
  exact (hasSubgaussianMGF_of_mem_Icc hF hIcc).measure_ge_le ht

end OneCoordinate

section BoundedMartingaleDifferences

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}
  [StandardBorelSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
  {ℱ : Filtration ℕ mOmega}

/-- Data needed after the model-specific Doob-martingale construction in v3 Proposition 3.4,
proof step (3).  The fields contain only measurability, centering, interval-width, and telescoping
facts; in particular, no tail estimate is assumed.

`Y 0` is allowed to be the deterministic zero increment.  For `i+1`, the endpoints may depend on
the already exposed coordinates (they are functions on the sample space); their difference is
bounded by `c i`. -/
structure BoundedDoobDifferences (F : Omega → ℝ) (N : ℕ) (c : ℕ → ℝ≥0) where
  Y : ℕ → Omega → ℝ
  stronglyAdapted : StronglyAdapted ℱ Y
  zero : Y 0 = fun _ ↦ 0
  telescopes : (∀ᵐ omega ∂mu,
    F omega - ∫ x, F x ∂mu = ∑ i ∈ Finset.range (N + 1), Y i omega)
  lower : ℕ → Omega → ℝ
  upper : ℕ → Omega → ℝ
  increment_kernel_mem_Icc : ∀ i < N, ∀ᵐ omega ∂(mu.trim (ℱ.le i)),
    ∀ᵐ y ∂(condExpKernel mu (ℱ i) omega),
      Y (i + 1) y ∈ Icc (lower i omega) (upper i omega)
  width_le : ∀ i < N, ∀ᵐ omega ∂(mu.trim (ℱ.le i)),
    ‖upper i omega - lower i omega‖₊ ≤ c i
  increment_abs_le : ∀ i < N, ∀ᵐ omega ∂mu, |Y (i + 1) omega| ≤ (c i : ℝ)
  condKernelCentered : ∀ i < N, ∀ᵐ omega ∂(mu.trim (ℱ.le i)),
    ∫ y, Y (i + 1) y ∂(condExpKernel mu (ℱ i) omega) = 0

/-- The sub-Gaussian proxy sequence for a Doob decomposition with a zero sentinel increment.
This indexing matches mathlib's Azuma theorem. -/
noncomputable def doobSubgaussianProxy (c : ℕ → ℝ≥0) : ℕ → ℝ≥0
  | 0 => 0
  | i + 1 => (c i / 2) ^ 2

@[simp] theorem doobSubgaussianProxy_zero (c : ℕ → ℝ≥0) :
    doobSubgaussianProxy c 0 = 0 := rfl

@[simp] theorem doobSubgaussianProxy_succ (c : ℕ → ℝ≥0) (i : ℕ) :
    doobSubgaussianProxy c (i + 1) = (c i / 2) ^ 2 := rfl

/-- v3 Proposition 3.4, proof step (3): the proxy sum for the zero-sentinel Doob indexing is
exactly the sum of the coordinate Hoeffding proxies. -/
theorem sum_doobSubgaussianProxy (c : ℕ → ℝ≥0) (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), doobSubgaussianProxy c i =
      ∑ i ∈ Finset.range N, (c i / 2) ^ 2 := by
  rw [Finset.sum_range_succ']
  simp

/-- v3 Proposition 3.4, proof step (3): conditional interval bounds for every Doob increment
imply the sharp McDiarmid tail bound.  This theorem proves the entire probability-theoretic core;
the remaining model-specific work is to construct `BoundedDoobDifferences` from the resolvent
trace's coordinatewise rank estimate. -/
theorem mcdiarmid_of_boundedDoobDifferences
    {F : Omega → ℝ} {N : ℕ} {c : ℕ → ℝ≥0}
    (h : BoundedDoobDifferences (ℱ := ℱ) (mu := mu) F N c) {t : ℝ} (ht : 0 ≤ t) :
    mu.real {omega | t ≤ F omega - ∫ x, F x ∂mu}
      ≤ exp (-t ^ 2 /
        (2 * (((∑ i ∈ Finset.range N, (c i / 2) ^ 2 : ℝ≥0)) : ℝ))) := by
  have hSubG : ∀ i < N,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (h.Y (i + 1)) ((c i / 2) ^ 2) mu := by
    intro i hi
    have hMeas : AEMeasurable (h.Y (i + 1)) mu :=
      ((h.stronglyAdapted (i + 1)).mono (ℱ.le (i + 1))).aemeasurable
    have hGlobalIcc : ∀ᵐ omega ∂mu,
        h.Y (i + 1) omega ∈ Icc (-(c i : ℝ)) (c i : ℝ) := by
      filter_upwards [h.increment_abs_le i hi] with omega hAbs
      exact (abs_le.mp hAbs)
    have hExp : ∀ t : ℝ, Integrable (fun omega ↦ exp (t * h.Y (i + 1) omega)) mu :=
      fun _ ↦ integrable_exp_mul_of_mem_Icc hMeas hGlobalIcc
    exact hasCondSubgaussianMGF_of_kernel_mem_Icc_of_width_le
      (ℱ.le i) hExp
      (h.increment_kernel_mem_Icc i hi) (h.width_le i hi) (h.condKernelCentered i hi)
  have hZero : HasSubgaussianMGF (h.Y 0) (doobSubgaussianProxy c 0) mu := by
    rw [h.zero]
    simp
  have hAzuma := measure_sum_ge_le_of_hasCondSubgaussianMGF
    (cY := doobSubgaussianProxy c) h.stronglyAdapted hZero (N + 1)
    (by simpa using hSubG) ht
  rw [sum_doobSubgaussianProxy] at hAzuma
  have hMeasureENN :
      mu {omega | t ≤ F omega - ∫ x, F x ∂mu} =
        mu {omega | t ≤ ∑ i ∈ Finset.range (N + 1), h.Y i omega} := by
    apply measure_congr
    filter_upwards [h.telescopes] with omega hTel
    change (t ≤ F omega - ∫ x, F x ∂mu) =
      (t ≤ ∑ i ∈ Finset.range (N + 1), h.Y i omega)
    rw [hTel]
  have hMeasure :
      mu.real {omega | t ≤ F omega - ∫ x, F x ∂mu} =
        mu.real {omega | t ≤ ∑ i ∈ Finset.range (N + 1), h.Y i omega} := by
    simpa only [measureReal_def] using congrArg ENNReal.toReal hMeasureENN
  rw [hMeasure]
  exact hAzuma

/-- Negating a bounded Doob decomposition preserves all its bounds.  This is the symmetry step
used to obtain the lower tail in v3 Proposition 3.4, proof step (3). -/
protected noncomputable def BoundedDoobDifferences.neg
    {F : Omega → ℝ} {N : ℕ} {c : ℕ → ℝ≥0}
    (h : BoundedDoobDifferences (ℱ := ℱ) (mu := mu) F N c) :
    BoundedDoobDifferences (ℱ := ℱ) (mu := mu) (fun omega ↦ -F omega) N c := by
  refine
    { Y := fun i omega ↦ -h.Y i omega
      stronglyAdapted := fun i ↦ (h.stronglyAdapted i).neg
      zero := ?_
      telescopes := ?_
      lower := fun i omega ↦ -h.upper i omega
      upper := fun i omega ↦ -h.lower i omega
      increment_kernel_mem_Icc := ?_
      width_le := ?_
      increment_abs_le := ?_
      condKernelCentered := ?_ }
  · simp only [h.zero, neg_zero]
  · filter_upwards [h.telescopes] with omega hTel
    calc
      -F omega - ∫ x, -F x ∂mu = -(F omega - ∫ x, F x ∂mu) := by
        rw [integral_neg]
        ring
      _ = -(∑ i ∈ Finset.range (N + 1), h.Y i omega) := by rw [hTel]
      _ = ∑ i ∈ Finset.range (N + 1), -h.Y i omega := by
        rw [Finset.sum_neg_distrib]
  · intro i hi
    filter_upwards [h.increment_kernel_mem_Icc i hi] with omega hOmega
    filter_upwards [hOmega] with y hy
    exact ⟨neg_le_neg hy.2, neg_le_neg hy.1⟩
  · intro i hi
    filter_upwards [h.width_le i hi] with omega hWidth
    simpa only [neg_sub_neg] using hWidth
  · intro i hi
    filter_upwards [h.increment_abs_le i hi] with omega hAbs
    simpa only [abs_neg] using hAbs
  · intro i hi
    filter_upwards [h.condKernelCentered i hi] with omega hMean
    rw [integral_neg, hMean, neg_zero]

/-- v3 Proposition 3.4, proof step (3): the matching lower-tail McDiarmid estimate. -/
theorem mcdiarmid_lower_of_boundedDoobDifferences
    {F : Omega → ℝ} {N : ℕ} {c : ℕ → ℝ≥0}
    (h : BoundedDoobDifferences (ℱ := ℱ) (mu := mu) F N c) {t : ℝ} (ht : 0 ≤ t) :
    mu.real {omega | t ≤ (∫ x, F x ∂mu) - F omega}
      ≤ exp (-t ^ 2 /
        (2 * (((∑ i ∈ Finset.range N, (c i / 2) ^ 2 : ℝ≥0)) : ℝ))) := by
  have hNeg := mcdiarmid_of_boundedDoobDifferences (h.neg) ht
  simpa only [integral_neg, sub_eq_add_neg, neg_neg, add_comm] using hNeg

/-- v3 Proposition 3.4, proof step (3): the two-sided scalar McDiarmid estimate obtained by
combining the upper and lower tails. -/
theorem mcdiarmid_two_sided_of_boundedDoobDifferences
    {F : Omega → ℝ} {N : ℕ} {c : ℕ → ℝ≥0}
    (h : BoundedDoobDifferences (ℱ := ℱ) (mu := mu) F N c) {t : ℝ} (ht : 0 ≤ t) :
    mu.real {omega | t ≤ |F omega - ∫ x, F x ∂mu|}
      ≤ 2 * exp (-t ^ 2 /
        (2 * (((∑ i ∈ Finset.range N, (c i / 2) ^ 2 : ℝ≥0)) : ℝ))) := by
  let R : ℝ := exp (-t ^ 2 /
    (2 * (((∑ i ∈ Finset.range N, (c i / 2) ^ 2 : ℝ≥0)) : ℝ)))
  have hUpper : mu.real {omega | t ≤ F omega - ∫ x, F x ∂mu} ≤ R :=
    mcdiarmid_of_boundedDoobDifferences h ht
  have hLower : mu.real {omega | t ≤ (∫ x, F x ∂mu) - F omega} ≤ R :=
    mcdiarmid_lower_of_boundedDoobDifferences h ht
  have hSet :
      {omega | t ≤ |F omega - ∫ x, F x ∂mu|} =
        {omega | t ≤ F omega - ∫ x, F x ∂mu} ∪
          {omega | t ≤ (∫ x, F x ∂mu) - F omega} := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    let D : ℝ := F omega - ∫ x, F x ∂mu
    have hD : D = F omega - ∫ x, F x ∂mu := rfl
    have hNegD : -D = (∫ x, F x ∂mu) - F omega := by
      rw [hD]
      ring
    rw [← hD, ← hNegD]
    constructor
    · intro hAbs
      by_cases hD : 0 ≤ D
      · exact Or.inl (by simpa [abs_of_nonneg hD] using hAbs)
      · exact Or.inr (by simpa [abs_of_nonpos (le_of_not_ge hD)] using hAbs)
    · rintro (hPos | hNeg)
      · exact hPos.trans (le_abs_self D)
      · exact hNeg.trans (neg_le_abs D)
  rw [hSet]
  calc
    mu.real ({omega | t ≤ F omega - ∫ x, F x ∂mu} ∪
        {omega | t ≤ (∫ x, F x ∂mu) - F omega})
        ≤ mu.real {omega | t ≤ F omega - ∫ x, F x ∂mu} +
          mu.real {omega | t ≤ (∫ x, F x ∂mu) - F omega} :=
      measureReal_union_le _ _
    _ ≤ R + R := add_le_add hUpper hLower
    _ = 2 * R := by ring

end BoundedMartingaleDifferences

end Arxiv2410V3

