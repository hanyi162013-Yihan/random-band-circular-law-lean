/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/DoobBridge.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.McDiarmid

/-!
# Mechanical bridge from a Doob martingale to bounded differences

This file isolates the genuinely model-specific input in v3 Proposition 3.4, proof step (3).
The input below contains a martingale, its two endpoint identifications, and conditional interval
bounds for its successive differences.  It contains no centering, telescoping, absolute-increment,
or concentration conclusion: those facts are derived here.
-/

namespace Arxiv2410V3

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}
  [StandardBorelSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
  {filtration : Filtration ℕ mOmega}

/-- v3 Proposition 3.4, proof step (3): the light, model-specific certificate needed after
constructing the Doob martingale.  In particular, conditional centering of increments and their
global absolute bounds are deliberately not fields of this structure. -/
structure DoobIntervalCertificate (F : Omega → ℝ) (N : ℕ) (c : ℕ → ℝ≥0) where
  M : ℕ → Omega → ℝ
  martingale : Martingale M filtration mu
  initial : M 0 =ᵐ[mu] fun _ ↦ ∫ x, F x ∂mu
  terminal : M N =ᵐ[mu] F
  lower : ℕ → Omega → ℝ
  upper : ℕ → Omega → ℝ
  increment_kernel_mem_Icc : ∀ i < N, ∀ᵐ omega ∂(mu.trim (filtration.le i)),
    ∀ᵐ y ∂(condExpKernel mu (filtration i) omega),
      M (i + 1) y - M i y ∈ Icc (lower i omega) (upper i omega)
  width_le : ∀ i < N, ∀ᵐ omega ∂(mu.trim (filtration.le i)),
    ‖upper i omega - lower i omega‖₊ ≤ c i

/-- v3 Proposition 3.4, proof step (3): the zero-sentinel increment process associated with a
Doob martingale. -/
def DoobIntervalCertificate.increment
    {F : Omega → ℝ} {N : ℕ} {c : ℕ → ℝ≥0}
    (h : DoobIntervalCertificate (filtration := filtration) (mu := mu) F N c) :
    ℕ → Omega → ℝ
  | 0 => fun _ ↦ 0
  | i + 1 => fun omega ↦ h.M (i + 1) omega - h.M i omega

@[simp] theorem DoobIntervalCertificate.increment_zero
    {F : Omega → ℝ} {N : ℕ} {c : ℕ → ℝ≥0}
    (h : DoobIntervalCertificate (filtration := filtration) (mu := mu) F N c) :
    h.increment 0 = fun _ ↦ 0 := rfl

@[simp] theorem DoobIntervalCertificate.increment_succ
    {F : Omega → ℝ} {N : ℕ} {c : ℕ → ℝ≥0}
    (h : DoobIntervalCertificate (filtration := filtration) (mu := mu) F N c) (i : ℕ) :
    h.increment (i + 1) = fun omega ↦ h.M (i + 1) omega - h.M i omega := rfl

omit [StandardBorelSpace Omega] in
/-- A centered random variable supported by an interval is bounded in absolute value by the
interval's width.  This elementary lemma is what makes the separate absolute-increment field of
`BoundedDoobDifferences` redundant. -/
theorem abs_le_nnnorm_sub_of_mem_Icc_of_integral_eq_zero
    {nu : Measure Omega} [IsProbabilityMeasure nu] {X : Omega → ℝ} {a b : ℝ}
    (hX : Integrable X nu) (hIcc : ∀ᵐ omega ∂nu, X omega ∈ Icc a b)
    (hzero : ∫ omega, X omega ∂nu = 0) :
    ∀ᵐ omega ∂nu, |X omega| ≤ (‖b - a‖₊ : ℝ) := by
  have ha : a ≤ 0 := by
    calc
      a = ∫ _ : Omega, a ∂nu := by simp
      _ ≤ ∫ omega, X omega ∂nu :=
        integral_mono_ae (integrable_const a) hX (hIcc.mono fun _ h ↦ h.1)
      _ = 0 := hzero
  have hb : 0 ≤ b := by
    calc
      0 = ∫ omega, X omega ∂nu := hzero.symm
      _ ≤ ∫ _ : Omega, b ∂nu :=
        integral_mono_ae hX (integrable_const b) (hIcc.mono fun _ h ↦ h.2)
      _ = b := by simp
  have hba : 0 ≤ b - a := sub_nonneg.mpr (ha.trans hb)
  filter_upwards [hIcc] with omega homega
  rw [show (‖b - a‖₊ : ℝ) = b - a by
    simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hba]]
  rw [abs_le]
  constructor <;> linarith [homega.1, homega.2]

/-- v3 Proposition 3.4, proof step (3): successive differences of an adapted martingale, with a
zero sentinel at index zero, are strongly adapted. -/
theorem DoobIntervalCertificate.stronglyAdapted_increment
    {F : Omega → ℝ} {N : ℕ} {c : ℕ → ℝ≥0}
    (h : DoobIntervalCertificate (filtration := filtration) (mu := mu) F N c) :
    StronglyAdapted filtration h.increment := by
  intro i
  cases i with
  | zero => exact stronglyMeasurable_const
  | succ i =>
      exact (h.martingale.stronglyMeasurable (i + 1)).sub
        (h.martingale.stronglyAdapted.stronglyMeasurable_le i.le_succ)

/-- v3 Proposition 3.4, proof step (3): martingale differences have conditional-kernel mean zero.
This is derived from the martingale identity, rather than requested in the certificate. -/
theorem DoobIntervalCertificate.increment_condKernelCentered
    {F : Omega → ℝ} {N : ℕ} {c : ℕ → ℝ≥0}
    (h : DoobIntervalCertificate (filtration := filtration) (mu := mu) F N c) (i : ℕ) :
    ∀ᵐ omega ∂(mu.trim (filtration.le i)),
      ∫ y, h.increment (i + 1) y ∂(condExpKernel mu (filtration i) omega) = 0 := by
  have hInt : Integrable (h.increment (i + 1)) mu := by
    change Integrable (h.M (i + 1) - h.M i) mu
    exact (h.martingale.integrable (i + 1)).sub (h.martingale.integrable i)
  have hCondMu :
      mu[h.increment (i + 1) | filtration i] =ᵐ[mu] (0 : Omega → ℝ) := by
    change mu[h.M (i + 1) - h.M i | filtration i] =ᵐ[mu] (0 : Omega → ℝ)
    calc
      mu[h.M (i + 1) - h.M i | filtration i] =ᵐ[mu]
          mu[h.M (i + 1) | filtration i] - mu[h.M i | filtration i] := by
            exact condExp_sub (h.martingale.integrable (i + 1))
              (h.martingale.integrable i) (filtration i)
      _ =ᵐ[mu] h.M i - h.M i :=
        (h.martingale.condExp_ae_eq i.le_succ).sub
          (h.martingale.condExp_ae_eq le_rfl)
      _ =ᵐ[mu] 0 := by simp
  have hCondTrim :
      mu[h.increment (i + 1) | filtration i] =ᵐ[mu.trim (filtration.le i)]
        (0 : Omega → ℝ) :=
    stronglyMeasurable_condExp.ae_eq_trim_of_stronglyMeasurable
      (filtration.le i) stronglyMeasurable_zero hCondMu
  have hKernel := condExp_ae_eq_trim_integral_condExpKernel
    (filtration.le i) hInt
  exact hKernel.symm.trans hCondTrim

/-- v3 Proposition 3.4, proof step (3): the endpoint identifications turn the sum of successive
martingale differences into `F - ℙ F`. -/
theorem DoobIntervalCertificate.increment_telescopes
    {F : Omega → ℝ} {N : ℕ} {c : ℕ → ℝ≥0}
    (h : DoobIntervalCertificate (filtration := filtration) (mu := mu) F N c) :
    ∀ᵐ omega ∂mu,
      F omega - ∫ x, F x ∂mu = ∑ i ∈ Finset.range (N + 1), h.increment i omega := by
  filter_upwards [h.initial, h.terminal] with omega hInitial hTerminal
  rw [Finset.sum_range_succ']
  simp only [h.increment_zero, h.increment_succ, add_zero]
  calc
    F omega - ∫ x, F x ∂mu = h.M N omega - h.M 0 omega := by rw [hInitial, hTerminal]
    _ = ∑ k ∈ Finset.range N, (h.M (k + 1) omega - h.M k omega) :=
      (Finset.sum_range_sub (fun k ↦ h.M k omega) N).symm

/-- v3 Proposition 3.4, proof step (3): conditional interval support, zero conditional mean, and
width `c i` imply the global absolute bound on the corresponding Doob increment. -/
theorem DoobIntervalCertificate.increment_abs_le
    {F : Omega → ℝ} {N : ℕ} {c : ℕ → ℝ≥0}
    (h : DoobIntervalCertificate (filtration := filtration) (mu := mu) F N c)
    (i : ℕ) (hi : i < N) :
    ∀ᵐ omega ∂mu, |h.increment (i + 1) omega| ≤ (c i : ℝ) := by
  have hInt : Integrable (h.increment (i + 1)) mu := by
    change Integrable (h.M (i + 1) - h.M i) mu
    exact (h.martingale.integrable (i + 1)).sub (h.martingale.integrable i)
  have hKernelInt : ∀ᵐ omega ∂(mu.trim (filtration.le i)),
      Integrable (h.increment (i + 1)) (condExpKernel mu (filtration i) omega) := by
    apply Measure.ae_integrable_of_integrable_comp
    simpa only [condExpKernel_comp_trim (filtration.le i)] using hInt
  have hNested : ∀ᵐ omega ∂(mu.trim (filtration.le i)),
      ∀ᵐ y ∂(condExpKernel mu (filtration i) omega),
        |h.increment (i + 1) y| ≤ (c i : ℝ) := by
    filter_upwards [hKernelInt, h.increment_kernel_mem_Icc i hi, h.width_le i hi,
      h.increment_condKernelCentered i] with omega hIntOmega hIcc hWidth hCentered
    have hAbs := abs_le_nnnorm_sub_of_mem_Icc_of_integral_eq_zero
      hIntOmega hIcc hCentered
    filter_upwards [hAbs] with y hy
    exact hy.trans (by exact_mod_cast hWidth)
  have hMeas : MeasurableSet
      {omega | |h.increment (i + 1) omega| ≤ (c i : ℝ)} := by
    apply measurableSet_le
    · simpa only [Real.norm_eq_abs] using
        ((h.stronglyAdapted_increment (i + 1)).mono (filtration.le (i + 1))).norm.measurable
    · exact measurable_const
  have hComp := Measure.ae_comp_of_ae_ae hMeas hNested
  simpa only [condExpKernel_comp_trim (filtration.le i)] using hComp

/-- v3 Proposition 3.4, proof step (3): the light Doob interval certificate mechanically
constructs the complete bounded-differences witness consumed by the proved McDiarmid theorem. -/
noncomputable def DoobIntervalCertificate.toBoundedDoobDifferences
    {F : Omega → ℝ} {N : ℕ} {c : ℕ → ℝ≥0}
    (h : DoobIntervalCertificate (filtration := filtration) (mu := mu) F N c) :
    BoundedDoobDifferences (ℱ := filtration) (mu := mu) F N c where
  Y := h.increment
  stronglyAdapted := h.stronglyAdapted_increment
  zero := h.increment_zero
  telescopes := h.increment_telescopes
  lower := h.lower
  upper := h.upper
  increment_kernel_mem_Icc := by
    intro i hi
    simpa only [h.increment_succ] using h.increment_kernel_mem_Icc i hi
  width_le := h.width_le
  increment_abs_le := h.increment_abs_le
  condKernelCentered := by
    intro i _
    exact h.increment_condKernelCentered i

end Arxiv2410V3

