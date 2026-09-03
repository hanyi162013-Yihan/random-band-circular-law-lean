import BernoulliSection10Complex.MultiAffine

/-!
# Public planar-density analytic statements

These entry points accept the original planar model, not an internally
normalized density bound. The full complex coefficient tensor is used.
-/

open scoped ENNReal NNReal Topology BigOperators
open Set MeasureTheory

noncomputable section

namespace BernoulliSection10Complex

def planarAffineLogConstant (L : ℝ) : ℝ := lemma10_2Constant (max 1 L)

/-- Lemma 10.2, coefficient-scale assertion for actual planar IID atoms. -/
theorem planar_lemma_10_2_rho
    {μ : Measure ℂ} {L : ℝ} (hμ : IsPlanarDensityAtom μ L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : ℕ} (hp : 0 < p) (v₀ : E) (v : Fin p → E)
    (hρ : 0 < affineRho v₀ v) :
    ∫⁻ x, ENNReal.ofReal
        (|Real.log ‖affineValue v₀ v x‖ - Real.log (affineRho v₀ v)| ^ 2)
        ∂(Measure.pi fun _ : Fin p => μ) ≤
      ENNReal.ofReal
        (planarAffineLogConstant L * Real.log (Real.exp 1 * (p : ℝ)) ^ 2) := by
  have hG : v₀ ≠ 0 ∨ v ≠ 0 := by
    by_contra! h
    simp [h.1, h.2, affineRho] at hρ
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  simpa [planarAffineLogConstant, Nat.succ_eq_add_one] using
    lemma_10_2_rho_lintegral_le hμ.normalized v₀ v hG

/-- Lemma 10.2, independent-resampling assertion, with its integrability
proved internally. All scalar samples here take values in `ℂ`. -/
theorem planar_lemma_10_2_resampling
    {μ : Measure ℂ} {L : ℝ} (hμ : IsPlanarDensityAtom μ L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : ℕ} (hp : 0 < p) (v₀ : E) (v : Fin p → E) :
    Integrable
      (fun z : (Fin p → ℂ) × (Fin p → ℂ) =>
        |Real.log ‖affineValue v₀ v z.1‖ - Real.log ‖affineValue v₀ v z.2‖| ^ 2)
      ((Measure.pi fun _ : Fin p => μ).prod (Measure.pi fun _ : Fin p => μ)) ∧
    ∫ x, ∫ x',
        |Real.log ‖affineValue v₀ v x‖ - Real.log ‖affineValue v₀ v x'‖| ^ 2
        ∂(Measure.pi fun _ : Fin p => μ)
        ∂(Measure.pi fun _ : Fin p => μ) ≤
      planarAffineLogConstant L * Real.log (Real.exp 1 * (p : ℝ)) ^ 2 :=
  ⟨lemma_10_2_resampling_integrable_of_pos hμ.normalized hp v₀ v,
    lemma_10_2_resampling_integral_le_of_pos hμ.normalized hp v₀ v⟩

/-- The nonzero affine function does not vanish on a positive-mass set. -/
theorem planar_affine_ne_zero_ae
    {μ : Measure ℂ} {L : ℝ} (hμ : IsPlanarDensityAtom μ L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : ℕ} (hp : 0 < p) (v₀ : E) (v : Fin p → E)
    (hG : v₀ ≠ 0 ∨ v ≠ 0) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin p => μ), affineValue v₀ v x ≠ 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  exact lemma_10_2_affineValue_ne_zero_ae hμ.normalized v₀ v hG

/-- Corollary 10.3: the whole complex coefficient tensor is constructed
from the function itself; no tensor or nonvanishing certificate is an input. -/
theorem planar_corollary_10_3
    {μ : Measure ℂ} {L : ℝ} (hμ : IsPlanarDensityAtom μ L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ps : List ℕ} {F : MultiAffineRows ps → E} (hF : IsMultiAffine F)
    (hpos : ∀ p ∈ ps, 0 < p) (hFne : F ≠ 0) :
    (∫⁻ x, ENNReal.ofReal
        |Real.log ‖F x‖ - Real.log ‖multiAffineTensorOfFunction F‖|
        ∂(multiAffineRowLaw μ ps) ≤ multiAffineLogCost (max 1 L) ps) ∧
      ∀ᵐ x ∂multiAffineRowLaw μ ps, F x ≠ 0 :=
  corollary_10_3 hμ.normalized hF hpos hFne

end BernoulliSection10Complex
