import CircularLawSection4.DirectionalVectorLaw
import CircularLawSection4.RealInputComplexOperatorAffine

/-!
# Operator-affine estimates under directional conditional products

The conditional directional coordinates are independent but not generally
identically distributed.  This file lifts the selected-coordinate
operator-affine argument to an arbitrary finite product of such laws, then
specializes it to the kernel constructed from the manuscript's atom law.
-/

open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory
open MeasureTheory Set ProbabilityTheory

noncomputable section

namespace CircularLawSection4

universe w x

/-- Reconstruct a complex atom from its orthogonal coordinate `v` and
directional coordinate `u`. -/
def reconstructedDirectionalAtom (phase : ℝ) (v u : ℝ) : ℂ :=
  Complex.exp ((phase : ℂ) * Complex.I) *
    ((u : ℂ) + Complex.I * (v : ℂ))

/-- The operator-affine expression evaluated at the reconstructed complex
row atoms. -/
def reconstructedDirectionalOperatorAffine {n : ℕ}
    (phase : ℝ) (b : Fin n → ℂ) (v u : Fin n → ℝ)
    {E : Type w} {F : Type x}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (M : Fin n → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F) :
    E →L[ℂ] F :=
  operatorAffine b (fun i => reconstructedDirectionalAtom phase (v i) (u i))
    M z M₀

/-- Coefficients of the real directional variables after undoing the fixed
phase rotation. -/
def reconstructedDirectionalWeight {n : ℕ} (phase : ℝ)
    (b : Fin n → ℂ) : Fin n → ℂ :=
  fun i => b i * Complex.exp ((phase : ℂ) * Complex.I)

/-- The part of the reconstructed operator-affine expression frozen by the
orthogonal vector. -/
def reconstructedDirectionalCenter {n : ℕ}
    (phase : ℝ) (b : Fin n → ℂ) (v : Fin n → ℝ)
    {E : Type w} {F : Type x}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (M : Fin n → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F) :
    E →L[ℂ] F :=
  (∑ i, (reconstructedDirectionalWeight phase b i *
      (Complex.I * (v i : ℂ))) • M i) - z • M₀

/-- After the orthogonal coordinates are frozen, the actual reconstructed
complex-row expression is precisely a real-input complex operator-affine
expression with a modified deterministic center. -/
theorem reconstructedDirectionalOperatorAffine_eq_realInput
    {n : ℕ} (phase : ℝ) (b : Fin n → ℂ) (v u : Fin n → ℝ)
    {E : Type w} {F : Type x}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (M : Fin n → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F) :
    reconstructedDirectionalOperatorAffine phase b v u M z M₀ =
      realInputComplexOperatorAffine (reconstructedDirectionalWeight phase b)
        u M 1 (-(reconstructedDirectionalCenter phase b v M z M₀)) := by
  unfold reconstructedDirectionalOperatorAffine reconstructedDirectionalAtom
    reconstructedDirectionalWeight reconstructedDirectionalCenter
    realInputComplexOperatorAffine operatorAffine
  simp only [mul_add, mul_assoc, add_smul, Finset.sum_add_distrib,
    one_smul, sub_neg_eq_add]
  simp only [reconstructedDirectionalWeight, mul_assoc]
  abel

/-- Fubini lifting of a selected-real-coordinate operator-affine estimate to
a heterogeneous finite product. -/
theorem pi_realInputComplexOperatorAffine_smallBall_of_oneCoordinate
    {n : ℕ} (μ : Fin (n + 1) → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] [∀ i, IsProbabilityMeasure (μ i)]
    {E : Type w} {F : Type x}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (s : Fin (n + 1)) (b : Fin (n + 1) → ℂ)
    (M : Fin (n + 1) → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F)
    {ε ρ : ℝ} {C : ℝ≥0∞}
    (hone : ∀ R : E →L[ℂ] F,
      μ s {u : ℝ | ‖R + (b s * (u : ℂ)) • M s‖ ≤ ε * ρ} ≤ C) :
    Measure.pi μ
        {ξ | ‖realInputComplexOperatorAffine b ξ M z M₀‖ ≤ ε * ρ} ≤ C := by
  let good : Set (Fin (n + 1) → ℝ) :=
    {ξ | ‖realInputComplexOperatorAffine b ξ M z M₀‖ ≤ ε * ρ}
  have hgood : MeasurableSet good := by
    simpa only [good] using
      measurableSet_realInputComplexOperatorAffine_norm_le b M z M₀ (ε * ρ)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) s
  have hpres : MeasurePreserving e (Measure.pi μ)
      ((μ s).prod (Measure.pi (fun j : Fin n => μ (s.succAbove j)))) := by
    simpa only [e] using measurePreserving_piFinSuccAbove μ s
  rw [← hpres.symm.map_eq, Measure.map_apply e.symm.measurable hgood,
    Measure.prod_apply_symm (hgood.preimage e.symm.measurable)]
  calc
    (∫⁻ y, μ s ((fun u => (u, y)) ⁻¹' (e.symm ⁻¹' good))
        ∂Measure.pi (fun j : Fin n => μ (s.succAbove j))) ≤
      ∫⁻ _y : Fin n → ℝ, C
        ∂Measure.pi (fun j : Fin n => μ (s.succAbove j)) := by
      apply lintegral_mono
      intro y
      let R : E →L[ℂ] F :=
        (∑ j : Fin n,
          (b (s.succAbove j) * (y j : ℂ)) • M (s.succAbove j)) - z • M₀
      have haffine (u : ℝ) :
          realInputComplexOperatorAffine b (s.insertNth u y) M z M₀ =
            R + (b s * (u : ℂ)) • M s := by
        rw [realInputComplexOperatorAffine, operatorAffine,
          s.sum_univ_succAbove]
        simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        dsimp only [R]
        abel
      have hsection :
          (fun u => (u, y)) ⁻¹' (e.symm ⁻¹' good) =
            {u : ℝ | ‖R + (b s * (u : ℂ)) • M s‖ ≤ ε * ρ} := by
        ext u
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, good, e,
          MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
        change
          ‖realInputComplexOperatorAffine b (s.insertNth u y) M z M₀‖ ≤
              ε * ρ ↔
            ‖R + (b s * (u : ℂ)) • M s‖ ≤ ε * ρ
        rw [haffine]
      change μ s ((fun u => (u, y)) ⁻¹' (e.symm ⁻¹' good)) ≤ C
      rw [hsection]
      exact hone R
    _ = C := by simp

/-- Selected-coordinate small-ball bound under a heterogeneous real product.
-/
theorem pi_realInputComplexOperatorAffine_arbitraryCoordinate_smallBall
    {n : ℕ} (μ : Fin (n + 1) → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] [∀ i, IsProbabilityMeasure (μ i)]
    {L : ℝ≥0∞} (hμ : ∀ i, RealIntervalBound (μ i) L)
    {E : Type w} {F : Type x}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (s : Fin (n + 1)) (b : Fin (n + 1) → ℂ)
    (M : Fin (n + 1) → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F)
    (x₀ : E) (ell : StrongDual ℂ F) (hx₀ : ‖x₀‖ ≤ 1)
    (hell : ‖ell‖ ≤ 1) {ε ρ : ℝ} (hρ : 0 ≤ ρ) (hε : 0 < ε)
    (hslope : ε ≤ ‖b s * ell (M s x₀)‖) :
    Measure.pi μ
        {ξ | ‖realInputComplexOperatorAffine b ξ M z M₀‖ ≤ ε * ρ} ≤
      (4 : ℝ≥0∞) * L * ENNReal.ofReal ρ := by
  apply pi_realInputComplexOperatorAffine_smallBall_of_oneCoordinate μ s b M z M₀
  intro R
  exact complex_operatorAffine_realInput_oneCoordinate_smallBall
    (hμ s) R (M s) (b s) x₀ ell hx₀ hell hρ hε hslope

/-- Fiberwise operator-affine small-ball bound for the corrected directional
conditional product. -/
theorem directionalProduct_fiber_operatorAffine_smallBall
    {n : ℕ} (D : DirectionalProductModel (n + 1))
    {L : ℝ≥0∞}
    (hinterval : ∀ v i,
      RealIntervalBound (D.coordinateLaw v i : Measure ℝ) L)
    (v : Fin (n + 1) → ℝ)
    {E : Type w} {F : Type x}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (s : Fin (n + 1)) (b : Fin (n + 1) → ℂ)
    (M : Fin (n + 1) → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F)
    (x₀ : E) (ell : StrongDual ℂ F) (hx₀ : ‖x₀‖ ≤ 1)
    (hell : ‖ell‖ ≤ 1) {ε ρ : ℝ} (hρ : 0 ≤ ρ) (hε : 0 < ε)
    (hslope : ε ≤ ‖b s * ell (M s x₀)‖) :
    D.conditionalULaw v
        {ξ | ‖realInputComplexOperatorAffine b ξ M z M₀‖ ≤ ε * ρ} ≤
      (4 : ℝ≥0∞) * L * ENNReal.ofReal ρ := by
  rw [D.conditionalULaw_eq_pi v]
  exact pi_realInputComplexOperatorAffine_arbitraryCoordinate_smallBall
    (fun i => (D.coordinateLaw v i : Measure ℝ))
    (fun i => hinterval v i) s b M z M₀ x₀ ell hx₀ hell hρ hε hslope

/-- Fiberwise zero-set removal and `L²` logarithmic-deficit estimate for a
complex operator-affine expression under the directional product kernel. -/
theorem directionalProduct_fiber_operatorAffine_logDeficit_L2
    {n : ℕ} (D : DirectionalProductModel (n + 1))
    {L : ℝ} (hL : 0 ≤ L)
    (hinterval : ∀ v i,
      RealIntervalBound (D.coordinateLaw v i : Measure ℝ) (ENNReal.ofReal L))
    (v : Fin (n + 1) → ℝ)
    {E : Type w} {F : Type x}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (s : Fin (n + 1)) (b : Fin (n + 1) → ℂ)
    (M : Fin (n + 1) → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F)
    (x₀ : E) (ell : StrongDual ℂ F) (hx₀ : ‖x₀‖ ≤ 1)
    (hell : ‖ell‖ ≤ 1) (scale theta : ℝ)
    (hscale : 0 < scale) (htheta : 0 < theta)
    (hslope : theta * scale ≤ ‖b s * ell (M s x₀)‖) :
    let radius : (Fin (n + 1) → ℝ) → ℝ := fun ξ =>
      ‖realInputComplexOperatorAffine b ξ M z M₀‖
    D.conditionalULaw v {ξ | radius ξ = 0} = 0 ∧
      MemLp (fun ξ => logDeficit scale (radius ξ)) 2
        (D.conditionalULaw v) ∧
      ∫ ξ, logDeficit scale (radius ξ) ^ 2 ∂D.conditionalULaw v ≤
        oneSidedLogSecondMomentBound ((4 * L) / theta) 1 := by
  let radius : (Fin (n + 1) → ℝ) → ℝ := fun ξ =>
    ‖realInputComplexOperatorAffine b ξ M z M₀‖
  have hradius : Measurable radius :=
    (continuous_realInputComplexOperatorAffine_fin b M z M₀).norm.measurable
  have hradius0 : ∀ ξ, 0 ≤ radius ξ := fun ξ => norm_nonneg _
  let _ := D.conditionalULaw_isMarkov
  let _ : IsProbabilityMeasure (D.conditionalULaw v) := by infer_instance
  apply zeroSet_memLp_two_and_integral_sq_logDeficit_of_threshold_linearSmallBall
    (D.conditionalULaw v) radius hradius hradius0
      scale theta (4 * L) hscale htheta (mul_nonneg (by norm_num) hL)
  intro ρ hρ
  calc
    D.conditionalULaw v {ξ | radius ξ ≤ theta * scale * ρ} ≤
        (4 : ℝ≥0∞) * ENNReal.ofReal L * ENNReal.ofReal ρ := by
      exact directionalProduct_fiber_operatorAffine_smallBall D hinterval v
        s b M z M₀ x₀ ell hx₀ hell hρ.le
          (mul_pos htheta hscale) hslope
    _ = ENNReal.ofReal ((4 * L) * ρ) := by
      rw [← ENNReal.ofReal_ofNat 4,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
        ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hL)]

/-- The `L²` logarithmic-deficit theorem for the actual complex row atoms
reconstructed from `(V,U)`.  Thus the operator-affine branch is attached to
the same rotated random vector identified in `DirectionalVectorLaw`. -/
theorem directionalProduct_fiber_reconstructedOperatorAffine_logDeficit_L2
    {n : ℕ} (D : DirectionalProductModel (n + 1))
    {L : ℝ} (hL : 0 ≤ L)
    (hinterval : ∀ v i,
      RealIntervalBound (D.coordinateLaw v i : Measure ℝ) (ENNReal.ofReal L))
    (phase : ℝ) (v : Fin (n + 1) → ℝ)
    {E : Type w} {F : Type x}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (s : Fin (n + 1)) (b : Fin (n + 1) → ℂ)
    (M : Fin (n + 1) → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F)
    (x₀ : E) (ell : StrongDual ℂ F) (hx₀ : ‖x₀‖ ≤ 1)
    (hell : ‖ell‖ ≤ 1) (scale theta : ℝ)
    (hscale : 0 < scale) (htheta : 0 < theta)
    (hslope : theta * scale ≤
      ‖reconstructedDirectionalWeight phase b s * ell (M s x₀)‖) :
    let radius : (Fin (n + 1) → ℝ) → ℝ := fun u =>
      ‖reconstructedDirectionalOperatorAffine phase b v u M z M₀‖
    D.conditionalULaw v {u | radius u = 0} = 0 ∧
      MemLp (fun u => logDeficit scale (radius u)) 2
        (D.conditionalULaw v) ∧
      ∫ u, logDeficit scale (radius u) ^ 2 ∂D.conditionalULaw v ≤
        oneSidedLogSecondMomentBound ((4 * L) / theta) 1 := by
  simpa only [reconstructedDirectionalOperatorAffine_eq_realInput] using
    directionalProduct_fiber_operatorAffine_logDeficit_L2 D hL hinterval v
      s (reconstructedDirectionalWeight phase b) M 1
      (-(reconstructedDirectionalCenter phase b v M z M₀))
      x₀ ell hx₀ hell scale theta hscale htheta hslope

/-- Raw manuscript directional-density specialization of the operator-affine
fiber theorem. -/
theorem paperDirectional_fiber_operatorAffine_logDeficit_L2
    {n : ℕ} (atom : ProbabilityMeasure ℂ) (phaseBound L : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phaseBound L)
    (hL : 0 ≤ L) (v : Fin (n + 1) → ℝ)
    {E : Type w} {F : Type x}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (s : Fin (n + 1)) (b : Fin (n + 1) → ℂ)
    (M : Fin (n + 1) → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F)
    (x₀ : E) (ell : StrongDual ℂ F) (hx₀ : ‖x₀‖ ≤ 1)
    (hell : ‖ell‖ ≤ 1) (scale theta : ℝ)
    (hscale : 0 < scale) (htheta : 0 < theta)
    (hslope : theta * scale ≤ ‖b s * ell (M s x₀)‖) :
    let D := paperDirectionalProductModel (n + 1) atom phaseBound L hdir
    let radius : (Fin (n + 1) → ℝ) → ℝ := fun ξ =>
      ‖realInputComplexOperatorAffine b ξ M z M₀‖
    D.conditionalULaw v {ξ | radius ξ = 0} = 0 ∧
      MemLp (fun ξ => logDeficit scale (radius ξ)) 2
        (D.conditionalULaw v) ∧
      ∫ ξ, logDeficit scale (radius ξ) ^ 2 ∂D.conditionalULaw v ≤
        oneSidedLogSecondMomentBound ((4 * L) / theta) 1 := by
  let D := paperDirectionalProductModel (n + 1) atom phaseBound L hdir
  exact directionalProduct_fiber_operatorAffine_logDeficit_L2
    D hL (paperDirectionalProductModel_intervalBound (n + 1)
      atom phaseBound L hdir) v s b M z M₀ x₀ ell hx₀ hell
      scale theta hscale htheta hslope

/-- Raw directional-density specialization for the reconstructed complex
operator-affine row itself. -/
theorem paperDirectional_fiber_reconstructedOperatorAffine_logDeficit_L2
    {n : ℕ} (atom : ProbabilityMeasure ℂ) (phase L : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L)
    (hL : 0 ≤ L) (v : Fin (n + 1) → ℝ)
    {E : Type w} {F : Type x}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (s : Fin (n + 1)) (b : Fin (n + 1) → ℂ)
    (M : Fin (n + 1) → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F)
    (x₀ : E) (ell : StrongDual ℂ F) (hx₀ : ‖x₀‖ ≤ 1)
    (hell : ‖ell‖ ≤ 1) (scale theta : ℝ)
    (hscale : 0 < scale) (htheta : 0 < theta)
    (hslope : theta * scale ≤
      ‖reconstructedDirectionalWeight phase b s * ell (M s x₀)‖) :
    let D := paperDirectionalProductModel (n + 1) atom phase L hdir
    let radius : (Fin (n + 1) → ℝ) → ℝ := fun u =>
      ‖reconstructedDirectionalOperatorAffine phase b v u M z M₀‖
    D.conditionalULaw v {u | radius u = 0} = 0 ∧
      MemLp (fun u => logDeficit scale (radius u)) 2
        (D.conditionalULaw v) ∧
      ∫ u, logDeficit scale (radius u) ^ 2 ∂D.conditionalULaw v ≤
        oneSidedLogSecondMomentBound ((4 * L) / theta) 1 := by
  let D := paperDirectionalProductModel (n + 1) atom phase L hdir
  exact directionalProduct_fiber_reconstructedOperatorAffine_logDeficit_L2
    D hL (paperDirectionalProductModel_intervalBound (n + 1)
      atom phase L hdir) phase v s b M z M₀ x₀ ell hx₀ hell
      scale theta hscale htheta hslope

end CircularLawSection4
