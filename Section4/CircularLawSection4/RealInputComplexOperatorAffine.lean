import CircularLawSection4.IIDOperatorAffineSmallBall
import CircularLawSection4.RealInputComplexMultiaffine
import CircularLawSection4.OperatorAffineNegativeL2

/-!
# Complex operator-affine expressions with real IID inputs

For the real-atom branch of the manuscript, the transfer operators and the
spectral parameter are complex, while each fresh random coordinate is real.
This module inserts real coordinates through `Complex.ofReal`, proves the
one-coordinate projection bound with constant `4 L ρ`, and lifts it through
an arbitrary coordinate of the finite IID product.

The final result combines this small-ball estimate with the threshold-scale
negative-log closure, producing the `L²` logarithmic-deficit input needed by
the paper's real branch.
-/

open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory Set

noncomputable section

namespace CircularLawSection4

universe u w x

/-- Evaluate a complex operator-affine expression on real scalar
coordinates. -/
def realInputComplexOperatorAffine {n : ℕ}
    (b : Fin n → ℂ) (ξ : Fin n → ℝ)
    {E : Type w} {F : Type x}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (M : Fin n → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F) :
    E →L[ℂ] F :=
  operatorAffine b (fun i => (ξ i : ℂ)) M z M₀

/-- The real-input complex operator-affine expression is continuous in all
real coordinates. -/
theorem continuous_realInputComplexOperatorAffine_fin {n : ℕ}
    {E : Type w} {F : Type x}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (b : Fin n → ℂ) (M : Fin n → E →L[ℂ] F)
    (z : ℂ) (M₀ : E →L[ℂ] F) :
    Continuous (fun ξ : Fin n → ℝ =>
      realInputComplexOperatorAffine b ξ M z M₀) := by
  unfold realInputComplexOperatorAffine operatorAffine
  fun_prop

/-- Measurability of a norm lower-tail event for real inputs and complex
operators. -/
theorem measurableSet_realInputComplexOperatorAffine_norm_le {n : ℕ}
    {E : Type w} {F : Type x}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (b : Fin n → ℂ) (M : Fin n → E →L[ℂ] F)
    (z : ℂ) (M₀ : E →L[ℂ] F) (r : ℝ) :
    MeasurableSet {ξ : Fin n → ℝ |
      ‖realInputComplexOperatorAffine b ξ M z M₀‖ ≤ r} := by
  change MeasurableSet
    ((fun ξ : Fin n → ℝ =>
      ‖realInputComplexOperatorAffine b ξ M z M₀‖) ⁻¹' Iic r)
  exact (continuous_realInputComplexOperatorAffine_fin b M z M₀).norm
    |>.measurable measurableSet_Iic

/-- A complex operator-affine function of one real variable has a linear
small-ball bound.  Projecting the complex slope onto a real or imaginary
component costs the convenient factor `4`. -/
theorem complex_operatorAffine_realInput_oneCoordinate_smallBall
    {E : Type w} {F : Type x}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    {ν : Measure ℝ} {L : ℝ≥0∞} (hν : RealIntervalBound ν L)
    (R M : E →L[ℂ] F) (b : ℂ) (x : E) (ell : StrongDual ℂ F)
    (hx : ‖x‖ ≤ 1) (hell : ‖ell‖ ≤ 1)
    {ε ρ : ℝ} (hρ : 0 ≤ ρ) (hε : 0 < ε)
    (hslope : ε ≤ ‖b * ell (M x)‖) :
    ν {u : ℝ | ‖R + (b * (u : ℂ)) • M‖ ≤ ε * ρ} ≤
      (4 : ℝ≥0∞) * L * ENNReal.ofReal ρ := by
  have hsub :
      {u : ℝ | ‖R + (b * (u : ℂ)) • M‖ ≤ ε * ρ} ⊆
        {u : ℝ | ‖ell (R x) + (u : ℂ) * (b * ell (M x))‖ ≤ ε * ρ} := by
    intro u hu
    have htest :=
      scalar_test_le_operator_norm (R + (b * (u : ℂ)) • M) x ell hx hell
    have hscalar :
        ell ((R + (b * (u : ℂ)) • M) x) =
          ell (R x) + (u : ℂ) * (b * ell (M x)) :=
      scalarize_operatorAffine_oneCoordinate R M b (u : ℂ) x ell
    change ‖ell (R x) + (u : ℂ) * (b * ell (M x))‖ ≤ ε * ρ
    rw [← hscalar]
    exact htest.trans hu
  calc
    ν {u : ℝ | ‖R + (b * (u : ℂ)) • M‖ ≤ ε * ρ} ≤
        ν {u : ℝ | ‖ell (R x) + (u : ℂ) *
          (b * ell (M x))‖ ≤ ε * ρ} := measure_mono hsub
    _ ≤ (4 : ℝ≥0∞) * L * ENNReal.ofReal ρ :=
      complexAffine_realInput_smallBall_of_intervalBound
        hν hρ hε hslope

/-- Fubini lifting of a one-real-coordinate bound for a complex
operator-affine expression.  The selected coordinate may be arbitrary. -/
theorem iid_realInputComplexOperatorAffine_smallBall_of_oneCoordinate
    {ν : Measure ℝ} [SigmaFinite ν] [IsProbabilityMeasure ν]
    {n : ℕ} {E : Type w} {F : Type x}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (s : Fin (n + 1)) (b : Fin (n + 1) → ℂ)
    (M : Fin (n + 1) → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F)
    {ε ρ : ℝ} {C : ℝ≥0∞}
    (hone : ∀ R : E →L[ℂ] F,
      ν {u : ℝ | ‖R + (b s * (u : ℂ)) • M s‖ ≤ ε * ρ} ≤ C) :
    iidMeasure ν (n + 1)
        {ξ | ‖realInputComplexOperatorAffine b ξ M z M₀‖ ≤ ε * ρ} ≤ C := by
  let good : Set (Fin (n + 1) → ℝ) :=
    {ξ | ‖realInputComplexOperatorAffine b ξ M z M₀‖ ≤ ε * ρ}
  have hgood : MeasurableSet good := by
    simpa only [good] using
      measurableSet_realInputComplexOperatorAffine_norm_le b M z M₀ (ε * ρ)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) s
  have hpres : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) => ν))
      (ν.prod (Measure.pi (fun _ : Fin n => ν))) := by
    simpa only [e] using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ν) s)
  rw [iidMeasure_eq_pi, ← hpres.symm.map_eq,
    Measure.map_apply e.symm.measurable hgood,
    Measure.prod_apply_symm (hgood.preimage e.symm.measurable)]
  calc
    (∫⁻ y, ν ((fun u => (u, y)) ⁻¹' (e.symm ⁻¹' good))
        ∂Measure.pi (fun _ : Fin n => ν)) ≤
        ∫⁻ _y : Fin n → ℝ, C ∂Measure.pi (fun _ : Fin n => ν) := by
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
      change ν ((fun u => (u, y)) ⁻¹' (e.symm ⁻¹' good)) ≤ C
      rw [hsection]
      exact hone R
    _ = C := by simp

/-- Real IID arbitrary-coordinate small-ball estimate for complex
operator-affine data. -/
theorem real_iid_complexOperatorAffine_arbitraryCoordinate_smallBall
    {ν : Measure ℝ} [SigmaFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ≥0∞} (hν : RealIntervalBound ν L)
    {n : ℕ} {E : Type w} {F : Type x}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (s : Fin (n + 1)) (b : Fin (n + 1) → ℂ)
    (M : Fin (n + 1) → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F)
    (x : E) (ell : StrongDual ℂ F) (hx : ‖x‖ ≤ 1) (hell : ‖ell‖ ≤ 1)
    {ε ρ : ℝ} (hρ : 0 ≤ ρ) (hε : 0 < ε)
    (hslope : ε ≤ ‖b s * ell (M s x)‖) :
    iidMeasure ν (n + 1)
        {ξ | ‖realInputComplexOperatorAffine b ξ M z M₀‖ ≤ ε * ρ} ≤
      (4 : ℝ≥0∞) * L * ENNReal.ofReal ρ := by
  apply iid_realInputComplexOperatorAffine_smallBall_of_oneCoordinate
    s b M z M₀
  intro R
  exact complex_operatorAffine_realInput_oneCoordinate_smallBall
    hν R (M s) (b s) x ell hx hell hρ hε hslope

/-- The real-IID/complex-operator small-ball estimate closes the negative
logarithmic half in `L²`.  Here `theta * scale` is the scalarized slope
reached at coordinate `s`. -/
theorem real_iid_complexOperatorAffine_logDeficit_L2_of_slope
    {ν : Measure ℝ} [SigmaFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ} (hL : 0 ≤ L)
    (hν : RealIntervalBound ν (ENNReal.ofReal L))
    {n : ℕ} {E : Type w} {F : Type x}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (s : Fin (n + 1)) (b : Fin (n + 1) → ℂ)
    (M : Fin (n + 1) → E →L[ℂ] F) (z : ℂ) (M₀ : E →L[ℂ] F)
    (x : E) (ell : StrongDual ℂ F) (hx : ‖x‖ ≤ 1) (hell : ‖ell‖ ≤ 1)
    (scale theta : ℝ) (hscale : 0 < scale) (htheta : 0 < theta)
    (hslope : theta * scale ≤ ‖b s * ell (M s x)‖) :
    let radius : (Fin (n + 1) → ℝ) → ℝ := fun ξ =>
      ‖realInputComplexOperatorAffine b ξ M z M₀‖
    iidMeasure ν (n + 1) {ξ | radius ξ = 0} = 0 ∧
      MemLp (fun ξ => logDeficit scale (radius ξ)) 2
        (iidMeasure ν (n + 1)) ∧
      ∫ ξ, logDeficit scale (radius ξ) ^ 2
          ∂iidMeasure ν (n + 1) ≤
        oneSidedLogSecondMomentBound ((4 * L) / theta) 1 := by
  let radius : (Fin (n + 1) → ℝ) → ℝ := fun ξ =>
    ‖realInputComplexOperatorAffine b ξ M z M₀‖
  have hradius : Measurable radius := by
    exact (continuous_realInputComplexOperatorAffine_fin b M z M₀).norm.measurable
  have hradius0 : ∀ ξ, 0 ≤ radius ξ := fun ξ => norm_nonneg _
  let _ := iidMeasure_isProbability ν (n + 1)
  apply zeroSet_memLp_two_and_integral_sq_logDeficit_of_threshold_linearSmallBall
    (iidMeasure ν (n + 1)) radius hradius hradius0
      scale theta (4 * L) hscale htheta (mul_nonneg (by norm_num) hL)
  intro ρ hρ
  calc
    iidMeasure ν (n + 1) {ξ | radius ξ ≤ theta * scale * ρ} ≤
        (4 : ℝ≥0∞) * ENNReal.ofReal L * ENNReal.ofReal ρ := by
      exact real_iid_complexOperatorAffine_arbitraryCoordinate_smallBall
        hν s b M z M₀ x ell hx hell hρ.le
          (mul_pos htheta hscale) hslope
    _ = ENNReal.ofReal ((4 * L) * ρ) := by
      rw [← ENNReal.ofReal_ofNat 4,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
        ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hL)]

end CircularLawSection4
