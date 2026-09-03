/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/EntryLindeberg.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.BVH.Coordinates
import Vendor.Arxiv2410.V3.BVH.ProductLindeberg

/-!
# One-entry Lindeberg cancellation for the Hermitized resolvent

This is the local probabilistic calculation in the specialization of BVH Remark 6.13 used by
arXiv:2410.16457v3.  The exact resolvent identity from `EntryResolvent.lean` is decomposed into
the two real first moments and the three real second moments of a complex entry.  If these five
moments match, all terms through degree two cancel after integration and only the two cubic
remainders remain.
-/

namespace Arxiv2410V3.BVH

open MeasureTheory ProbabilityTheory Complex

noncomputable section

private structure CoordinatePolynomialIntegrable (P : Measure ℂ) : Prop where
  re : Integrable (fun w : ℂ ↦ (w.re : ℂ)) P
  im : Integrable (fun w : ℂ ↦ (w.im : ℂ)) P
  re_re : Integrable (fun w : ℂ ↦ ((w.re * w.re : ℝ) : ℂ)) P
  re_im : Integrable (fun w : ℂ ↦ ((w.re * w.im : ℝ) : ℂ)) P
  im_re : Integrable (fun w : ℂ ↦ ((w.im * w.re : ℝ) : ℂ)) P
  im_im : Integrable (fun w : ℂ ↦ ((w.im * w.im : ℝ) : ℂ)) P

/-- A finite third absolute moment supplies every real coordinate monomial of degree at most
two that occurs in the entrywise resolvent expansion. -/
private theorem coordinatePolynomialIntegrable_of_cube
    {P : Measure ℂ} [IsFiniteMeasure P]
    (hcube : Integrable (fun w : ℂ ↦ ‖w‖ ^ 3) P) :
    CoordinatePolynomialIntegrable P := by
  have hId : AEStronglyMeasurable (fun w : ℂ ↦ w) P :=
    measurable_id.aestronglyMeasurable
  have hnormOne : Integrable (fun w : ℂ ↦ ‖w‖ ^ 1) P :=
    integrable_norm_pow_of_le hId (by norm_num) hcube
  have hnormTwo : Integrable (fun w : ℂ ↦ ‖w‖ ^ 2) P :=
    integrable_norm_pow_of_le hId (by norm_num) hcube
  have hreR : Integrable (fun w : ℂ ↦ w.re) P := by
    apply hnormOne.mono' (by fun_prop)
    filter_upwards [] with w
    simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm w
  have himR : Integrable (fun w : ℂ ↦ w.im) P := by
    apply hnormOne.mono' (by fun_prop)
    filter_upwards [] with w
    simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm w
  have hre_reR : Integrable (fun w : ℂ ↦ w.re * w.re) P := by
    apply hnormTwo.mono' (by fun_prop)
    filter_upwards [] with w
    have h := Complex.abs_re_le_norm w
    simpa [Real.norm_eq_abs, abs_mul, pow_two] using
      (mul_le_mul h h (abs_nonneg w.re) (norm_nonneg w))
  have hre_imR : Integrable (fun w : ℂ ↦ w.re * w.im) P := by
    apply hnormTwo.mono' (by fun_prop)
    filter_upwards [] with w
    have hre := Complex.abs_re_le_norm w
    have him := Complex.abs_im_le_norm w
    simpa [Real.norm_eq_abs, abs_mul, pow_two] using
      (mul_le_mul hre him (abs_nonneg w.im) (norm_nonneg w))
  have him_reR : Integrable (fun w : ℂ ↦ w.im * w.re) P := by
    simpa [mul_comm] using hre_imR
  have him_imR : Integrable (fun w : ℂ ↦ w.im * w.im) P := by
    apply hnormTwo.mono' (by fun_prop)
    filter_upwards [] with w
    have h := Complex.abs_im_le_norm w
    simpa [Real.norm_eq_abs, abs_mul, pow_two] using
      (mul_le_mul h h (abs_nonneg w.im) (norm_nonneg w))
  exact ⟨hreR.ofReal, himR.ofReal, hre_reR.ofReal, hre_imR.ofReal,
    him_reR.ofReal, him_imR.ofReal⟩

private theorem measurable_update_complex {n : ℕ}
    (x : Fin n → ℂ) (k : Fin n) :
    Measurable (fun w : ℂ ↦ Function.update x k w) := by
  apply measurable_pi_lambda
  intro l
  by_cases h : l = k
  · subst l
    have hfun : (fun w : ℂ ↦ Function.update x k w k) = id := by
      funext w
      simp [Function.update]
    rw [hfun]
    exact measurable_id
  · simp [Function.update, h]

/-- The exact local second-order expansion and moment cancellation for one matrix entry.

This is the machine-checked replacement of the Taylor sentence in the proof of v3 (3.12).
The coefficient of the remainder is exactly `1 / (n * (Im eta)^4)`. -/
noncomputable def stieltjesTrace_coordinate_secondOrderCubicExpansion
    {n : ℕ} [NeZero n]
    (P Q : Measure ℂ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (x : Fin (n * n) → ℂ) (k : Fin (n * n)) (z : ℂ) {eta : ℂ}
    (heta : 0 < eta.im)
    (hcubeP : Integrable (fun w : ℂ ↦ ‖w‖ ^ 3) P)
    (hcubeQ : Integrable (fun w : ℂ ↦ ‖w‖ ^ 3) Q)
    (hre : (∫ w, w.re ∂P) = ∫ w, w.re ∂Q)
    (him : (∫ w, w.im ∂P) = ∫ w, w.im ∂Q)
    (hre_re : (∫ w, w.re * w.re ∂P) = ∫ w, w.re * w.re ∂Q)
    (hre_im : (∫ w, w.re * w.im ∂P) = ∫ w, w.re * w.im ∂Q)
    (him_im : (∫ w, w.im * w.im ∂P) = ∫ w, w.im * w.im ∂Q) :
    SecondOrderCubicExpansion
      (fun w ↦ stieltjesTrace (matrixOfCoordinates (Function.update x k w)) z eta)
      P Q (fun w ↦ ‖w‖ ^ 3) (1 / ((n : ℝ) * eta.im ^ 4)) := by
  let ij : Fin n × Fin n := finProdFinEquiv.symm k
  let X0 : Matrix (Fin n) (Fin n) ℂ :=
    matrixOfCoordinates (Function.update x k 0)
  let A : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ := hermitization X0 z
  let R : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ :=
    (A - eta • (1 : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ))⁻¹
  let Hr := entryHermitianSummand ij.1 ij.2 1
  let Hi := entryHermitianSummand ij.1 ij.2 Complex.I
  let phi : ℂ → ℂ :=
    fun w ↦ stieltjesTrace (matrixOfCoordinates (Function.update x k w)) z eta
  let constant : ℂ := normalizedTrace R
  let first : ℂ → ℂ := fun w ↦
    -((w.re : ℂ) * normalizedTrace (R * Hr * R)) -
      (w.im : ℂ) * normalizedTrace (R * Hi * R)
  let second : ℂ → ℂ := fun w ↦
    ((w.re * w.re : ℝ) : ℂ) * normalizedTrace (R * Hr * R * Hr * R) +
      ((w.re * w.im : ℝ) : ℂ) * normalizedTrace (R * Hr * R * Hi * R) +
      ((w.im * w.re : ℝ) : ℂ) * normalizedTrace (R * Hi * R * Hr * R) +
      ((w.im * w.im : ℝ) : ℂ) * normalizedTrace (R * Hi * R * Hi * R)
  let remainder : ℂ → ℂ := fun w ↦
    phi w - constant - first w - second w
  have hpolyP := coordinatePolynomialIntegrable_of_cube hcubeP
  have hpolyQ := coordinatePolynomialIntegrable_of_cube hcubeQ
  have hfirstP : Integrable first P := by
    exact (hpolyP.re.mul_const _).neg.sub (hpolyP.im.mul_const _)
  have hfirstQ : Integrable first Q := by
    exact (hpolyQ.re.mul_const _).neg.sub (hpolyQ.im.mul_const _)
  have hsecondP : Integrable second P := by
    exact (((hpolyP.re_re.mul_const _).add (hpolyP.re_im.mul_const _)).add
      (hpolyP.im_re.mul_const _)).add (hpolyP.im_im.mul_const _)
  have hsecondQ : Integrable second Q := by
    exact (((hpolyQ.re_re.mul_const _).add (hpolyQ.re_im.mul_const _)).add
      (hpolyQ.im_re.mul_const _)).add (hpolyQ.im_im.mul_const _)
  have hphiStrong : StronglyMeasurable phi := by
    exact (stronglyMeasurable_stieltjesTrace_matrixOfCoordinates z eta).comp_measurable
      (measurable_update_complex x k)
  have hremStrong : StronglyMeasurable remainder := by
    dsimp only [remainder]
    fun_prop
  have integral_ofReal_match {f : ℂ → ℝ}
      (h : (∫ w, f w ∂P) = ∫ w, f w ∂Q) :
      (∫ w, (f w : ℂ) ∂P) = ∫ w, (f w : ℂ) ∂Q := by
    calc
      (∫ w, (f w : ℂ) ∂P) = Complex.ofReal (∫ w, f w ∂P) :=
        integral_complex_ofReal
      _ = Complex.ofReal (∫ w, f w ∂Q) := congrArg Complex.ofReal h
      _ = ∫ w, (f w : ℂ) ∂Q := integral_complex_ofReal.symm
  let firstRe : ℂ → ℂ := fun w ↦
    (w.re : ℂ) * normalizedTrace (R * Hr * R)
  let firstIm : ℂ → ℂ := fun w ↦
    (w.im : ℂ) * normalizedTrace (R * Hi * R)
  have hfirstReP : Integrable firstRe P := hpolyP.re.mul_const _
  have hfirstImP : Integrable firstIm P := hpolyP.im.mul_const _
  have hfirstReQ : Integrable firstRe Q := hpolyQ.re.mul_const _
  have hfirstImQ : Integrable firstIm Q := hpolyQ.im.mul_const _
  have hfirstFormulaP :
      (∫ w, first w ∂P) = -(∫ w, firstRe w ∂P) - ∫ w, firstIm w ∂P := by
    change (∫ w, ((-firstRe) - firstIm) w ∂P) = _
    calc
      (∫ w, ((-firstRe) - firstIm) w ∂P) =
          (∫ w, (-firstRe) w ∂P) - ∫ w, firstIm w ∂P := by
        simpa only [Pi.sub_apply] using integral_sub hfirstReP.neg hfirstImP
      _ = -(∫ w, firstRe w ∂P) - ∫ w, firstIm w ∂P := by
        rw [integral_neg' firstRe]
  have hfirstFormulaQ :
      (∫ w, first w ∂Q) = -(∫ w, firstRe w ∂Q) - ∫ w, firstIm w ∂Q := by
    change (∫ w, ((-firstRe) - firstIm) w ∂Q) = _
    calc
      (∫ w, ((-firstRe) - firstIm) w ∂Q) =
          (∫ w, (-firstRe) w ∂Q) - ∫ w, firstIm w ∂Q := by
        simpa only [Pi.sub_apply] using integral_sub hfirstReQ.neg hfirstImQ
      _ = -(∫ w, firstRe w ∂Q) - ∫ w, firstIm w ∂Q := by
        rw [integral_neg' firstRe]
  have hfirstReMatch : ∫ w, firstRe w ∂P = ∫ w, firstRe w ∂Q := by
    dsimp only [firstRe]
    rw [integral_mul_const, integral_mul_const,
      integral_ofReal_match (f := fun w ↦ w.re) hre]
  have hfirstImMatch : ∫ w, firstIm w ∂P = ∫ w, firstIm w ∂Q := by
    dsimp only [firstIm]
    rw [integral_mul_const, integral_mul_const,
      integral_ofReal_match (f := fun w ↦ w.im) him]
  have hfirstMatch : ∫ w, first w ∂P = ∫ w, first w ∂Q := by
    rw [hfirstFormulaP, hfirstFormulaQ, hfirstReMatch, hfirstImMatch]
  have him_re : (∫ w, w.im * w.re ∂P) = ∫ w, w.im * w.re ∂Q := by
    simpa [mul_comm] using hre_im
  let secondRR : ℂ → ℂ := fun w ↦
    ((w.re * w.re : ℝ) : ℂ) * normalizedTrace (R * Hr * R * Hr * R)
  let secondRI : ℂ → ℂ := fun w ↦
    ((w.re * w.im : ℝ) : ℂ) * normalizedTrace (R * Hr * R * Hi * R)
  let secondIR : ℂ → ℂ := fun w ↦
    ((w.im * w.re : ℝ) : ℂ) * normalizedTrace (R * Hi * R * Hr * R)
  let secondII : ℂ → ℂ := fun w ↦
    ((w.im * w.im : ℝ) : ℂ) * normalizedTrace (R * Hi * R * Hi * R)
  have hsecondRRP : Integrable secondRR P := hpolyP.re_re.mul_const _
  have hsecondRIP : Integrable secondRI P := hpolyP.re_im.mul_const _
  have hsecondIRP : Integrable secondIR P := hpolyP.im_re.mul_const _
  have hsecondIIP : Integrable secondII P := hpolyP.im_im.mul_const _
  have hsecondRRQ : Integrable secondRR Q := hpolyQ.re_re.mul_const _
  have hsecondRIQ : Integrable secondRI Q := hpolyQ.re_im.mul_const _
  have hsecondIRQ : Integrable secondIR Q := hpolyQ.im_re.mul_const _
  have hsecondIIQ : Integrable secondII Q := hpolyQ.im_im.mul_const _
  have hsecondFormulaP :
      (∫ w, second w ∂P) =
        (∫ w, secondRR w ∂P) + (∫ w, secondRI w ∂P) +
          (∫ w, secondIR w ∂P) + ∫ w, secondII w ∂P := by
    have h12 : Integrable (secondRR + secondRI) P := hsecondRRP.add hsecondRIP
    have h123 : Integrable (secondRR + secondRI + secondIR) P := h12.add hsecondIRP
    have e12 :
        (∫ w, (secondRR + secondRI) w ∂P) =
          (∫ w, secondRR w ∂P) + ∫ w, secondRI w ∂P := by
      simpa only [Pi.add_apply] using integral_add hsecondRRP hsecondRIP
    have e123 :
        (∫ w, (secondRR + secondRI + secondIR) w ∂P) =
          (∫ w, (secondRR + secondRI) w ∂P) + ∫ w, secondIR w ∂P := by
      simpa only [Pi.add_apply] using integral_add h12 hsecondIRP
    have e1234 :
        (∫ w, (secondRR + secondRI + secondIR + secondII) w ∂P) =
          (∫ w, (secondRR + secondRI + secondIR) w ∂P) +
            ∫ w, secondII w ∂P := by
      simpa only [Pi.add_apply] using integral_add h123 hsecondIIP
    change (∫ w, (secondRR + secondRI + secondIR + secondII) w ∂P) = _
    rw [e1234, e123, e12]
  have hsecondFormulaQ :
      (∫ w, second w ∂Q) =
        (∫ w, secondRR w ∂Q) + (∫ w, secondRI w ∂Q) +
          (∫ w, secondIR w ∂Q) + ∫ w, secondII w ∂Q := by
    have h12 : Integrable (secondRR + secondRI) Q := hsecondRRQ.add hsecondRIQ
    have h123 : Integrable (secondRR + secondRI + secondIR) Q := h12.add hsecondIRQ
    have e12 :
        (∫ w, (secondRR + secondRI) w ∂Q) =
          (∫ w, secondRR w ∂Q) + ∫ w, secondRI w ∂Q := by
      simpa only [Pi.add_apply] using integral_add hsecondRRQ hsecondRIQ
    have e123 :
        (∫ w, (secondRR + secondRI + secondIR) w ∂Q) =
          (∫ w, (secondRR + secondRI) w ∂Q) + ∫ w, secondIR w ∂Q := by
      simpa only [Pi.add_apply] using integral_add h12 hsecondIRQ
    have e1234 :
        (∫ w, (secondRR + secondRI + secondIR + secondII) w ∂Q) =
          (∫ w, (secondRR + secondRI + secondIR) w ∂Q) +
            ∫ w, secondII w ∂Q := by
      simpa only [Pi.add_apply] using integral_add h123 hsecondIIQ
    change (∫ w, (secondRR + secondRI + secondIR + secondII) w ∂Q) = _
    rw [e1234, e123, e12]
  have hsecondRRMatch : ∫ w, secondRR w ∂P = ∫ w, secondRR w ∂Q := by
    dsimp only [secondRR]
    rw [integral_mul_const, integral_mul_const,
      integral_ofReal_match (f := fun w ↦ w.re * w.re) hre_re]
  have hsecondRIMatch : ∫ w, secondRI w ∂P = ∫ w, secondRI w ∂Q := by
    dsimp only [secondRI]
    rw [integral_mul_const, integral_mul_const,
      integral_ofReal_match (f := fun w ↦ w.re * w.im) hre_im]
  have hsecondIRMatch : ∫ w, secondIR w ∂P = ∫ w, secondIR w ∂Q := by
    dsimp only [secondIR]
    rw [integral_mul_const, integral_mul_const,
      integral_ofReal_match (f := fun w ↦ w.im * w.re) him_re]
  have hsecondIIMatch : ∫ w, secondII w ∂P = ∫ w, secondII w ∂Q := by
    dsimp only [secondII]
    rw [integral_mul_const, integral_mul_const,
      integral_ofReal_match (f := fun w ↦ w.im * w.im) him_im]
  have hsecondMatch : ∫ w, second w ∂P = ∫ w, second w ∂Q := by
    rw [hsecondFormulaP, hsecondFormulaQ, hsecondRRMatch, hsecondRIMatch,
      hsecondIRMatch, hsecondIIMatch]
  have hphi_as_resolvent (w : ℂ) :
      phi w = normalizedTrace
        ((A + entryHermitianSummand ij.1 ij.2 w -
          eta • (1 : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ))⁻¹) := by
    dsimp only [phi, stieltjesTrace, greenFunction]
    rw [matrixOfCoordinates_update_eq_add_single]
    rw [hermitization_add_singleEntryMatrix]
  have hremainder (w : ℂ) :
      remainder w = -normalizedTrace
        (resolventCubicRemainder A (entryHermitianSummand ij.1 ij.2 w) eta) := by
    have hexact := normalizedTrace_entry_resolvent_second_order_expansion_re_im
      A (hermitization_isHermitian X0 z) ij.1 ij.2 w heta
    dsimp only [remainder]
    rw [hphi_as_resolvent w]
    dsimp only [constant, first, second, R, Hr, Hi]
    dsimp only at hexact
    rw [hexact]
    push_cast
    ring
  refine
    { constant := constant
      first := first
      second := second
      remainder := remainder
      expansion := ?_
      first_integrable_mu := hfirstP
      first_integrable_nu := hfirstQ
      second_integrable_mu := hsecondP
      second_integrable_nu := hsecondQ
      remainder_stronglyMeasurable := hremStrong
      first_match := hfirstMatch
      second_match := hsecondMatch
      remainder_norm_le := ?_ }
  · intro w
    dsimp only [remainder]
    abel
  · intro w
    rw [hremainder w, norm_neg]
    have hbound := norm_normalizedTrace_entry_resolventCubicRemainder_le
      A (hermitization_isHermitian X0 z) ij.1 ij.2 w heta
    calc
      ‖normalizedTrace (resolventCubicRemainder A
          (entryHermitianSummand ij.1 ij.2 w) eta)‖ ≤
          ‖w‖ ^ 3 * ((n : ℝ) * eta.im ^ 4)⁻¹ := hbound
      _ = 1 / ((n : ℝ) * eta.im ^ 4) * ‖w‖ ^ 3 := by
        rw [one_div, mul_comm]

end

end Arxiv2410V3.BVH

