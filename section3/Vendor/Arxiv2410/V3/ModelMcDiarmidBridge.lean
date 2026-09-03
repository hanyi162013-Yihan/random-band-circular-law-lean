/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/ModelMcDiarmidBridge.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.RowIndependence
import Vendor.Arxiv2410.V3.RowSensitivity
import Vendor.Arxiv2410.V3.ScalarConcentration
import Vendor.Arxiv2410.V3.TraceMeasurability
import Vendor.Arxiv2410.V3.McDiarmidArithmetic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.SubGaussian

/-!
# From independent rows to McDiarmid, without an external Doob certificate

This file supplies the model-specific bridge which is implicit in proof step (3) of
arXiv:2410.16457v3, Proposition 3.4.  The joint law of the rows is first identified with a finite
product measure.  A finite-product bounded-differences theorem is then proved by iterated
Fubini--Hoeffding tensorization.  Thus neither a martingale, a conditional-increment interval, nor
a tail estimate is an input to the final model theorem.

The tensorization below uses the symmetric interval around one reference value.  Consequently it
assigns variance proxy `c i ^ 2` to coordinate `i` (rather than the sharp `c i ^ 2 / 4`).  This
only changes the harmless absolute constant in Proposition 3.4 and keeps the proof substantially
more robust at the product-measure boundary.
-/

namespace Arxiv2410V3

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

section ProductTensorization

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {muA : Measure A} {muB : Measure B}
  [IsProbabilityMeasure muA] [IsProbabilityMeasure muB]

/-- The two-factor tensorization step used in the finite-product proof of McDiarmid.

`g` is a centered sub-Gaussian function of the first coordinate.  For every first-coordinate
value, `h a` is a centered sub-Gaussian function of the second coordinate, with a uniform proxy.
The conclusion is proved directly by Fubini and the two moment-generating-function bounds. -/
theorem hasSubgaussianMGF_prod_add_of_fiberwise
    {g : A → ℝ} {h : A → B → ℝ} {cG cH : ℝ≥0}
    (hgMeas : StronglyMeasurable g)
    (hhMeas : StronglyMeasurable (Function.uncurry h))
    (hg : HasSubgaussianMGF g cG muA)
    (hh : ∀ a, HasSubgaussianMGF (h a) cH muB)
    {LG LH : ℝ} (hgBound : ∀ a, |g a| ≤ LG) (hhBound : ∀ a b, |h a b| ≤ LH) :
    HasSubgaussianMGF (fun p : A × B ↦ g p.1 + h p.1 p.2) (cG + cH) (muA.prod muB) := by
  have hsumMeas : StronglyMeasurable (fun p : A × B ↦ g p.1 + h p.1 p.2) :=
    (hgMeas.comp_measurable measurable_fst).add hhMeas
  refine ⟨?_, ?_⟩
  · intro t
    apply Integrable.of_bound (by fun_prop) (Real.exp (|t| * (LG + LH)))
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_exp]
    apply Real.exp_le_exp.mpr
    calc
      t * (g p.1 + h p.1 p.2) ≤ |t| * |g p.1 + h p.1 p.2| :=
        le_trans (le_abs_self _) (by rw [abs_mul])
      _ ≤ |t| * (|g p.1| + |h p.1 p.2|) := by
        exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg t)
      _ ≤ |t| * (LG + LH) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (hgBound _) (hhBound _ _)) (abs_nonneg t)
  · intro t
    have hExpInt : Integrable
        (fun p : A × B ↦ Real.exp (t * (g p.1 + h p.1 p.2))) (muA.prod muB) := by
      apply Integrable.of_bound (by fun_prop) (Real.exp (|t| * (LG + LH)))
      filter_upwards with p
      rw [Real.norm_eq_abs, abs_exp]
      apply Real.exp_le_exp.mpr
      calc
        t * (g p.1 + h p.1 p.2) ≤ |t| * |g p.1 + h p.1 p.2| :=
          le_trans (le_abs_self _) (by rw [abs_mul])
        _ ≤ |t| * (|g p.1| + |h p.1 p.2|) := by
          exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg t)
        _ ≤ |t| * (LG + LH) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add (hgBound _) (hhBound _ _)) (abs_nonneg t)
    have hRightInt : Integrable
        (fun a ↦ Real.exp (t * g a) * Real.exp ((cH : ℝ) * t ^ 2 / 2)) muA :=
      (hg.integrable_exp_mul t).mul_const _
    have hLeftInt : Integrable
        (fun a ↦ Real.exp (t * g a) * ∫ b, Real.exp (t * h a b) ∂muB) muA := by
      have hIterated := hExpInt.integral_prod_left
      convert hIterated using 1
      funext a
      simp_rw [mul_add, Real.exp_add, integral_const_mul]
    rw [mgf, integral_prod _ hExpInt]
    simp_rw [mul_add, Real.exp_add, integral_const_mul]
    calc
      ∫ a, Real.exp (t * g a) * ∫ b, Real.exp (t * h a b) ∂muB ∂muA
          ≤ ∫ a, Real.exp (t * g a) * Real.exp ((cH : ℝ) * t ^ 2 / 2) ∂muA := by
        apply integral_mono_ae hLeftInt hRightInt
        filter_upwards with a
        exact mul_le_mul_of_nonneg_left ((hh a).mgf_le t) (Real.exp_nonneg _)
      _ = (∫ a, Real.exp (t * g a) ∂muA) * Real.exp ((cH : ℝ) * t ^ 2 / 2) := by
        rw [integral_mul_const]
      _ ≤ Real.exp ((cG : ℝ) * t ^ 2 / 2) *
          Real.exp ((cH : ℝ) * t ^ 2 / 2) := by
        gcongr
        exact hg.mgf_le t
      _ = Real.exp (((cG + cH : ℝ≥0) : ℝ) * t ^ 2 / 2) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

end ProductTensorization

section FiniteProductMcDiarmid

variable {B : Type*} [MeasurableSpace B] [Nonempty B]

/-- Pointwise bounded differences for a function on `n` coordinates.  The update formulation is
exactly what the row-replacement resolvent estimate supplies. -/
def FinCoordinateBound {n : ℕ} (f : (Fin n → B) → ℝ) (c : Fin n → ℝ≥0) : Prop :=
  ∀ i x y, |f x - f (Function.update x i y)| ≤ (c i : ℝ)

/-- A convenient pointwise boundedness package.  Resolvent traces satisfy it with
`L = (Im η)⁻¹`. -/
def FinProductBounded {n : ℕ} (f : (Fin n → B) → ℝ) (L : ℝ) : Prop :=
  ∀ x, |f x| ≤ L

/-- Finite-product bounded differences, proved by induction using the preceding two-factor
Fubini--Hoeffding tensorization.  Each coordinate contributes proxy `c i ^ 2`.

This is a complete McDiarmid input theorem: its hypotheses mention only product laws,
measurability, pointwise boundedness, and deterministic coordinate replacement. -/
theorem hasSubgaussianMGF_centered_pi_of_finCoordinateBound
    {n : ℕ} (P : Fin n → Measure B) [∀ i, IsProbabilityMeasure (P i)]
    (f : (Fin n → B) → ℝ) (hf : StronglyMeasurable f)
    {L : ℝ} (hfBound : FinProductBounded f L)
    (c : Fin n → ℝ≥0) (hc : FinCoordinateBound f c) :
    HasSubgaussianMGF
      (fun x ↦ f x - ∫ y, f y ∂Measure.pi P)
      (∑ i, (c i) ^ 2) (Measure.pi P) := by
  induction n with
  | zero =>
      let x0 : Fin 0 → B := fun i ↦ Fin.elim0 i
      have hconst : f = fun _ ↦ f x0 := by
        funext x
        congr 1
        exact Subsingleton.elim x x0
      rw [show (∑ i, c i ^ 2) = 0 by simp]
      apply (HasSubgaussianMGF.fun_zero (μ := Measure.pi P)).congr
      apply ae_of_all
      intro x
      have hx : f x = f x0 := congrFun hconst x
      have hint : (∫ y, f y ∂Measure.pi P) = f x0 := by
        rw [integral_congr_ae (ae_of_all _ fun y ↦ congrFun hconst y)]
        simp
      change (0 : ℝ) = f x - ∫ y, f y ∂Measure.pi P
      rw [hx, hint, sub_self]
  | succ n ih =>
      let e : (Fin (n + 1) → B) ≃ᵐ B × (Fin n → B) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ B) 0
      let Prest : Fin n → Measure B := fun i ↦ P i.succ
      let F : B → (Fin n → B) → ℝ := fun a r ↦ f (e.symm (a, r))
      have hFMeas : StronglyMeasurable (Function.uncurry F) := by
        exact hf.comp_measurable e.symm.measurable
      have hFSectionMeas (a : B) : StronglyMeasurable (F a) := by
        exact hFMeas.comp_measurable measurable_prodMk_left
      have hFBound (a : B) : FinProductBounded (F a) L := by
        intro r
        exact hfBound _
      have hFCoord (a : B) : FinCoordinateBound (F a) (fun i ↦ c i.succ) := by
        intro i r b
        have h := hc i.succ (e.symm (a, r)) b
        have heq : Function.update (e.symm (a, r)) i.succ b =
            e.symm (a, Function.update r i b) := by
          funext k
          refine Fin.cases ?_ (fun j ↦ ?_) k
          · have hne : (0 : Fin (n + 1)) ≠ i.succ := i.succ_ne_zero.symm
            simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Function.update, hne]
          · by_cases hji : j = i
            · subst j
              simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Function.update]
            · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Function.update, hji]
        simpa only [F, heq] using h
      have hSection (a : B) :
          HasSubgaussianMGF
            (fun r ↦ F a r - ∫ s, F a s ∂Measure.pi Prest)
            (∑ i : Fin n, (c i.succ) ^ 2) (Measure.pi Prest) := by
        exact ih Prest (F a) (hFSectionMeas a) (hFBound a) (fun i ↦ c i.succ) (hFCoord a)
      let g : B → ℝ := fun a ↦ ∫ r, F a r ∂Measure.pi Prest
      have hFInt (a : B) : Integrable (F a) (Measure.pi Prest) := by
        apply Integrable.of_bound (hFSectionMeas a).aestronglyMeasurable L
        exact ae_of_all _ fun r ↦ by simpa [Real.norm_eq_abs] using hFBound a r
      have hgMeas : StronglyMeasurable g := by
        exact hFMeas.integral_prod_right
      have hgBound : ∀ a, |g a| ≤ L := by
        intro a
        have h := norm_integral_le_of_norm_le_const
          (μ := Measure.pi Prest) (f := F a)
          (ae_of_all _ fun r ↦ by simpa [Real.norm_eq_abs] using hFBound a r)
        simpa [g, Real.norm_eq_abs] using h
      have hgOsc : ∀ a a', |g a - g a'| ≤ (c 0 : ℝ) := by
        intro a a'
        change |∫ r, F a r ∂Measure.pi Prest - ∫ r, F a' r ∂Measure.pi Prest| ≤ _
        rw [← integral_sub (hFInt a) (hFInt a')]
        have h := norm_integral_le_of_norm_le_const
          (μ := Measure.pi Prest) (f := fun r ↦ F a r - F a' r)
          (C := (c 0 : ℝ))
          (ae_of_all _ fun r ↦ ?_)
        · simpa [Real.norm_eq_abs] using h
        · have hc0 := hc 0 (e.symm (a, r)) a'
          have heq0 : Function.update (e.symm (a, r)) 0 a' = e.symm (a', r) := by
            funext k
            refine Fin.cases ?_ (fun j ↦ ?_) k
            · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Function.update]
            · have hne : (Fin.succ j : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero j
              simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Function.update, hne]
          rw [heq0] at hc0
          simpa [F, Real.norm_eq_abs] using hc0
      let a0 : B := Classical.choice inferInstance
      have hgIcc : ∀ a, g a ∈ Icc (g a0 - (c 0 : ℝ)) (g a0 + (c 0 : ℝ)) := by
        intro a
        have ha := abs_le.mp (hgOsc a a0)
        constructor <;> linarith
      have hgRaw := hasSubgaussianMGF_of_mem_Icc (μ := P 0)
        hgMeas.measurable.aemeasurable
        (ae_of_all _ hgIcc)
      have hg : HasSubgaussianMGF
          (fun a ↦ g a - ∫ a', g a' ∂P 0) ((c 0) ^ 2) (P 0) := by
        convert hgRaw using 1
        ext
        push_cast
        simp only [Real.norm_eq_abs]
        have hc0 : (0 : ℝ) ≤ (c 0 : ℝ) := NNReal.coe_nonneg _
        rw [show g a0 + (c 0 : ℝ) - (g a0 - (c 0 : ℝ)) =
            2 * (c 0 : ℝ) by ring]
        rw [abs_of_nonneg (mul_nonneg (by norm_num) hc0)]
        ring
      let G : B → ℝ := fun a ↦ g a - ∫ a', g a' ∂P 0
      let H : B → (Fin n → B) → ℝ := fun a r ↦ F a r - g a
      have hGMeas : StronglyMeasurable G := hgMeas.sub stronglyMeasurable_const
      have hHMeas : StronglyMeasurable (Function.uncurry H) :=
        hFMeas.sub (hgMeas.comp_measurable measurable_fst)
      have hgMeanBound : |∫ a, g a ∂P 0| ≤ L := by
        have h := norm_integral_le_of_norm_le_const
          (μ := P 0) (f := g)
          (ae_of_all _ fun a ↦ by simpa [Real.norm_eq_abs] using hgBound a)
        simpa [Real.norm_eq_abs] using h
      have hGBound : ∀ a, |G a| ≤ L + L := by
        intro a
        exact (abs_sub (g a) _).trans (add_le_add (hgBound a) hgMeanBound)
      have hHBound : ∀ a r, |H a r| ≤ L + L := by
        intro a r
        exact (abs_sub (F a r) (g a)).trans (add_le_add (hFBound a r) (hgBound a))
      have hTensor : HasSubgaussianMGF
          (fun p : B × (Fin n → B) ↦ G p.1 + H p.1 p.2)
          ((c 0) ^ 2 + ∑ i : Fin n, (c i.succ) ^ 2)
            ((P 0).prod (Measure.pi Prest)) := by
        exact hasSubgaussianMGF_prod_add_of_fiberwise hGMeas hHMeas hg
          (by simpa [H, g] using hSection) hGBound hHBound
      have hFJointInt : Integrable (Function.uncurry F) ((P 0).prod (Measure.pi Prest)) := by
        apply Integrable.of_bound hFMeas.aestronglyMeasurable L
        exact ae_of_all _ fun p ↦ by
          rw [Real.norm_eq_abs]
          change |f (e.symm p)| ≤ L
          exact hfBound _
      have hFIntegral :
          (∫ p, Function.uncurry F p ∂((P 0).prod (Measure.pi Prest))) =
            ∫ a, g a ∂P 0 := by
        rw [integral_prod _ hFJointInt]
        rfl
      have hTensorCentered : HasSubgaussianMGF
          (fun p : B × (Fin n → B) ↦
            Function.uncurry F p -
              ∫ q, Function.uncurry F q ∂((P 0).prod (Measure.pi Prest)))
          ((c 0) ^ 2 + ∑ i : Fin n, (c i.succ) ^ 2)
            ((P 0).prod (Measure.pi Prest)) := by
        apply hTensor.congr
        exact ae_of_all _ fun p ↦ by
          rw [hFIntegral]
          simp only [G, H, Function.uncurry]
          ring
      have he := measurePreserving_piFinSuccAbove P 0
      have hMapped : HasSubgaussianMGF
          (fun p : B × (Fin n → B) ↦
            Function.uncurry F p -
              ∫ q, Function.uncurry F q ∂((P 0).prod (Measure.pi Prest)))
          ((c 0) ^ 2 + ∑ i : Fin n, (c i.succ) ^ 2)
          ((Measure.pi P).map e) := by
        rw [he.map_eq]
        exact hTensorCentered
      have hPull := HasSubgaussianMGF.of_map e.measurable.aemeasurable hMapped
      have hIntegralMap :
          (∫ q, Function.uncurry F q ∂((P 0).prod (Measure.pi Prest))) =
            ∫ y, f y ∂Measure.pi P := by
        symm
        have hcomp (y : Fin (n + 1) → B) : Function.uncurry F (e y) = f y := by
          change f (e.symm (e y)) = f y
          rw [e.symm_apply_apply]
        calc
          ∫ y, f y ∂Measure.pi P =
              ∫ y, Function.uncurry F (e y) ∂Measure.pi P := by
                apply integral_congr_ae
                exact ae_of_all _ fun y ↦ (hcomp y).symm
          _ = ∫ q, Function.uncurry F q ∂((P 0).prod (Measure.pi Prest)) := by
                have htransport := he.integral_comp' (Function.uncurry F)
                change (∫ y, Function.uncurry F (e y) ∂Measure.pi P) =
                  ∫ q, Function.uncurry F q ∂((P 0).prod (Measure.pi Prest)) at htransport
                exact htransport
      rw [Fin.sum_univ_succ]
      apply hPull.congr
      exact ae_of_all _ fun x ↦ by
        change Function.uncurry F (e x) -
            ∫ q, Function.uncurry F q ∂((P 0).prod (Measure.pi Prest)) =
          f x - ∫ y, f y ∂Measure.pi P
        rw [hIntegralMap]
        change f (e.symm (e x)) - ∫ y, f y ∂Measure.pi P =
          f x - ∫ y, f y ∂Measure.pi P
        rw [e.symm_apply_apply]

end FiniteProductMcDiarmid

section IndependentCoordinates

variable {Omega B : Type*} [MeasurableSpace Omega] [MeasurableSpace B] [Nonempty B]
  {mu : Measure Omega} [IsProbabilityMeasure mu]

/-- Bounded differences pulled back from the product of the coordinate laws to an arbitrary
probability space carrying independent coordinates.  This is the measure-theoretic bridge needed
for the actual independent rows: the product law is a theorem (`iIndepFun.map_fun_eq_pi_map`), not
an extra model assumption. -/
theorem hasSubgaussianMGF_centered_of_iIndepFun_finCoordinateBound
    {n : ℕ} (X : Fin n → Omega → B)
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X mu)
    (f : (Fin n → B) → ℝ) (hf : StronglyMeasurable f)
    {L : ℝ} (hfBound : FinProductBounded f L)
    (c : Fin n → ℝ≥0) (hc : FinCoordinateBound f c) :
    HasSubgaussianMGF
      (fun omega ↦ f (fun i ↦ X i omega) -
        ∫ omega', f (fun i ↦ X i omega') ∂mu)
      (∑ i, (c i) ^ 2) mu := by
  let P : Fin n → Measure B := fun i ↦ mu.map (X i)
  let _ (i : Fin n) : IsProbabilityMeasure (P i) :=
    Measure.isProbabilityMeasure_map (hX i).aemeasurable
  let R : Omega → (Fin n → B) := fun omega i ↦ X i omega
  have hR : Measurable R := measurable_pi_lambda _ hX
  have hLaw : mu.map R = Measure.pi P := by
    exact hIndep.map_fun_eq_pi_map (fun i ↦ (hX i).aemeasurable)
  have hProduct := hasSubgaussianMGF_centered_pi_of_finCoordinateBound
    P f hf hfBound c hc
  rw [← hLaw] at hProduct
  have hPull := HasSubgaussianMGF.of_map hR.aemeasurable hProduct
  have hIntegralMap :
      (∫ y, f y ∂mu.map R) = ∫ omega, f (R omega) ∂mu := by
    exact integral_map hR.aemeasurable hf.aestronglyMeasurable
  apply hPull.congr
  exact ae_of_all _ fun omega ↦ by
    change f (R omega) - ∫ y, f y ∂mu.map R =
      f (R omega) - ∫ omega', f (R omega') ∂mu
    rw [hIntegralMap]

/-- Direct complex McDiarmid concentration for independent coordinates.

The conclusion is a probability inequality, not a Doob/martingale/tail certificate.  Its only
probabilistic premise is independence of the genuine coordinates; all four scalar tails and their
union bound are derived internally.  The variance proxy is `∑ i, c i²`, as in the product theorem
above. -/
theorem probabilityAtLeast_complexConcentrationGood_of_iIndepFun_finCoordinateBound
    {n : ℕ} (X : Fin n → Omega → B)
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X mu)
    (trace : (Fin n → B) → ℂ) (htrace : StronglyMeasurable trace)
    {L : ℝ} (htraceBound : ∀ x, ‖trace x‖ ≤ L)
    (c : Fin n → ℝ≥0)
    (hcoord : ∀ i x y,
      ‖trace x - trace (Function.update x i y)‖ ≤ (c i : ℝ))
    {bound : ℝ} (hbound : 0 ≤ bound) :
    ProbabilityAtLeast mu
      (ComplexConcentrationGood
        (fun omega ↦ trace (fun i ↦ X i omega))
        (∫ omega, trace (fun i ↦ X i omega) ∂mu) bound)
      (1 - 4 * exp (-(bound / 2) ^ 2 /
        (2 * (((∑ i, (c i) ^ 2 : ℝ≥0)) : ℝ)))) := by
  let R : Omega → (Fin n → B) := fun omega i ↦ X i omega
  have hR : Measurable R := measurable_pi_lambda _ hX
  have htraceOmega : Measurable (fun omega ↦ trace (R omega)) :=
    htrace.measurable.comp hR
  have htraceInt : Integrable (fun omega ↦ trace (R omega)) mu := by
    apply Integrable.of_bound htraceOmega.aestronglyMeasurable L
    exact ae_of_all _ fun omega ↦ htraceBound (R omega)
  have hreMeas : StronglyMeasurable (fun x ↦ (trace x).re) :=
    Complex.continuous_re.comp_stronglyMeasurable htrace
  have himMeas : StronglyMeasurable (fun x ↦ (trace x).im) :=
    Complex.continuous_im.comp_stronglyMeasurable htrace
  have hreBound : FinProductBounded (fun x ↦ (trace x).re) L := by
    intro x
    exact (Complex.abs_re_le_norm (trace x)).trans (htraceBound x)
  have himBound : FinProductBounded (fun x ↦ (trace x).im) L := by
    intro x
    exact (Complex.abs_im_le_norm (trace x)).trans (htraceBound x)
  have hreCoord : FinCoordinateBound (fun x ↦ (trace x).re) c := by
    intro i x y
    calc
      |(trace x).re - (trace (Function.update x i y)).re| =
          |(trace x - trace (Function.update x i y)).re| := by rw [Complex.sub_re]
      _ ≤ ‖trace x - trace (Function.update x i y)‖ := Complex.abs_re_le_norm _
      _ ≤ (c i : ℝ) := hcoord i x y
  have himCoord : FinCoordinateBound (fun x ↦ (trace x).im) c := by
    intro i x y
    calc
      |(trace x).im - (trace (Function.update x i y)).im| =
          |(trace x - trace (Function.update x i y)).im| := by rw [Complex.sub_im]
      _ ≤ ‖trace x - trace (Function.update x i y)‖ := Complex.abs_im_le_norm _
      _ ≤ (c i : ℝ) := hcoord i x y
  have hre := hasSubgaussianMGF_centered_of_iIndepFun_finCoordinateBound
    X hX hIndep (fun x ↦ (trace x).re) hreMeas hreBound c hreCoord
  have him := hasSubgaussianMGF_centered_of_iIndepFun_finCoordinateBound
    X hX hIndep (fun x ↦ (trace x).im) himMeas himBound c himCoord
  have hreMean : (∫ omega, (trace (R omega)).re ∂mu) =
      (∫ omega, trace (R omega) ∂mu).re := integral_re htraceInt
  have himMean : (∫ omega, (trace (R omega)).im ∂mu) =
      (∫ omega, trace (R omega) ∂mu).im := integral_im htraceInt
  apply probabilityAtLeast_complexConcentrationGood_of_four_tails
    htraceOmega hbound
  · have h := hre.measure_ge_le (by positivity : 0 ≤ bound / 2)
    rw [hreMean] at h
    simpa only [centeredUpperTail, R] using h
  · have h := hre.neg.measure_ge_le (by positivity : 0 ≤ bound / 2)
    rw [hreMean] at h
    simpa only [centeredLowerTail, Pi.neg_apply, R] using h
  · have h := him.measure_ge_le (by positivity : 0 ≤ bound / 2)
    rw [himMean] at h
    simpa only [centeredUpperTail, R] using h
  · have h := him.neg.measure_ge_le (by positivity : 0 ≤ bound / 2)
    rw [himMean] at h
    simpa only [centeredLowerTail, Pi.neg_apply, R] using h

end IndependentCoordinates

section ActualRandomMatrixModel

variable {Omega OmegaXi : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
  {mu : Measure Omega} {nu : Measure OmegaXi}
  [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]

/-- The genuine random-matrix specialization of the preceding independent-coordinate theorem.

This is v3 Proposition 3.4, proof step (3), before choosing the numerical threshold.  The theorem
has no Doob, martingale, or tail premise: row independence is derived from the model's independent
entries, the deterministic coordinate estimate is `norm_stieltjesTrace_sub_le_of_differsOnlyOnRow`,
and measurability/integrability follow from the finite-dimensional resolvent construction and its
upper-half-plane norm bound. -/
theorem probabilityAtLeast_stieltjesTrace_complexConcentrationGood_of_randomMatrixModel
    {n : ℕ} (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (z : ℂ) {eta : ℂ} (heta : 0 < eta.im) (hn : 2 ≤ n)
    {bound : ℝ} (hbound : 0 ≤ bound) :
    ProbabilityAtLeast mu
      (ComplexConcentrationGood
        (fun omega ↦ stieltjesTrace (model.matrix omega) z eta)
        (∫ omega, stieltjesTrace (model.matrix omega) z eta ∂mu) bound)
      (1 - 4 * exp (-(bound / 2) ^ 2 /
        (2 * (((∑ _i : Fin n,
          (Real.toNNReal (2 / ((n : ℝ) * eta.im))) ^ 2 : ℝ≥0)) : ℝ)))) := by
  let _ : NeZero n := ⟨by omega⟩
  let traceRows : (Fin n → (Fin n → ℂ)) → ℂ :=
    fun rows ↦ stieltjesTrace (fun i j ↦ rows i j) z eta
  have hentryRows (i j : Fin n) :
      Measurable (fun rows : Fin n → (Fin n → ℂ) ↦ rows i j) :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  have htraceRows : StronglyMeasurable traceRows := by
    exact (measurable_stieltjesTrace hentryRows z eta).stronglyMeasurable
  have htraceRowsBound : ∀ rows, ‖traceRows rows‖ ≤ eta.im⁻¹ := by
    intro rows
    exact norm_stieltjesTrace_le_inv_im (fun i j ↦ rows i j) z heta
  have hsensitivityNonneg : 0 ≤ 2 / ((n : ℝ) * eta.im) := by positivity
  have hsensitivityCoe :
      (Real.toNNReal (2 / ((n : ℝ) * eta.im)) : ℝ) =
        2 / ((n : ℝ) * eta.im) :=
    Real.coe_toNNReal _ hsensitivityNonneg
  have hcoord : ∀ (i : Fin n) rows row,
      ‖traceRows rows - traceRows (Function.update rows i row)‖ ≤
        (Real.toNNReal (2 / ((n : ℝ) * eta.im)) : ℝ) := by
    intro i rows row
    rw [hsensitivityCoe]
    apply norm_stieltjesTrace_sub_le_of_differsOnlyOnRow
      (fun k j ↦ rows k j)
      (fun k j ↦ Function.update rows i row k j) z heta i
    intro k j hki
    simp [Function.update, hki]
  have h :=
    probabilityAtLeast_complexConcentrationGood_of_iIndepFun_finCoordinateBound
      (fun i omega j ↦ model.matrix omega i j)
      model.row_measurable model.rows_independent
      traceRows htraceRows htraceRowsBound
      (fun _i ↦ Real.toNNReal (2 / ((n : ℝ) * eta.im))) hcoord hbound
  simpa only [traceRows] using h

/-- Exact exponent arithmetic for the direct-product proxy used in this file.  With row
sensitivity `2/(n v)` and threshold constant `32`, every one-sided scalar tail is `n⁻³²`, so
the four-tail complex bound is `4 n⁻³²`. -/
theorem four_exp_fin_product_threshold_thirtytwo_eq_four_mul_zpow_neg32
    {n : ℕ} (hn : 2 ≤ n) {v : ℝ} (hv : 0 < v) :
    4 * exp
      (-((32 * Real.sqrt (Real.log (n : ℝ)) /
          (Real.sqrt (n : ℝ) * v)) / 2) ^ 2 /
        (2 * (((∑ _i : Fin n,
          (Real.toNNReal (2 / ((n : ℝ) * v))) ^ 2 : ℝ≥0)) : ℝ))) =
      4 * (n : ℝ) ^ (-32 : ℤ) := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hnOne : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hnPos.ne')
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnOne
  have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  let d : ℝ≥0 := Real.toNNReal (2 / ((n : ℝ) * v))
  let Q : ℝ := (((∑ _i : Fin n, d ^ 2 : ℝ≥0)) : ℝ)
  have hdCoe : (d : ℝ) = 2 / ((n : ℝ) * v) := by
    exact Real.coe_toNNReal _ (by positivity)
  have hQformula : Q = 4 / ((n : ℝ) * v ^ 2) := by
    dsimp [Q]
    push_cast
    simp [hdCoe]
    field_simp [hnR.ne', hv.ne']
    ring
  have hnumerator :
      ((32 * Real.sqrt (Real.log (n : ℝ)) /
        (Real.sqrt (n : ℝ) * v)) / 2) ^ 2 =
        256 * Real.log (n : ℝ) / ((n : ℝ) * v ^ 2) := by
    field_simp [hsqrtn.ne', hv.ne', hnR.ne']
    nlinarith [Real.sq_sqrt hlog, Real.sq_sqrt hnR.le]
  have hquotient :
      ((32 * Real.sqrt (Real.log (n : ℝ)) /
        (Real.sqrt (n : ℝ) * v)) / 2) ^ 2 / (2 * Q) =
        32 * Real.log (n : ℝ) := by
    rw [hnumerator, hQformula]
    field_simp [hnR.ne', hv.ne']
    ring
  have hexpPower :
      exp (-(32 * Real.log (n : ℝ))) = (n : ℝ) ^ (-32 : ℤ) := by
    rw [show -(32 * Real.log (n : ℝ)) =
        Real.log ((n : ℝ) ^ (-32 : ℤ)) by
      rw [Real.log_zpow]
      norm_num]
    exact Real.exp_log (zpow_pos hnR _)
  change 4 * exp
      (-((32 * Real.sqrt (Real.log (n : ℝ)) /
        (Real.sqrt (n : ℝ) * v)) / 2) ^ 2 / (2 * Q)) =
      4 * (n : ℝ) ^ (-32 : ℤ)
  rw [neg_div, hquotient, hexpPower]

/-- The unrelaxed pointwise probability needed before the finite `eta`-net union bound.

This theorem is the actual `RandomMatrixModelV3.rows` route and has no conclusion-valued input:
the good event at threshold constant `32` has probability at least `1 - 4 n⁻³²`. -/
theorem probabilityAtLeast_stieltjesTrace_complexConcentrationGood_v3_thirtytwo_n32
    {n : ℕ} (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (z : ℂ) {eta : ℂ} (heta : 0 < eta.im) (hn : 2 ≤ n) :
    ProbabilityAtLeast mu
      (ComplexConcentrationGood
        (fun omega ↦ stieltjesTrace (model.matrix omega) z eta)
        (∫ omega, stieltjesTrace (model.matrix omega) z eta ∂mu)
        (32 * Real.sqrt (Real.log (n : ℝ)) /
          (Real.sqrt (n : ℝ) * eta.im)))
      (1 - 4 * (n : ℝ) ^ (-32 : ℤ)) := by
  have hbound : 0 ≤ 32 * Real.sqrt (Real.log (n : ℝ)) /
      (Real.sqrt (n : ℝ) * eta.im) := by positivity
  have hbase :=
    probabilityAtLeast_stieltjesTrace_complexConcentrationGood_of_randomMatrixModel
      model z heta hn hbound
  rw [four_exp_fin_product_threshold_thirtytwo_eq_four_mul_zpow_neg32 hn heta] at hbase
  exact hbase

/-- v3 Proposition 3.4, proof step (3), with the numerical probability `1 - n⁻¹⁰`.

Our direct product proof assigns proxy `cᵢ²` rather than the sharper Hoeffding proxy `cᵢ²/4`.
Accordingly the displayed threshold uses the harmless absolute constant `32` instead of `16`.
The exponent is exactly the same: both numerator and proxy are four times their sharp versions. -/
theorem probabilityAtLeast_stieltjesTrace_complexConcentrationGood_v3_thirtytwo
    {n : ℕ} (model : RandomMatrixModelV3 n Omega OmegaXi mu nu)
    (z : ℂ) {eta : ℂ} (heta : 0 < eta.im) (hn : 2 ≤ n) :
    ProbabilityAtLeast mu
      (ComplexConcentrationGood
        (fun omega ↦ stieltjesTrace (model.matrix omega) z eta)
        (∫ omega, stieltjesTrace (model.matrix omega) z eta ∂mu)
        (32 * Real.sqrt (Real.log (n : ℝ)) /
          (Real.sqrt (n : ℝ) * eta.im)))
      (1 - (n : ℝ) ^ (-10 : ℤ)) := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  let d : ℝ≥0 := Real.toNNReal (2 / ((n : ℝ) * eta.im))
  let cNat : ℕ → ℝ≥0 := fun _ ↦ d
  let A : ℝ := Real.sqrt (Real.log (n : ℝ)) /
    (Real.sqrt (n : ℝ) * eta.im)
  let S : ℝ := (((∑ i ∈ Finset.range n, (cNat i / 2) ^ 2 : ℝ≥0)) : ℝ)
  let Q : ℝ := (((∑ _i : Fin n, d ^ 2 : ℝ≥0)) : ℝ)
  have hdPos : 0 < d := by
    dsimp [d]
    exact Real.toNNReal_pos.mpr (by positivity)
  have hcNat : ∀ i < n, (cNat i : ℝ) ≤ 2 / ((n : ℝ) * eta.im) := by
    intro i hi
    change (d : ℝ) ≤ 2 / ((n : ℝ) * eta.im)
    have hdCoe : (d : ℝ) = 2 / ((n : ℝ) * eta.im) := by
      exact Real.coe_toNNReal _ (by positivity)
    exact hdCoe.le
  have hpos : ∃ i < n, 0 < cNat i := ⟨0, hnPos, by simpa [cNat] using hdPos⟩
  have hSPos : 0 < S := by
    exact mcdiarmid_proxy_sum_pos_of_one_pos hpos
  have hQeq : Q = 4 * S := by
    dsimp [Q, S, cNat]
    push_cast
    simp
    ring
  have hold := four_exp_mcdiarmid_threshold_sixteen_le_of_one_pos
    hn heta hcNat hpos
  have hA16 : 16 * A =
      16 * Real.sqrt (Real.log (n : ℝ)) /
        (Real.sqrt (n : ℝ) * eta.im) := by
    dsimp [A]
    ring
  have hold' : 4 * exp (-((16 * A) / 2) ^ 2 / (2 * S)) ≤
      (n : ℝ) ^ (-10 : ℤ) := by
    rw [hA16]
    exact hold
  have harg :
      -((32 * A) / 2) ^ 2 / (2 * Q) =
        -((16 * A) / 2) ^ 2 / (2 * S) := by
    rw [hQeq]
    field_simp [hSPos.ne']
    ring
  have hexponent :
      4 * exp (-((32 * A) / 2) ^ 2 / (2 * Q)) ≤
        (n : ℝ) ^ (-10 : ℤ) := by
    rw [harg]
    exact hold'
  have hbound : 0 ≤ 32 * Real.sqrt (Real.log (n : ℝ)) /
      (Real.sqrt (n : ℝ) * eta.im) := by positivity
  have hbase :=
    probabilityAtLeast_stieltjesTrace_complexConcentrationGood_of_randomMatrixModel
      model z heta hn hbound
  have hA32 : 32 * A =
      32 * Real.sqrt (Real.log (n : ℝ)) /
        (Real.sqrt (n : ℝ) * eta.im) := by
    dsimp [A]
    ring
  have htailEq :
      1 - 4 * exp (-((32 * A) / 2) ^ 2 / (2 * Q)) =
        1 - 4 * exp
          (-((32 * Real.sqrt (Real.log (n : ℝ)) /
              (Real.sqrt (n : ℝ) * eta.im)) / 2) ^ 2 /
            (2 * (((∑ _i : Fin n,
              (Real.toNNReal (2 / ((n : ℝ) * eta.im))) ^ 2 : ℝ≥0)) : ℝ))) := by
    rw [hA32]
  have horder :
      ENNReal.ofReal (1 - (n : ℝ) ^ (-10 : ℤ)) ≤
        ENNReal.ofReal (1 - 4 * exp (-((32 * A) / 2) ^ 2 / (2 * Q))) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  rw [htailEq] at horder
  exact horder.trans hbase

end ActualRandomMatrixModel

end Arxiv2410V3

