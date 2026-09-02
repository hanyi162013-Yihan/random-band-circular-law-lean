import CircularLawSection4.IIDOperatorAffineSmallBall
import CircularLawSection4.RawContinuousEfronStein
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Arbitrary-coordinate IID fibers and L2 resampling

The recursive finite IID law can be split at any coordinate, not only at its
last coordinate.  We record Tonelli and Bochner-Fubini formulas using
`Fin.insertNth`, then use them to turn a uniform conditional square bound
around a frozen fiber center into the raw Efron--Stein replacement bound
`4 * V`.
-/

open scoped ENNReal BigOperators
open MeasureTheory ProbabilityTheory

namespace CircularLawSection4

universe u v

section FiberFubini

variable {K : Type u} [MeasurableSpace K]
  (ν : Measure K) [SigmaFinite ν]

/-- Tonelli's formula for the recursive IID law, with an arbitrary selected
coordinate integrated on the inside. -/
theorem lintegral_iidMeasure_insertNth {n : ℕ} (s : Fin (n + 1))
    (g : (Fin (n + 1) → K) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, g x ∂iidMeasure ν (n + 1)) =
      ∫⁻ y, ∫⁻ a, g (s.insertNth a y) ∂ν ∂iidMeasure ν n := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => K) s
  have hpres : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) => ν))
      (ν.prod (Measure.pi (fun _ : Fin n => ν))) := by
    simpa only [e] using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ν) s)
  have hcomp : Measurable (fun p : K × (Fin n → K) => g (e.symm p)) :=
    hg.comp e.symm.measurable
  calc
    (∫⁻ x, g x ∂iidMeasure ν (n + 1)) =
        ∫⁻ x, g x ∂Measure.pi (fun _ : Fin (n + 1) => ν) := by
      rw [iidMeasure_eq_pi]
    _ = ∫⁻ p, g (e.symm p)
          ∂ν.prod (Measure.pi (fun _ : Fin n => ν)) :=
      (hpres.symm.lintegral_comp_emb e.symm.measurableEmbedding g).symm
    _ = ∫⁻ y, ∫⁻ a, g (e.symm (a, y)) ∂ν
          ∂Measure.pi (fun _ : Fin n => ν) :=
      lintegral_prod_symm _ hcomp.aemeasurable
    _ = ∫⁻ y, ∫⁻ a, g (s.insertNth a y) ∂ν
          ∂iidMeasure ν n := by
      rw [iidMeasure_eq_pi]
      congr 1

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Integrability itself is invariant under splitting off an arbitrary IID
coordinate. -/
theorem integrable_iidMeasure_insertNth_iff {n : ℕ} (s : Fin (n + 1))
    (g : (Fin (n + 1) → K) → E) :
    Integrable g (iidMeasure ν (n + 1)) ↔
      Integrable (fun p : K × (Fin n → K) => g (s.insertNth p.1 p.2))
        (ν.prod (iidMeasure ν n)) := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => K) s
  have hpres : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) => ν))
      (ν.prod (Measure.pi (fun _ : Fin n => ν))) := by
    simpa only [e] using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ν) s)
  rw [iidMeasure_eq_pi, iidMeasure_eq_pi]
  have hiff := hpres.symm.integrable_comp_emb
    e.symm.measurableEmbedding (g := g)
  simpa only [Function.comp_def, e,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk] using hiff.symm

/-- Bochner-Fubini for the recursive IID law at an arbitrary coordinate. -/
theorem integral_iidMeasure_insertNth {n : ℕ} (s : Fin (n + 1))
    (g : (Fin (n + 1) → K) → E)
    (hg : Integrable g (iidMeasure ν (n + 1))) :
    (∫ x, g x ∂iidMeasure ν (n + 1)) =
      ∫ y, ∫ a, g (s.insertNth a y) ∂ν ∂iidMeasure ν n := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => K) s
  have hpres : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) => ν))
      (ν.prod (Measure.pi (fun _ : Fin n => ν))) := by
    simpa only [e] using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ν) s)
  have hgpi : Integrable g (Measure.pi (fun _ : Fin (n + 1) => ν)) := by
    simpa only [iidMeasure_eq_pi] using hg
  have hcomp : Integrable (fun p : K × (Fin n → K) => g (e.symm p))
      (ν.prod (Measure.pi (fun _ : Fin n => ν))) :=
    hpres.symm.integrable_comp_of_integrable hgpi
  calc
    (∫ x, g x ∂iidMeasure ν (n + 1)) =
        ∫ x, g x ∂Measure.pi (fun _ : Fin (n + 1) => ν) := by
      rw [iidMeasure_eq_pi]
    _ = ∫ p, g (e.symm p)
          ∂ν.prod (Measure.pi (fun _ : Fin n => ν)) :=
      (hpres.symm.integral_comp' g).symm
    _ = ∫ y, ∫ a, g (e.symm (a, y)) ∂ν
          ∂Measure.pi (fun _ : Fin n => ν) :=
      integral_prod_symm _ hcomp
    _ = ∫ y, ∫ a, g (s.insertNth a y) ∂ν
          ∂iidMeasure ν n := by
      rw [iidMeasure_eq_pi]
      congr 1

/-- Integrating along the selected coordinate preserves integrability on
the remaining-coordinate IID law. -/
theorem integrable_integral_insertNth_of_integrable_iid {n : ℕ}
    [IsProbabilityMeasure ν]
    (s : Fin (n + 1)) (g : (Fin (n + 1) → K) → E)
    (hg : Integrable g (iidMeasure ν (n + 1))) :
    Integrable (fun y => ∫ a, g (s.insertNth a y) ∂ν)
      (iidMeasure ν n) := by
  let _ := iidMeasure_isProbability ν n
  have hprod :=
    (integrable_iidMeasure_insertNth_iff ν s g).mp hg
  exact hprod.integral_prod_right

end FiberFubini

section RawFiber

variable {K : Type u} [MeasurableSpace K]
  (ν : Measure K) [SigmaFinite ν] [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
/-- The raw replacement energy at an arbitrary coordinate is the expected
two-sample square difference on the corresponding frozen fiber. -/
theorem iidRawResamplingEnergy_eq_integral_fiber {n : ℕ}
    (f : (Fin (n + 1) → K) → ℝ) (s : Fin (n + 1))
    (hrawOuter : Integrable (fun x => ∫ a',
      (f x - f (Function.update x s a')) ^ 2 ∂ν)
      (iidMeasure ν (n + 1))) :
    iidRawResamplingEnergy ν f s =
      ∫ y, ∫ a, ∫ a',
        (f (s.insertNth a y) - f (s.insertNth a' y)) ^ 2
        ∂ν ∂ν ∂iidMeasure ν n := by
  unfold iidRawResamplingEnergy
  rw [integral_iidMeasure_insertNth ν s _ hrawOuter]
  simp only [Fin.update_insertNth]

/-- A uniform conditional `L²` bound around an arbitrary frozen fiber center
controls the raw replacement energy by `4 * V`.

The explicit integrability assumptions are exactly those needed for the
Bochner integrals in the pointwise two-sample comparison.  Integrability of
the outer frozen-fiber energy is derived from `hrawOuter` by the IID splitting
equivalence. -/
theorem iidRawResamplingEnergy_le_four_mul_of_fiber_center
    {n : ℕ} (f : (Fin (n + 1) → K) → ℝ) (s : Fin (n + 1))
    (center : (Fin n → K) → ℝ) {V : ℝ}
    (hrawOuter : Integrable (fun x => ∫ a',
      (f x - f (Function.update x s a')) ^ 2 ∂ν)
      (iidMeasure ν (n + 1)))
    (hrawPair : ∀ y a, Integrable (fun a' =>
      (f (s.insertNth a y) - f (s.insertNth a' y)) ^ 2) ν)
    (hrawFiber : ∀ y, Integrable (fun a => ∫ a',
      (f (s.insertNth a y) - f (s.insertNth a' y)) ^ 2 ∂ν) ν)
    (hcenterFiber : ∀ y, Integrable (fun a =>
      (f (s.insertNth a y) - center y) ^ 2) ν)
    (hcenter : ∀ y, ∫ a,
      (f (s.insertNth a y) - center y) ^ 2 ∂ν ≤ V) :
    iidRawResamplingEnergy ν f s ≤ 4 * V := by
  let _ := iidMeasure_isProbability ν n
  let rawInner : (Fin (n + 1) → K) → ℝ := fun x => ∫ a',
    (f x - f (Function.update x s a')) ^ 2 ∂ν
  have hrawFiberOuter : Integrable (fun y => ∫ a, ∫ a',
      (f (s.insertNth a y) - f (s.insertNth a' y)) ^ 2 ∂ν ∂ν)
      (iidMeasure ν n) := by
    have hout := integrable_integral_insertNth_of_integrable_iid
      ν s rawInner hrawOuter
    simpa only [rawInner, Fin.update_insertNth] using hout
  have hfiberBound (y : Fin n → K) :
      (∫ a, ∫ a',
        (f (s.insertNth a y) - f (s.insertNth a' y)) ^ 2 ∂ν ∂ν) ≤
        4 * V := by
    let err : K → ℝ := fun a => f (s.insertNth a y) - center y
    have hinner (a : K) :
        (∫ a',
          (f (s.insertNth a y) - f (s.insertNth a' y)) ^ 2 ∂ν) ≤
          2 * err a ^ 2 + 2 * ∫ a', err a' ^ 2 ∂ν := by
      calc
        (∫ a',
            (f (s.insertNth a y) - f (s.insertNth a' y)) ^ 2 ∂ν) ≤
            ∫ a', (2 * err a ^ 2 + 2 * err a' ^ 2) ∂ν := by
          apply integral_mono (hrawPair y a)
            ((integrable_const _).add ((hcenterFiber y).const_mul 2))
          intro a'
          change
            (f (s.insertNth a y) - f (s.insertNth a' y)) ^ 2 ≤
              2 * (f (s.insertNth a y) - center y) ^ 2 +
                2 * (f (s.insertNth a' y) - center y) ^ 2
          have hdiff :
              f (s.insertNth a y) - f (s.insertNth a' y) =
                (f (s.insertNth a y) - center y) -
                  (f (s.insertNth a' y) - center y) := by ring
          rw [hdiff]
          nlinarith [sq_nonneg
            ((f (s.insertNth a y) - center y) +
              (f (s.insertNth a' y) - center y))]
        _ = 2 * err a ^ 2 + 2 * ∫ a', err a' ^ 2 ∂ν := by
          rw [integral_add (integrable_const _)
              ((hcenterFiber y).const_mul 2),
            integral_const_mul (μ := ν) 2 (fun _a' : K => err a ^ 2),
            integral_const_mul (μ := ν) 2 (fun a' => err a' ^ 2)]
          simp
    have hright : Integrable (fun a =>
        2 * err a ^ 2 + 2 * ∫ a', err a' ^ 2 ∂ν) ν :=
      ((hcenterFiber y).const_mul 2).add (integrable_const _)
    calc
      (∫ a, ∫ a',
          (f (s.insertNth a y) - f (s.insertNth a' y)) ^ 2 ∂ν ∂ν) ≤
          ∫ a, (2 * err a ^ 2 +
            2 * ∫ a', err a' ^ 2 ∂ν) ∂ν :=
        integral_mono (hrawFiber y) hright hinner
      _ = 4 * ∫ a, err a ^ 2 ∂ν := by
        rw [integral_add ((hcenterFiber y).const_mul 2) (integrable_const _),
          integral_const_mul, integral_const]
        simp
        ring
      _ ≤ 4 * V := by
        gcongr
        simpa only [err] using hcenter y
  rw [iidRawResamplingEnergy_eq_integral_fiber ν f s hrawOuter]
  calc
    (∫ y, ∫ a, ∫ a',
        (f (s.insertNth a y) - f (s.insertNth a' y)) ^ 2
        ∂ν ∂ν ∂iidMeasure ν n) ≤
        ∫ _y : Fin n → K, 4 * V ∂iidMeasure ν n := by
      apply integral_mono hrawFiberOuter (integrable_const _)
      exact hfiberBound
    _ = 4 * V := by simp

end RawFiber

end CircularLawSection4
