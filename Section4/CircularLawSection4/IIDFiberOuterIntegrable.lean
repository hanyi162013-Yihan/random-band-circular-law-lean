import CircularLawSection4.IIDFiberMemLpResampling

/-!
# Uniform L2 fibers imply outer replacement integrability

The unbounded Efron--Stein interface uses a Bochner integral of the
one-coordinate replacement energy.  A uniform conditional `L²` estimate is
already enough to make that outer integral integrable: after splitting off
the selected coordinate, the fiber center cancels between two independent
copies.  This file records the resulting measure-theoretic closure.
-/

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace CircularLawSection4

universe u

variable {K : Type u} [MeasurableSpace K]
  (nu : Measure K) [SigmaFinite nu] [IsProbabilityMeasure nu]

/-- Insertion of a selected coordinate, with both the inserted coordinate
and the complementary tuple allowed to vary, is measurable. -/
theorem measurable_fin_insertNth_uncurry {n : Nat} (s : Fin (n + 1)) :
    Measurable (fun p : K × (Fin n -> K) =>
      @Fin.insertNth n (fun _ => K) s p.1 p.2) := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => K) s
  simpa only [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk] using e.symm.measurable

/-- A measurable observable with a uniformly bounded `L²` error on every
frozen selected-coordinate fiber automatically satisfies the outer Bochner
integrability hypothesis for its raw replacement energy.

No measurability or integrability of the fiber center is needed: it cancels
from the difference of the original and independently replaced coordinate.
-/
theorem iidRawResamplingOuter_integrable_of_fiber_memLp
    {n : Nat} (f : (Fin (n + 1) -> K) -> Real) (hf : Measurable f)
    (s : Fin (n + 1)) (center : (Fin n -> K) -> Real) {V : Real}
    (hfiber : forall y, MemLp (fun a =>
      f (@Fin.insertNth n (fun _ => K) s a y) - center y) 2 nu)
    (hbound : forall y, integral nu (fun a =>
      (f (@Fin.insertNth n (fun _ => K) s a y) - center y) ^ 2) <= V) :
    Integrable (fun x => integral nu (fun a' =>
      (f x - f (Function.update x s a')) ^ 2))
      (iidMeasure nu (n + 1)) := by
  let Y := Fin n -> K
  let raw : Y -> K -> K -> Real := fun y a a' =>
    (f (@Fin.insertNth n (fun _ => K) s a y) -
      f (@Fin.insertNth n (fun _ => K) s a' y)) ^ 2
  let rawInner : (Fin (n + 1) -> K) -> Real := fun x => integral nu (fun a' =>
    (f x - f (Function.update x s a')) ^ 2)
  let _ := iidMeasure_isProbability nu n

  have hinsert : Measurable (fun p : K × Y =>
      @Fin.insertNth n (fun _ => K) s p.1 p.2) :=
    measurable_fin_insertNth_uncurry s
  have hfirst : Measurable (fun p : (K × Y) × K =>
      @Fin.insertNth n (fun _ => K) s p.1.1 p.1.2) :=
    hinsert.comp measurable_fst
  have hsecond : Measurable (fun p : (K × Y) × K =>
      @Fin.insertNth n (fun _ => K) s p.2 p.1.2) :=
    hinsert.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hrawMeas : Measurable (fun p : (K × Y) × K =>
      raw p.1.2 p.1.1 p.2) := by
    simpa only [raw, Function.comp_apply, Pi.sub_apply, Pi.pow_apply] using
      ((hf.comp hfirst).sub (hf.comp hsecond)).pow_const 2
  have hinnerStrong : StronglyMeasurable (fun p : K × Y =>
      integral nu (fun a' => raw p.2 p.1 a')) := by
    simpa only [Function.uncurry_apply_pair] using
      hrawMeas.stronglyMeasurable.integral_prod_right
  have henergyStrong : StronglyMeasurable (fun y : Y =>
      integral nu (fun a => integral nu (fun a' => raw y a a'))) := by
    simpa only using hinnerStrong.integral_prod_left'

  have herrInt (y : Y) : Integrable (fun a =>
      (f (@Fin.insertNth n (fun _ => K) s a y) - center y) ^ 2) nu :=
    (hfiber y).integrable_sq
  have hpairOneInt (y : Y) (a : K) : Integrable (fun a' =>
      raw y a a') nu := by
    let err : K -> Real := fun b =>
      f (@Fin.insertNth n (fun _ => K) s b y) - center y
    have hmem : MemLp (fun a' => err a - err a') 2 nu :=
      (memLp_const (err a)).sub (hfiber y)
    have hint := hmem.integrable_sq
    convert hint using 1
    funext a'
    dsimp only [raw, err]
    ring
  have hpairInt (y : Y) : Integrable (fun p : K × K =>
      raw y p.1 p.2) (nu.prod nu) := by
    let err : K -> Real := fun a =>
      f (@Fin.insertNth n (fun _ => K) s a y) - center y
    have hfst : MemLp (fun p : K × K => err p.1) 2 (nu.prod nu) :=
      (hfiber y).comp_fst nu
    have hsnd : MemLp (fun p : K × K => err p.2) 2 (nu.prod nu) :=
      (hfiber y).comp_snd nu
    have hdiff := (hfst.sub hsnd).integrable_sq
    convert hdiff using 1
    funext p
    change
      (f (@Fin.insertNth n (fun _ => K) s p.1 y) -
          f (@Fin.insertNth n (fun _ => K) s p.2 y)) ^ 2 =
        ((f (@Fin.insertNth n (fun _ => K) s p.1 y) - center y) -
          (f (@Fin.insertNth n (fun _ => K) s p.2 y) - center y)) ^ 2
    ring
  have hiterInt (y : Y) : Integrable (fun a =>
      integral nu (fun a' => raw y a a')) nu := by
    simpa only using (hpairInt y).integral_prod_left
  have hinnerNonneg (y : Y) (a : K) :
      0 <= integral nu (fun a' => raw y a a') := by
    apply integral_nonneg
    intro a'
    exact sq_nonneg _
  have henergyNonneg (y : Y) :
      0 <= integral nu (fun a => integral nu (fun a' => raw y a a')) := by
    apply integral_nonneg
    exact hinnerNonneg y

  have henergyBound (y : Y) :
      integral nu (fun a => integral nu (fun a' => raw y a a')) <=
        4 * V := by
    let err : K -> Real := fun a =>
      f (@Fin.insertNth n (fun _ => K) s a y) - center y
    have hinner (a : K) :
        integral nu (fun a' => raw y a a') <=
          2 * err a ^ 2 + 2 * integral nu (fun a' => err a' ^ 2) := by
      calc
        integral nu (fun a' => raw y a a') <=
            integral nu (fun a' => 2 * err a ^ 2 + 2 * err a' ^ 2) := by
          apply integral_mono
          · exact hpairOneInt y a
          · exact (integrable_const _).add ((herrInt y).const_mul 2)
          · intro a'
            dsimp only [raw, err]
            have hrewrite :
                f (@Fin.insertNth n (fun _ => K) s a y) -
                    f (@Fin.insertNth n (fun _ => K) s a' y) =
                  (f (@Fin.insertNth n (fun _ => K) s a y) - center y) -
                    (f (@Fin.insertNth n (fun _ => K) s a' y) - center y) := by ring
            rw [hrewrite]
            nlinarith [sq_nonneg
              ((f (@Fin.insertNth n (fun _ => K) s a y) - center y) +
                (f (@Fin.insertNth n (fun _ => K) s a' y) - center y))]
        _ = 2 * err a ^ 2 +
            2 * integral nu (fun a' => err a' ^ 2) := by
          rw [integral_add (integrable_const _)
              ((herrInt y).const_mul 2),
            integral_const_mul (μ := nu) 2 (fun _a' : K => err a ^ 2),
            integral_const_mul (μ := nu) 2 (fun a' => err a' ^ 2)]
          simp
    have hright : Integrable (fun a =>
        2 * err a ^ 2 + 2 * integral nu (fun a' => err a' ^ 2)) nu :=
      ((herrInt y).const_mul 2).add (integrable_const _)
    calc
      integral nu (fun a => integral nu (fun a' => raw y a a')) <=
          integral nu (fun a =>
            2 * err a ^ 2 + 2 * integral nu (fun a' => err a' ^ 2)) :=
        integral_mono (hiterInt y) hright hinner
      _ = 4 * integral nu (fun a => err a ^ 2) := by
        rw [integral_add ((herrInt y).const_mul 2) (integrable_const _),
          integral_const_mul, integral_const]
        simp
        ring
      _ <= 4 * V := by
        gcongr
        simpa only [err] using hbound y

  have henergyInt : Integrable (fun y : Y =>
      integral nu (fun a => integral nu (fun a' => raw y a a')))
      (iidMeasure nu n) := by
    apply Integrable.of_bound henergyStrong.aestronglyMeasurable (4 * V)
    exact ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (henergyNonneg y)]
      exact henergyBound y
  have hnormEnergyInt : Integrable (fun y : Y =>
      integral nu (fun a =>
        norm (integral nu (fun a' => raw y a a'))))
      (iidMeasure nu n) := by
    convert henergyInt using 1
    funext y
    apply integral_congr_ae
    exact ae_of_all _ fun a => by
      change norm (integral nu (fun a' => raw y a a')) =
        integral nu (fun a' => raw y a a')
      rw [Real.norm_eq_abs, abs_of_nonneg (hinnerNonneg y a)]

  have hsplit : Integrable (fun p : K × Y =>
      integral nu (fun a' => raw p.2 p.1 a'))
      (nu.prod (iidMeasure nu n)) := by
    apply (integrable_prod_iff' hinnerStrong.aestronglyMeasurable).2
    exact ⟨ae_of_all _ hiterInt, hnormEnergyInt⟩
  apply (integrable_iidMeasure_insertNth_iff nu s rawInner).2
  simpa only [rawInner, raw, Fin.update_insertNth] using hsplit

/-- The raw replacement-energy estimate with its outer integrability
hypothesis discharged automatically from the same uniform fiber `L²` data. -/
theorem iidRawResamplingEnergy_le_four_mul_of_fiber_memLp_auto
    {n : Nat} (f : (Fin (n + 1) -> K) -> Real) (hf : Measurable f)
    (s : Fin (n + 1)) (center : (Fin n -> K) -> Real) {V : Real}
    (hfiber : forall y, MemLp (fun a =>
      f (@Fin.insertNth n (fun _ => K) s a y) - center y) 2 nu)
    (hbound : forall y, integral nu (fun a =>
      (f (@Fin.insertNth n (fun _ => K) s a y) - center y) ^ 2) <= V) :
    iidRawResamplingEnergy nu f s <= 4 * V := by
  apply iidRawResamplingEnergy_le_four_mul_of_fiber_memLp
    nu f s center
  · exact iidRawResamplingOuter_integrable_of_fiber_memLp
      nu f hf s center hfiber hbound
  · exact hfiber
  · exact hbound

end CircularLawSection4
