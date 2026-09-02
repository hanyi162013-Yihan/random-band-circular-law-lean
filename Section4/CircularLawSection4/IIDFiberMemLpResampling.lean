import CircularLawSection4.IIDFiberL2Resampling
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# L2 fibers imply a raw IID replacement bound

The paper's row lemma naturally returns `MemLp` on every frozen one-row
fiber.  This file packages the routine two-copy argument which turns that
statement into the integrability hypotheses used by the raw Efron--Stein
energy.  Only the outer raw-energy integrability remains explicit.
-/

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace CircularLawSection4

universe u

variable {K : Type u} [MeasurableSpace K]
  (nu : Measure K) [SigmaFinite nu] [IsProbabilityMeasure nu]

/-- Inserting a variable value into one fixed finite coordinate, while all
other coordinates are frozen, is measurable. -/
theorem measurable_fin_insertNth_left {n : Nat} (s : Fin (n + 1))
    (y : Fin n -> K) : Measurable (fun a : K =>
      @Fin.insertNth n (fun _ => K) s a y) := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => K) s
  have hpair : Measurable (fun a : K => (a, y)) :=
    measurable_id.prodMk measurable_const
  have h := e.symm.measurable.comp hpair
  simpa only [Function.comp_def, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk] using h

/-- A uniform conditional `L^2` estimate around a frozen center bounds the
raw replacement energy by `4 * V`.  Pair and iterated-fiber integrability
are consequences of the conditional `MemLp` hypothesis. -/
theorem iidRawResamplingEnergy_le_four_mul_of_fiber_memLp
    {n : Nat} (f : (Fin (n + 1) -> K) -> Real) (s : Fin (n + 1))
    (center : (Fin n -> K) -> Real) {V : Real}
    (hrawOuter : Integrable (fun x => integral nu (fun a' =>
      (f x - f (Function.update x s a')) ^ 2))
      (iidMeasure nu (n + 1)))
    (hfiber : forall y, MemLp (fun a =>
      f (s.insertNth a y) - center y) 2 nu)
    (hbound : forall y, integral nu (fun a =>
      (f (s.insertNth a y) - center y) ^ 2) <= V) :
    iidRawResamplingEnergy nu f s <= 4 * V := by
  let err : (Fin n -> K) -> K -> Real := fun y a =>
    f (s.insertNth a y) - center y
  have herrInt (y : Fin n -> K) :
      Integrable (fun a => err y a ^ 2) nu :=
    (hfiber y).integrable_sq
  have hpair (y : Fin n -> K) (a : K) : Integrable (fun a' =>
      (f (s.insertNth a y) - f (s.insertNth a' y)) ^ 2) nu := by
    have hmem : MemLp (fun a' => err y a - err y a') 2 nu :=
      (memLp_const (err y a)).sub (hfiber y)
    have hint := hmem.integrable_sq
    convert hint using 1
    funext a'
    dsimp only [err]
    ring
  have hiter (y : Fin n -> K) : Integrable (fun a => integral nu (fun a' =>
      (f (s.insertNth a y) - f (s.insertNth a' y)) ^ 2)) nu := by
    have hfst : MemLp (fun p : K × K => err y p.1) 2 (nu.prod nu) :=
      (hfiber y).comp_fst nu
    have hsnd : MemLp (fun p : K × K => err y p.2) 2 (nu.prod nu) :=
      (hfiber y).comp_snd nu
    have hprod : Integrable (fun p : K × K =>
        (err y p.1 - err y p.2) ^ 2) (nu.prod nu) :=
      (hfst.sub hsnd).integrable_sq
    have hout := hprod.integral_prod_left
    convert hout using 1
    funext a
    apply integral_congr_ae
    filter_upwards with a'
    dsimp only [err]
    ring
  exact iidRawResamplingEnergy_le_four_mul_of_fiber_center nu f s center
    hrawOuter hpair hiter herrInt hbound

end CircularLawSection4
