import CircularLawSection4.ContinuousEfronStein
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Raw-coordinate Efron--Stein for the recursive continuous IID law

This module relates the recursive Doob resampling budget to the standard
sum of independent coordinate-replacement energies.
-/

open scoped ENNReal BigOperators
open MeasureTheory ProbabilityTheory

namespace CircularLawSection4

universe u

section RawEnergy

variable {K : Type u} [MeasurableSpace K]
  (ν : Measure K) [SFinite ν] [IsProbabilityMeasure ν]

/-- Standard raw coordinate-replacement energy
`E[(f X - f (Xⁱ←A'))²]`, with `A'` an independent sample from `ν`. -/
noncomputable def iidRawResamplingEnergy {n : ℕ}
    (f : (Fin n → K) → ℝ) (i : Fin n) : ℝ :=
  ∫ x, ∫ a', (f x - f (Function.update x i a')) ^ 2
    ∂ν ∂iidMeasure ν n

/-- Conditional mean after averaging out the fresh last coordinate. -/
noncomputable def iidLastAverage {n : ℕ}
    (f : (Fin (n + 1) → K) → ℝ) (y : Fin n → K) : ℝ :=
  ∫ a, f (joinLast (y, a)) ∂ν

omit [IsProbabilityMeasure ν] in
theorem stronglyMeasurable_iidLastAverage {n : ℕ}
    {f : (Fin (n + 1) → K) → ℝ} (hf : Measurable f) :
    StronglyMeasurable (iidLastAverage ν f) := by
  exact (hf.comp measurable_joinLast).stronglyMeasurable.integral_prod_right'

omit [SFinite ν] in
theorem norm_iidLastAverage_le {n : ℕ}
    {f : (Fin (n + 1) → K) → ℝ} {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (y : Fin n → K) :
    ‖iidLastAverage ν f y‖ ≤ C := by
  exact norm_integral_le_bound (μ := ν) (fun a => hC (joinLast (y, a)))

omit [MeasurableSpace K] in
theorem norm_sub_sq_le_bound {α : Type*} {f : α → ℝ} {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (x y : α) :
    ‖(f x - f y) ^ 2‖ ≤ (2 * |C|) ^ 2 := by
  have hxy : ‖f x - f y‖ ≤ 2 * |C| := by
    calc
      ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hC x) (hC y)
      _ ≤ 2 * |C| := by nlinarith [le_abs_self C]
  have hnonneg : 0 ≤ 2 * |C| := by positivity
  have hmul := mul_nonneg (sub_nonneg.mpr hxy)
    (add_nonneg hnonneg (norm_nonneg (f x - f y)))
  rw [norm_pow]
  nlinarith

theorem measurable_rawReplacementSq {n : ℕ}
    {f : (Fin n → K) → ℝ} (hf : Measurable f) (i : Fin n) :
    Measurable (fun z : (Fin n → K) × K =>
      (f z.1 - f (Function.update z.1 i z.2)) ^ 2) := by
  fun_prop

omit [IsProbabilityMeasure ν] in
theorem stronglyMeasurable_rawInner {n : ℕ}
    {f : (Fin n → K) → ℝ} (hf : Measurable f) (i : Fin n) :
    StronglyMeasurable (fun x => ∫ a',
      (f x - f (Function.update x i a')) ^ 2 ∂ν) := by
  exact (measurable_rawReplacementSq hf i).stronglyMeasurable.integral_prod_right'

omit [SFinite ν] in
theorem norm_rawInner_le {n : ℕ}
    {f : (Fin n → K) → ℝ} {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (i : Fin n) (x : Fin n → K) :
    ‖∫ a', (f x - f (Function.update x i a')) ^ 2 ∂ν‖ ≤
      (2 * |C|) ^ 2 := by
  exact norm_integral_le_bound (μ := ν) (fun a' =>
    norm_sub_sq_le_bound hC x (Function.update x i a'))

theorem integrable_rawInner {n : ℕ}
    {f : (Fin n → K) → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (i : Fin n) :
    Integrable (fun x => ∫ a',
      (f x - f (Function.update x i a')) ^ 2 ∂ν)
      (iidMeasure ν n) := by
  let _ := iidMeasure_isProbability ν n
  exact Integrable.of_bound (stronglyMeasurable_rawInner ν hf i).aestronglyMeasurable
    ((2 * |C|) ^ 2) (ae_of_all _ (norm_rawInner_le ν hC i))

omit [MeasurableSpace K] in
@[simp] theorem update_joinLast_last {n : ℕ}
    (y : Fin n → K) (a a' : K) :
    Function.update (joinLast (y, a)) (Fin.last n) a' =
      joinLast (y, a') := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp
  · simp [Fin.castSucc_ne_last]

omit [MeasurableSpace K] in
@[simp] theorem update_joinLast_castSucc {n : ℕ}
    (y : Fin n → K) (a a' : K) (i : Fin n) :
    Function.update (joinLast (y, a)) i.castSucc a' =
      joinLast (Function.update y i a', a) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have hne : Fin.last n ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
    simp [hne]
  · by_cases hki : k = i
    · subst k
      simp
    · simp [hki]

/-- The raw energy of the last coordinate is exactly the fresh-coordinate
term in the recursive resampling budget. -/
theorem iidRawResamplingEnergy_last_eq {n : ℕ}
    (f : (Fin (n + 1) → K) → ℝ) (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) :
    iidRawResamplingEnergy ν f (Fin.last n) =
      ∫ y, ∫ a, ∫ a',
        (f (joinLast (y, a)) - f (joinLast (y, a'))) ^ 2
        ∂ν ∂ν ∂iidMeasure ν n := by
  unfold iidRawResamplingEnergy
  rw [integral_iidMeasure_succ ν
    (integrable_rawInner ν hf hC (Fin.last n))]
  simp only [update_joinLast_last]

/-- Expanding a prefix-coordinate raw energy through the successor product
law leaves the fresh last coordinate unchanged. -/
theorem iidRawResamplingEnergy_castSucc_eq {n : ℕ}
    (f : (Fin (n + 1) → K) → ℝ) (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (i : Fin n) :
    iidRawResamplingEnergy ν f i.castSucc =
      ∫ y, ∫ a, ∫ a',
        (f (joinLast (y, a)) -
          f (joinLast (Function.update y i a', a))) ^ 2
        ∂ν ∂ν ∂iidMeasure ν n := by
  unfold iidRawResamplingEnergy
  rw [integral_iidMeasure_succ ν
    (integrable_rawInner ν hf hC i.castSucc)]
  simp only [update_joinLast_castSucc]

omit [SFinite ν] in
/-- Pointwise Jensen contraction: replacing a prefix coordinate after
averaging the last coordinate cannot increase the squared change beyond the
average squared change before averaging. -/
theorem iidLastAverage_update_sq_le {n : ℕ}
    (f : (Fin (n + 1) → K) → ℝ) (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (y : Fin n → K) (i : Fin n) (a' : K) :
    (iidLastAverage ν f y -
      iidLastAverage ν f (Function.update y i a')) ^ 2 ≤
      ∫ a, (f (joinLast (y, a)) -
        f (joinLast (Function.update y i a', a))) ^ 2 ∂ν := by
  have hy : Integrable (fun a => f (joinLast (y, a))) ν :=
    Integrable.of_bound
      (hf.comp (measurable_joinLast.comp measurable_prodMk_left)).aestronglyMeasurable
      C (ae_of_all _ fun a => hC (joinLast (y, a)))
  have hy' : Integrable
      (fun a => f (joinLast (Function.update y i a', a))) ν :=
    Integrable.of_bound
      (hf.comp (measurable_joinLast.comp measurable_prodMk_left)).aestronglyMeasurable
      C (ae_of_all _ fun a => hC (joinLast (Function.update y i a', a)))
  have hdiff : Measurable (fun a =>
      f (joinLast (y, a)) -
        f (joinLast (Function.update y i a', a))) := by
    exact (hf.comp (measurable_joinLast.comp measurable_prodMk_left)).sub
      (hf.comp (measurable_joinLast.comp measurable_prodMk_left))
  have hdiffC : ∀ a,
      ‖f (joinLast (y, a)) -
        f (joinLast (Function.update y i a', a))‖ ≤ 2 * |C| := by
    intro a
    calc
      ‖f (joinLast (y, a)) -
          f (joinLast (Function.update y i a', a))‖ ≤
          ‖f (joinLast (y, a))‖ +
            ‖f (joinLast (Function.update y i a', a))‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hC _) (hC _)
      _ ≤ 2 * |C| := by nlinarith [le_abs_self C]
  unfold iidLastAverage
  rw [← integral_sub hy hy']
  exact sq_integral_le_integral_sq hdiff (2 * |C|) hdiffC

/-- Prefix-coordinate Jensen contraction for the standard raw replacement
energy.  This is the substantive bridge from the recursive conditional mean
back to the original coordinate energy. -/
theorem iidRawResamplingEnergy_iidLastAverage_le {n : ℕ}
    (f : (Fin (n + 1) → K) → ℝ) (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (i : Fin n) :
    iidRawResamplingEnergy ν (iidLastAverage ν f) i ≤
      iidRawResamplingEnergy ν f i.castSucc := by
  let _ := iidMeasure_isProbability ν n
  let Y := Fin n → K
  let g : Y → ℝ := iidLastAverage ν f
  let L : Y × K → ℝ := fun z =>
    (g z.1 - g (Function.update z.1 i z.2)) ^ 2
  let D : (Y × K) × K → ℝ := fun z =>
    (f (joinLast (z.1.1, z.2)) -
      f (joinLast (Function.update z.1.1 i z.1.2, z.2))) ^ 2
  let R : Y × K → ℝ := fun z => ∫ a, D (z, a) ∂ν
  have hgsm : StronglyMeasurable g := stronglyMeasurable_iidLastAverage ν hf
  have hg : Measurable g := hgsm.measurable
  have hgC : ∀ y, ‖g y‖ ≤ C := norm_iidLastAverage_le ν hC
  have hupdate : Measurable (fun z : Y × K =>
      Function.update z.1 i z.2) := measurable_update'
  have hL : Measurable L := by
    exact ((hg.comp measurable_fst).sub (hg.comp hupdate)).pow_const 2
  have hLbound : ∀ z, ‖L z‖ ≤ (2 * |C|) ^ 2 := by
    intro z
    exact norm_sub_sq_le_bound hgC z.1 (Function.update z.1 i z.2)
  have hcurrent : Measurable (fun z : (Y × K) × K =>
      joinLast (z.1.1, z.2)) := by
    exact measurable_joinLast.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hreplaced : Measurable (fun z : (Y × K) × K =>
      joinLast (Function.update z.1.1 i z.1.2, z.2)) := by
    exact measurable_joinLast.comp
      ((measurable_update'.comp measurable_fst).prodMk measurable_snd)
  have hD : Measurable D := by
    exact ((hf.comp hcurrent).sub (hf.comp hreplaced)).pow_const 2
  have hDbound : ∀ z, ‖D z‖ ≤ (2 * |C|) ^ 2 := by
    intro z
    exact norm_sub_sq_le_bound hC _ _
  have hRsm : StronglyMeasurable R := by
    exact hD.stronglyMeasurable.integral_prod_right'
  have hRbound : ∀ z, ‖R z‖ ≤ (2 * |C|) ^ 2 := by
    intro z
    exact norm_integral_le_bound (μ := ν) (fun a => hDbound (z, a))
  have hLint (y : Y) : Integrable (fun b => L (y, b)) ν := by
    exact Integrable.of_bound
      (hL.stronglyMeasurable.comp_measurable measurable_prodMk_left).aestronglyMeasurable
      ((2 * |C|) ^ 2) (ae_of_all _ fun b => hLbound (y, b))
  have hRint (y : Y) : Integrable (fun b => R (y, b)) ν := by
    exact Integrable.of_bound
      (hRsm.comp_measurable measurable_prodMk_left).aestronglyMeasurable
      ((2 * |C|) ^ 2) (ae_of_all _ fun b => hRbound (y, b))
  have hpoint (y : Y) (b : K) : L (y, b) ≤ R (y, b) := by
    exact iidLastAverage_update_sq_le ν f hf hC y i b
  have hinner (y : Y) :
      (∫ b, L (y, b) ∂ν) ≤ ∫ b, R (y, b) ∂ν :=
    integral_mono (hLint y) (hRint y) (hpoint y)
  have hLOsm : StronglyMeasurable (fun y => ∫ b, L (y, b) ∂ν) :=
    hL.stronglyMeasurable.integral_prod_right'
  have hROsm : StronglyMeasurable (fun y => ∫ b, R (y, b) ∂ν) :=
    hRsm.integral_prod_right'
  have hLObound : ∀ y, ‖∫ b, L (y, b) ∂ν‖ ≤ (2 * |C|) ^ 2 := by
    intro y
    exact norm_integral_le_bound (μ := ν) (fun b => hLbound (y, b))
  have hRObound : ∀ y, ‖∫ b, R (y, b) ∂ν‖ ≤ (2 * |C|) ^ 2 := by
    intro y
    exact norm_integral_le_bound (μ := ν) (fun b => hRbound (y, b))
  have hLOint : Integrable (fun y => ∫ b, L (y, b) ∂ν)
      (iidMeasure ν n) :=
    Integrable.of_bound hLOsm.aestronglyMeasurable ((2 * |C|) ^ 2)
      (ae_of_all _ hLObound)
  have hROint : Integrable (fun y => ∫ b, R (y, b) ∂ν)
      (iidMeasure ν n) :=
    Integrable.of_bound hROsm.aestronglyMeasurable ((2 * |C|) ^ 2)
      (ae_of_all _ hRObound)
  have houter :
      (∫ y, ∫ b, L (y, b) ∂ν ∂iidMeasure ν n) ≤
        ∫ y, ∫ b, R (y, b) ∂ν ∂iidMeasure ν n :=
    integral_mono hLOint hROint hinner
  have hswap (y : Y) :
      (∫ b, ∫ a, D ((y, b), a) ∂ν ∂ν) =
        ∫ a, ∫ b, D ((y, b), a) ∂ν ∂ν := by
    have hDy : Measurable (fun z : K × K => D ((y, z.1), z.2)) := by
      exact hD.comp
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    have hDyInt : Integrable (fun z : K × K => D ((y, z.1), z.2))
        (ν.prod ν) :=
      Integrable.of_bound hDy.aestronglyMeasurable ((2 * |C|) ^ 2)
        (ae_of_all _ fun z => hDbound ((y, z.1), z.2))
    exact integral_integral_swap hDyInt
  have hswapOuter :
      (∫ y, ∫ b, R (y, b) ∂ν ∂iidMeasure ν n) =
        ∫ y, ∫ a, ∫ b, D ((y, b), a) ∂ν ∂ν ∂iidMeasure ν n := by
    apply integral_congr_ae
    exact ae_of_all _ hswap
  calc
    iidRawResamplingEnergy ν (iidLastAverage ν f) i =
        ∫ y, ∫ b, L (y, b) ∂ν ∂iidMeasure ν n := by
      rfl
    _ ≤ ∫ y, ∫ b, R (y, b) ∂ν ∂iidMeasure ν n := houter
    _ = ∫ y, ∫ a, ∫ b,
        (f (joinLast (y, a)) -
          f (joinLast (Function.update y i b, a))) ^ 2
        ∂ν ∂ν ∂iidMeasure ν n := hswapOuter
    _ = iidRawResamplingEnergy ν f i.castSucc :=
      (iidRawResamplingEnergy_castSucc_eq ν f hf hC i).symm

/-- The recursive Doob resampling budget is bounded by the sum of the raw
coordinate-replacement energies. -/
theorem iidRecursiveResamplingBudget_le_sum_raw :
    ∀ (n : ℕ) (f : (Fin n → K) → ℝ), Measurable f →
      ∀ (C : ℝ), (∀ x, ‖f x‖ ≤ C) →
      iidRecursiveResamplingBudget ν n f ≤
        ∑ i, iidRawResamplingEnergy ν f i := by
  intro n
  induction n with
  | zero =>
      intro f hf C hC
      simp [iidRecursiveResamplingBudget]
  | succ n ih =>
      intro f hf C hC
      let g : (Fin n → K) → ℝ := iidLastAverage ν f
      have hgsm : StronglyMeasurable g := stronglyMeasurable_iidLastAverage ν hf
      have hgC : ∀ y, ‖g y‖ ≤ C := norm_iidLastAverage_le ν hC
      have hih := ih g hgsm.measurable C hgC
      have hprefix :
          (∑ i, iidRawResamplingEnergy ν g i) ≤
            ∑ i : Fin n, iidRawResamplingEnergy ν f i.castSucc := by
        exact Finset.sum_le_sum fun i _ =>
          iidRawResamplingEnergy_iidLastAverage_le ν f hf hC i
      have hlast := iidRawResamplingEnergy_last_eq ν f hf hC
      change
        (∫ y, ∫ a, ∫ a',
          (f (joinLast (y, a)) - f (joinLast (y, a'))) ^ 2
          ∂ν ∂ν ∂iidMeasure ν n) +
            iidRecursiveResamplingBudget ν n g ≤
          ∑ i, iidRawResamplingEnergy ν f i
      calc
        (∫ y, ∫ a, ∫ a',
            (f (joinLast (y, a)) - f (joinLast (y, a'))) ^ 2
            ∂ν ∂ν ∂iidMeasure ν n) +
              iidRecursiveResamplingBudget ν n g ≤
            (∫ y, ∫ a, ∫ a',
              (f (joinLast (y, a)) - f (joinLast (y, a'))) ^ 2
              ∂ν ∂ν ∂iidMeasure ν n) +
              ∑ i, iidRawResamplingEnergy ν g i :=
          add_le_add (le_refl _) hih
        _ ≤ (∫ y, ∫ a, ∫ a',
              (f (joinLast (y, a)) - f (joinLast (y, a'))) ^ 2
              ∂ν ∂ν ∂iidMeasure ν n) +
              ∑ i : Fin n, iidRawResamplingEnergy ν f i.castSucc :=
          add_le_add (le_refl _) hprefix
        _ = ∑ i, iidRawResamplingEnergy ν f i := by
          rw [Fin.sum_univ_castSucc, ← hlast]
          ring

/-- Standard finite-dimensional Efron--Stein inequality for the continuous
IID product `iidMeasure ν n`, with explicit raw coordinate replacement. -/
theorem variance_iidMeasure_le_half_sum_raw {n : ℕ}
    (f : (Fin n → K) → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) :
    variance f (iidMeasure ν n) ≤
      (1 / 2 : ℝ) * ∑ i, iidRawResamplingEnergy ν f i := by
  exact (variance_iidMeasure_le_half_recursiveResamplingBudget_bounded
    ν n f hf C hC).trans
      (mul_le_mul_of_nonneg_left
        (iidRecursiveResamplingBudget_le_sum_raw ν n f hf C hC)
        (by positivity))

theorem variance_iidMeasure_le_half_card_mul_of_raw_le {n : ℕ}
    (f : (Fin n → K) → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, ‖f x‖ ≤ C) {D : ℝ}
    (hD : ∀ i, iidRawResamplingEnergy ν f i ≤ D) :
    variance f (iidMeasure ν n) ≤ (1 / 2 : ℝ) * (n : ℝ) * D := by
  refine (variance_iidMeasure_le_half_sum_raw ν f hf C hC).trans ?_
  calc
    (1 / 2 : ℝ) * ∑ i, iidRawResamplingEnergy ν f i ≤
        (1 / 2 : ℝ) * ∑ _i : Fin n, D := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun i _ => hD i
    _ = (1 / 2 : ℝ) * (n : ℝ) * D := by simp; ring

/-- Standard raw-coordinate Efron--Stein followed by the Section 4 pressure
maximal-deviation closure. -/
theorem pressure_maximal_concentration_iid_raw
    (n W : ℕ) (Y : Fin (2 * W).succ → (Fin n → K) → ℝ)
    (hY : ∀ r, Measurable (Y r)) (C : ℝ)
    (hC : ∀ r x, ‖Y r x‖ ≤ C) {D : ℝ}
    (hD : ∀ r i, iidRawResamplingEnergy ν (Y r) i ≤ D) :
    (∫ ω, maxCenteredAbs (iidMeasure ν n) Y ω ∂iidMeasure ν n) ≤
      Real.sqrt (((2 * W + 1 : ℕ) : ℝ) *
        ((1 / 2 : ℝ) * (n : ℝ) * D)) := by
  let _ := iidMeasure_isProbability ν n
  apply pressure_maximal_concentration_of_variance W
  · intro r
    exact memLp_of_measurable_of_bound (hY r) C (hC r) 2
  · intro r
    exact variance_iidMeasure_le_half_card_mul_of_raw_le
      ν (Y r) (hY r) C (hC r) (hD r)

end RawEnergy

end CircularLawSection4
