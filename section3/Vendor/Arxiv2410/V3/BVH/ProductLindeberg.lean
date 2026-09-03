/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/ProductLindeberg.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Direct Lindeberg replacement on finite product measures

This file isolates the measure-theoretic telescoping argument needed for the specialized
`p = 3` route behind Brailovskaya--van Handel, Remark 6.13.  It contains no random-matrix
comparison theorem.  Its inputs are only one-coordinate estimates; the comparison of the two
full product expectations is proved here by exact hybrid measures and a finite telescoping sum.

The final theorem also packages the standard local use of matching zeroth, first, and second
Taylor terms.  The zeroth term cancels because both coordinate laws are probability measures,
the first and second terms are required to have matching integrals, and only the two cubic
remainders contribute.
-/

namespace Arxiv2410V3.BVH

open MeasureTheory
open scoped BigOperators

noncomputable section

/-! ## Exact hybrid product measures -/

/-- At hybrid time `k`, coordinates with index `< k` use `nu`; the remaining coordinates use
`mu`.  Thus time `0` is the original product and time `n` is the replacement product. -/
def hybridCoordinateLaw {B : Type*} [MeasurableSpace B] {n : ℕ}
    (mu nu : Fin n → Measure B) (k : ℕ) : Fin n → Measure B :=
  fun i ↦ if i.val < k then nu i else mu i

/-- The product measure associated with `hybridCoordinateLaw`. -/
def hybridProductMeasure {B : Type*} [MeasurableSpace B] {n : ℕ}
    (mu nu : Fin n → Measure B) (k : ℕ) : Measure (Fin n → B) :=
  Measure.pi (hybridCoordinateLaw mu nu k)

@[simp]
theorem hybridCoordinateLaw_zero {B : Type*} [MeasurableSpace B] {n : ℕ}
    (mu nu : Fin n → Measure B) :
    hybridCoordinateLaw mu nu 0 = mu := by
  funext i
  simp [hybridCoordinateLaw]

theorem hybridCoordinateLaw_eq_right_of_card_le {B : Type*} [MeasurableSpace B] {n k : ℕ}
    (mu nu : Fin n → Measure B) (hk : n ≤ k) :
    hybridCoordinateLaw mu nu k = nu := by
  funext i
  simp only [hybridCoordinateLaw]
  rw [if_pos (lt_of_lt_of_le i.isLt hk)]

@[simp]
theorem hybridCoordinateLaw_card {B : Type*} [MeasurableSpace B] {n : ℕ}
    (mu nu : Fin n → Measure B) :
    hybridCoordinateLaw mu nu n = nu :=
  hybridCoordinateLaw_eq_right_of_card_le mu nu le_rfl

@[simp]
theorem hybridProductMeasure_zero {B : Type*} [MeasurableSpace B] {n : ℕ}
    (mu nu : Fin n → Measure B) :
    hybridProductMeasure mu nu 0 = Measure.pi mu := by
  simp [hybridProductMeasure]

@[simp]
theorem hybridProductMeasure_card {B : Type*} [MeasurableSpace B] {n : ℕ}
    (mu nu : Fin n → Measure B) :
    hybridProductMeasure mu nu n = Measure.pi nu := by
  simp [hybridProductMeasure]

/-- Consecutive hybrids differ by exactly one `Function.update`. -/
theorem hybridCoordinateLaw_succ_eq_update {B : Type*} [MeasurableSpace B] {n k : ℕ}
    (mu nu : Fin n → Measure B) (hk : k < n) :
    hybridCoordinateLaw mu nu (k + 1) =
      Function.update (hybridCoordinateLaw mu nu k) ⟨k, hk⟩ (nu ⟨k, hk⟩) := by
  classical
  funext j
  by_cases hj : j = ⟨k, hk⟩
  · subst j
    simp [hybridCoordinateLaw]
  · have hjval : j.val ≠ k := by
      intro h
      apply hj
      exact Fin.ext h
    have hlt : (j.val < k + 1) ↔ (j.val < k) := by omega
    simp only [hybridCoordinateLaw]
    rw [Function.update, dif_neg hj]
    rw [if_congr hlt rfl rfl]
    rfl

/-! ## One-coordinate replacement inside a product -/

section OneCoordinate

variable {B E : Type*} [MeasurableSpace B] [Nonempty B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Fubini lifts a uniform one-coordinate comparison to product measures which differ only in
that coordinate.  The hypothesis is deliberately fiberwise: it is the local conclusion supplied
by Taylor expansion and moment cancellation, not the desired full-product comparison. -/
theorem norm_integral_pi_sub_integral_pi_update_le
    {n : ℕ} (P : Fin (n + 1) → Measure B) [∀ j, IsProbabilityMeasure (P j)]
    (i : Fin (n + 1)) (rho : Measure B) [IsProbabilityMeasure rho]
    (f : (Fin (n + 1) → B) → E) (hf : StronglyMeasurable f)
    {L delta : ℝ} (hfBound : ∀ x, ‖f x‖ ≤ L)
    (hfiber : ∀ x,
      ‖(∫ b, f (Function.update x i b) ∂P i) -
          ∫ b, f (Function.update x i b) ∂rho‖ ≤ delta) :
    ‖(∫ x, f x ∂Measure.pi P) -
        ∫ x, f x ∂Measure.pi (Function.update P i rho)‖ ≤ delta := by
  classical
  let Q : Fin (n + 1) → Measure B := Function.update P i rho
  letI hQ (j : Fin (n + 1)) : IsProbabilityMeasure (Q j) := by
    by_cases hji : j = i
    · subst j
      simpa [Q] using (inferInstance : IsProbabilityMeasure rho)
    · simpa [Q, Function.update, hji] using
        (inferInstance : IsProbabilityMeasure (P j))
  let e : (Fin (n + 1) → B) ≃ᵐ B × (Fin n → B) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ B) i
  let R : Fin n → Measure B := fun j ↦ P (i.succAbove j)
  letI hR (j : Fin n) : IsProbabilityMeasure (R j) := by
    dsimp only [R]
    infer_instance
  have heP : MeasurePreserving e (Measure.pi P) ((P i).prod (Measure.pi R)) := by
    simpa [e, R] using measurePreserving_piFinSuccAbove P i
  have heQ : MeasurePreserving e (Measure.pi Q) (rho.prod (Measure.pi R)) := by
    have h := measurePreserving_piFinSuccAbove Q i
    simpa [e, Q, R, Function.update, Fin.succAbove_ne] using h
  have hfP : Integrable f (Measure.pi P) := by
    apply Integrable.of_bound hf.aestronglyMeasurable L
    exact ae_of_all _ hfBound
  have hfQ : Integrable f (Measure.pi Q) := by
    apply Integrable.of_bound hf.aestronglyMeasurable L
    exact ae_of_all _ hfBound
  have hfCompP : Integrable (fun p : B × (Fin n → B) ↦ f (e.symm p))
      ((P i).prod (Measure.pi R)) := by
    exact (heP.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hfP
  have hfCompQ : Integrable (fun p : B × (Fin n → B) ↦ f (e.symm p))
      (rho.prod (Measure.pi R)) := by
    exact (heQ.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hfQ
  let b0 : B := Classical.choice inferInstance
  have hupdate (r : Fin n → B) (b : B) :
      Function.update (e.symm (b0, r)) i b = e.symm (b, r) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [e]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
      simp [e, Function.update, Fin.succAbove_ne]
  let fiberP : (Fin n → B) → E :=
    fun r ↦ ∫ b, f (e.symm (b, r)) ∂P i
  let fiberQ : (Fin n → B) → E :=
    fun r ↦ ∫ b, f (e.symm (b, r)) ∂rho
  have hfiberBound (r : Fin n → B) : ‖fiberP r - fiberQ r‖ ≤ delta := by
    simpa only [fiberP, fiberQ, hupdate] using hfiber (e.symm (b0, r))
  have hFiberPInt : Integrable fiberP (Measure.pi R) := by
    simpa only [fiberP] using hfCompP.integral_prod_right
  have hFiberQInt : Integrable fiberQ (Measure.pi R) := by
    simpa only [fiberQ] using hfCompQ.integral_prod_right
  have htotalP :
      (∫ x, f x ∂Measure.pi P) = ∫ r, fiberP r ∂Measure.pi R := by
    calc
      (∫ x, f x ∂Measure.pi P) =
          ∫ p, f (e.symm p) ∂((P i).prod (Measure.pi R)) :=
        (heP.symm.integral_comp' f).symm
      _ = ∫ r, ∫ b, f (e.symm (b, r)) ∂P i ∂Measure.pi R :=
        integral_prod_symm _ hfCompP
      _ = ∫ r, fiberP r ∂Measure.pi R := rfl
  have htotalQ :
      (∫ x, f x ∂Measure.pi Q) = ∫ r, fiberQ r ∂Measure.pi R := by
    calc
      (∫ x, f x ∂Measure.pi Q) =
          ∫ p, f (e.symm p) ∂(rho.prod (Measure.pi R)) :=
        (heQ.symm.integral_comp' f).symm
      _ = ∫ r, ∫ b, f (e.symm (b, r)) ∂rho ∂Measure.pi R :=
        integral_prod_symm _ hfCompQ
      _ = ∫ r, fiberQ r ∂Measure.pi R := rfl
  change ‖(∫ x, f x ∂Measure.pi P) - ∫ x, f x ∂Measure.pi Q‖ ≤ delta
  rw [htotalP, htotalQ, ← integral_sub hFiberPInt hFiberQInt]
  simpa using norm_integral_le_of_norm_le_const
    (μ := Measure.pi R) (ae_of_all _ hfiberBound)

end OneCoordinate

/-! ## Finite telescoping -/

section Telescoping

variable {E : Type*} [NormedAddCommGroup E]

/-- A finite normed telescoping inequality, stated separately so that the probability theorem
below has no hidden summation step. -/
theorem norm_sub_le_sum_range_of_step
    (g : ℕ → E) (d : ℕ → ℝ) (n : ℕ)
    (hstep : ∀ k < n, ‖g k - g (k + 1)‖ ≤ d k) :
    ‖g 0 - g n‖ ≤ ∑ k ∈ Finset.range n, d k := by
  have htel : g 0 - g n = ∑ k ∈ Finset.range n, (g k - g (k + 1)) := by
    induction n with
    | zero => simp
    | succ n ih =>
        have ih' := ih (fun k hk ↦ hstep k (hk.trans (Nat.lt_succ_self n)))
        rw [Finset.sum_range_succ, ← ih']
        abel
  rw [htel]
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun k hk ↦ hstep k (Finset.mem_range.mp hk))

end Telescoping

section ProductLindeberg

variable {B E : Type*} [MeasurableSpace B] [Nonempty B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Direct finite-product Lindeberg principle.

The only comparison premise is local: after freezing all other coordinates, replacing coordinate
`i` changes the fiber expectation by at most `delta i`.  The conclusion for the two complete
product laws is derived by the exact hybrids `hybridProductMeasure mu nu k`. -/
theorem norm_integral_pi_sub_integral_pi_le_of_coordinate
    {n : ℕ} (mu nu : Fin n → Measure B)
    [∀ i, IsProbabilityMeasure (mu i)] [∀ i, IsProbabilityMeasure (nu i)]
    (f : (Fin n → B) → E) (hf : StronglyMeasurable f)
    {L : ℝ} (hfBound : ∀ x, ‖f x‖ ≤ L) (delta : Fin n → ℝ)
    (hcoordinate : ∀ i x,
      ‖(∫ b, f (Function.update x i b) ∂mu i) -
          ∫ b, f (Function.update x i b) ∂nu i‖ ≤ delta i) :
    ‖(∫ x, f x ∂Measure.pi mu) - ∫ x, f x ∂Measure.pi nu‖ ≤
      ∑ i, delta i := by
  cases n with
  | zero =>
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
      simp
  | succ n =>
      let G : ℕ → E := fun k ↦ ∫ x, f x ∂hybridProductMeasure mu nu k
      have hstep (k : ℕ) (hk : k < n + 1) :
          ‖G k - G (k + 1)‖ ≤ delta ⟨k, hk⟩ := by
        let i : Fin (n + 1) := ⟨k, hk⟩
        let P : Fin (n + 1) → Measure B := hybridCoordinateLaw mu nu k
        letI hP (j : Fin (n + 1)) : IsProbabilityMeasure (P j) := by
          dsimp only [P, hybridCoordinateLaw]
          split <;> infer_instance
        have hPi : P i = mu i := by simp [P, i, hybridCoordinateLaw]
        have hadj :
            hybridCoordinateLaw mu nu (k + 1) = Function.update P i (nu i) := by
          simpa only [P, i] using hybridCoordinateLaw_succ_eq_update mu nu hk
        have hlocal := norm_integral_pi_sub_integral_pi_update_le
          P i (nu i) f hf hfBound
          (fun x ↦ by simpa only [hPi] using hcoordinate i x)
        simpa only [G, hybridProductMeasure, P, hadj] using hlocal
      let d : ℕ → ℝ := fun k ↦ if hk : k < n + 1 then delta ⟨k, hk⟩ else 0
      have hstepD : ∀ k < n + 1, ‖G k - G (k + 1)‖ ≤ d k := by
        intro k hk
        dsimp only [d]
        rw [dif_pos hk]
        exact hstep k hk
      have htel := norm_sub_le_sum_range_of_step G d (n + 1) hstepD
      have hsum : ∑ k ∈ Finset.range (n + 1), d k = ∑ i, delta i := by
        rw [← Fin.sum_univ_eq_sum_range d]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [d]
        rw [dif_pos i.isLt]
      rw [hsum] at htel
      simpa only [G, hybridProductMeasure_zero, hybridProductMeasure_card] using htel

end ProductLindeberg

/-! ## Local second-order cancellation with cubic remainders -/

section SecondOrder

variable {B E : Type*} [MeasurableSpace B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Data for one fiber of a second-order Taylor expansion.  This is local analytic data, not a
comparison certificate for product expectations.  The `first_match` and `second_match` fields are
the precise places where matching first and second moments are used. -/
structure SecondOrderCubicExpansion
    (phi : B → E) (mu nu : Measure B) (cubic : B → ℝ) (C : ℝ) where
  constant : E
  first : B → E
  second : B → E
  remainder : B → E
  expansion : ∀ b, phi b = constant + first b + second b + remainder b
  first_integrable_mu : Integrable first mu
  first_integrable_nu : Integrable first nu
  second_integrable_mu : Integrable second mu
  second_integrable_nu : Integrable second nu
  remainder_stronglyMeasurable : StronglyMeasurable remainder
  first_match : ∫ b, first b ∂mu = ∫ b, first b ∂nu
  second_match : ∫ b, second b ∂mu = ∫ b, second b ∂nu
  remainder_norm_le : ∀ b, ‖remainder b‖ ≤ C * cubic b

/-- Matching constant, first, and second terms leaves only the two cubic Taylor remainders. -/
theorem SecondOrderCubicExpansion.integral_comparison
    {mu nu : Measure B} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {phi : B → E} {cubic : B → ℝ} {C : ℝ}
    (h : SecondOrderCubicExpansion phi mu nu cubic C)
    (hcubicMu : Integrable cubic mu) (hcubicNu : Integrable cubic nu) :
    ‖(∫ b, phi b ∂mu) - ∫ b, phi b ∂nu‖ ≤
      C * ((∫ b, cubic b ∂mu) + ∫ b, cubic b ∂nu) := by
  have hscaledMu : Integrable (fun b ↦ C * cubic b) mu := hcubicMu.const_mul C
  have hscaledNu : Integrable (fun b ↦ C * cubic b) nu := hcubicNu.const_mul C
  have hremMu : Integrable h.remainder mu :=
    hscaledMu.mono' h.remainder_stronglyMeasurable.aestronglyMeasurable
      (ae_of_all _ h.remainder_norm_le)
  have hremNu : Integrable h.remainder nu :=
    hscaledNu.mono' h.remainder_stronglyMeasurable.aestronglyMeasurable
      (ae_of_all _ h.remainder_norm_le)
  have hconstMu : Integrable (fun _ : B ↦ h.constant) mu := integrable_const _
  have hconstNu : Integrable (fun _ : B ↦ h.constant) nu := integrable_const _
  let cfun : B → E := fun _ ↦ h.constant
  have hcfunMu : Integrable cfun mu := hconstMu
  have hcfunNu : Integrable cfun nu := hconstNu
  have hfirstSumMu : Integrable (cfun + h.first) mu := hcfunMu.add h.first_integrable_mu
  have hfirstSumNu : Integrable (cfun + h.first) nu := hcfunNu.add h.first_integrable_nu
  have hsecondSumMu : Integrable (cfun + h.first + h.second) mu :=
    hfirstSumMu.add h.second_integrable_mu
  have hsecondSumNu : Integrable (cfun + h.first + h.second) nu :=
    hfirstSumNu.add h.second_integrable_nu
  have hintFirstMu :
      (∫ b, (cfun + h.first) b ∂mu) =
        (∫ b, cfun b ∂mu) + ∫ b, h.first b ∂mu := by
    simpa only [Pi.add_apply] using integral_add hcfunMu h.first_integrable_mu
  have hintFirstNu :
      (∫ b, (cfun + h.first) b ∂nu) =
        (∫ b, cfun b ∂nu) + ∫ b, h.first b ∂nu := by
    simpa only [Pi.add_apply] using integral_add hcfunNu h.first_integrable_nu
  have hintSecondMu :
      (∫ b, (cfun + h.first + h.second) b ∂mu) =
        (∫ b, (cfun + h.first) b ∂mu) + ∫ b, h.second b ∂mu := by
    simpa only [Pi.add_apply] using integral_add hfirstSumMu h.second_integrable_mu
  have hintSecondNu :
      (∫ b, (cfun + h.first + h.second) b ∂nu) =
        (∫ b, (cfun + h.first) b ∂nu) + ∫ b, h.second b ∂nu := by
    simpa only [Pi.add_apply] using integral_add hfirstSumNu h.second_integrable_nu
  have hphiMu : Integrable phi mu := by
    apply hsecondSumMu.add hremMu |>.congr
    exact ae_of_all _ fun b ↦ (h.expansion b).symm
  have hphiNu : Integrable phi nu := by
    apply hsecondSumNu.add hremNu |>.congr
    exact ae_of_all _ fun b ↦ (h.expansion b).symm
  have hintMu :
      (∫ b, phi b ∂mu) = h.constant + (∫ b, h.first b ∂mu) +
          (∫ b, h.second b ∂mu) + ∫ b, h.remainder b ∂mu := by
    rw [integral_congr_ae (ae_of_all _ h.expansion)]
    calc
      (∫ b, h.constant + h.first b + h.second b + h.remainder b ∂mu) =
          (∫ b, (cfun + h.first + h.second) b ∂mu) +
            ∫ b, h.remainder b ∂mu := by
        simpa only [cfun, Pi.add_apply] using integral_add hsecondSumMu hremMu
      _ = ((∫ b, (cfun + h.first) b ∂mu) + ∫ b, h.second b ∂mu) +
            ∫ b, h.remainder b ∂mu := by
        rw [hintSecondMu]
      _ = (((∫ b, cfun b ∂mu) + ∫ b, h.first b ∂mu) +
            ∫ b, h.second b ∂mu) + ∫ b, h.remainder b ∂mu := by
        rw [hintFirstMu]
      _ = h.constant + (∫ b, h.first b ∂mu) +
          (∫ b, h.second b ∂mu) + ∫ b, h.remainder b ∂mu := by
        simp [cfun]
  have hintNu :
      (∫ b, phi b ∂nu) = h.constant + (∫ b, h.first b ∂nu) +
          (∫ b, h.second b ∂nu) + ∫ b, h.remainder b ∂nu := by
    rw [integral_congr_ae (ae_of_all _ h.expansion)]
    calc
      (∫ b, h.constant + h.first b + h.second b + h.remainder b ∂nu) =
          (∫ b, (cfun + h.first + h.second) b ∂nu) +
            ∫ b, h.remainder b ∂nu := by
        simpa only [cfun, Pi.add_apply] using integral_add hsecondSumNu hremNu
      _ = ((∫ b, (cfun + h.first) b ∂nu) + ∫ b, h.second b ∂nu) +
            ∫ b, h.remainder b ∂nu := by
        rw [hintSecondNu]
      _ = (((∫ b, cfun b ∂nu) + ∫ b, h.first b ∂nu) +
            ∫ b, h.second b ∂nu) + ∫ b, h.remainder b ∂nu := by
        rw [hintFirstNu]
      _ = h.constant + (∫ b, h.first b ∂nu) +
          (∫ b, h.second b ∂nu) + ∫ b, h.remainder b ∂nu := by
        simp [cfun]
  have hcancel :
      (∫ b, phi b ∂mu) - ∫ b, phi b ∂nu =
        (∫ b, h.remainder b ∂mu) - ∫ b, h.remainder b ∂nu := by
    rw [hintMu, hintNu, h.first_match, h.second_match]
    abel
  rw [hcancel]
  calc
    ‖(∫ b, h.remainder b ∂mu) - ∫ b, h.remainder b ∂nu‖
        ≤ ‖∫ b, h.remainder b ∂mu‖ + ‖∫ b, h.remainder b ∂nu‖ :=
      norm_sub_le _ _
    _ ≤ (∫ b, C * cubic b ∂mu) + ∫ b, C * cubic b ∂nu :=
      add_le_add
        (norm_integral_le_of_norm_le hscaledMu (ae_of_all _ h.remainder_norm_le))
        (norm_integral_le_of_norm_le hscaledNu (ae_of_all _ h.remainder_norm_le))
    _ = C * ((∫ b, cubic b ∂mu) + ∫ b, cubic b ∂nu) := by
      rw [integral_const_mul, integral_const_mul]
      ring

/-- Product Lindeberg comparison obtained from honest fiberwise second-order expansions.

For a matrix application, `cubic i b` is typically `‖b‖^3`; the two integrals in the right-hand
side are exactly the original and Gaussian third-moment budgets. -/
theorem norm_integral_pi_sub_integral_pi_le_of_secondOrderCubic
    {n : ℕ} [Nonempty B]
    (mu nu : Fin n → Measure B)
    [∀ i, IsProbabilityMeasure (mu i)] [∀ i, IsProbabilityMeasure (nu i)]
    (f : (Fin n → B) → E) (hf : StronglyMeasurable f)
    {L : ℝ} (hfBound : ∀ x, ‖f x‖ ≤ L)
    (cubic : Fin n → B → ℝ) (C : Fin n → ℝ)
    (hcubicMu : ∀ i, Integrable (cubic i) (mu i))
    (hcubicNu : ∀ i, Integrable (cubic i) (nu i))
    (hexpansion : ∀ i x,
      SecondOrderCubicExpansion
        (fun b ↦ f (Function.update x i b)) (mu i) (nu i) (cubic i) (C i)) :
    ‖(∫ x, f x ∂Measure.pi mu) - ∫ x, f x ∂Measure.pi nu‖ ≤
      ∑ i, C i * ((∫ b, cubic i b ∂mu i) + ∫ b, cubic i b ∂nu i) := by
  apply norm_integral_pi_sub_integral_pi_le_of_coordinate mu nu f hf hfBound
  intro i x
  exact (hexpansion i x).integral_comparison (hcubicMu i) (hcubicNu i)

end SecondOrder

end

end Arxiv2410V3.BVH
