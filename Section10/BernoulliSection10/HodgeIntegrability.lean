import BernoulliSection10.IntegratedHodge
import BernoulliSection10.MultiAffineSecondMoment
import BernoulliSection10.PhysicalAffinity

/-!
# Concrete Hodge integrability for interval products

This module supplies the analytic input used by Lemma 10.5.  The interval
product is separately affine in its `sW` complete physical rows.  A fixed
diagonal configuration makes both extreme blocks equal to the identity, so
every cleared exterior factor and every degree product is invertible there.
The witness is internal; caller-facing results retain only the paper's
bounded-density hypotheses.
-/

open scoped BigOperators Matrix ENNReal NNReal Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace BernoulliSection10

open Matrix Set Set.powersetCard
open BernoulliLinearAlgebra

set_option maxHeartbeats 800000

/-! ## Flat finite rows versus recursive multiaffine rows -/

/-- Turn a flat `Fin n` family of `p`-atom rows into the recursive row space
used by `MultiAffineTensor`.  Coordinate order is preserved: the head is
outer coordinate `0`, followed by `Fin.tail`. -/
def finRowsToMultiAffineRows (p : ℕ) :
    (n : ℕ) → (Fin n → (Fin p → ℝ)) →
      MultiAffineRows (List.replicate n p)
  | 0, _ => PUnit.unit
  | n + 1, x =>
      (x 0, finRowsToMultiAffineRows p n (Fin.tail x))

/-- Inverse flattening map. -/
def multiAffineRowsToFinRows (p : ℕ) :
    (n : ℕ) → MultiAffineRows (List.replicate n p) →
      (Fin n → (Fin p → ℝ))
  | 0, _ => fun i => Fin.elim0 i
  | n + 1, x =>
      Fin.cons x.1 (multiAffineRowsToFinRows p n x.2)

theorem multiAffineRowsToFinRows_leftInverse (p : ℕ) :
    ∀ (n : ℕ) (x : Fin n → (Fin p → ℝ)),
      multiAffineRowsToFinRows p n (finRowsToMultiAffineRows p n x) = x := by
  intro n
  induction n with
  | zero =>
      intro x
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      intro x
      simp only [finRowsToMultiAffineRows, multiAffineRowsToFinRows]
      rw [ih (Fin.tail x)]
      exact Fin.cons_self_tail x

theorem multiAffineRowsToFinRows_rightInverse (p : ℕ) :
    ∀ (n : ℕ) (x : MultiAffineRows (List.replicate n p)),
      finRowsToMultiAffineRows p n (multiAffineRowsToFinRows p n x) = x := by
  intro n
  induction n with
  | zero =>
      intro x
      simp only [List.replicate_zero] at x ⊢
      cases x
      rfl
  | succ n ih =>
      rintro ⟨x, xs⟩
      simp only [multiAffineRowsToFinRows, finRowsToMultiAffineRows,
        Fin.cons_zero, Fin.tail_cons]
      rw [ih xs]

theorem measurable_finRowsToMultiAffineRows (p : ℕ) :
    ∀ n : ℕ, Measurable (finRowsToMultiAffineRows p n) := by
  intro n
  induction n with
  | zero =>
      change Measurable (fun _ : Fin 0 → (Fin p → ℝ) ↦ PUnit.unit)
      exact measurable_const
  | succ n ih =>
      change Measurable (fun x : Fin (n + 1) → (Fin p → ℝ) ↦
        (x 0, finRowsToMultiAffineRows p n (Fin.tail x)))
      exact (measurable_pi_apply 0).prodMk
        (ih.comp (measurable_pi_iff.2 fun i ↦ measurable_pi_apply i.succ))

theorem measurable_multiAffineRowsToFinRows (p : ℕ) :
    ∀ n : ℕ, Measurable (multiAffineRowsToFinRows p n) := by
  intro n
  induction n with
  | zero =>
      change Measurable (fun _ : PUnit ↦
        (fun i : Fin 0 => Fin.elim0 i : Fin 0 → (Fin p → ℝ)))
      exact measurable_const
  | succ n ih =>
      change @Measurable
        ((Fin p → ℝ) × MultiAffineRows (List.replicate n p))
        (Fin (n + 1) → (Fin p → ℝ))
        (multiAffineRowsMeasurableSpace
          (p :: List.replicate n p))
        MeasurableSpace.pi
        (fun x ↦ Fin.cons x.1
          (multiAffineRowsToFinRows p n x.2))
      rw [multiAffineRowsMeasurableSpace_cons]
      apply measurable_pi_iff.2
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa [multiAffineRowsToFinRows] using
          (measurable_fst : Measurable
            (fun x : (Fin p → ℝ) ×
              MultiAffineRows (List.replicate n p) ↦ x.1))
      · have hsnd : Measurable (fun x : (Fin p → ℝ) ×
            MultiAffineRows (List.replicate n p) ↦ x.2) := measurable_snd
        have htail : Measurable (fun x : (Fin p → ℝ) ×
            MultiAffineRows (List.replicate n p) ↦
              multiAffineRowsToFinRows p n x.2) := ih.comp hsnd
        have h : Measurable (fun x : (Fin p → ℝ) ×
            MultiAffineRows (List.replicate n p) ↦
              multiAffineRowsToFinRows p n x.2 j) :=
          (measurable_pi_apply j).comp htail
        simpa only [Fin.cons_succ] using h

/-- Measurable equivalence between the flat physical-row configuration and
the recursive multiaffine row representation. -/
def finRowsMultiAffineRowsMeasurableEquiv (p n : ℕ) :
    (Fin n → (Fin p → ℝ)) ≃ᵐ MultiAffineRows (List.replicate n p) where
  toFun := finRowsToMultiAffineRows p n
  invFun := multiAffineRowsToFinRows p n
  left_inv := multiAffineRowsToFinRows_leftInverse p n
  right_inv := multiAffineRowsToFinRows_rightInverse p n
  measurable_toFun := measurable_finRowsToMultiAffineRows p n
  measurable_invFun := measurable_multiAffineRowsToFinRows p n

@[simp] theorem finRowsMultiAffineRowsMeasurableEquiv_apply
    (p n : ℕ) (x : Fin n → (Fin p → ℝ)) :
    finRowsMultiAffineRowsMeasurableEquiv p n x =
      finRowsToMultiAffineRows p n x := rfl

@[simp] theorem finRowsMultiAffineRowsMeasurableEquiv_symm_apply
    (p n : ℕ) (x : MultiAffineRows (List.replicate n p)) :
    (finRowsMultiAffineRowsMeasurableEquiv p n).symm x =
      multiAffineRowsToFinRows p n x := rfl

/-- The equivalence exactly transports the flat finite product law to the
recursive product law. -/
theorem finRowsMultiAffineRows_measurePreserving
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℕ) :
    ∀ n : ℕ, MeasurePreserving (finRowsMultiAffineRowsMeasurableEquiv p n)
      (Measure.pi fun _ : Fin n ↦ Measure.pi fun _ : Fin p ↦ μ)
      (multiAffineRowLaw μ (List.replicate n p)) := by
  intro n
  induction n with
  | zero =>
      let e := finRowsMultiAffineRowsMeasurableEquiv p 0
      refine ⟨e.measurable, ?_⟩
      rw [Measure.pi_of_empty, Measure.map_dirac' e.measurable]
      rfl
  | succ n ih =>
      let ν : Measure (Fin p → ℝ) := Measure.pi fun _ : Fin p ↦ μ
      let split := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) ↦ (Fin p → ℝ)) 0
      have hsplit : MeasurePreserving split
          (Measure.pi fun _ : Fin (n + 1) ↦ ν)
          (ν.prod (Measure.pi fun _ : Fin n ↦ ν)) := by
        simpa [split] using
          (measurePreserving_piFinSuccAbove
            (fun _ : Fin (n + 1) ↦ ν) 0)
      have hprod : MeasurePreserving
          (Prod.map id (finRowsMultiAffineRowsMeasurableEquiv p n))
          (ν.prod (Measure.pi fun _ : Fin n ↦ ν))
          (ν.prod (multiAffineRowLaw μ (List.replicate n p))) :=
        (MeasurePreserving.id ν).prod ih
      have hcomp := hprod.comp hsplit
      let e := finRowsMultiAffineRowsMeasurableEquiv p (n + 1)
      have heq : (e : (Fin (n + 1) → (Fin p → ℝ)) →
          MultiAffineRows (List.replicate (n + 1) p)) =
          (Prod.map id (finRowsMultiAffineRowsMeasurableEquiv p n)) ∘ split := by
        funext x
        change finRowsToMultiAffineRows p (n + 1) x =
          (Prod.map id (finRowsMultiAffineRowsMeasurableEquiv p n)) (split x)
        simp [e, split, finRowsMultiAffineRowsMeasurableEquiv,
          finRowsToMultiAffineRows, MeasurableEquiv.piFinSuccAbove,
          Fin.insertNthEquiv]
        rfl
      refine ⟨e.measurable, ?_⟩
      change Measure.map e
          (Measure.pi fun _ : Fin (n + 1) ↦ ν) =
        ν.prod (multiAffineRowLaw μ (List.replicate n p))
      rw [heq]
      exact hcomp.map_eq

/-! ## Separate affinity in recursive row coordinates -/

/-- A function which is affine under replacement of every coordinate of a
flat finite row family becomes `IsMultiAffine` after the recursive reindexing.
-/
theorem isMultiAffine_comp_multiAffineRowsToFinRows
    {p : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E] :
    ∀ {n : ℕ} (F : (Fin n → (Fin p → ℝ)) → E),
      (∀ (x : Fin n → (Fin p → ℝ)) (i : Fin n)
        (u v : Fin p → ℝ) (t : ℝ),
        F (Function.update x i ((1 - t) • u + t • v)) =
          (1 - t) • F (Function.update x i u) +
            t • F (Function.update x i v)) →
      IsMultiAffine
        (fun y : MultiAffineRows (List.replicate n p) ↦
          F (multiAffineRowsToFinRows p n y)) := by
  intro n
  induction n with
  | zero =>
      intro F hF
      trivial
  | succ n ih =>
      intro F hF
      constructor
      · intro tail u v t
        let x : Fin (n + 1) → (Fin p → ℝ) :=
          Fin.cons u (multiAffineRowsToFinRows p n tail)
        have h := hF x 0 u v t
        simpa [multiAffineRowsToFinRows, x, Fin.update_cons_zero] using h
      · intro u
        apply ih (F := fun tail ↦ F (Fin.cons u tail))
        intro tail i v w t
        have h := hF (Fin.cons u tail) i.succ v w t
        simpa [Fin.cons_update] using h

/-- The concrete interval product, written on recursive complete-row
coordinates, is multiaffine. -/
theorem intervalClearedProduct_isMultiAffine
    (W s : ℕ) (z : ℂ) (r : Fin (2 * W + 1)) :
    IsMultiAffine
      (fun y : MultiAffineRows (List.replicate (s * W) (3 * W)) ↦
        intervalClearedProduct W s z
          (multiAffineRowsToFinRows (3 * W) (s * W) y) r) := by
  apply isMultiAffine_comp_multiAffineRowsToFinRows
    (p := 3 * W) (n := s * W)
    (F := fun x ↦ intervalClearedProduct W s z x r)
  intro x i u v t
  exact intervalClearedProduct_update_line W s z x r i u v t

/-! ## A deterministic nonzero configuration -/

/-- At physical row `a`, choose the `B` and `C` atoms on the diagonal to be
the inverse normalization and every other atom to be zero.  After the paper's normalization
this gives the `a`th rows of the two identity matrices. -/
def identityPhysicalRowAtoms (W : ℕ) (a : Fin W) : PhysicalRowAtoms W :=
  fun i ↦
    let bc : Fin 3 × Fin W :=
      (finProdFinEquiv : Fin 3 × Fin W ≃ Fin (3 * W)).symm i
    if (bc.1 = 0 ∨ bc.1 = 2) ∧ bc.2 = a then
      (blockNormalization W)⁻¹
    else 0

/-- The interval configuration formed from the identity physical rows. -/
def identityIntervalRows (W s : ℕ) : IntervalRows W s :=
  fun i ↦
    let ja : Fin s × Fin W :=
      (finProdFinEquiv : Fin s × Fin W ≃ Fin (s * W)).symm i
    identityPhysicalRowAtoms W ja.2

@[simp] theorem identityIntervalRows_intervalRowIndex
    (W s : ℕ) (j : Fin s) (a : Fin W) :
    identityIntervalRows W s (intervalRowIndex j a) =
      identityPhysicalRowAtoms W a := by
  simp [identityIntervalRows, intervalRowIndex]

@[simp] theorem identityPhysicalRowAtoms_physicalAtomIndex
    (W : ℕ) (a : Fin W) (b : Fin 3) (c : Fin W) :
    identityPhysicalRowAtoms W a (physicalAtomIndex b c) =
      if (b = 0 ∨ b = 2) ∧ c = a then
        (blockNormalization W)⁻¹
      else 0 := by
  simp [identityPhysicalRowAtoms, physicalAtomIndex]

/-- The normalization cancels the chosen diagonal atom. -/
theorem normalizedIdentityPhysicalRowAtom
    (W : ℕ) (hW : 0 < W) (a c : Fin W) (b : Fin 3)
    (hb : b = 0 ∨ b = 2) :
    normalizedPhysicalAtom (identityPhysicalRowAtoms W a) b c =
      if c = a then 1 else 0 := by
  have hnormalization : blockNormalization W ≠ 0 := by
    unfold blockNormalization
    apply inv_ne_zero
    exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  by_cases hca : c = a
  · simp [normalizedPhysicalAtom, identityPhysicalRowAtoms_physicalAtomIndex,
      hb, hca, hnormalization]
  · simp [normalizedPhysicalAtom, identityPhysicalRowAtoms_physicalAtomIndex,
      hb, hca]

theorem identityIntervalRows_siteB
    (W s : ℕ) (hW : 0 < W) (z : ℂ) (j : Fin s) :
    (intervalSiteBlocks z (identityIntervalRows W s) j).B = 1 := by
  ext a c
  change normalizedPhysicalAtom
      (identityIntervalRows W s (intervalRowIndex j a)) 0 c =
    (1 : Matrix (Fin W) (Fin W) ℂ) a c
  rw [identityIntervalRows_intervalRowIndex,
    normalizedIdentityPhysicalRowAtom W hW a c 0 (Or.inl rfl)]
  change (if c = a then 1 else 0) = if a = c then 1 else 0
  by_cases hac : a = c <;> simp [hac, eq_comm]

theorem identityIntervalRows_siteC
    (W s : ℕ) (hW : 0 < W) (z : ℂ) (j : Fin s) :
    (intervalSiteBlocks z (identityIntervalRows W s) j).C = 1 := by
  ext a c
  change normalizedPhysicalAtom
      (identityIntervalRows W s (intervalRowIndex j a)) 2 c =
    (1 : Matrix (Fin W) (Fin W) ℂ) a c
  rw [identityIntervalRows_intervalRowIndex,
    normalizedIdentityPhysicalRowAtom W hW a c 2 (Or.inr rfl)]
  change (if c = a then 1 else 0) = if a = c then 1 else 0
  by_cases hac : a = c <;> simp [hac, eq_comm]

/-- At the identity configuration every one-site cleared exterior factor is
invertible, in every degree `0 ≤ r ≤ 2W`. -/
theorem identityIntervalRows_step_det_isUnit
    (W s : ℕ) (hW : 0 < W) (z : ℂ)
    (r : Fin (2 * W + 1)) (j : Fin s) :
    IsUnit (intervalClearedStep W z (identityIntervalRows W s) r j).det := by
  have hr : r.1 ≤ Fintype.card (Fin W ⊕ Fin W) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  unfold intervalClearedStep
  apply clearedStepCompound_det_isUnit r.1 hr
  · rw [identityIntervalRows_siteB W s hW z j]
    simp
  · rw [identityIntervalRows_siteC W s hW z j]
    simp

/-- Consequently the full interval product is nonzero at the fixed identity
configuration.  This is the internal witness used to show that the canonical
multiaffine coefficient tensor is nonzero. -/
theorem identityIntervalRows_product_ne_zero
    (W s : ℕ) (hW : 0 < W) (z : ℂ)
    (r : Fin (2 * W + 1)) :
    intervalClearedProduct W s z (identityIntervalRows W s) r ≠ 0 := by
  have hstep (j : Fin s) :
      IsUnit (intervalClearedStep W z (identityIntervalRows W s) r j) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (identityIntervalRows_step_det_isUnit W s hW z r j)
  letI : Nonempty (powersetCard (Fin W ⊕ Fin W) r.1) := by
    rw [← Finite.card_pos_iff, Set.powersetCard.card,
      Nat.card_eq_fintype_card]
    apply Nat.choose_pos
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hprod : IsUnit
      ((List.ofFn fun j : Fin s ↦
        intervalClearedStep W z (identityIntervalRows W s) r j.rev).prod) := by
    apply List.prod_isUnit
    intro A hA
    simp only [List.mem_ofFn] at hA
    obtain ⟨j, rfl⟩ := hA
    exact hstep j.rev
  exact hprod.ne_zero

/-- The same fixed witness in the recursive multiaffine coordinates. -/
def identityMultiAffineRows (W s : ℕ) :
    MultiAffineRows (List.replicate (s * W) (3 * W)) :=
  finRowsToMultiAffineRows (3 * W) (s * W) (identityIntervalRows W s)

@[simp] theorem identityMultiAffineRows_toFinRows (W s : ℕ) :
    multiAffineRowsToFinRows (3 * W) (s * W)
        (identityMultiAffineRows W s) =
      identityIntervalRows W s := by
  exact multiAffineRowsToFinRows_leftInverse (3 * W) (s * W)
    (identityIntervalRows W s)

theorem identityMultiAffineRows_product_ne_zero
    (W s : ℕ) (hW : 0 < W) (z : ℂ)
    (r : Fin (2 * W + 1)) :
    intervalClearedProduct W s z
        (multiAffineRowsToFinRows (3 * W) (s * W)
          (identityMultiAffineRows W s)) r ≠ 0 := by
  simpa only [identityMultiAffineRows_toFinRows] using
    identityIntervalRows_product_ne_zero W s hW z r

/-! ## Concrete logarithmic integrability -/

/-- On recursive row coordinates, the logarithm of the concrete interval
product is in `L²`.  Its coefficient tensor and its nonzero witness are both
constructed internally from the interval product. -/
theorem intervalClearedProduct_recursive_memLp_two
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ)
    (r : Fin (2 * W + 1)) :
    MemLp (fun y : MultiAffineRows (List.replicate (s * W) (3 * W)) ↦
        Real.log ‖intervalClearedProduct W s z
          (multiAffineRowsToFinRows (3 * W) (s * W) y) r‖)
      2 (multiAffineRowLaw μ (List.replicate (s * W) (3 * W))) := by
  letI := hμ.toIsProbabilityMeasure
  let F : MultiAffineRows (List.replicate (s * W) (3 * W)) →
      Matrix (powersetCard (Fin W ⊕ Fin W) r.1)
        (powersetCard (Fin W ⊕ Fin W) r.1) ℂ := fun y ↦
    intervalClearedProduct W s z
      (multiAffineRowsToFinRows (3 * W) (s * W) y) r
  have hF : IsMultiAffine F :=
    intervalClearedProduct_isMultiAffine W s z r
  have hpos : ∀ p ∈ List.replicate (s * W) (3 * W), 0 < p := by
    intro p hp
    simp only [List.mem_replicate] at hp
    omega
  let c := multiAffineTensorOfFunction F
  have hcenter : MemLp (fun y ↦
      Real.log ‖multiAffineEval c y‖ - Real.log ‖c‖)
      2 (multiAffineRowLaw μ (List.replicate (s * W) (3 * W))) :=
    multiAffineEval_log_memLp_two hμ hpos c
  have hconst : MemLp (fun _ :
      MultiAffineRows (List.replicate (s * W) (3 * W)) ↦ Real.log ‖c‖)
      2 (multiAffineRowLaw μ (List.replicate (s * W) (3 * W))) :=
    memLp_const _
  have hfull := hcenter.add hconst
  apply MemLp.ae_eq _ hfull
  filter_upwards [] with y
  change (Real.log ‖multiAffineEval c y‖ - Real.log ‖c‖) +
      Real.log ‖c‖ = Real.log ‖F y‖
  rw [sub_add_cancel, congrFun hF.eval_tensorOfFunction y]

/-- Caller-facing `L²` input for Lemma 10.5 on the paper's flat family of
physical rows.  No affinity, coefficient, or nonvanishing certificate remains
in the statement. -/
theorem intervalDegreeLog_memLp_two
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ)
    (r : Fin (2 * W + 1)) :
    MemLp (intervalDegreeLog W s z r) 2 (intervalRowsLaw W s μ) := by
  letI := hμ.toIsProbabilityMeasure
  let e := finRowsMultiAffineRowsMeasurableEquiv (3 * W) (s * W)
  have hmp : MeasurePreserving e (intervalRowsLaw W s μ)
      (multiAffineRowLaw μ (List.replicate (s * W) (3 * W))) := by
    simpa only [intervalRowsLaw, physicalRowLaw] using
      finRowsMultiAffineRows_measurePreserving μ (3 * W) (s * W)
  have hrecursive :=
    intervalClearedProduct_recursive_memLp_two hμ W s hW z r
  have hflat := hrecursive.comp_measurePreserving hmp
  apply MemLp.ae_eq _ hflat
  filter_upwards [] with x
  change Real.log ‖intervalClearedProduct W s z
      (multiAffineRowsToFinRows (3 * W) (s * W)
        (finRowsToMultiAffineRows (3 * W) (s * W) x)) r‖ =
    intervalDegreeLog W s z r x
  rw [multiAffineRowsToFinRows_leftInverse]
  rfl

end BernoulliSection10
