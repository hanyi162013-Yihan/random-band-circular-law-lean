import CircularLawSection4.DeterministicWeightedProduct
import Mathlib.LinearAlgebra.Matrix.Permutation

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

theorem step_star_exteriorState_iff {d : ℕ} {q : ExteriorDegree (d + 1)}
    (A B : ExteriorIndex (d + 1) q) :
    ResetWord.step .star (exteriorState A) = some (exteriorState B) ↔
      (0 : Fin (d + 1)) ∉ A.val ∧
      Fin.last d ∉ B.val ∧
      ∀ i : Fin d, Fin.castSucc i ∈ B.val ↔ i.succ ∈ A.val := by
  by_cases hzero : (0 : Fin (d + 1)) ∈ A.val
  · constructor
    · intro h
      simp [ResetWord.step, exteriorState, List.ofFn_succ,
        ResetWord.shiftInsert, hzero] at h
    · rintro ⟨hz, _, _⟩
      exact (hz hzero).elim
  · let shiftedA : Fin (d + 1) → Bool :=
      Fin.lastCases false (fun i : Fin d => decide (i.succ ∈ A.val))
    have hshifted :
        List.ofFn shiftedA =
          (List.ofFn fun i : Fin d => decide (i.succ ∈ A.val)).concat false := by
      rw [List.ofFn_succ']
      simp [shiftedA]
    have hstep :
        ResetWord.step .star (exteriorState A) = some (exteriorState B) ↔
          shiftedA = fun i : Fin (d + 1) => decide (i ∈ B.val) := by
      have hAstate : exteriorState A =
          false :: List.ofFn (fun i : Fin d => decide (i.succ ∈ A.val)) := by
        rw [exteriorState, List.ofFn_succ]
        simp [hzero]
      calc
        ResetWord.step .star (exteriorState A) = some (exteriorState B) ↔
            (List.ofFn fun i : Fin d => decide (i.succ ∈ A.val)) ++ [false] =
              exteriorState B := by
                rw [ResetWord.step, hAstate]
                simp [ResetWord.shiftInsert]
        _ ↔ List.ofFn shiftedA = exteriorState B := by
          rw [hshifted, List.concat_eq_append]
        _ ↔ shiftedA = fun i : Fin (d + 1) => decide (i ∈ B.val) := by
          rw [exteriorState, List.ofFn_inj]
    rw [hstep]
    constructor
    · intro hfun
      refine ⟨hzero, ?_, ?_⟩
      · have hlast := congrFun hfun (Fin.last d)
        simpa [shiftedA] using hlast
      · intro i
        have hi := congrFun hfun i.castSucc
        simpa [shiftedA] using hi.symm
    · rintro ⟨_, hlast, hshift⟩
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [shiftedA, hlast]
      · have hj := hshift j
        simpa [shiftedA] using hj.symm

theorem rowFreeCompound_finLeftShift_ne_zero_iff_step_star
    {d : ℕ} (q : ExteriorDegree (d + 1))
    (B A : ExteriorIndex (d + 1) q) :
    rowFreeCompound q.val (finLeftShift d) (Fin.last d) B A ≠ 0 ↔
      ResetWord.step .star (exteriorState A) = some (exteriorState B) := by
  classical
  let R := ofFinEmbEquiv.symm B
  let C := ofFinEmbEquiv.symm A
  have hRmem (x : Fin q.val) : R x ∈ B.val := by
    exact (mem_range_ofFinEmbEquiv_symm_iff_mem B (R x)).mp ⟨x, rfl⟩
  have hCmem (y : Fin q.val) : C y ∈ A.val := by
    exact (mem_range_ofFinEmbEquiv_symm_iff_mem A (C y)).mp ⟨y, rfl⟩
  constructor
  · intro hne
    have hBlast : Fin.last d ∉ B.val := by
      intro h
      apply hne
      simp [rowFreeCompound, h]
    have hcomp : compound q.val (finLeftShift d) B A ≠ 0 := by
      simpa [rowFreeCompound, hBlast] using hne
    have hdet : ((finLeftShift d).submatrix R C).det ≠ 0 := by
      simpa [compound_apply, minor, R, C] using hcomp
    have hzero : (0 : Fin (d + 1)) ∉ A.val := by
      intro h0
      obtain ⟨y, hy⟩ :=
        (mem_range_ofFinEmbEquiv_symm_iff_mem A (0 : Fin (d + 1))).mpr h0
      apply hdet
      apply Matrix.det_eq_zero_of_column_eq_zero y
      intro x
      simp [finLeftShift, Matrix.submatrix_apply, C, hy]
    have hshift : ∀ i : Fin d,
        i.castSucc ∈ B.val ↔ i.succ ∈ A.val := by
      intro i
      constructor
      · intro hiB
        by_contra hiA
        obtain ⟨x, hx⟩ :=
          (mem_range_ofFinEmbEquiv_symm_iff_mem B i.castSucc).mpr hiB
        apply hdet
        apply Matrix.det_eq_zero_of_row_eq_zero x
        intro y
        have hneq : (R x).val + 1 ≠ (C y).val := by
          intro heq
          apply hiA
          have hcy : C y = i.succ := by
            apply Fin.ext
            have hxv := congrArg Fin.val hx
            simp only [Fin.val_castSucc] at hxv
            calc
              (C y).val = (R x).val + 1 := heq.symm
              _ = i.val + 1 := congrArg (fun n : ℕ => n + 1) hxv
              _ = (i.succ).val := rfl
          rw [← hcy]
          exact hCmem y
        simp [Matrix.submatrix_apply, finLeftShift, hneq]
      · intro hiA
        by_contra hiB
        obtain ⟨y, hy⟩ :=
          (mem_range_ofFinEmbEquiv_symm_iff_mem A i.succ).mpr hiA
        apply hdet
        apply Matrix.det_eq_zero_of_column_eq_zero y
        intro x
        have hneq : (R x).val + 1 ≠ (C y).val := by
          intro heq
          apply hiB
          have hrx : R x = i.castSucc := by
            apply Fin.ext
            have hyv := congrArg Fin.val hy
            simp only [Fin.val_succ] at hyv
            simp only [Fin.val_castSucc]
            exact Nat.add_right_cancel (by
              calc
                (R x).val + 1 = (C y).val := heq
                _ = i.val + 1 := hyv)
          rw [← hrx]
          exact hRmem x
        simp [Matrix.submatrix_apply, finLeftShift, hneq]
    exact (step_star_exteriorState_iff A B).mpr ⟨hzero, hBlast, hshift⟩
  · intro hstep
    obtain ⟨hzero, hBlast, hshift⟩ :=
      (step_star_exteriorState_iff A B).mp hstep
    have hRlast (x : Fin q.val) : R x ≠ Fin.last d := by
      intro hx
      apply hBlast
      rw [← hx]
      exact hRmem x
    let shiftedRows : Fin q.val ↪o Fin (d + 1) :=
      OrderEmbedding.ofStrictMono
        (fun x => (Fin.castPred (R x) (hRlast x)).succ)
        (by
          intro x y hxy
          apply Fin.mk_lt_mk.mpr
          exact Nat.add_lt_add_right (R.strictMono hxy) 1)
    have hsets : ofFinEmbEquiv shiftedRows = A := by
      apply Subtype.ext
      ext a
      change a ∈ ofFinEmbEquiv shiftedRows ↔ a ∈ A
      rw [mem_ofFinEmbEquiv_iff_mem_range]
      constructor
      · rintro ⟨x, rfl⟩
        let i : Fin d := Fin.castPred (R x) (hRlast x)
        have hiB : i.castSucc ∈ B.val := by
          rw [Fin.castSucc_castPred]
          exact hRmem x
        exact (hshift i).mp hiB
      · intro ha
        have ha0 : a ≠ 0 := by
          intro haz
          subst a
          exact hzero ha
        let i : Fin d := Fin.pred a ha0
        have his : i.succ ∈ A.val := by
          change i.succ ∈ A
          simpa [i, Fin.succ_pred] using ha
        have hiB : i.castSucc ∈ B.val := (hshift i).mpr his
        obtain ⟨x, hx⟩ :=
          (mem_range_ofFinEmbEquiv_symm_iff_mem B i.castSucc).mpr hiB
        refine ⟨x, ?_⟩
        change (Fin.castPred (R x) (hRlast x)).succ = a
        have hpred : Fin.castPred (R x) (hRlast x) = i := by
          apply Fin.castSucc_injective
          rw [Fin.castSucc_castPred]
          exact hx
        rw [hpred]
        exact Fin.succ_pred a ha0
    have hEmb : shiftedRows = C := by
      apply ofFinEmbEquiv.injective
      simpa [C] using hsets
    have hmatrix : (finLeftShift d).submatrix R C = 1 := by
      ext x y
      have hiff : (R x).val + 1 = (R y).val + 1 ↔ x = y := by
        constructor
        · intro h
          apply R.injective
          apply Fin.ext
          omega
        · intro h
          subst y
          rfl
      rw [← hEmb]
      have hentry : (R x).val + 1 = (shiftedRows y).val ↔ x = y := by
        change (R x).val + 1 =
          (Fin.castPred (R y) (hRlast y)).succ.val ↔ x = y
        simpa using hiff
      simp only [Matrix.submatrix_apply, finLeftShift, Matrix.one_apply]
      exact if_congr hentry rfl rfl
    have hcomp : compound q.val (finLeftShift d) B A = 1 := by
      rw [compound_apply]
      unfold minor
      change ((finLeftShift d).submatrix R C).det = 1
      rw [hmatrix, Matrix.det_one]
    simp [rowFreeCompound, hBlast, hcomp]

theorem orderedCoefficient_star_ne_zero_iff_booleanSupportK
    {d : ℕ} (q : ExteriorDegree (d + 1))
    (B A : ExteriorIndex (d + 1) q) :
    orderedCoefficient d q none B A ≠ 0 ↔
      booleanSupportK q none B A ≠ 0 := by
  rw [show orderedCoefficient d q none =
      rowFreeCompound q.val (finLeftShift d) (Fin.last d) by rfl]
  rw [rowFreeCompound_finLeftShift_ne_zero_iff_step_star q B A]
  change ResetWord.step .star (exteriorState A) = some (exteriorState B) ↔
    (if exteriorSupportStep .star A = some B then (1 : ℂ) else 0) ≠ 0
  constructor
  · intro h
    have hs : exteriorSupportStep .star A = some B :=
      (exteriorSupportStep_eq_some_iff .star A B).mpr h
    simp [hs]
  · intro hne
    by_contra h
    have hs : exteriorSupportStep .star A ≠ some B := by
      intro hs
      exact h ((exteriorSupportStep_eq_some_iff .star A B).mp hs)
    simp [hs] at hne

theorem contractAt_ofFn {n : ℕ} (f : Fin n → Bool) (j : Fin n) :
    ResetWord.contractAt j.val (List.ofFn f) =
      if f j then
        some (List.ofFn fun i => if i = j then false else f i)
      else none := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [List.ofFn_succ]
      refine Fin.cases ?_ (fun j' => ?_) j
      · cases h : f 0 <;>
          simp [ResetWord.contractAt, h, List.ofFn_succ]
      · simp only [Fin.val_succ, ResetWord.contractAt]
        rw [ih (fun i => f i.succ) j']
        by_cases hj : f j'.succ = true
        · simp only [hj, if_true, Option.map_some]
          congr 2
          rw [List.ofFn_succ]
          congr 1
          apply List.ofFn_inj.mpr
          funext i
          simp
        · simp [hj]

theorem step_reset_exteriorState_iff {d : ℕ} {q : ExteriorDegree (d + 1)}
    (j : Fin (d + 1)) (A B : ExteriorIndex (d + 1) q) :
    ResetWord.step (.reset j.val) (exteriorState A) = some (exteriorState B) ↔
      j ∈ A.val ∧
      (j = 0 ∨ (0 : Fin (d + 1)) ∉ A.val) ∧
      Fin.last d ∈ B.val ∧
      ∀ i : Fin d,
        i.castSucc ∈ B.val ↔ i.succ ∈ A.val ∧ i.succ ≠ j := by
  classical
  let occA : Fin (d + 1) → Bool := fun i => decide (i ∈ A.val)
  let cleared : Fin (d + 1) → Bool :=
    fun i => if i = j then false else occA i
  let shifted : Fin (d + 1) → Bool :=
    Fin.lastCases true (fun i : Fin d => cleared i.succ)
  have hcleared (a : Fin (d + 1)) :
      cleared a = decide (a ∈ A.val ∧ a ≠ j) := by
    by_cases ha : a = j
    · subst a
      simp [cleared]
    · simp [cleared, occA, ha]
  have hshifted :
      List.ofFn shifted =
        (List.ofFn fun i : Fin d => cleared i.succ).concat true := by
    rw [List.ofFn_succ']
    simp [shifted]
  by_cases hjA : j ∈ A.val
  · have hjbool : occA j = true := by simp [occA, hjA]
    have hcontract :
        ResetWord.contractAt j.val (exteriorState A) =
          some (List.ofFn cleared) := by
      rw [exteriorState, contractAt_ofFn occA j]
      simp only [hjbool, if_true]
      rfl
    by_cases hgate : j = 0 ∨ (0 : Fin (d + 1)) ∉ A.val
    · have hclear0 : cleared 0 = false := by
        rcases hgate with hj0 | hA0
        · subst j
          simp [cleared]
        · have hj0 : (0 : Fin (d + 1)) ≠ j := by
            intro h
            subst j
            exact hA0 hjA
          simp [cleared, occA, hj0, hA0]
      have hstep :
          ResetWord.step (.reset j.val) (exteriorState A) =
              some (exteriorState B) ↔
            shifted = fun i : Fin (d + 1) => decide (i ∈ B.val) := by
        calc
          ResetWord.step (.reset j.val) (exteriorState A) =
                some (exteriorState B) ↔
              (List.ofFn fun i : Fin d => cleared i.succ) ++ [true] =
                exteriorState B := by
                  rw [ResetWord.step, hcontract, Option.bind_some,
                    List.ofFn_succ]
                  simp [ResetWord.shiftInsert, hclear0]
          _ ↔ List.ofFn shifted = exteriorState B := by
            rw [hshifted, List.concat_eq_append]
          _ ↔ shifted = fun i : Fin (d + 1) => decide (i ∈ B.val) := by
            rw [exteriorState, List.ofFn_inj]
      rw [hstep]
      constructor
      · intro hfun
        refine ⟨hjA, hgate, ?_, ?_⟩
        · have hlast := congrFun hfun (Fin.last d)
          simpa [shifted] using hlast.symm
        · intro i
          have hi := congrFun hfun i.castSucc
          simp only [shifted, Fin.lastCases_castSucc] at hi
          rw [hcleared] at hi
          exact (decide_eq_decide.mp hi).symm
      · rintro ⟨_, _, hlast, hmove⟩
        funext i
        refine Fin.lastCases ?_ (fun t => ?_) i
        · simp [shifted, hlast]
        · have ht := hmove t
          simp only [shifted, Fin.lastCases_castSucc]
          rw [hcleared]
          exact decide_eq_decide.mpr ht.symm
    · have hj0 : j ≠ 0 := fun h => hgate (Or.inl h)
      have hA0 : (0 : Fin (d + 1)) ∈ A.val := by
        by_contra h
        exact hgate (Or.inr h)
      have hclear0 : cleared 0 = true := by
        have h0j : (0 : Fin (d + 1)) ≠ j := fun h => hj0 h.symm
        simp [cleared, occA, h0j, hA0]
      constructor
      · intro h
        rw [ResetWord.step, hcontract, Option.bind_some,
          List.ofFn_succ] at h
        simp [ResetWord.shiftInsert, hclear0] at h
      · rintro ⟨_, hg, _, _⟩
        exact (hgate hg).elim
  · have hjbool : occA j = false := by simp [occA, hjA]
    have hcontract : ResetWord.contractAt j.val (exteriorState A) = none := by
      rw [exteriorState, contractAt_ofFn occA j]
      simp [hjbool]
    constructor
    · intro h
      rw [ResetWord.step, hcontract] at h
      simp at h
    · rintro ⟨h, _, _, _⟩
      exact (hjA h).elim

theorem rowMinorCoefficient_finLeftShift_ne_zero_imp_step_reset
    {d : ℕ} (q : ExteriorDegree (d + 1)) (j : Fin (d + 1))
    (B A : ExteriorIndex (d + 1) q)
    (hne : rowMinorCoefficient q.val (finLeftShift d) (Fin.last d) j B A ≠ 0) :
    ResetWord.step (.reset j.val) (exteriorState A) = some (exteriorState B) := by
  classical
  let R := ofFinEmbEquiv.symm B
  let C := ofFinEmbEquiv.symm A
  let U := (finLeftShift d).updateRow (Fin.last d) (Pi.single j 1)
  have hRmem (x : Fin q.val) : R x ∈ B.val :=
    (mem_range_ofFinEmbEquiv_symm_iff_mem B (R x)).mp ⟨x, rfl⟩
  have hCmem (y : Fin q.val) : C y ∈ A.val :=
    (mem_range_ofFinEmbEquiv_symm_iff_mem A (C y)).mp ⟨y, rfl⟩
  have hBlast : Fin.last d ∈ B.val := by
    by_contra h
    apply hne
    simp [rowMinorCoefficient, h]
  have hcomp : compound q.val U B A ≠ 0 := by
    simpa [rowMinorCoefficient, hBlast, U] using hne
  have hdet : (U.submatrix R C).det ≠ 0 := by
    simpa [compound_apply, minor, R, C] using hcomp
  obtain ⟨xlast, hxlast⟩ :=
    (mem_range_ofFinEmbEquiv_symm_iff_mem B (Fin.last d)).mpr hBlast
  have hjA : j ∈ A.val := by
    by_contra hj
    apply hdet
    apply Matrix.det_eq_zero_of_row_eq_zero xlast
    intro y
    have hcy : C y ≠ j := by
      intro h
      apply hj
      rw [← h]
      exact hCmem y
    have hxlastR : R xlast = Fin.last d := hxlast
    simp only [Matrix.submatrix_apply, U, Matrix.updateRow_apply]
    rw [if_pos hxlastR]
    exact Pi.single_eq_of_ne hcy 1
  have hgate : j = 0 ∨ (0 : Fin (d + 1)) ∉ A.val := by
    by_cases hj0 : j = 0
    · exact Or.inl hj0
    · refine Or.inr ?_
      intro hA0
      obtain ⟨yzero, hyzero⟩ :=
        (mem_range_ofFinEmbEquiv_symm_iff_mem A (0 : Fin (d + 1))).mpr hA0
      apply hdet
      apply Matrix.det_eq_zero_of_column_eq_zero yzero
      intro x
      by_cases hx : R x = Fin.last d
      · have h0j : (0 : Fin (d + 1)) ≠ j := fun h => hj0 h.symm
        simp only [Matrix.submatrix_apply, U, Matrix.updateRow_apply]
        rw [if_pos hx, hyzero]
        exact Pi.single_eq_of_ne h0j 1
      · simp only [Matrix.submatrix_apply, U, Matrix.updateRow_apply]
        rw [if_neg hx, hyzero]
        simp [finLeftShift]
  have hmove : ∀ i : Fin d,
      i.castSucc ∈ B.val ↔ i.succ ∈ A.val ∧ i.succ ≠ j := by
    intro i
    constructor
    · intro hiB
      obtain ⟨x, hx⟩ :=
        (mem_range_ofFinEmbEquiv_symm_iff_mem B i.castSucc).mpr hiB
      have hxne : R x ≠ Fin.last d := by
        rw [hx]
        exact Fin.castSucc_ne_last i
      have hiA : i.succ ∈ A.val := by
        by_contra hi
        apply hdet
        apply Matrix.det_eq_zero_of_row_eq_zero x
        intro y
        have hneq : (R x).val + 1 ≠ (C y).val := by
          intro heq
          apply hi
          have hcy : C y = i.succ := by
            apply Fin.ext
            have hxv := congrArg Fin.val hx
            simp only [Fin.val_castSucc] at hxv
            calc
              (C y).val = (R x).val + 1 := heq.symm
              _ = i.val + 1 := congrArg (fun n : ℕ => n + 1) hxv
              _ = (i.succ).val := rfl
          rw [← hcy]
          exact hCmem y
        simp [Matrix.submatrix_apply, U, Matrix.updateRow_apply, hxne,
          finLeftShift, hneq]
      refine ⟨hiA, ?_⟩
      intro hij
      have hxx : x ≠ xlast := by
        intro h
        apply hxne
        rw [h, hxlast]
      apply hdet
      apply Matrix.det_zero_of_row_eq hxx
      funext y
      have hxlast' : R xlast = Fin.last d := hxlast
      simp only [Matrix.submatrix_apply, U, Matrix.updateRow_apply]
      rw [if_neg hxne, if_pos hxlast']
      have hshiftj : (R x).val + 1 = j.val := by
        calc
          (R x).val + 1 = i.castSucc.val + 1 :=
            congrArg (fun z : Fin (d + 1) => z.val + 1) hx
          _ = i.succ.val := rfl
          _ = j.val := congrArg Fin.val hij
      by_cases hcy : C y = j
      · rw [hcy]
        simp [finLeftShift, hshiftj]
      · have hneval : j.val ≠ (C y).val := by
          intro h
          apply hcy
          apply Fin.ext
          exact h.symm
        simp [finLeftShift, hcy, hshiftj, hneval]
    · rintro ⟨hiA, hij⟩
      by_contra hiB
      obtain ⟨y, hy⟩ :=
        (mem_range_ofFinEmbEquiv_symm_iff_mem A i.succ).mpr hiA
      apply hdet
      apply Matrix.det_eq_zero_of_column_eq_zero y
      intro x
      by_cases hx : R x = Fin.last d
      · have hcy : C y ≠ j := by
          intro h
          apply hij
          rw [← hy]
          exact h
        simp [Matrix.submatrix_apply, U, Matrix.updateRow_apply, hx, hcy]
      · have hneq : (R x).val + 1 ≠ (C y).val := by
          intro heq
          apply hiB
          have hrx : R x = i.castSucc := by
            apply Fin.ext
            have hyv := congrArg Fin.val hy
            simp only [Fin.val_succ] at hyv
            simp only [Fin.val_castSucc]
            exact Nat.add_right_cancel (by
              calc
                (R x).val + 1 = (C y).val := heq
                _ = i.val + 1 := hyv)
          rw [← hrx]
          exact hRmem x
        simp [Matrix.submatrix_apply, U, Matrix.updateRow_apply, hx,
          finLeftShift, hneq]
  exact (step_reset_exteriorState_iff j A B).mpr
    ⟨hjA, hgate, hBlast, hmove⟩

theorem rowMinorCoefficient_finLeftShift_ne_zero_of_step_reset
    {d : ℕ} (q : ExteriorDegree (d + 1)) (j : Fin (d + 1))
    (B A : ExteriorIndex (d + 1) q)
    (hstep : ResetWord.step (.reset j.val) (exteriorState A) =
      some (exteriorState B)) :
    rowMinorCoefficient q.val (finLeftShift d) (Fin.last d) j B A ≠ 0 := by
  classical
  obtain ⟨hjA, _hgate, hBlast, hmove⟩ :=
    (step_reset_exteriorState_iff j A B).mp hstep
  let R := ofFinEmbEquiv.symm B
  let C := ofFinEmbEquiv.symm A
  let U := (finLeftShift d).updateRow (Fin.last d) (Pi.single j 1)
  have hRmem (x : Fin q.val) : R x ∈ B.val :=
    (mem_range_ofFinEmbEquiv_symm_iff_mem B (R x)).mp ⟨x, rfl⟩
  let g : Fin q.val → Fin (d + 1) := fun x =>
    if hx : R x = Fin.last d then j
    else (Fin.castPred (R x) hx).succ
  have hg_mem (x : Fin q.val) : g x ∈ A.val := by
    by_cases hx : R x = Fin.last d
    · simpa [g, hx] using hjA
    · let i : Fin d := Fin.castPred (R x) hx
      have hiB : i.castSucc ∈ B.val := by
        rw [Fin.castSucc_castPred]
        exact hRmem x
      have hiA := (hmove i).mp hiB
      simpa [g, hx, i] using hiA.1
  have hg_ne_j (x : Fin q.val) (hx : R x ≠ Fin.last d) : g x ≠ j := by
    let i : Fin d := Fin.castPred (R x) hx
    have hiB : i.castSucc ∈ B.val := by
      rw [Fin.castSucc_castPred]
      exact hRmem x
    have hne := (hmove i).mp hiB |>.2
    simpa [g, hx, i] using hne
  have hg_inj : Function.Injective g := by
    intro x y hxy
    by_cases hx : R x = Fin.last d
    · by_cases hy : R y = Fin.last d
      · exact R.injective (hx.trans hy.symm)
      · exfalso
        apply hg_ne_j y hy
        rw [← hxy]
        simp [g, hx]
    · by_cases hy : R y = Fin.last d
      · exfalso
        apply hg_ne_j x hx
        rw [hxy]
        simp [g, hy]
      · apply R.injective
        rw [← Fin.castSucc_castPred (i := R x) hx,
          ← Fin.castSucc_castPred (i := R y) hy]
        apply Fin.succ_injective
        simpa [g, hx, hy] using hxy
  have hexists (x : Fin q.val) : ∃ y : Fin q.val, C y = g x :=
    (mem_range_ofFinEmbEquiv_symm_iff_mem A (g x)).mpr (hg_mem x)
  let f : Fin q.val → Fin q.val := fun x => (hexists x).choose
  have hf_spec (x : Fin q.val) : C (f x) = g x := (hexists x).choose_spec
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply hg_inj
    rw [← hf_spec x, ← hf_spec y, hxy]
  have hf_bij : Function.Bijective f :=
    ⟨hf_inj, Finite.injective_iff_surjective.mp hf_inj⟩
  let e : Equiv.Perm (Fin q.val) := Equiv.ofBijective f hf_bij
  have hmatrix : U.submatrix R C = e.permMatrix ℂ := by
    ext x y
    have hentry : U (R x) (C y) = if g x = C y then 1 else 0 := by
      by_cases hx : R x = Fin.last d
      · by_cases h : j = C y <;>
          simp [U, g, hx, h, eq_comm]
      · simp only [U, Matrix.updateRow_apply, if_neg hx,
          finLeftShift, g, dif_neg hx]
        apply if_congr
        · constructor
          · intro h
            apply Fin.ext
            exact h
          · intro h
            exact congrArg Fin.val h
        · rfl
        · rfl
    rw [Matrix.submatrix_apply, hentry]
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Option.mem_def]
    have hiff : g x = C y ↔ some (e x) = some y := by
      simp only [Option.some.injEq]
      rw [← hf_spec x]
      rw [C.injective.eq_iff]
      rfl
    exact if_congr hiff rfl rfl
  have hdet : (U.submatrix R C).det ≠ 0 := by
    rw [hmatrix, Matrix.det_permutation]
    simp
  simpa [rowMinorCoefficient, hBlast, compound_apply, minor, R, C, U] using hdet

theorem rowMinorCoefficient_finLeftShift_ne_zero_iff_step_reset
    {d : ℕ} (q : ExteriorDegree (d + 1)) (j : Fin (d + 1))
    (B A : ExteriorIndex (d + 1) q) :
    rowMinorCoefficient q.val (finLeftShift d) (Fin.last d) j B A ≠ 0 ↔
      ResetWord.step (.reset j.val) (exteriorState A) =
        some (exteriorState B) := by
  constructor
  · exact rowMinorCoefficient_finLeftShift_ne_zero_imp_step_reset q j B A
  · exact rowMinorCoefficient_finLeftShift_ne_zero_of_step_reset q j B A

theorem orderedCoefficient_ne_zero_iff_exteriorSupportStep
    {d : ℕ} (q : ExteriorDegree (d + 1))
    (ell : ResetLabel (d + 1)) (B A : ExteriorIndex (d + 1) q) :
    orderedCoefficient d q ell B A ≠ 0 ↔
      exteriorSupportStep (supportLabel ell) A = some B := by
  cases ell with
  | none =>
      rw [show orderedCoefficient d q none =
        rowFreeCompound q.val (finLeftShift d) (Fin.last d) by rfl]
      rw [rowFreeCompound_finLeftShift_ne_zero_iff_step_star q B A]
      exact (exteriorSupportStep_eq_some_iff .star A B).symm
  | some j =>
      change -rowMinorCoefficient q.val (finLeftShift d) (Fin.last d) j B A ≠ 0 ↔
        exteriorSupportStep (.reset j.val) A = some B
      rw [neg_ne_zero, rowMinorCoefficient_finLeftShift_ne_zero_iff_step_reset q j B A]
      exact (exteriorSupportStep_eq_some_iff (.reset j.val) A B).symm

theorem orderedCoefficient_ne_zero_iff_booleanSupportK
    {d : ℕ} (q : ExteriorDegree (d + 1))
    (ell : ResetLabel (d + 1)) (B A : ExteriorIndex (d + 1) q) :
    orderedCoefficient d q ell B A ≠ 0 ↔
      booleanSupportK q ell B A ≠ 0 := by
  rw [orderedCoefficient_ne_zero_iff_exteriorSupportStep q ell B A]
  simp [booleanSupportK, partialMapMatrix]

noncomputable def orderedCoefficient_arbitrarySingletonCertificate
    {d : ℕ} (r : ExteriorDegree (d + 1))
    (I J : ExteriorIndex (d + 1) r) :
    SingletonWordCertificate (orderedCoefficient d) (arbitrarySupportWord I J)
      r I J :=
  singletonWordCertificate_of_step_data
    (booleanSupport_arbitrarySingletonCertificate r I J)
    (fun q ell B A =>
      orderedCoefficient_ne_zero_iff_exteriorSupportStep q ell B A)
    (fun q ell B A hne =>
      norm_orderedCoefficient_eq_one_of_ne_zero d q ell B A hne)

end CircularLawSection4
