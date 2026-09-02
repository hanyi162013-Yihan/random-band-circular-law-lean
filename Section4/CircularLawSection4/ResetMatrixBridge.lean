import CircularLawSection4.Isolation
import CircularLawSection4.ResetWord
import Mathlib.Data.Bool.Count
import Mathlib.Data.Fintype.Vector

/-!
# Boolean reset words as finite matrices

This module transports the Boolean support dynamics from `ResetWord.lean` to
the concrete `Set.powersetCard` coordinate types used by the exterior-matrix
modules.  It constructs a genuine diagonal `SingletonWordCertificate` for the
canonical support matrices.  Exterior orientation signs are deliberately not
inserted here; a later bridge may replace every surviving `1` by its unit
phase without changing the support argument.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

namespace ResetWord

theorem particleCount_append (A B : State) :
    particleCount (A ++ B) = particleCount A + particleCount B := by
  induction A with
  | nil => simp [particleCount]
  | cons b A ih =>
      cases b
      · simp [particleCount, ih]
      · simp [particleCount, ih]
        omega

theorem contractAt_preserves_length {j : ℕ} {A B : State}
    (h : contractAt j A = some B) : B.length = A.length := by
  induction j generalizing A B with
  | zero =>
      cases A with
      | nil => simp [contractAt] at h
      | cons b A =>
          cases b <;> simp [contractAt] at h
          subst B
          simp
  | succ j ih =>
      cases A with
      | nil => simp [contractAt] at h
      | cons b A =>
          simp only [contractAt] at h
          cases hc : contractAt j A with
          | none => simp [hc] at h
          | some C =>
              simp [hc] at h
              subst B
              simp [ih hc]

theorem contractAt_decreases_particleCount {j : ℕ} {A B : State}
    (h : contractAt j A = some B) : particleCount B + 1 = particleCount A := by
  induction j generalizing A B with
  | zero =>
      cases A with
      | nil => simp [contractAt] at h
      | cons b A =>
          cases b <;> simp [contractAt] at h
          subst B
          simp [particleCount]
  | succ j ih =>
      cases A with
      | nil => simp [contractAt] at h
      | cons b A =>
          simp only [contractAt] at h
          cases hc : contractAt j A with
          | none => simp [hc] at h
          | some C =>
              simp [hc] at h
              subst B
              cases b <;> simp [particleCount, ih hc, Nat.add_comm]

theorem shiftInsert_preserves_length {new : Bool} {A B : State}
    (h : shiftInsert new A = some B) : B.length = A.length := by
  cases A with
  | nil => simp [shiftInsert] at h
  | cons b A =>
      cases b <;> simp [shiftInsert] at h
      subst B
      simp

theorem shiftInsert_particleCount {new : Bool} {A B : State}
    (h : shiftInsert new A = some B) :
    particleCount B = particleCount A + new.toNat := by
  cases A with
  | nil => simp [shiftInsert] at h
  | cons b A =>
      cases b <;> simp [shiftInsert] at h
      subst B
      cases new <;> simp [particleCount, particleCount_append]

theorem step_preserves_length {ℓ : Label} {A B : State}
    (h : step ℓ A = some B) : B.length = A.length := by
  cases ℓ with
  | star => exact shiftInsert_preserves_length h
  | reset j =>
      simp only [step] at h
      cases hc : contractAt j A with
      | none => simp [hc] at h
      | some C =>
          simp [hc] at h
          exact (shiftInsert_preserves_length h).trans
            (contractAt_preserves_length hc)

theorem step_preserves_particleCount {ℓ : Label} {A B : State}
    (h : step ℓ A = some B) : particleCount B = particleCount A := by
  cases ℓ with
  | star =>
      simpa using shiftInsert_particleCount h
  | reset j =>
      simp only [step] at h
      cases hc : contractAt j A with
      | none => simp [hc] at h
      | some C =>
          simp [hc] at h
          have hs := shiftInsert_particleCount h
          have hcCount := contractAt_decreases_particleCount hc
          simp only [Bool.toNat_true, Nat.add_one] at hs
          omega

end ResetWord

/-- Boolean occupation list of an exterior-basis subset. -/
def exteriorState {d : ℕ} {q : ExteriorDegree d}
    (A : ExteriorIndex d q) : ResetWord.State :=
  List.ofFn fun i : Fin d => decide (i ∈ (A : Finset (Fin d)))

@[simp] theorem exteriorState_length {d : ℕ} {q : ExteriorDegree d}
    (A : ExteriorIndex d q) : (exteriorState A).length = d := by
  simp [exteriorState]

theorem fin_countP_indicator {d : ℕ} (s : Finset (Fin d)) :
    Fin.countP (fun i => decide (i ∈ s)) = s.card := by
  classical
  rw [Fin.countP, Fin.sum_eq_sum_map_finRange]
  rw [← List.sum_toFinset _ (List.nodup_finRange d)]
  have hterm (i : Fin d) :
      (decide (i ∈ s)).toNat = if i ∈ s then 1 else 0 := by
    by_cases hi : i ∈ s <;> simp [hi]
  simp_rw [hterm]
  simpa only [List.toFinset_finRange] using
    (Finset.card_eq_sum_ite (s := s) (t := Finset.univ)
      (Finset.subset_univ s)).symm

theorem particleCount_ofFn {d : ℕ} (f : Fin d → Bool) :
    ResetWord.particleCount (List.ofFn f) = Fin.countP f := by
  induction d with
  | zero => simp [ResetWord.particleCount]
  | succ d ih =>
      rw [List.ofFn_succ, Fin.countP_succ]
      cases h : f 0 <;>
        simp [ResetWord.particleCount, ih (f := fun i => f i.succ), Nat.add_comm]

@[simp] theorem exteriorState_particleCount {d : ℕ} {q : ExteriorDegree d}
    (A : ExteriorIndex d q) : ResetWord.particleCount (exteriorState A) = q.val := by
  rw [exteriorState, particleCount_ofFn, fin_countP_indicator]
  exact A.prop

theorem exteriorState_injective {d : ℕ} {q : ExteriorDegree d} :
    Function.Injective (exteriorState : ExteriorIndex d q → ResetWord.State) := by
  intro A B h
  apply Subtype.ext
  ext i
  have hf :
      (fun j : Fin d => decide (j ∈ (A : Finset (Fin d)))) =
        fun j : Fin d => decide (j ∈ (B : Finset (Fin d))) :=
    List.ofFn_inj.mp h
  have hi := congrFun hf i
  by_cases hA : i ∈ (A : Finset (Fin d)) <;>
    by_cases hB : i ∈ (B : Finset (Fin d)) <;> simp_all

/-- Recover a finite subset from a Boolean state of the specified length. -/
def finsetOfState {d : ℕ} (S : ResetWord.State) (hlen : S.length = d) :
    Finset (Fin d) :=
  Finset.univ.filter fun i => S.get (Fin.cast hlen.symm i)

@[simp] theorem exteriorState_finsetOfState {d : ℕ} (S : ResetWord.State)
    (hlen : S.length = d) :
    List.ofFn (fun i : Fin d => decide (i ∈ finsetOfState S hlen)) = S := by
  apply List.ext_get (by simp [hlen])
  intro n hleft hright
  simp [finsetOfState]

/-- Turn a Boolean state of length `d` and particle number `q` back into the
corresponding exterior-coordinate index. -/
def exteriorIndexOfState {d : ℕ} {q : ExteriorDegree d}
    (S : ResetWord.State) (hlen : S.length = d)
    (hcount : ResetWord.particleCount S = q.val) : ExteriorIndex d q :=
  ⟨finsetOfState S hlen, by
    have h := particleCount_ofFn
      (fun i : Fin d => decide (i ∈ finsetOfState S hlen))
    rw [exteriorState_finsetOfState S hlen, hcount,
      fin_countP_indicator] at h
    exact h.symm⟩

@[simp] theorem exteriorState_exteriorIndexOfState {d : ℕ}
    {q : ExteriorDegree d} (S : ResetWord.State) (hlen : S.length = d)
    (hcount : ResetWord.particleCount S = q.val) :
    exteriorState (exteriorIndexOfState S hlen hcount) = S := by
  exact exteriorState_finsetOfState S hlen

theorem exists_exteriorState_of_step_eq_some {d : ℕ}
    {q : ExteriorDegree d} (ℓ : ResetWord.Label) (A : ExteriorIndex d q)
    {S : ResetWord.State} (h : ResetWord.step ℓ (exteriorState A) = some S) :
    ∃ B : ExteriorIndex d q, S = exteriorState B := by
  have hlen : S.length = d :=
    (ResetWord.step_preserves_length h).trans (exteriorState_length A)
  have hcount : ResetWord.particleCount S = q.val :=
    (ResetWord.step_preserves_particleCount h).trans
      (exteriorState_particleCount A)
  exact ⟨exteriorIndexOfState S hlen hcount,
    (exteriorState_exteriorIndexOfState S hlen hcount).symm⟩

/-- Partial action of one reset label on fixed exterior degree, retaining only
the Boolean support and assigning coefficient `1` to a surviving transition. -/
noncomputable def exteriorSupportStep {d : ℕ} {q : ExteriorDegree d}
    (ℓ : ResetWord.Label) (A : ExteriorIndex d q) : Option (ExteriorIndex d q) :=
  if h : ∃ B : ExteriorIndex d q,
      ResetWord.step ℓ (exteriorState A) = some (exteriorState B) then
    some h.choose
  else none

theorem exteriorSupportStep_eq_some_iff {d : ℕ} {q : ExteriorDegree d}
    (ℓ : ResetWord.Label) (A B : ExteriorIndex d q) :
    exteriorSupportStep ℓ A = some B ↔
      ResetWord.step ℓ (exteriorState A) = some (exteriorState B) := by
  classical
  unfold exteriorSupportStep
  split_ifs with h
  · constructor
    · intro heq
      have hchoose : h.choose = B := Option.some.inj heq
      simpa [hchoose] using h.choose_spec
    · intro hB
      apply congrArg some
      apply exteriorState_injective
      exact Option.some.inj (h.choose_spec.symm.trans hB)
  · constructor
    · simp
    · intro hB
      exact False.elim (h ⟨B, hB⟩)

theorem exteriorSupportStep_map {d : ℕ} {q : ExteriorDegree d}
    (ℓ : ResetWord.Label) (A : ExteriorIndex d q) :
    Option.map exteriorState (exteriorSupportStep ℓ A) =
      ResetWord.step ℓ (exteriorState A) := by
  cases hs : ResetWord.step ℓ (exteriorState A) with
  | none =>
      cases he : exteriorSupportStep ℓ A with
      | none => rfl
      | some B =>
          have := (exteriorSupportStep_eq_some_iff ℓ A B).mp he
          rw [hs] at this
          contradiction
  | some S =>
      obtain ⟨B, hSB⟩ := exists_exteriorState_of_step_eq_some ℓ A hs
      have he : exteriorSupportStep ℓ A = some B :=
        (exteriorSupportStep_eq_some_iff ℓ A B).mpr (by simpa [hSB] using hs)
      simp [he, hSB]

/-- Partial support action of a reset word. -/
def exteriorSupportRun {d : ℕ} {q : ExteriorDegree d} :
    List ResetWord.Label → ExteriorIndex d q → Option (ExteriorIndex d q)
  | [], A => some A
  | ℓ :: w, A => (exteriorSupportStep ℓ A).bind (exteriorSupportRun w)

theorem exteriorSupportRun_map {d : ℕ} {q : ExteriorDegree d}
    (w : List ResetWord.Label) (A : ExteriorIndex d q) :
    Option.map exteriorState (exteriorSupportRun w A) =
      ResetWord.run w (exteriorState A) := by
  induction w generalizing A with
  | nil => rfl
  | cons ℓ w ih =>
      simp only [exteriorSupportRun, ResetWord.run_cons]
      cases he : exteriorSupportStep ℓ A with
      | none =>
          have hm := exteriorSupportStep_map ℓ A
          simp [he] at hm
          rw [← hm]
          rfl
      | some B =>
          have hm := exteriorSupportStep_map ℓ A
          simp [he] at hm
          rw [← hm]
          simpa using ih B

theorem exteriorSupportRun_singleton {d : ℕ} {q : ExteriorDegree d}
    (J A : ExteriorIndex d q) :
    exteriorSupportRun (ResetWord.singletonWord (exteriorState J)) A =
      if A = J then some J else none := by
  apply Option.map_injective exteriorState_injective
  rw [exteriorSupportRun_map]
  have h := ResetWord.singleton_domain_word (exteriorState J) (exteriorState A)
    (by simp)
  simpa [exteriorState_injective.eq_iff] using h

theorem exteriorSupportRun_singleton_other_degree {d : ℕ}
    {r q : ExteriorDegree d} (hrq : q ≠ r)
    (J : ExteriorIndex d r) (A : ExteriorIndex d q) :
    exteriorSupportRun (ResetWord.singletonWord (exteriorState J)) A = none := by
  apply Option.map_injective exteriorState_injective
  rw [exteriorSupportRun_map]
  have hdegree :
      ResetWord.particleCount (exteriorState A) ≠
        ResetWord.particleCount (exteriorState J) := by
    simp only [exteriorState_particleCount]
    intro hval
    apply hrq
    exact Fin.ext hval
  simpa using ResetWord.singletonWord_kills_other_degree
    (exteriorState J) (exteriorState A) (by simp) hdegree

section PartialMapMatrix

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Matrix of a deterministic partial map, with columns as inputs. -/
def partialMapMatrix (f : α → Option α) : Matrix α α ℂ :=
  fun B A => if f A = some B then 1 else 0

theorem partialMapMatrix_bind (f g : α → Option α) :
    partialMapMatrix g * partialMapMatrix f =
      partialMapMatrix fun A => (f A).bind g := by
  classical
  ext B A
  cases h : f A with
  | none => simp [partialMapMatrix, Matrix.mul_apply, h]
  | some C => simp [partialMapMatrix, Matrix.mul_apply, h]

/-- Apply a chronological list of deterministic partial maps. -/
def partialMapRun : List (α → Option α) → α → Option α
  | [], A => some A
  | f :: fs, A => (f A).bind (partialMapRun fs)

theorem chronological_partialMapMatrix
    (fs : List (α → Option α)) :
    chronologicalProduct (fs.map partialMapMatrix) =
      partialMapMatrix (partialMapRun fs) := by
  induction fs with
  | nil =>
      ext B A
      simp [partialMapMatrix, partialMapRun, Matrix.one_apply, eq_comm]
  | cons f fs ih =>
      simp only [List.map_cons, chronologicalProduct_cons, ih, partialMapRun]
      rw [partialMapMatrix_bind]

theorem partialMapRun_exteriorSupport {d : ℕ} {q : ExteriorDegree d}
    (w : List ResetWord.Label) :
    partialMapRun (w.map fun ℓ => exteriorSupportStep (q := q) ℓ) =
      exteriorSupportRun w := by
  funext A
  induction w generalizing A with
  | nil => rfl
  | cons ℓ w ih =>
      simp only [List.map_cons, partialMapRun, exteriorSupportRun]
      cases exteriorSupportStep ℓ A <;> simp [ih]

end PartialMapMatrix

/-- Convert the manuscript label type (`none = star`) to the Boolean model. -/
def supportLabel {d : ℕ} : ResetLabel d → ResetWord.Label
  | none => .star
  | some j => .reset j.val

/-- Concrete Boolean-support matrices on every exterior degree. -/
def booleanSupportK {d : ℕ} (q : ExteriorDegree d) (ℓ : ResetLabel d) :
    Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ :=
  partialMapMatrix (exteriorSupportStep (supportLabel ℓ))

/-- The diagonal word reads the occupation bit at time `t`; an occupied bit
uses reset label `0`, and an empty bit uses `star`. -/
def diagonalSupportWord {d : ℕ} {r : ExteriorDegree d}
    (J : ExteriorIndex d r) (t : Fin d) : ResetLabel d :=
  if t ∈ (J : Finset (Fin d)) then
    some ⟨0, Nat.zero_lt_of_lt t.isLt⟩
  else none

theorem supportLabel_diagonalSupportWord_list {d : ℕ}
    {r : ExteriorDegree d} (J : ExteriorIndex d r) :
    List.ofFn (fun t => supportLabel (diagonalSupportWord J t)) =
      ResetWord.singletonWord (exteriorState J) := by
  rw [ResetWord.singletonWord, exteriorState, List.map_ofFn]
  rw [List.ofFn_inj]
  funext t
  simp only [Function.comp_apply]
  by_cases ht : t ∈ (J : Finset (Fin d)) <;>
    simp [diagonalSupportWord, supportLabel, ResetWord.readLabel, ht]

theorem wordOperator_booleanSupportK {d : ℕ} {q : ExteriorDegree d}
    (ω : Fin d → ResetLabel d) :
    wordOperator (booleanSupportK q) ω =
      partialMapMatrix
        (exteriorSupportRun (List.ofFn fun t => supportLabel (ω t))) := by
  unfold wordOperator booleanSupportK
  let labels := List.ofFn fun t => supportLabel (ω t)
  let fs := labels.map fun ℓ => exteriorSupportStep (q := q) ℓ
  have hrun : partialMapRun fs = exteriorSupportRun labels := by
    simpa only [fs] using
      (partialMapRun_exteriorSupport (q := q) labels)
  calc
    chronologicalProduct
        (List.ofFn fun t => partialMapMatrix
          (exteriorSupportStep (q := q) (supportLabel (ω t)))) =
        chronologicalProduct (fs.map partialMapMatrix) := by
      congr 1
      simp [fs, labels, List.map_ofFn, Function.comp_def]
    _ = partialMapMatrix (partialMapRun fs) :=
      chronological_partialMapMatrix fs
    _ = partialMapMatrix (exteriorSupportRun labels) :=
      congrArg partialMapMatrix hrun
    _ = partialMapMatrix
        (exteriorSupportRun (List.ofFn fun t => supportLabel (ω t))) := rfl

theorem partialMapMatrix_singleton (α : Type*) [Fintype α] [DecidableEq α]
    (J : α) :
    partialMapMatrix (fun A => if A = J then some J else none) =
      Matrix.single J J (1 : ℂ) := by
  classical
  ext B A
  simp [partialMapMatrix, Matrix.single_apply, eq_comm, and_comm]

theorem partialMapMatrix_none (α : Type*) [Fintype α] [DecidableEq α] :
    partialMapMatrix (fun _ : α => none) = (0 : Matrix α α ℂ) := by
  ext B A
  simp [partialMapMatrix]

/-- The Boolean reset theorem now produces a concrete matrix-level singleton
certificate on `Set.powersetCard` coordinates (diagonal `I = J`). -/
def booleanSupport_singletonCertificate {d : ℕ}
    (r : ExteriorDegree d) (J : ExteriorIndex d r) :
    SingletonWordCertificate booleanSupportK (diagonalSupportWord J) r J J := by
  refine
    { phase := 1
      phase_norm := by simp
      selected_degree := ?_
      other_degrees := ?_ }
  · rw [wordOperator_booleanSupportK]
    rw [supportLabel_diagonalSupportWord_list]
    have hfun :
        exteriorSupportRun (ResetWord.singletonWord (exteriorState J)) =
          fun A => if A = J then some J else none := by
      funext A
      exact exteriorSupportRun_singleton J A
    rw [hfun, partialMapMatrix_singleton]
    simp
  · intro q hqr
    rw [wordOperator_booleanSupportK]
    rw [supportLabel_diagonalSupportWord_list]
    have hfun :
        exteriorSupportRun (q := q)
            (ResetWord.singletonWord (exteriorState J)) =
          fun _ => none := by
      funext A
      exact exteriorSupportRun_singleton_other_degree hqr J A
    rw [hfun, partialMapMatrix_none]

/-- Certificate-free diagonal trace extraction in the concrete Boolean
support matrix model. -/
theorem fullMonomialCoefficient_booleanSupport_eq {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (r : ExteriorDegree d) (J : ExteriorIndex d r) :
    fullMonomialCoefficient B booleanSupportK (diagonalSupportWord J) =
      (-1 : ℂ) ^ r.val * B r J J := by
  simpa [booleanSupport_singletonCertificate] using
    fullMonomialCoefficient_eq_of_singleton B booleanSupportK
    (diagonalSupportWord J) r J J (booleanSupport_singletonCertificate r J)

/-- Exact modulus of the extracted diagonal entry, now with no singleton
operator certificate among the assumptions. -/
theorem norm_fullMonomialCoefficient_booleanSupport_eq {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (r : ExteriorDegree d) (J : ExteriorIndex d r) :
    ‖fullMonomialCoefficient B booleanSupportK (diagonalSupportWord J)‖ =
      ‖B r J J‖ := by
  simpa using norm_fullMonomialCoefficient_eq_of_singleton B booleanSupportK
    (diagonalSupportWord J) r J J (booleanSupport_singletonCertificate r J)

/-- Quantitative diagonal lower bound in the concrete Boolean support model. -/
theorem isolated_booleanSupport_diagonal_lower_bound {d : ℕ}
    (weight : ResetLabel d → ℂ)
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (r : ExteriorDegree d) (J : ExteriorIndex d r)
    (bmin entryLower : ℝ) (hbmin : 0 ≤ bmin)
    (hweight : ∀ t : Fin d, bmin ≤ ‖weight (diagonalSupportWord J t)‖)
    (hentry : entryLower ≤ ‖B r J J‖) (hentry_nonneg : 0 ≤ entryLower) :
    bmin ^ d * entryLower ≤
      ‖weightedFullMonomialCoefficient weight B booleanSupportK
        (diagonalSupportWord J)‖ := by
  exact isolated_full_monomial_lower_bound weight B booleanSupportK
    (diagonalSupportWord J) r J J (booleanSupport_singletonCertificate r J)
    bmin entryLower hbmin hweight hentry hentry_nonneg

end CircularLawSection4
