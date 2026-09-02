import CircularLawSection4.ResetMatrixBridge

/-!
# Prefix/suffix reset words with arbitrary input and output supports

The central list theorem in this file implements the suffix in the
manuscript's singleton-word construction.  A suffix schedule consumes one
distinct canonical right-block particle whenever the requested output bit is
occupied.  It maps the empty left block to the prescribed output and kills a
state with any extra particle in that block.
-/

open scoped BigOperators Matrix

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

namespace ResetWord

/-! ## Elementary list dynamics -/

theorem contractAt_append_right (A B : State) (j : ℕ) :
    contractAt (A.length + j) (A ++ B) =
      (contractAt j B).map (fun B' => A ++ B') := by
  induction A with
  | nil => simp
  | cons b A ih =>
      simp only [List.cons_append]
      rw [show (b :: A).length + j = Nat.succ (A.length + j) by
        simp only [List.length_cons]
        omega]
      rw [contractAt.eq_4 (A.length + j) b (A ++ B)]
      rw [ih]
      cases contractAt j B <;> rfl

theorem contractAt_append_index {M : State} (O : State) {k : ℕ}
    (hk : k < M.length) (hbit : M[k] = true) :
    contractAt k (M ++ O) = some (M.set k false ++ O) := by
  induction k generalizing M with
  | zero =>
      cases M with
      | nil => simp at hk
      | cons b M =>
          simp only [List.getElem_cons_zero] at hbit
          subst b
          rfl
  | succ k ih =>
      cases M with
      | nil => simp at hk
      | cons b M =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
          simp only [List.getElem_cons_succ] at hbit
          simp only [List.cons_append, contractAt, List.set]
          rw [ih hk hbit]
          rfl

/-- Reset a selected middle particle.  The first list `E` is the unprocessed
left block, `M` is the canonical particle block, and `O` consists of output
bits already emitted. -/
theorem step_reset_middle_false (E M O : State) (k : ℕ)
    (hk : k < M.length) (hbit : M[k] = true) :
    step (.reset ((false :: E).length + k))
        ((false :: E) ++ M ++ O) =
      some (E ++ M.set k false ++ O ++ [true]) := by
  simp only [step]
  rw [List.append_assoc]
  rw [contractAt_append_right (false :: E) (M ++ O) k]
  rw [contractAt_append_index O hk hbit]
  simp [shiftInsert, List.append_assoc]

theorem step_reset_middle_true (E M O : State) (k : ℕ)
    (hk : k < M.length) (hbit : M[k] = true) :
    step (.reset ((true :: E).length + k))
        ((true :: E) ++ M ++ O) = none := by
  simp only [step]
  rw [List.append_assoc]
  rw [contractAt_append_right (true :: E) (M ++ O) k]
  rw [contractAt_append_index O hk hbit]
  rfl

@[simp] theorem step_star_blocks_false (E M O : State) :
    step .star ((false :: E) ++ M ++ O) =
      some (E ++ M ++ O ++ [false]) := by
  simp [step, shiftInsert, List.append_assoc]

@[simp] theorem step_star_blocks_true (E M O : State) :
    step .star ((true :: E) ++ M ++ O) = none := by
  rfl

/-! ## A no-hole suffix scheduler -/

/-- Clear the listed locations, in chronological order. -/
def clearMany : State → List ℕ → State
  | M, [] => M
  | M, k :: ks => clearMany (M.set k false) ks

@[simp] theorem clearMany_nil (M : State) : clearMany M [] = M := rfl

@[simp] theorem clearMany_cons (M : State) (k : ℕ) (ks : List ℕ) :
    clearMany M (k :: ks) = clearMany (M.set k false) ks := rfl

/-- The suffix word.  A `false` output bit uses `star`; a `true` output bit
consumes the next scheduled middle particle.  The reset index is
`high.length + k`, i.e. `L - u + k` at suffix time `u`. -/
def suffixLabels : State → List ℕ → List Label
  | [], _ => []
  | false :: high, ks => .star :: suffixLabels high ks
  | true :: _high, [] => []
  | true :: high, k :: ks =>
      .reset ((true :: high).length + k) :: suffixLabels high ks

@[simp] theorem suffixLabels_nil (ks : List ℕ) :
    suffixLabels [] ks = [] := rfl

@[simp] theorem suffixLabels_false (high : State) (ks : List ℕ) :
    suffixLabels (false :: high) ks = .star :: suffixLabels high ks := rfl

@[simp] theorem suffixLabels_true_cons (high : State) (k : ℕ)
    (ks : List ℕ) :
    suffixLabels (true :: high) (k :: ks) =
      .reset ((true :: high).length + k) :: suffixLabels high ks := rfl

theorem particleCount_eq_zero_iff (A : State) :
    particleCount A = 0 ↔ A = List.replicate A.length false := by
  induction A with
  | nil => simp [particleCount]
  | cons b A ih =>
      cases b
      · rw [particleCount, ih, List.length_cons, List.replicate_succ]
        simp
      · rw [particleCount, List.length_cons, List.replicate_succ]
        simp

theorem set_getElem_of_ne {M : State} {i j : ℕ}
    (hij : i ≠ j) (hj : j < M.length) :
    (M.set i false)[j]'(by simpa using hj) = M[j] := by
  rw [List.getElem_set]
  simp [hij]

/-- Every still-scheduled location remains occupied after clearing a distinct
earlier location. -/
theorem scheduled_true_after_clear {M : State} {k : ℕ} {ks : List ℕ}
    (hnodup : (k :: ks).Nodup)
    (htrue : ∀ j, j ∈ k :: ks → ∀ hj : j < M.length, M[j] = true) :
    ∀ j, j ∈ ks → ∀ hj : j < (M.set k false).length,
      (M.set k false)[j] = true := by
  intro j hj hlen
  have hjM : j < M.length := by simpa using hlen
  have hkj : k ≠ j := by
    intro h
    subst j
    exact hnodup.notMem hj
  rw [set_getElem_of_ne hkj hjM]
  exact htrue j (by simp [hj]) hjM

@[simp] theorem cons_false_eq_replicate_false (E : State) :
    false :: E = List.replicate (false :: E).length false ↔
      E = List.replicate E.length false := by
  rw [List.length_cons, List.replicate_succ]
  simp

@[simp] theorem cons_true_ne_replicate_false (E : State) :
    true :: E ≠ List.replicate (true :: E).length false := by
  rw [List.length_cons, List.replicate_succ]
  simp

/-- Exact suffix theorem.  It has no hidden hole condition: among states of
the form `E ++ M ++ O`, the word survives precisely when the whole unprocessed
left block `E` is empty. -/
theorem run_suffixLabels (high E M O : State) (ks : List ℕ)
    (hlen : E.length = high.length)
    (hcount : ks.length = particleCount high)
    (hnodup : ks.Nodup)
    (htrue : ∀ k, k ∈ ks → ∀ hk : k < M.length, M[k] = true)
    (hbound : ∀ k, k ∈ ks → k < M.length) :
    run (suffixLabels high ks) (E ++ M ++ O) =
      if E = List.replicate E.length false then
        some (clearMany M ks ++ O ++ high)
      else none := by
  induction high generalizing E M O ks with
  | nil =>
      have hE : E = [] := List.eq_nil_of_length_eq_zero hlen
      subst E
      have hks : ks = [] := List.eq_nil_of_length_eq_zero
        (by simpa [particleCount] using hcount)
      subst ks
      simp [clearMany]
  | cons b high ih =>
      cases E with
      | nil => simp at hlen
      | cons e E =>
          have hlen' : E.length = high.length := by simpa using hlen
          cases b
          · have hcount' : ks.length = particleCount high := by
              simpa [particleCount] using hcount
            cases e
            · have hstep :
                  step .star (false :: (E ++ M ++ O)) =
                    some (E ++ M ++ O ++ [false]) := by
                  simp [List.append_assoc]
              simp only [suffixLabels_false, run_cons, List.cons_append]
              rw [hstep]
              simp only [Option.bind_some]
              rw [show E ++ M ++ O ++ [false] =
                  E ++ M ++ (O ++ [false]) by simp [List.append_assoc]]
              rw [ih E M (O ++ [false]) ks hlen' hcount' hnodup htrue hbound]
              by_cases hE : E = List.replicate E.length false
              · rw [if_pos hE, if_pos]
                · simp [List.append_assoc]
                · exact (cons_false_eq_replicate_false E).2 hE
              · rw [if_neg hE, if_neg]
                exact fun h => hE ((cons_false_eq_replicate_false E).1 h)
            · simp [suffixLabels]
              exact cons_true_ne_replicate_false E
          ·
            cases ks with
            | nil => simp [particleCount] at hcount
            | cons k ks =>
                have hkscount : ks.length = particleCount high := by
                  simpa [particleCount] using hcount
                have hkbound : k < M.length := hbound k (by simp)
                have hktrue : M[k] = true := htrue k (by simp) hkbound
                have hnodup' : ks.Nodup := hnodup.tail
                have htrue' := scheduled_true_after_clear hnodup htrue
                have hbound' : ∀ j, j ∈ ks → j < (M.set k false).length := by
                  intro j hj
                  simpa using hbound j (by simp [hj])
                cases e
                · have hstep :
                      step (.reset ((true :: high).length + k))
                          (false :: (E ++ M ++ O)) =
                        some (E ++ M.set k false ++ O ++ [true]) := by
                      simpa [List.append_assoc, hlen'] using
                        step_reset_middle_false E M O k hkbound hktrue
                  simp only [suffixLabels_true_cons, run_cons, List.cons_append]
                  rw [hstep]
                  simp only [Option.bind_some]
                  rw [show E ++ M.set k false ++ O ++ [true] =
                      E ++ M.set k false ++ (O ++ [true]) by
                    simp [List.append_assoc]]
                  rw [ih E (M.set k false) (O ++ [true]) ks hlen'
                    hkscount hnodup' htrue' hbound']
                  by_cases hE : E = List.replicate E.length false
                  · rw [if_pos hE, if_pos]
                    · simp [List.append_assoc, clearMany]
                    · exact (cons_false_eq_replicate_false E).2 hE
                  · rw [if_neg hE, if_neg]
                    exact fun h => hE ((cons_false_eq_replicate_false E).1 h)
                · have hstep :
                      step (.reset ((true :: high).length + k))
                          (true :: (E ++ M ++ O)) = none := by
                      simpa [List.append_assoc, hlen'] using
                        step_reset_middle_true E M O k hkbound hktrue
                  simp only [suffixLabels_true_cons, run_cons, List.cons_append]
                  rw [hstep]
                  simp
                  exact cons_true_ne_replicate_false E

/-! ## Canonical right block to an arbitrary target -/

/-- Positions of the holes in a Boolean block, in increasing order. -/
def falsePositions : State → List ℕ
  | [] => []
  | false :: A => 0 :: (falsePositions A).map Nat.succ
  | true :: A => (falsePositions A).map Nat.succ

@[simp] theorem falsePositions_nil : falsePositions [] = [] := rfl

@[simp] theorem falsePositions_false (A : State) :
    falsePositions (false :: A) = 0 :: (falsePositions A).map Nat.succ := rfl

@[simp] theorem falsePositions_true (A : State) :
    falsePositions (true :: A) = (falsePositions A).map Nat.succ := rfl

theorem particleCount_le_length (A : State) : particleCount A ≤ A.length := by
  induction A with
  | nil => simp [particleCount]
  | cons b A ih =>
      cases b
      · simpa [particleCount] using Nat.le.step ih
      · simpa [particleCount] using Nat.add_le_add_right ih 1

@[simp] theorem falsePositions_length (A : State) :
    (falsePositions A).length = A.length - particleCount A := by
  induction A with
  | nil => simp [falsePositions, particleCount]
  | cons b A ih =>
      cases b
      · simp [falsePositions, particleCount, ih]
        have := particleCount_le_length A
        omega
      · simp [falsePositions, particleCount, ih]

theorem falsePositions_nodup (A : State) : (falsePositions A).Nodup := by
  induction A with
  | nil => simp
  | cons b A ih =>
      cases b
      · simp only [falsePositions_false, List.nodup_cons, List.mem_map]
        constructor
        · rintro ⟨k, _, hk⟩
          omega
        · exact ih.map Nat.succ_injective
      · simpa using ih.map Nat.succ_injective

theorem mem_falsePositions_lt {A : State} {k : ℕ}
    (hk : k ∈ falsePositions A) : k < A.length := by
  induction A generalizing k with
  | nil => simp at hk
  | cons b A ih =>
      cases b <;> simp only [falsePositions_false, falsePositions_true,
        List.mem_cons, List.mem_map] at hk
      · rcases hk with rfl | ⟨j, hj, rfl⟩
        · simp
        · simpa using Nat.succ_lt_succ (ih hj)
      · rcases hk with ⟨j, hj, rfl⟩
        simpa using Nat.succ_lt_succ (ih hj)

theorem clearMany_map_succ (b : Bool) (M : State) (ks : List ℕ) :
    clearMany (b :: M) (ks.map Nat.succ) = b :: clearMany M ks := by
  induction ks generalizing M with
  | nil => rfl
  | cons k ks ih =>
      simp only [List.map_cons, clearMany_cons, List.set]
      exact ih (M.set k false)

/-- Clearing precisely the holes of an all-occupied block produces the
prescribed Boolean block. -/
theorem clearMany_falsePositions (A : State) :
    clearMany (List.replicate A.length true) (falsePositions A) = A := by
  induction A with
  | nil => rfl
  | cons b A ih =>
      cases b
      · simp only [List.length_cons, List.replicate_succ,
          falsePositions_false, clearMany_cons, List.set]
        rw [clearMany_map_succ, ih]
      · simp only [List.length_cons, List.replicate_succ,
          falsePositions_true]
        rw [clearMany_map_succ, ih]

/-- The number of high occupied target positions equals the number of holes
in the low block. -/
theorem falsePositions_take_length_eq_particleCount_drop
    (I : State) (r : ℕ) (hcount : particleCount I = r) :
    (falsePositions (I.take r)).length = particleCount (I.drop r) := by
  have hr : r ≤ I.length := by
    rw [← hcount]
    exact particleCount_le_length I
  have htake : (I.take r).length = r := by simp [hr]
  have hsplit :
      particleCount I = particleCount (I.take r) + particleCount (I.drop r) := by
    rw [← particleCount_append, List.take_append_drop]
  rw [falsePositions_length, htake]
  omega

theorem suffixLabels_length (high : State) (ks : List ℕ)
    (hcount : ks.length = particleCount high) :
    (suffixLabels high ks).length = high.length := by
  induction high generalizing ks with
  | nil => simp [suffixLabels]
  | cons b high ih =>
      cases b
      · simp only [particleCount] at hcount
        simp [suffixLabels, ih ks hcount]
      · cases ks with
        | nil => simp [particleCount] at hcount
        | cons k ks =>
            have htail : ks.length = particleCount high := by
              simpa [particleCount] using hcount
            simp [suffixLabels, ih ks htail]

/-- Instantiation of the suffix theorem for an arbitrary target `I`.  It
kills every nonempty extra left block and otherwise maps the canonical right
block to `I`. -/
theorem run_targetSuffix (I E : State) (r : ℕ)
    (hcount : particleCount I = r)
    (hlen : E.length = (I.drop r).length) :
    run (suffixLabels (I.drop r) (falsePositions (I.take r)))
        (E ++ List.replicate (I.take r).length true) =
      if E = List.replicate E.length false then some I else none := by
  let low := I.take r
  let high := I.drop r
  let ks := falsePositions low
  have hkscount : ks.length = particleCount high := by
    simpa [low, high, ks] using
      falsePositions_take_length_eq_particleCount_drop I r hcount
  have hnodup : ks.Nodup := by
    exact falsePositions_nodup low
  have hbound : ∀ k, k ∈ ks → k < (List.replicate low.length true).length := by
    intro k hk
    simpa using mem_falsePositions_lt hk
  have htrue : ∀ k, k ∈ ks →
      ∀ hk : k < (List.replicate low.length true).length,
        (List.replicate low.length true)[k] = true := by
    intro k hk hkl
    simp
  have hrun := run_suffixLabels high E
    (List.replicate low.length true) [] ks (by simpa [high] using hlen)
    hkscount hnodup htrue hbound
  rw [clearMany_falsePositions low] at hrun
  simpa [low, high, ks, List.take_append_drop, List.append_assoc] using hrun

/-- In particular, the canonical right block reaches every target of the
same particle number. -/
theorem run_targetSuffix_rightBlock (I : State) (r : ℕ)
    (hcount : particleCount I = r) :
    run (suffixLabels (I.drop r) (falsePositions (I.take r)))
        (List.replicate (I.drop r).length false ++
          List.replicate (I.take r).length true) = some I := by
  simpa using run_targetSuffix I (List.replicate (I.drop r).length false)
    r hcount (by simp)

/-! ## Arbitrary source to the canonical right block -/

/-- Reset indices for the manuscript prefix.  At the `t`-th occupied source
site this is `j_t - t`, equivalently the number of holes preceding that
particle. -/
def prefixIndices : State → List ℕ
  | [] => []
  | false :: A => (prefixIndices A).map Nat.succ
  | true :: A => 0 :: prefixIndices A

def prefixLabels (A : State) : List Label :=
  (prefixIndices A).map Label.reset

@[simp] theorem prefixIndices_nil : prefixIndices [] = [] := rfl

@[simp] theorem prefixIndices_false (A : State) :
    prefixIndices (false :: A) = (prefixIndices A).map Nat.succ := rfl

@[simp] theorem prefixIndices_true (A : State) :
    prefixIndices (true :: A) = 0 :: prefixIndices A := rfl

@[simp] theorem prefixLabels_nil : prefixLabels [] = [] := rfl

@[simp] theorem prefixLabels_false (A : State) :
    prefixLabels (false :: A) =
      (prefixLabels A).map (fun ℓ => match ℓ with
        | .star => .star
        | .reset j => .reset j.succ) := by
  simp [prefixLabels, List.map_map, Function.comp_def]

@[simp] theorem prefixLabels_true (A : State) :
    prefixLabels (true :: A) = .reset 0 :: prefixLabels A := by
  simp [prefixLabels]

@[simp] theorem prefixIndices_length (A : State) :
    (prefixIndices A).length = particleCount A := by
  induction A with
  | nil => rfl
  | cons b A ih => cases b <;> simp [prefixIndices, particleCount, ih]

@[simp] theorem prefixLabels_length (A : State) :
    (prefixLabels A).length = particleCount A := by
  simp [prefixLabels]

/-- Adding one protected empty site on the left increments a successful reset
index and preserves the successful transition. -/
theorem step_reset_succ_of_step_reset {A B : State} {j : ℕ}
    (h : step (.reset j) A = some B) :
    step (.reset j.succ) (false :: A) = some (false :: B) := by
  simp only [step] at h ⊢
  cases hc : contractAt j A with
  | none => simp [hc] at h
  | some C =>
      simp only [hc, Option.bind_some] at h
      cases C with
      | nil => simp [shiftInsert] at h
      | cons b C =>
          cases b
          · simp only [shiftInsert] at h
            injection h with hB
            subst B
            rw [contractAt.eq_4, hc]
            simp [shiftInsert]
          · simp [shiftInsert] at h

/-- Shift every reset index through a protected all-zero prefix. -/
theorem step_reset_add_of_step_reset (z : ℕ) {A B : State} {j : ℕ}
    (h : step (.reset j) A = some B) :
    step (.reset (z + j)) (List.replicate z false ++ A) =
      some (List.replicate z false ++ B) := by
  induction z with
  | zero => simpa using h
  | succ z ih =>
      rw [List.replicate_succ, List.cons_append]
      rw [show z.succ + j = (z + j).succ by omega]
      exact step_reset_succ_of_step_reset ih

/-- Lift an entire successful all-reset run through an all-zero prefix. -/
theorem run_reset_add_of_run (z : ℕ) (js : List ℕ) {A B : State}
    (h : run (js.map Label.reset) A = some B) :
    run (js.map (fun j => Label.reset (z + j)))
        (List.replicate z false ++ A) =
      some (List.replicate z false ++ B) := by
  induction js generalizing A B with
  | nil => simpa using h
  | cons j js ih =>
      simp only [List.map_cons, run_cons] at h ⊢
      cases hs : step (.reset j) A with
      | none => simp [hs] at h
      | some A' =>
          simp only [hs, Option.bind_some] at h
          rw [step_reset_add_of_step_reset z hs]
          simp only [Option.bind_some]
          exact ih h

/-- Exact prefix trajectory, including an arbitrary untouched suffix `R`.
Every selected source particle is moved to the right boundary. -/
theorem run_prefixLabels_append (J R : State) :
    run (prefixLabels J) (J ++ R) =
      some (List.replicate (J.length - particleCount J) false ++ R ++
        List.replicate (particleCount J) true) := by
  induction J generalizing R with
  | nil => simp [prefixLabels, particleCount]
  | cons b J ih =>
      cases b
      · have hrun := run_reset_add_of_run 1 (prefixIndices J)
            (ih R)
        have hlabels :
            (prefixIndices J).map (fun j => Label.reset (1 + j)) =
              (prefixIndices J).map (fun j => Label.reset j.succ) := by
          apply List.map_congr_left
          intro j hj
          congr 1
          omega
        rw [hlabels] at hrun
        have hholes : J.length + 1 - particleCount J =
            (J.length - particleCount J) + 1 := by
          have := particleCount_le_length J
          omega
        simpa [prefixLabels, prefixIndices, List.map_map, Function.comp_def,
          particleCount, List.replicate_succ,
          List.append_assoc, hholes] using hrun
      · simp only [prefixLabels_true, run_cons, List.cons_append,
          step_reset_zero, Option.bind_some]
        rw [List.append_assoc]
        rw [ih (R ++ [true])]
        have hle := particleCount_le_length J
        simp [particleCount, List.append_assoc, List.replicate_succ]

/-- Prefix specialization `J → 0^(d-r)1^r`. -/
theorem run_prefixLabels (J : State) :
    run (prefixLabels J) J =
      some (List.replicate (J.length - particleCount J) false ++
        List.replicate (particleCount J) true) := by
  simpa using run_prefixLabels_append J []

/-! ## Singleton domain of the concatenated word -/

theorem shiftInsert_some_injective {new : Bool} {A B C : State}
    (hA : shiftInsert new A = some C) (hB : shiftInsert new B = some C) :
    A = B := by
  cases A with
  | nil => simp [shiftInsert] at hA
  | cons a A =>
      cases B with
      | nil => simp [shiftInsert] at hB
      | cons b B =>
          cases a <;> cases b <;> simp [shiftInsert] at hA hB
          exact congrArg (fun T => false :: T)
            ((List.append_left_injective [new]) (hA.trans hB.symm))

theorem contractAt_some_injective {j : ℕ} {A B C : State}
    (hA : contractAt j A = some C) (hB : contractAt j B = some C) :
    A = B := by
  induction j generalizing A B C with
  | zero =>
      cases A with
      | nil => simp [contractAt] at hA
      | cons a A =>
          cases B with
          | nil => simp [contractAt] at hB
          | cons b B =>
              cases a
              · simp [contractAt] at hA
              · cases b
                · simp [contractAt] at hB
                · simp only [contractAt, Option.some.injEq] at hA hB
                  have htails : A = B := by
                    simpa using hA.trans hB.symm
                  subst B
                  rfl
  | succ j ih =>
      cases A with
      | nil => simp [contractAt] at hA
      | cons a A =>
          cases B with
          | nil => simp [contractAt] at hB
          | cons b B =>
              rw [contractAt.eq_4] at hA hB
              cases hAc : contractAt j A with
              | none => simp [hAc] at hA
              | some AC =>
                  cases hBc : contractAt j B with
                  | none => simp [hBc] at hB
                  | some BC =>
                      simp only [hAc, hBc, Option.map_some,
                        Option.some.injEq] at hA hB
                      have habc : a :: AC = b :: BC := hA.trans hB.symm
                      injection habc with hab hACBC
                      subst b
                      subst BC
                      exact congrArg (fun T => a :: T) (ih hAc hBc)

theorem step_some_injective {ℓ : Label} {A B C : State}
    (hA : step ℓ A = some C) (hB : step ℓ B = some C) : A = B := by
  cases ℓ with
  | star => exact shiftInsert_some_injective hA hB
  | reset j =>
      simp only [step] at hA hB
      cases hAc : contractAt j A with
      | none => simp [hAc] at hA
      | some AC =>
          cases hBc : contractAt j B with
          | none => simp [hBc] at hB
          | some BC =>
              simp only [hAc, hBc, Option.bind_some] at hA hB
              have hACBC := shiftInsert_some_injective hA hB
              subst BC
              exact contractAt_some_injective hAc hBc

/-- A reset word is a partial injection. -/
theorem run_some_injective {w : List Label} {A B C : State}
    (hA : run w A = some C) (hB : run w B = some C) : A = B := by
  induction w generalizing A B with
  | nil => simpa using hA.trans hB.symm
  | cons ℓ w ih =>
      simp only [run_cons] at hA hB
      cases hAs : step ℓ A with
      | none => simp [hAs] at hA
      | some A' =>
          cases hBs : step ℓ B with
          | none => simp [hBs] at hB
          | some B' =>
              simp only [hAs, hBs, Option.bind_some] at hA hB
              have hAB' : A' = B' := ih hA hB
              subst B'
              exact step_some_injective hAs hBs

theorem run_preserves_length {w : List Label} {A B : State}
    (h : run w A = some B) : B.length = A.length := by
  induction w generalizing A with
  | nil =>
      have hAB : A = B := Option.some.inj h
      subst B
      rfl
  | cons ℓ w ih =>
      simp only [run_cons] at h
      cases hs : step ℓ A with
      | none => simp [hs] at h
      | some A' =>
          simp only [hs, Option.bind_some] at h
          exact (ih h).trans (step_preserves_length hs)

/-- At active length `d`, every reset index stays strictly before the suffix
of particles already moved to the right. -/
inductive ValidResetSchedule : ℕ → List ℕ → Prop
  | nil (d : ℕ) : ValidResetSchedule d []
  | cons {d j : ℕ} {js : List ℕ} (hj : j < d + 1)
      (tail : ValidResetSchedule d js) :
      ValidResetSchedule (d + 1) (j :: js)

theorem ValidResetSchedule.succMap {d : ℕ} {js : List ℕ}
    (h : ValidResetSchedule d js) :
    ValidResetSchedule (d + 1) (js.map Nat.succ) := by
  induction h with
  | nil d => exact .nil _
  | @cons d j js hj htail ih =>
      exact .cons (by omega) ih

theorem prefixIndices_valid (J : State) :
    ValidResetSchedule J.length (prefixIndices J) := by
  induction J with
  | nil => exact .nil 0
  | cons b J ih =>
      cases b
      · exact ih.succMap
      · exact .cons (by simp) ih

theorem contractAt_append_left {A R : State} {j : ℕ}
    (hj : j < A.length) :
    contractAt j (A ++ R) =
      (contractAt j A).map (fun A' => A' ++ R) := by
  induction j generalizing A with
  | zero =>
      cases A with
      | nil => simp at hj
      | cons b A => cases b <;> rfl
  | succ j ih =>
      cases A with
      | nil => simp at hj
      | cons b A =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hj
          simp only [List.cons_append]
          rw [show j + 1 = j.succ by omega, contractAt.eq_4,
            contractAt.eq_4, ih hj]
          cases contractAt j A <;> rfl

/-- One successful reset inside `A` leaves an arbitrary suffix `R` untouched
and appends the newly moved particle after it. -/
theorem step_reset_prefix_decompose {A R B : State} {j : ℕ}
    (hj : j < A.length) (h : step (.reset j) (A ++ R) = some B) :
    ∃ A' : State, A'.length + 1 = A.length ∧
      B = A' ++ R ++ [true] := by
  simp only [step] at h
  rw [contractAt_append_left hj] at h
  cases hc : contractAt j A with
  | none => simp [hc] at h
  | some C =>
      simp only [hc, Option.map_some, Option.bind_some] at h
      cases C with
      | nil =>
          exfalso
          have hlen := contractAt_preserves_length hc
          simp at hlen
          omega
      | cons b C =>
          cases b
          · simp only [shiftInsert] at h
            injection h with hB
            subst B
            refine ⟨C, ?_, by simp [List.append_assoc]⟩
            have hlen := contractAt_preserves_length hc
            simp at hlen
            omega
          · simp [shiftInsert] at h

/-- A successful valid schedule ends in one new occupied suffix bit per reset. -/
theorem run_validResetSchedule_suffix {d : ℕ} {js : List ℕ}
    (hv : ValidResetSchedule d js) {A R B : State}
    (hlen : A.length = d)
    (h : run (js.map Label.reset) (A ++ R) = some B) :
    ∃ E : State, B = E ++ R ++ List.replicate js.length true := by
  induction hv generalizing A R B with
  | nil d =>
      simp only [List.map_nil, run_nil, Option.some.injEq] at h
      subst B
      exact ⟨A, by simp⟩
  | @cons d j js hj hv ih =>
      simp only [List.map_cons, run_cons] at h
      cases hs : step (.reset j) (A ++ R) with
      | none => simp [hs] at h
      | some Aone =>
          simp only [hs, Option.bind_some] at h
          have hjA : j < A.length := by omega
          obtain ⟨A', hA'len, hAone⟩ :=
            step_reset_prefix_decompose hjA hs
          subst Aone
          obtain ⟨E, hE⟩ := ih (A := A') (R := R ++ [true])
            (B := B) (by omega) (by simpa [List.append_assoc] using h)
          refine ⟨E, ?_⟩
          rw [hE]
          simp [List.replicate_succ, List.append_assoc]

/-- Every surviving prefix output has the canonical occupied suffix. -/
theorem run_prefixLabels_has_rightBlock {J A B : State}
    (hlen : A.length = J.length)
    (h : run (prefixLabels J) A = some B) :
    ∃ E : State,
      B = E ++ List.replicate (particleCount J) true := by
  have hv := prefixIndices_valid J
  have hrun : run ((prefixIndices J).map Label.reset) (A ++ []) = some B := by
    simpa [prefixLabels] using h
  obtain ⟨E, hE⟩ := run_validResetSchedule_suffix hv hlen hrun
  exact ⟨E, by simpa using hE⟩

/-- The manuscript's full prefix/suffix label list. -/
def arbitrarySingletonLabels (I J : State) : List Label :=
  prefixLabels J ++
    suffixLabels (I.drop (particleCount J))
      (falsePositions (I.take (particleCount J)))

theorem arbitrarySingletonLabels_length (I J : State)
    (hlen : I.length = J.length)
    (hcount : particleCount I = particleCount J) :
    (arbitrarySingletonLabels I J).length = J.length := by
  unfold arbitrarySingletonLabels
  rw [List.length_append, prefixLabels_length]
  rw [suffixLabels_length _ _
    (falsePositions_take_length_eq_particleCount_drop I
      (particleCount J) hcount)]
  have hr : particleCount J ≤ I.length := by
    rw [← hcount]
    exact particleCount_le_length I
  have hrJ : particleCount J ≤ J.length := by simpa [← hlen] using hr
  simp only [List.length_drop]
  omega

/-- Full arbitrary-source/arbitrary-target singleton-domain theorem in the
Boolean dynamics.  It simultaneously kills every other particle degree. -/
theorem arbitrary_singleton_domain_word (I J A : State)
    (hIJlen : I.length = J.length)
    (hIAlen : I.length = A.length)
    (hcount : particleCount I = particleCount J) :
    run (arbitrarySingletonLabels I J) A =
      if A = J then some I else none := by
  by_cases hAJ : A = J
  · subst A
    rw [if_pos rfl]
    rw [arbitrarySingletonLabels, run_append, run_prefixLabels]
    simp only [Option.bind_some]
    have hholes : J.length - particleCount J =
        (I.drop (particleCount J)).length := by
      have hr : particleCount J ≤ I.length := by
        rw [← hcount]
        exact particleCount_le_length I
      simp [List.length_drop, hIJlen]
    have htakes : (I.take (particleCount J)).length = particleCount J := by
      have hr : particleCount J ≤ I.length := by
        rw [← hcount]
        exact particleCount_le_length I
      simp [hr]
    simpa [hholes, htakes] using
      run_targetSuffix_rightBlock I (particleCount J) hcount
  · rw [if_neg hAJ]
    rw [arbitrarySingletonLabels, run_append]
    cases hp : run (prefixLabels J) A with
    | none => rfl
    | some P =>
        simp only [Option.bind_some]
        cases hs : run
            (suffixLabels (I.drop (particleCount J))
              (falsePositions (I.take (particleCount J)))) P with
        | none => rfl
        | some Q =>
            exfalso
            obtain ⟨E, hP⟩ := run_prefixLabels_has_rightBlock
              (J := J) (A := A) (B := P) (hIAlen.symm.trans hIJlen) hp
            have hPlen : P.length = A.length := run_preserves_length hp
            have hElen : E.length = (I.drop (particleCount J)).length := by
              have hr : particleCount J ≤ I.length := by
                rw [← hcount]
                exact particleCount_le_length I
              rw [hP, List.length_append, List.length_replicate] at hPlen
              simp only [List.length_drop]
              omega
            have hsuffix := run_targetSuffix I E (particleCount J) hcount hElen
            have htakes : (I.take (particleCount J)).length = particleCount J := by
              have hr : particleCount J ≤ I.length := by
                rw [← hcount]
                exact particleCount_le_length I
              simp [hr]
            rw [htakes] at hsuffix
            rw [← hP] at hsuffix
            rw [hs] at hsuffix
            by_cases hEzero : E = List.replicate E.length false
            · rw [if_pos hEzero] at hsuffix
              have hQ : Q = I := Option.some.inj hsuffix
              subst Q
              have htarget :
                  run (prefixLabels J) J = some P := by
                rw [run_prefixLabels]
                rw [hP, hEzero]
                congr 2
                have hElenJ : E.length = J.length - particleCount J := by
                  have hr : particleCount J ≤ I.length := by
                    rw [← hcount]
                    exact particleCount_le_length I
                  simp [hElen, List.length_drop, hIJlen]
                rw [hElenJ]
              exact hAJ (run_some_injective hp htarget)
            · rw [if_neg hEzero] at hsuffix
              contradiction

/-! ## Bounded labels for the `Fin d` matrix interface -/

def Label.Bounded (d : ℕ) : Label → Prop
  | .star => True
  | .reset j => j < d

theorem Label.Bounded.mono {d e : ℕ} (hde : d ≤ e) {ℓ : Label}
    (h : ℓ.Bounded d) : ℓ.Bounded e := by
  cases ℓ with
  | star => trivial
  | reset j => exact lt_of_lt_of_le h hde

theorem ValidResetSchedule.mem_lt {d : ℕ} {js : List ℕ}
    (h : ValidResetSchedule d js) {j : ℕ} (hj : j ∈ js) : j < d := by
  induction h with
  | nil d => simp at hj
  | @cons d k ks hk htail ih =>
      simp only [List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact hk
      · exact lt_of_lt_of_le (ih hj) (by omega)

theorem prefixLabels_bounded (J : State) :
    ∀ ℓ, ℓ ∈ prefixLabels J → ℓ.Bounded J.length := by
  intro ℓ hℓ
  simp only [prefixLabels, List.mem_map] at hℓ
  obtain ⟨j, hj, rfl⟩ := hℓ
  exact (prefixIndices_valid J).mem_lt hj

theorem suffixLabels_bounded (high : State) (ks : List ℕ) (r : ℕ)
    (hks : ∀ k, k ∈ ks → k < r) :
    ∀ ℓ, ℓ ∈ suffixLabels high ks →
      ℓ.Bounded (high.length + r) := by
  induction high generalizing ks with
  | nil => simp [suffixLabels]
  | cons b high ih =>
      cases b
      · intro ℓ hℓ
        simp only [suffixLabels_false, List.mem_cons] at hℓ
        rcases hℓ with rfl | hℓ
        · trivial
        · exact (ih ks hks ℓ hℓ).mono (by simp)
      · cases ks with
        | nil => simp [suffixLabels]
        | cons k ks =>
            intro ℓ hℓ
            simp only [suffixLabels_true_cons, List.mem_cons] at hℓ
            rcases hℓ with rfl | hℓ
            · simp only [Label.Bounded]
              have hk := hks k (by simp)
              omega
            · have htail : ∀ j, j ∈ ks → j < r := by
                intro j hj
                exact hks j (by simp [hj])
              exact (ih ks htail ℓ hℓ).mono (by simp)

theorem arbitrarySingletonLabels_bounded (I J : State)
    (hlen : I.length = J.length)
    (hcount : particleCount I = particleCount J) :
    ∀ ℓ, ℓ ∈ arbitrarySingletonLabels I J →
      ℓ.Bounded J.length := by
  intro ℓ hℓ
  simp only [arbitrarySingletonLabels, List.mem_append] at hℓ
  rcases hℓ with hp | hs
  · exact prefixLabels_bounded J ℓ hp
  · let low := I.take (particleCount J)
    let high := I.drop (particleCount J)
    let ks := falsePositions low
    have hks : ∀ k, k ∈ ks → k < low.length := by
      intro k hk
      exact mem_falsePositions_lt hk
    have hb := suffixLabels_bounded high ks low.length hks ℓ (by simpa [high, ks] using hs)
    have hsum : high.length + low.length = J.length := by
      have hr : particleCount J ≤ I.length := by
        rw [← hcount]
        exact particleCount_le_length I
      have hrJ : particleCount J ≤ J.length := by
        simpa [← hlen] using hr
      simp [high, low, List.length_drop, hrJ, hlen]
    simpa [hsum] using hb

/-- Convert a proved-bounded Boolean label to the manuscript's `Option (Fin d)`
label type. -/
def toResetLabel {d : ℕ} (ℓ : Label) (h : ℓ.Bounded d) : ResetLabel d :=
  match ℓ with
  | .star => none
  | .reset j => some ⟨j, h⟩

@[simp] theorem supportLabel_toResetLabel {d : ℕ} (ℓ : Label)
    (h : ℓ.Bounded d) : supportLabel (toResetLabel ℓ h) = ℓ := by
  cases ℓ <;> rfl

/-- Pointwise bounded conversion of a label list. -/
def toResetLabelList {d : ℕ} (w : List Label)
    (h : ∀ ℓ, ℓ ∈ w → ℓ.Bounded d) : List (ResetLabel d) :=
  match w with
  | [] => []
  | ℓ :: ws =>
      toResetLabel ℓ (h ℓ (by simp)) ::
        toResetLabelList ws (fun k hk => h k (by simp [hk]))

@[simp] theorem toResetLabelList_length {d : ℕ} (w : List Label)
    (h : ∀ ℓ, ℓ ∈ w → ℓ.Bounded d) :
    (toResetLabelList w h).length = w.length := by
  induction w with
  | nil => rfl
  | cons ℓ w ih =>
      simp only [toResetLabelList, List.length_cons]
      rw [ih]

@[simp] theorem map_supportLabel_toResetLabelList {d : ℕ} (w : List Label)
    (h : ∀ ℓ, ℓ ∈ w → ℓ.Bounded d) :
    (toResetLabelList w h).map supportLabel = w := by
  induction w with
  | nil => rfl
  | cons ℓ w ih =>
      simp only [toResetLabelList, List.map_cons, supportLabel_toResetLabel,
        List.cons.injEq, true_and]
      exact ih _

def listWord {d : ℕ} {α : Type*} (w : List α) (h : w.length = d) :
    Fin d → α := fun t => w.get (Fin.cast h.symm t)

@[simp] theorem ofFn_listWord {d : ℕ} {α : Type*}
    (w : List α) (h : w.length = d) :
    List.ofFn (listWord w h) = w := by
  subst d
  exact List.ofFn_get w

end ResetWord

/-! ## Powerset-card matrices and the certificate constructor -/

/-- Bounded `ResetLabel` list implementing the arbitrary Boolean word. -/
noncomputable def arbitrarySupportLabelList {d : ℕ}
    {r : ExteriorDegree d} (I J : ExteriorIndex d r) :
    List (ResetLabel d) := by
  let SI := exteriorState I
  let SJ := exteriorState J
  let labels := ResetWord.arbitrarySingletonLabels SI SJ
  have hb := ResetWord.arbitrarySingletonLabels_bounded SI SJ
    (by simp [SI, SJ]) (by simp [SI, SJ])
  exact ResetWord.toResetLabelList labels (fun ℓ hℓ => by
    have h := hb ℓ hℓ
    simpa [SJ] using h)

@[simp] theorem arbitrarySupportLabelList_length {d : ℕ}
    {r : ExteriorDegree d} (I J : ExteriorIndex d r) :
    (arbitrarySupportLabelList I J).length = d := by
  simp only [arbitrarySupportLabelList, ResetWord.toResetLabelList_length]
  simpa using ResetWord.arbitrarySingletonLabels_length (exteriorState I)
    (exteriorState J) (by simp) (by simp)

theorem map_supportLabel_arbitrarySupportLabelList {d : ℕ}
    {r : ExteriorDegree d} (I J : ExteriorIndex d r) :
    (arbitrarySupportLabelList I J).map supportLabel =
      ResetWord.arbitrarySingletonLabels (exteriorState I) (exteriorState J) := by
  simp [arbitrarySupportLabelList,
    ResetWord.map_supportLabel_toResetLabelList]

/-- The length-`d` manuscript-label word for arbitrary source `J` and target
`I`. -/
noncomputable def arbitrarySupportWord {d : ℕ}
    {r : ExteriorDegree d} (I J : ExteriorIndex d r) :
    Fin d → ResetLabel d :=
  ResetWord.listWord (arbitrarySupportLabelList I J)
    (arbitrarySupportLabelList_length I J)

theorem supportLabel_arbitrarySupportWord_list {d : ℕ}
    {r : ExteriorDegree d} (I J : ExteriorIndex d r) :
    List.ofFn (fun t => supportLabel (arbitrarySupportWord I J t)) =
      ResetWord.arbitrarySingletonLabels (exteriorState I) (exteriorState J) := by
  change List.ofFn (supportLabel ∘ arbitrarySupportWord I J) = _
  rw [← List.map_ofFn]
  unfold arbitrarySupportWord
  rw [ResetWord.ofFn_listWord]
  exact map_supportLabel_arbitrarySupportLabelList I J

theorem exteriorSupportRun_arbitrary {d : ℕ} {r : ExteriorDegree d}
    (I J A : ExteriorIndex d r) :
    exteriorSupportRun
        (ResetWord.arbitrarySingletonLabels (exteriorState I) (exteriorState J)) A =
      if A = J then some I else none := by
  apply Option.map_injective exteriorState_injective
  rw [exteriorSupportRun_map]
  have h := ResetWord.arbitrary_singleton_domain_word
    (exteriorState I) (exteriorState J) (exteriorState A)
    (by simp) (by simp) (by simp)
  simpa [exteriorState_injective.eq_iff] using h

theorem exteriorSupportRun_arbitrary_other_degree {d : ℕ}
    {r q : ExteriorDegree d} (hqr : q ≠ r)
    (I J : ExteriorIndex d r) (A : ExteriorIndex d q) :
    exteriorSupportRun
        (ResetWord.arbitrarySingletonLabels (exteriorState I) (exteriorState J)) A =
      none := by
  apply Option.map_injective exteriorState_injective
  rw [exteriorSupportRun_map]
  have h := ResetWord.arbitrary_singleton_domain_word
    (exteriorState I) (exteriorState J) (exteriorState A)
    (by simp) (by simp) (by simp)
  have hne : exteriorState A ≠ exteriorState J := by
    intro hstate
    have hpc := congrArg ResetWord.particleCount hstate
    simp only [exteriorState_particleCount] at hpc
    apply hqr
    exact Fin.ext hpc
  simpa [hne] using h

theorem partialMapMatrix_singleton_to
    (α : Type*) [Fintype α] [DecidableEq α] (I J : α) :
    partialMapMatrix (fun A => if A = J then some I else none) =
      Matrix.single I J (1 : ℂ) := by
  classical
  ext B A
  simp [partialMapMatrix, Matrix.single_apply, eq_comm, and_comm]

/-- Fully constructed arbitrary Boolean-support singleton certificate.  No
selected-operator or other-degree equality is accepted as an input field. -/
noncomputable def booleanSupport_arbitrarySingletonCertificate {d : ℕ}
    (r : ExteriorDegree d) (I J : ExteriorIndex d r) :
    SingletonWordCertificate booleanSupportK (arbitrarySupportWord I J)
      r I J := by
  refine
    { phase := 1
      phase_norm := by simp
      selected_degree := ?_
      other_degrees := ?_ }
  · rw [wordOperator_booleanSupportK]
    rw [supportLabel_arbitrarySupportWord_list]
    have hfun :
        exteriorSupportRun
            (ResetWord.arbitrarySingletonLabels
              (exteriorState I) (exteriorState J)) =
      fun A => if A = J then some I else none := by
      funext A
      exact exteriorSupportRun_arbitrary I J A
    rw [hfun, partialMapMatrix_singleton_to]
    simp
  · intro q hqr
    rw [wordOperator_booleanSupportK]
    rw [supportLabel_arbitrarySupportWord_list]
    have hfun :
        exteriorSupportRun (q := q)
            (ResetWord.arbitrarySingletonLabels
              (exteriorState I) (exteriorState J)) =
          fun _ => none := by
      funext A
      exact exteriorSupportRun_arbitrary_other_degree hqr I J A
    rw [hfun, partialMapMatrix_none]

/-- Certificate-free trace extraction for arbitrary source and target in the
concrete Boolean support matrix model. -/
theorem fullMonomialCoefficient_booleanSupport_arbitrary_eq {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (r : ExteriorDegree d) (I J : ExteriorIndex d r) :
    fullMonomialCoefficient B booleanSupportK (arbitrarySupportWord I J) =
      (-1 : ℂ) ^ r.val * B r J I := by
  simpa [booleanSupport_arbitrarySingletonCertificate] using
    fullMonomialCoefficient_eq_of_singleton B booleanSupportK
      (arbitrarySupportWord I J) r I J
      (booleanSupport_arbitrarySingletonCertificate r I J)

/-- Exact modulus of the arbitrary entry isolated by the Boolean word. -/
theorem norm_fullMonomialCoefficient_booleanSupport_arbitrary_eq {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (r : ExteriorDegree d) (I J : ExteriorIndex d r) :
    ‖fullMonomialCoefficient B booleanSupportK (arbitrarySupportWord I J)‖ =
      ‖B r J I‖ := by
  simpa using norm_fullMonomialCoefficient_eq_of_singleton B booleanSupportK
    (arbitrarySupportWord I J) r I J
    (booleanSupport_arbitrarySingletonCertificate r I J)

/-- Quantitative arbitrary-entry lower bound with the singleton certificate
fully discharged by the Boolean prefix/suffix construction. -/
theorem isolated_booleanSupport_arbitrary_lower_bound {d : ℕ}
    (weight : ResetLabel d → ℂ)
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (r : ExteriorDegree d) (I J : ExteriorIndex d r)
    (bmin entryLower : ℝ) (hbmin : 0 ≤ bmin)
    (hweight : ∀ t : Fin d, bmin ≤ ‖weight (arbitrarySupportWord I J t)‖)
    (hentry : entryLower ≤ ‖B r J I‖) (hentry_nonneg : 0 ≤ entryLower) :
    bmin ^ d * entryLower ≤
      ‖weightedFullMonomialCoefficient weight B booleanSupportK
        (arbitrarySupportWord I J)‖ := by
  exact isolated_full_monomial_lower_bound weight B booleanSupportK
    (arbitrarySupportWord I J) r I J
    (booleanSupport_arbitrarySingletonCertificate r I J)
    bmin entryLower hbmin hweight hentry hentry_nonneg

end CircularLawSection4
