import Init.Data.List.Lemmas

/-!
# Bit-vector model of the reset operators

Sites are Boolean-list entries numbered from zero.  `true` means occupied;
`none` means that the corresponding exterior-basis vector was killed.

This file proves a length-`d` singleton-domain word for every `d`-site state.
It is the diagonal (`I = J`) specialization of the manuscript's construction
and already kills wrong inputs in every particle-number sector at once.
-/

namespace CircularLawSection4.ResetWord

abbrev State := List Bool

inductive Label where
  | star
  | reset (j : Nat)
  deriving DecidableEq, Repr

/-- Contract the particle at `j`, leaving an empty bit there. -/
def contractAt : Nat → State → Option State
  | _, [] => none
  | 0, true :: tail => some (false :: tail)
  | 0, false :: _ => none
  | j + 1, b :: tail =>
      (contractAt j tail).map (fun tail' => b :: tail')

/-- Shift left and insert a new rightmost bit; an occupied first site dies. -/
def shiftInsert (new : Bool) : State → Option State
  | false :: tail => some (tail ++ [new])
  | _ => none

def step : Label → State → Option State
  | .star, A => shiftInsert false A
  | .reset j, A => (contractAt j A).bind (shiftInsert true)

def run : List Label → State → Option State
  | [], A => some A
  | l :: w, A => (step l A).bind (run w)

@[simp] theorem run_nil (A : State) : run [] A = some A := rfl

@[simp] theorem run_cons (l : Label) (w : List Label) (A : State) :
    run (l :: w) A = (step l A).bind (run w) := rfl

@[simp] theorem run_append (u v : List Label) (A : State) :
    run (u ++ v) A = (run u A).bind (run v) := by
  induction u generalizing A with
  | nil => rfl
  | cons l u ih =>
      simp only [List.cons_append, run_cons]
      cases h : step l A with
      | none => rfl
      | some A' => exact ih A'

@[simp] theorem step_reset_zero (tail : State) :
    step (.reset 0) (true :: tail) = some (tail ++ [true]) := rfl

@[simp] theorem step_reset_zero_empty (tail : State) :
    step (.reset 0) (false :: tail) = none := rfl

@[simp] theorem step_star_empty (tail : State) :
    step .star (false :: tail) = some (tail ++ [false]) := rfl

@[simp] theorem step_star_occupied (tail : State) :
    step .star (true :: tail) = none := rfl

/-- Read the prescribed first bit, rotate it right, and fail on a mismatch. -/
def readLabel : Bool → Label
  | false => .star
  | true => .reset 0

def singletonWord (J : State) : List Label := J.map readLabel

@[simp] theorem singletonWord_length (J : State) :
    (singletonWord J).length = J.length := by
  simp [singletonWord]

@[simp] theorem step_readLabel (b : Bool) (tail : State) :
    step (readLabel b) (b :: tail) = some (tail ++ [b]) := by
  cases b <;> rfl

@[simp] theorem step_readLabel_not (b : Bool) (tail : State) :
    step (readLabel b) ((!b) :: tail) = none := by
  cases b <;> rfl

@[simp] theorem singletonWord_nil : singletonWord [] = [] := rfl

@[simp] theorem singletonWord_cons (b : Bool) (J : State) :
    singletonWord (b :: J) = readLabel b :: singletonWord J := rfl

/-- After reading prefix `J`, its bits have rotated to the right boundary. -/
theorem run_singletonWord_append (J R : State) :
    run (singletonWord J) (J ++ R) = some (R ++ J) := by
  induction J generalizing R with
  | nil => simp
  | cons b J ih =>
      simp only [singletonWord_cons, run_cons, List.cons_append,
        step_readLabel, Option.bind_some]
      rw [List.append_assoc]
      rw [ih (R ++ [b])]
      simp [List.append_assoc]

/-- Converse: a surviving equal-length prefix must equal the prescribed one. -/
theorem eq_of_run_singletonWord_prefix
    (J A R B : State) (hlen : A.length = J.length)
    (h : run (singletonWord J) (A ++ R) = some B) : A = J := by
  induction J generalizing A R B with
  | nil =>
      cases A with
      | nil => rfl
      | cons a A => simp at hlen
  | cons b J ih =>
      cases A with
      | nil => simp at hlen
      | cons a A =>
          have hlen' : A.length = J.length := by simpa using hlen
          cases a <;> cases b
          · simp only [singletonWord_cons, run_cons, List.cons_append,
              readLabel, step_star_empty, Option.bind_some] at h
            have htail : A = J :=
              ih A (R ++ [false]) B hlen' (by
                simpa only [List.append_assoc] using h)
            exact congrArg (fun T => false :: T) htail
          · simp [singletonWord_cons, readLabel] at h
          · simp [singletonWord_cons, readLabel] at h
          · simp only [singletonWord_cons, run_cons, List.cons_append,
              readLabel, step_reset_zero, Option.bind_some] at h
            have htail : A = J :=
              ih A (R ++ [true]) B hlen' (by
                simpa only [List.append_assoc] using h)
            exact congrArg (fun T => true :: T) htail

/-- Full singleton-domain assertion: the word fixes `J` and kills every
other input of the same length, regardless of particle number. -/
theorem singleton_domain_word (J A : State) (hlen : A.length = J.length) :
    run (singletonWord J) A = if A = J then some J else none := by
  by_cases hAJ : A = J
  · subst A
    rw [if_pos rfl]
    simpa using run_singletonWord_append J []
  · rw [if_neg hAJ]
    cases hrun : run (singletonWord J) A with
    | none => rfl
    | some B =>
        exfalso
        apply hAJ
        exact eq_of_run_singletonWord_prefix J A [] B hlen (by simpa using hrun)

/-- Number of occupied sites, i.e. exterior degree. -/
def particleCount : State → Nat
  | [] => 0
  | false :: tail => particleCount tail
  | true :: tail => particleCount tail + 1

/-- The singleton word kills every other exterior degree explicitly. -/
theorem singletonWord_kills_other_degree (J A : State)
    (hlen : A.length = J.length)
    (hdegree : particleCount A ≠ particleCount J) :
    run (singletonWord J) A = none := by
  have hAJ : A ≠ J := by
    intro h
    apply hdegree
    exact congrArg particleCount h
  rw [singleton_domain_word J A hlen, if_neg hAJ]

theorem exists_singleton_domain_word (d : Nat) (J : State)
    (hJ : J.length = d) :
    ∃ w : List Label, w.length = d ∧
      ∀ A : State, A.length = d →
        run w A = if A = J then some J else none := by
  refine ⟨singletonWord J, ?_, ?_⟩
  · exact (singletonWord_length J).trans hJ
  · intro A hA
    apply singleton_domain_word J A
    exact hA.trans hJ.symm

/-- Canonical prefix which moves a left block of particles to the right. -/
def leftBlock (d r : Nat) : State :=
  List.replicate r true ++ List.replicate (d - r) false

def rightBlock (d r : Nat) : State :=
  List.replicate (d - r) false ++ List.replicate r true

def resetPrefix (r : Nat) : List Label := List.replicate r (.reset 0)

theorem singletonWord_replicate_true (r : Nat) :
    singletonWord (List.replicate r true) = resetPrefix r := by
  simp [singletonWord, resetPrefix, readLabel]

theorem resetPrefix_sends_leftBlock_to_rightBlock (d r : Nat) :
    run (resetPrefix r) (leftBlock d r) = some (rightBlock d r) := by
  simpa [leftBlock, rightBlock, singletonWord_replicate_true] using
    run_singletonWord_append (List.replicate r true)
      (List.replicate (d - r) false)

/-- Corrected index from the manuscript: after the prefix the canonical
particles occupy `d-r+k`, not the out-of-range `d+k`. -/
def correctedPrefixPosition (d r k : Nat) : Nat := d - r + k

theorem correctedPrefixPosition_lt (d r k : Nat)
    (hr : r ≤ d) (hk : k < r) :
    correctedPrefixPosition d r k < d := by
  unfold correctedPrefixPosition
  have h := Nat.add_lt_add_left hk (d - r)
  simpa [Nat.sub_add_cancel hr] using h

end CircularLawSection4.ResetWord
