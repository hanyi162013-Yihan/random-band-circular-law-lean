import BernoulliSection10.CyclicEntryGeometry
import BernoulliSection10.FiniteIIDCoordinates
import BernoulliSection10.FiniteIIDLawOfLargeNumbers

/-!
# Embedding the displayed block atoms into a full square IID array

Every displayed physical coordinate occupies a distinct matrix entry.
Selecting those entries from a square IID array therefore produces exactly
the physical-row law, including the independence of all displayed atoms.
-/

open MeasureTheory

noncomputable section

namespace BernoulliSection10

open BernoulliLinearAlgebra

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def physicalNeighborSite {s : ℕ} (j : Fin (s + 3)) (b : Fin 3) : Fin (s + 3) :=
  if b = 0 then cyclicSiteSucc j else if b = 1 then j else (cyclicSiteSucc (m := s + 2)).symm j

theorem physicalNeighborSite_injective {s : ℕ} (j : Fin (s + 3)) :
    Function.Injective (physicalNeighborSite j) := by
  intro a b hab
  obtain ⟨h1, h2, h3⟩ := cyclic_three_positions_distinct s j
  fin_cases a <;> fin_cases b <;> norm_num [physicalNeighborSite] at hab ⊢
  all_goals first
    | exact (h1 hab).elim
    | exact (h1 hab.symm).elim
    | exact (h2 hab).elim
    | exact (h2 hab.symm).elim
    | exact (h3 hab).elim
    | exact (h3 hab.symm).elim

def physicalColumn (W s : ℕ) (i : Fin ((s + 3) * W)) (a : Fin (3 * W)) :
    Fin ((s + 3) * W) :=
  finProdFinEquiv (physicalNeighborSite (finProdFinEquiv.symm i).1
    (finProdFinEquiv.symm a).1, (finProdFinEquiv.symm a).2)

theorem physicalColumn_injective (W s : ℕ) (i : Fin ((s + 3) * W)) :
    Function.Injective (physicalColumn W s i) := by
  intro a b hab
  have h := finProdFinEquiv.injective hab
  have hj := physicalNeighborSite_injective _ (congrArg Prod.fst h)
  have hc := congrArg Prod.snd h
  exact finProdFinEquiv.symm.injective (Prod.ext hj hc)

def physicalSquareCoordinate (W s : ℕ) :
    (Fin ((s + 3) * W) × Fin (3 * W)) ↪
      (Fin ((s + 3) * W) × Fin ((s + 3) * W)) where
  toFun p := (p.1, physicalColumn W s p.1 p.2)
  inj' := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hi : i = j := congrArg Prod.fst h
    subst j
    have ha := physicalColumn_injective W s i (congrArg Prod.snd h)
    exact Prod.ext rfl ha

def physicalRowsFromSquare (W s : ℕ)
    (x : Fin ((s + 3) * W) × Fin ((s + 3) * W) → ℝ) : IntervalRows W (s + 3) :=
  fun i a => x (i, physicalColumn W s i a)

theorem physicalRowsFromSquare_measurePreserving
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (W s : ℕ) :
    MeasurePreserving (physicalRowsFromSquare W s)
      (Measure.pi fun _ : Fin ((s + 3) * W) × Fin ((s + 3) * W) => μ)
      (intervalRowsLaw W (s + 3) μ) :=
  (measurePreserving_iid_curry μ).comp
    (measurePreserving_pi_restrict_embedding μ (physicalSquareCoordinate W s))

def squareIIDFromSequence (n : ℕ) (ω : ℕ → ℝ) : Fin n × Fin n → ℝ :=
  fun p => ω (finProdFinEquiv p).val

theorem squareIIDFromSequence_measurePreserving
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (squareIIDFromSequence n) (Measure.infinitePi fun _ : ℕ => μ)
      (Measure.pi fun _ : Fin n × Fin n => μ) :=
  (measurePreserving_iid_reindex μ (finProdFinEquiv : Fin n × Fin n ≃ Fin (n * n))).comp
    (measurePreserving_initialIIDCoordinates μ (n * n))

def physicalRowsFromSequence (W s : ℕ) (ω : ℕ → ℝ) : IntervalRows W (s + 3) :=
  physicalRowsFromSquare W s (squareIIDFromSequence ((s + 3) * W) ω)

theorem physicalRowsFromSequence_measurePreserving
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (W s : ℕ) :
    MeasurePreserving (physicalRowsFromSequence W s)
      (Measure.infinitePi fun _ : ℕ => μ) (intervalRowsLaw W (s + 3) μ) :=
  (physicalRowsFromSquare_measurePreserving μ W s).comp
    (squareIIDFromSequence_measurePreserving μ ((s + 3) * W))

end BernoulliSection10
