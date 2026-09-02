import CircularLawSections56.Section6.CyclicBand
import TaoVuReplacement.WeylSecondMoment
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp

/-! # Actual cyclic matrices and their finite-dimensional energy

Atoms are indexed by `(row, cyclic displacement)`. Vanishing weights encode
inactive entries, so the same constructor represents the full matrix, core,
and tail. The energy statements do not require Gaussianity or independence
beyond the coordinate laws of the displayed product probability space.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace CircularLawSection6

def cyclicOffsetEquiv (N : ℕ) (i : ZMod N) : ZMod N ≃ ZMod N where
  toFun j := j - i
  invFun s := s + i
  left_inv _ := by simp
  right_inv _ := by simp

def weightedCyclicMatrix (N : ℕ) (q : ZMod N → ℝ)
    (ω : ZMod N × ZMod N → ℂ) : Matrix (ZMod N) (ZMod N) ℂ :=
  fun i j => (Real.sqrt (q (j - i)) : ℂ) * ω (i, j - i)

def cyclicEnergy (N : ℕ) [NeZero N] (A : Matrix (ZMod N) (ZMod N) ℂ) : ℝ :=
  TaoVuReplacement.hilbertSchmidtSq A / (N : ℝ)

def maskedWeight {ι : Type*} [DecidableEq ι] (S : Finset ι) (q : ι → ℝ) (s : ι) : ℝ :=
  if s ∈ S then q s else 0

theorem weightedCyclicMatrix_measurable (N : ℕ) (q : ZMod N → ℝ) (i j : ZMod N) :
    Measurable (fun ω => weightedCyclicMatrix N q ω i j) :=
  measurable_const.mul (measurable_pi_apply _)

theorem cyclic_row_variance_sum (N : ℕ) [NeZero N] (q : ZMod N → ℝ) (i : ZMod N) :
    ∑ j, q (j - i) = ∑ s, q s :=
  (cyclicOffsetEquiv N i).sum_comp q

theorem cyclic_column_variance_sum (N : ℕ) [NeZero N] (q : ZMod N → ℝ) (j : ZMod N) :
    ∑ i, q (j - i) = ∑ s, q s := by
  let e : ZMod N ≃ ZMod N :=
    ⟨(fun i => j - i), (fun s => j - s), (by intro i; simp), (by intro s; simp)⟩
  exact e.sum_comp q

theorem weightedCyclicMatrix_hilbertSchmidtSq
    (N : ℕ) [NeZero N] (q : ZMod N → ℝ) (hq : ∀ s, 0 ≤ q s)
    (ω : ZMod N × ZMod N → ℂ) :
    TaoVuReplacement.hilbertSchmidtSq (weightedCyclicMatrix N q ω) =
      ∑ i : ZMod N, ∑ s : ZMod N, q s * ‖ω (i, s)‖ ^ 2 := by
  unfold TaoVuReplacement.hilbertSchmidtSq weightedCyclicMatrix
  simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hq _)]
  apply Finset.sum_congr rfl
  intro i _
  exact (cyclicOffsetEquiv N i).sum_comp (fun s => q s * ‖ω (i, s)‖ ^ 2)

theorem weightedCyclicMatrix_core_add_tail
    (N : ℕ) [NeZero N] (S : Finset (ZMod N)) (q : ZMod N → ℝ)
    (ω : ZMod N × ZMod N → ℂ) :
    weightedCyclicMatrix N (maskedWeight S q) ω +
      weightedCyclicMatrix N (maskedWeight Sᶜ q) ω = weightedCyclicMatrix N q ω := by
  ext i j
  by_cases h : j - i ∈ S <;> simp [weightedCyclicMatrix, maskedWeight, h]

/-- Exact additivity holds because core and tail occupy disjoint entries. -/
theorem cyclicEnergy_core_add_tail
    (N : ℕ) [NeZero N] (S : Finset (ZMod N)) (q : ZMod N → ℝ)
    (ω : ZMod N × ZMod N → ℂ) :
    cyclicEnergy N (weightedCyclicMatrix N (maskedWeight S q) ω) +
      cyclicEnergy N (weightedCyclicMatrix N (maskedWeight Sᶜ q) ω) =
        cyclicEnergy N (weightedCyclicMatrix N q ω) := by
  unfold cyclicEnergy TaoVuReplacement.hilbertSchmidtSq
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j - i ∈ S <;> simp [weightedCyclicMatrix, maskedWeight, h]

def cyclicAtomLaw (N : ℕ) [NeZero N] (ν : Measure ℂ) : Measure (ZMod N × ZMod N → ℂ) :=
  Measure.pi (fun _ => ν)

instance cyclicAtomLaw_isProbability (N : ℕ) [NeZero N]
    (ν : Measure ℂ) [IsProbabilityMeasure ν] : IsProbabilityMeasure (cyclicAtomLaw N ν) := by
  unfold cyclicAtomLaw
  infer_instance

/-- The expected normalized HS square is the total variance weight times the
actual atom second moment. In particular it is exactly one for normalized
weights and normalized atoms; it is the core/tail mass for masked weights. -/
theorem weightedCyclicMatrix_expected_energy
    (N : ℕ) [NeZero N] (q : ZMod N → ℝ) (hq : ∀ s, 0 ≤ q s)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν) :
    Integrable (fun ω => cyclicEnergy N (weightedCyclicMatrix N q ω)) (cyclicAtomLaw N ν) ∧
      (∫ ω, cyclicEnergy N (weightedCyclicMatrix N q ω) ∂cyclicAtomLaw N ν) =
        (∑ s, q s) * ∫ u : ℂ, ‖u‖ ^ 2 ∂ν := by
  let μ := cyclicAtomLaw N ν
  have hMP (i s : ZMod N) : MeasurePreserving
      (fun ω : ZMod N × ZMod N → ℂ => ω (i, s)) μ ν := measurePreserving_eval _ (i, s)
  have ht (i s : ZMod N) : Integrable (fun ω => q s * ‖ω (i, s)‖ ^ 2) μ := by
    exact ((hMP i s).integrable_comp_of_integrable hInt).const_mul _
  have hcoord (i s : ZMod N) :
      (∫ ω, ‖ω (i, s)‖ ^ 2 ∂μ) = ∫ u : ℂ, ‖u‖ ^ 2 ∂ν := by
    have hf : AEStronglyMeasurable (fun u : ℂ => ‖u‖ ^ 2)
        (Measure.map (fun ω : ZMod N × ZMod N → ℂ => ω (i, s)) μ) := by
      rw [(hMP i s).map_eq]
      exact hInt.aestronglyMeasurable
    calc
      _ = ∫ u : ℂ, ‖u‖ ^ 2 ∂Measure.map (fun ω => ω (i, s)) μ :=
        (integral_map (hMP i s).measurable.aemeasurable hf).symm
      _ = _ := by rw [(hMP i s).map_eq]
  have hsum : Integrable (fun ω => ∑ i : ZMod N, ∑ s : ZMod N,
      q s * ‖ω (i, s)‖ ^ 2) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun s _ => ht i s
  simp_rw [cyclicEnergy, weightedCyclicMatrix_hilbertSchmidtSq N q hq]
  refine ⟨hsum.div_const _, ?_⟩
  rw [integral_div, integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun s _ => ht i s))]
  have heq (i : ZMod N) : (∫ ω, ∑ s : ZMod N, q s * ‖ω (i, s)‖ ^ 2 ∂μ) =
      (∑ s, q s) * ∫ u : ℂ, ‖u‖ ^ 2 ∂ν := by
    rw [integral_finsetSum _ (fun s _ => ht i s)]
    simp_rw [integral_const_mul, hcoord]
    exact (Finset.sum_mul _ _ _).symm
  simp_rw [heq]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp

end CircularLawSection6
