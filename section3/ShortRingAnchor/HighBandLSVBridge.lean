import Vendor.HighBandLSV
import ShortRingAnchor.LeastSingularValueAdapter
import ShortRingAnchor.SourceScales
import ShortRingAnchor.SecondMoment
import Mathlib.Probability.IdentDistrib

/-!
# Exact scalar and event bridges for the copied Theorem 3.1

The two least-singular-value definitions agree definitionally. Substituting
`t=N^(-2)` gives exactly the manuscript's `exp(-L_N)`. The strict lower-tail
event is Borel, so equality of matrix laws suffices to transport the published
bound. No measurability of a chosen singular vector is needed.
-/

open MeasureTheory ProbabilityTheory Set HighBandLSV
open scoped ENNReal BigOperators
noncomputable section
namespace ShortRingAnchor

local instance (N : ℕ) : MeasurableSpace (Matrix (Fin N) (Fin N) ℂ) := borel _
local instance (N : ℕ) : BorelSpace (Matrix (Fin N) (Fin N) ℂ) := ⟨rfl⟩

/-- Theorem 3.1 to manuscript (3.10): both projects use the same least singular value. -/
theorem ginibreLeastSingularValue_eq_last {N : ℕ} (hN : 0 < N)
    (X : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) :
    GinibreLSV.leastSingularValue (shifted X z) =
      shiftedSingularValueFamily X z (lastSingularValueIndex N hN) := rfl

/-- Theorem 3.1 with `t=N^-2`: exact agreement with the hard-edge scale used in (3.10). -/
theorem highBand_threshold_eq_source_exp {M W : ℕ → ℕ} (k : ℕ) (hM : 0 < M k) (kappa : ℝ) :
    HighBandLSV.tau (M k) (W k) kappa ((M k : ℝ) ^ (-(2 : ℝ))) =
      Real.exp (-(sourceHardEdgeScale M W kappa k)) := by
  have hn : (0 : ℝ) < M k := by exact_mod_cast hM
  have hp : (M k : ℝ) ^ (1 + 3 * kappa) / (W k : ℝ) =
      (M k : ℝ) ^ (3 * kappa) * ((M k : ℝ) / (W k : ℝ)) := by
    rw [Real.rpow_add hn, Real.rpow_one]
    ring
  have ht : (M k : ℝ) ^ (-(2 : ℝ)) = Real.exp (-(2 * Real.log (M k))) := by
    rw [Real.rpow_def_of_pos hn]
    congr 1
    ring
  simp only [HighBandLSV.tau, Section5Formalization.leastSingularThreshold,
    sourceHardEdgeScale, hp, ht, neg_add, Real.exp_add]
  ring

/-- Theorem 3.1 law transport: the strict least-value sublevel is open. -/
theorem isOpen_leastSingularValue_lt {N : ℕ} (hN : 0 < N) (t : ℝ) :
    IsOpen {A : Matrix (Fin N) (Fin N) ℂ | GinibreLSV.leastSingularValue A < t} := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  letI : Nontrivial (EuclideanSpace ℂ (Fin N)) := inferInstance
  let V := {x : EuclideanSpace ℂ (Fin N) // x ≠ 0}
  letI : Nonempty V := by
    obtain ⟨x, hx⟩ := exists_ne (0 : EuclideanSpace ℂ (Fin N))
    exact ⟨⟨x, hx⟩⟩
  have heq : {A : Matrix (Fin N) (Fin N) ℂ | GinibreLSV.leastSingularValue A < t} =
      ⋃ x : V, {A | LinearMap.singularQuotient A.toEuclideanLin
        (x : EuclideanSpace ℂ (Fin N)) < t} := by
    ext A
    rw [mem_setOf_eq, GinibreLSV.leastSingularValue_eq_iInf_singularQuotient hN,
      ciInf_lt_iff (show BddBelow (range (fun x : V =>
        LinearMap.singularQuotient A.toEuclideanLin (x : EuclideanSpace ℂ (Fin N)))) from
          ⟨0, by rintro _ ⟨x, rfl⟩; unfold LinearMap.singularQuotient; positivity⟩)]
    simp only [mem_iUnion, mem_setOf_eq]
  rw [heq]
  apply isOpen_iUnion
  intro x
  have hc : Continuous (fun A : Matrix (Fin N) (Fin N) ℂ => A.toEuclideanLin x) := by
    change Continuous (fun A : Matrix (Fin N) (Fin N) ℂ =>
      WithLp.toLp 2 (Matrix.mulVec A (WithLp.ofLp (x : EuclideanSpace ℂ (Fin N)))))
    exact (PiLp.continuous_toLp 2 _).comp (continuous_id.matrix_mulVec continuous_const)
  exact isOpen_lt (hc.norm.div_const _) continuous_const

/-- Theorem 3.1 law transport: its intersection with the HS cutoff is Borel. -/
theorem measurableSet_highBand_strict_bad {N : ℕ} (hN : 0 < N) (z : ℂ) (t R : ℝ) :
    MeasurableSet {A : Matrix (Fin N) (Fin N) ℂ |
      GinibreLSV.leastSingularValue (shifted A z) < t ∧
        hilbertSchmidt A ≤ R * Real.sqrt (N : ℝ)} := by
  have hs : Continuous (fun A : Matrix (Fin N) (Fin N) ℂ => shifted A z) := by
    unfold shifted
    fun_prop
  have hh : Continuous (fun A : Matrix (Fin N) (Fin N) ℂ => hilbertSchmidt A) := by
    simp only [hilbertSchmidt_formula]
    fun_prop
  exact ((isOpen_leastSingularValue_lt hN t).preimage hs).measurableSet.inter
    (isClosed_le hh continuous_const).measurableSet

/-- Theorem 3.1 law transport to the actual array: a strict bad event is
bounded by the copied theorem's non-strict bad event on the product space. -/
theorem highBand_strict_bad_le_of_identDistrib
    {Omega Omega' : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega']
    {mu : Measure Omega} {mu' : Measure Omega'} {N : ℕ} (hN : 0 < N)
    {X : Omega → Matrix (Fin N) (Fin N) ℂ} {Y : Omega' → Matrix (Fin N) (Fin N) ℂ}
    (hlaw : IdentDistrib X Y mu mu') (z : ℂ) (t R : ℝ) :
    mu {sample | GinibreLSV.leastSingularValue (shifted (X sample) z) < t ∧
        hilbertSchmidt (X sample) ≤ R * Real.sqrt (N : ℝ)} ≤
      mu' (leastSingularBadEvent (fun sample => shifted (Y sample) z) t ∩ hsEvent Y R) := by
  calc
    _ = mu' {sample | GinibreLSV.leastSingularValue (shifted (Y sample) z) < t ∧
        hilbertSchmidt (Y sample) ≤ R * Real.sqrt (N : ℝ)} :=
      hlaw.measure_mem_eq (measurableSet_highBand_strict_bad hN z t R)
    _ ≤ _ := by
      apply measure_mono
      intro sample hs
      exact ⟨hs.1.le, hs.2⟩

/-- Manuscript (3.13): the empirical second moment is exactly `HS(X)^2/N`. -/
theorem empiricalSecondMoment_zero_eq_hilbertSchmidt_sq {N : ℕ}
    (X : Matrix (Fin N) (Fin N) ℂ) :
    empiricalAverage (shiftedSingularValueFamily X 0) (fun t => t ^ 2) =
      hilbertSchmidt X ^ 2 / (N : ℝ) := by
  rw [empiricalSecondMoment_shiftedSingularValueFamily, hilbertSchmidt_formula,
    Real.sq_sqrt (by positivity)]
  simp

end ShortRingAnchor
