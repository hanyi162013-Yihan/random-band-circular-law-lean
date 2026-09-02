import SubgaussianSection8.HighBand
import BernoulliSection8.MesoscopicScales
import BernoulliSection10.CyclicSeamAssembly
import BernoulliSection10.ProbabilityTransport

/-!
# The Section 3 input on the actual finite row laws

The exact many-cell anchor is in the high-band regime. A target below
that anchor is also in that regime, uniformly in its dimension. Filling
the complementary indices with the anchor proves the direct branch even
when short and long targets alternate arbitrarily.
-/

open Filter MeasureTheory
open scoped Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace SubgaussianSection8
open BernoulliSection8

open BernoulliSection10 BernoulliSection10.ProbabilityLimits
open ShortRingAnchor BernoulliSection10.DiskReference

theorem normalizedShiftLogDet_subgaussianMatrix (Ξ : Atom) (W s : ℕ) (z : ℂ) (x : ℕ → ℝ) :
    normalizedShiftLogDet (matrix W s x) z =
      densityCyclicLogDet W s z (physicalRowsFromSequence W s x) /
        (((s + 3) * W : ℕ) : ℝ) := by
  unfold normalizedShiftLogDet densityCyclicLogDet matrix
  rw [densityShiftedCyclicMatrix_eq_sub_scalar]

/-- No matrix estimate is used in this equivalence: the finite law is
exactly the marginal of the displayed IID sequence coordinates. -/
theorem subgaussian_log_converges_iff_physical_rows (Ξ : Atom)
    (W s : ℕ → ℕ) (z : ℂ) (u : ℝ) :
    TendstoInMeasure (sequenceLaw Ξ)
      (fun n x => normalizedShiftLogDet (matrix (W n) (s n) x) z)
      atTop (fun _ => u) ↔
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) Ξ.law)
      (fun n x => densityCyclicLogDet (W n) (s n) z x /
        (((s n + 3) * W n : ℕ) : ℝ)) u := by
  have h := tendstoInProbabilityTri_measurePreserving_iff
    (fun _ => (sequenceLaw Ξ))
    (fun n => intervalRowsLaw (W n) (s n + 3) Ξ.law)
    (fun n => physicalRowsFromSequence (W n) (s n))
    (fun n => physicalRowsFromSequence_measurePreserving Ξ.law (W n) (s n))
    (fun n x => densityCyclicLogDet (W n) (s n) z x /
      (((s n + 3) * W n : ℕ) : ℝ))
    (fun n => (measurable_densityCyclicLogDet (W n) (s n) z).div_const _) u
  simpa only [TendstoInProbabilityTri, tendstoInMeasure_iff_measureReal_norm,
    Real.norm_eq_abs, ← (normalizedShiftLogDet_subgaussianMatrix Ξ)] using h

theorem subgaussian_high_band_rows_log_potential (Ξ : Atom)
    (hSource : Section3Input Ξ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hs : ∀ n, 0 < s n)
    (hWtop : Tendsto W atTop atTop)
    (ω : ℝ) (hω : 0 < ω) (hωlt : ω < 1 / 9)
    (hband : ∀ᶠ n in atTop,
      (((s n + 3) * W n : ℕ) : ℝ) ^ (8 / 9 + ω) ≤ W n) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) Ξ.law)
      (fun n x => densityCyclicLogDet (W n) (s n) z x /
        (((s n + 3) * W n : ℕ) : ℝ)) (circularLogPotential z) :=
  ((subgaussian_log_converges_iff_physical_rows Ξ) W s z _).1
    (high_band_log_potential Ξ hSource W s hW hs hWtop ω hω hωlt hband z)

/-- The independent anchor's normalized actual cyclic determinant. -/
def anchorLogPotential (Ξ : Atom) (W : ℕ) (z : ℂ) (x : IntervalRows W (anchorSites W)) : ℝ :=
  densityCyclicLogDet W (anchorCells W * cellSites W) z x / (anchorSize W : ℝ)

/-- The only external input here is the permitted Proposition 3.8.
The number of complete cells is the literal `K_W=ceil(W^(1/200))`. -/
theorem subgaussian_anchor_log_potential (Ξ : Atom)
    (hSource : Section3Input Ξ)
    (W : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (anchorSites (W n)) Ξ.law)
      (fun n => (anchorLogPotential Ξ) (W n) z) (circularLogPotential z) := by
  have hs (n : ℕ) : 0 < anchorCells (W n) * cellSites (W n) :=
    Nat.mul_pos (anchorCells_pos (hW n)) (cellSites_pos _)
  have hb : ∀ᶠ n in atTop,
      ((((anchorCells (W n) * cellSites (W n) + 3) * W n : ℕ) : ℝ) ^
        (8 / 9 + 1 / 20 : ℝ)) ≤ W n := by
    simpa only [anchorSize, anchorSites, Nat.mul_comm] using
      hWtop.eventually eventually_anchor_highBand
  have h := (subgaussian_high_band_rows_log_potential Ξ) hSource W
    (fun n => anchorCells (W n) * cellSites (W n)) hW hs hWtop
    (1 / 20) (by norm_num) (by norm_num) hb z
  apply h.congr
  · intro n x
    simp only [(anchorLogPotential Ξ), anchorSize, anchorSites, Nat.mul_comm]
  · rfl

/-- Source lengths for the direct branch, with anchors at the other
indices so no eventual branch choice is needed. -/
def directOrAnchorCoreSites (Ξ : Atom) (W s : ℕ) : ℕ :=
  if (s + 3) * W < anchorSize W then s else anchorCells W * cellSites W

theorem directOrAnchorCoreSites_pos (Ξ : Atom) {W s : ℕ} (hW : 0 < W) (hs : 0 < s) :
    0 < (directOrAnchorCoreSites Ξ) W s := by
  unfold directOrAnchorCoreSites
  split
  · exact hs
  · exact Nat.mul_pos (anchorCells_pos hW) (cellSites_pos W)

theorem eventually_directOrAnchor_highBand (Ξ : Atom) (W s : ℕ → ℕ)
    (hWtop : Tendsto W atTop atTop) :
    ∀ᶠ n in atTop,
      ((((directOrAnchorCoreSites Ξ) (W n) (s n) + 3) * W n : ℕ) : ℝ) ^
        (8 / 9 + 1 / 20 : ℝ) ≤ W n := by
  filter_upwards [hWtop.eventually eventually_anchor_highBand,
    hWtop.eventually eventually_direct_highBand] with n ha hd
  unfold directOrAnchorCoreSites
  split
  · exact hd _ ‹_›
  · simpa only [anchorSize, anchorSites, Nat.mul_comm] using ha

/-- A direct-branch observable on every target's own finite row space.
At the complementary indices it takes the limiting constant. -/
def directBranchLogPotential (Ξ : Atom) (W s : ℕ) (z : ℂ) (x : IntervalRows W (s + 3)) : ℝ :=
  if (s + 3) * W < anchorSize W then
    densityCyclicLogDet W s z x / (((s + 3) * W : ℕ) : ℝ)
  else circularLogPotential z

/-- Direct convergence holds under arbitrary alternation with the long
branch. The long-branch constant only fills unused indices. -/
theorem subgaussian_direct_branch_log_potential (Ξ : Atom)
    (hSource : Section3Input Ξ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hs : ∀ n, 0 < s n)
    (hWtop : Tendsto W atTop atTop) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) Ξ.law)
      (fun n => (directBranchLogPotential Ξ) (W n) (s n) z) (circularLogPotential z) := by
  have h := (subgaussian_high_band_rows_log_potential Ξ) hSource W
    (fun n => (directOrAnchorCoreSites Ξ) (W n) (s n)) hW
    (fun n => (directOrAnchorCoreSites_pos Ξ) (hW n) (hs n)) hWtop
    (1 / 20) (by norm_num) (by norm_num)
    ((eventually_directOrAnchor_highBand Ξ) W s hWtop) z
  intro ε hε
  refine squeeze_zero (t₀ := (atTop : Filter ℕ))
    (f := fun n : ℕ => (intervalRowsLaw (W n) (s n + 3) Ξ.law).real
      {x : IntervalRows (W n) (s n + 3) |
        ε ≤ |(directBranchLogPotential Ξ) (W n) (s n) z x - circularLogPotential z|})
    (fun n : ℕ => measureReal_nonneg) ?_ (h ε hε)
  intro n
  by_cases hn : (s n + 3) * W n < anchorSize (W n)
  · let F : ℕ → ℝ := fun q =>
      (intervalRowsLaw (W n) (q + 3) Ξ.law).real
        {x : IntervalRows (W n) (q + 3) |
          ε ≤ |densityCyclicLogDet (W n) q z x /
            (((q + 3) * W n : ℕ) : ℝ) - circularLogPotential z|}
    have hsites : (directOrAnchorCoreSites Ξ) (W n) (s n) = s n := by
      simp only [(directOrAnchorCoreSites Ξ), if_pos hn]
    have hvalue : (intervalRowsLaw (W n) (s n + 3) Ξ.law).real
        {x : IntervalRows (W n) (s n + 3) |
          ε ≤ |(directBranchLogPotential Ξ) (W n) (s n) z x - circularLogPotential z|} =
        F (s n) := by
      simp only [F, (directBranchLogPotential Ξ), if_pos hn]
    exact (hvalue.trans (congrArg F hsites).symm).le
  · simp only [(directBranchLogPotential Ξ), if_neg hn, sub_self, abs_zero]
    have he : {x : IntervalRows (W n) (s n + 3) | ε ≤ (0 : ℝ)} = ∅ := by
      ext x
      simp [not_le_of_gt hε]
    rw [he, measureReal_empty]
    exact measureReal_nonneg

end SubgaussianSection8
