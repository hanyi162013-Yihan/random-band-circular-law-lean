import CircularLawSections56.Section6.RadialAndCutoff
import Mathlib.Topology.Order.Basic

/-!
# The two-limit compact-core squeeze

The matrix-size limit and the truncation-radius limit are distinct. This file
does not replace them with an unjustified diagonal sequence. For each fixed
radius the matrix-size bounds are only required eventually; their limiting
endpoints subsequently converge as the radius grows.
-/

open Filter Topology

namespace CircularLawSection6

open CircularLawSections56.Section6

/-- A genuine iterated squeeze, with no uniformity in the auxiliary radius. -/
theorem tendsto_of_iterated_squeeze
    (mean : ℕ → ℝ) (lower upper : ℕ → ℕ → ℝ)
    (lowerLimit upperLimit : ℕ → ℝ) (target : ℝ)
    (hLower : ∀ R, ∀ᶠ n in atTop, lower R n ≤ mean n)
    (hUpper : ∀ R, ∀ᶠ n in atTop, mean n ≤ upper R n)
    (hLowerLimit : ∀ R, Tendsto (lower R) atTop (𝓝 (lowerLimit R)))
    (hUpperLimit : ∀ R, Tendsto (upper R) atTop (𝓝 (upperLimit R)))
    (hLowerTarget : Tendsto lowerLimit atTop (𝓝 target))
    (hUpperTarget : Tendsto upperLimit atTop (𝓝 target)) :
    Tendsto mean atTop (𝓝 target) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨R, hR⟩ := (hLowerTarget.eventually (Ioi_mem_nhds ha)).exists
    filter_upwards [(hLowerLimit R).eventually (Ioi_mem_nhds hR), hLower R]
      with n hn hbound
    exact hn.trans_le hbound
  · intro b hb
    obtain ⟨R, hR⟩ := (hUpperTarget.eventually (Iio_mem_nhds hb)).exists
    filter_upwards [(hUpperLimit R).eventually (Iio_mem_nhds hR), hUpper R]
      with n hn hbound
    exact hbound.trans_lt hn

/-- Version allowing all radius hypotheses to hold only eventually. This is
needed when the hard-edge estimate applies only for small cutoffs. -/
theorem tendsto_of_eventual_iterated_squeeze
    (mean : ℕ → ℝ) (lower upper : ℕ → ℕ → ℝ)
    (lowerLimit upperLimit : ℕ → ℝ) (target : ℝ)
    (hBounds : ∀ᶠ R in atTop,
      (∀ᶠ n in atTop, lower R n ≤ mean n ∧ mean n ≤ upper R n) ∧
      Tendsto (lower R) atTop (𝓝 (lowerLimit R)) ∧
      Tendsto (upper R) atTop (𝓝 (upperLimit R)))
    (hLowerTarget : Tendsto lowerLimit atTop (𝓝 target))
    (hUpperTarget : Tendsto upperLimit atTop (𝓝 target)) :
    Tendsto mean atTop (𝓝 target) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨R, hR, hdata⟩ :=
      ((hLowerTarget.eventually (Ioi_mem_nhds ha)).and hBounds).exists
    filter_upwards [hdata.2.1.eventually (Ioi_mem_nhds hR), hdata.1]
      with n hn hbound
    exact hn.trans_le hbound.1
  · intro b hb
    obtain ⟨R, hR, hdata⟩ :=
      ((hUpperTarget.eventually (Iio_mem_nhds hb)).and hBounds).exists
    filter_upwards [hdata.2.2.eventually (Iio_mem_nhds hR), hdata.1]
      with n hn hbound
    exact hbound.2.trans_lt hn

/-- Section 6's raw-mean limit, with the compact-core convergence, finite-size
tail comparison, and eventual hard-edge estimate kept as separate inputs.
The upper cutoff may depend on `R`, but is fixed during each `n` limit. -/
theorem sparse_mean_tendsto_of_compact_core_limits
    (mean : ℕ → ℝ) (coreRaw coreCut tailMass : ℕ → ℕ → ℝ)
    (rawLimit cutLimit tailLimit : ℕ → ℝ) (target C : ℝ)
    (hTail : ∀ R, 0 < tailLimit R)
    (hTailZero : Tendsto tailLimit atTop (𝓝 0))
    (hRawTarget : Tendsto rawLimit atTop (𝓝 target))
    (hRaw : ∀ R, Tendsto (coreRaw R) atTop (𝓝 (rawLimit R)))
    (hCut : ∀ R, Tendsto (coreCut R) atTop (𝓝 (cutLimit R)))
    (hMass : ∀ R, Tendsto (tailMass R) atTop (𝓝 (tailLimit R)))
    (hLower : ∀ R, ∀ᶠ n in atTop, coreRaw R n ≤ mean n)
    (hUpper : ∀ R, ∀ᶠ n in atTop, mean n ≤ coreCut R n +
      Real.sqrt (tailMass R n) / fourthRoot (tailLimit R))
    (hHardEdge : ∀ᶠ R in atTop,
      0 ≤ cutLimit R - rawLimit R ∧
      cutLimit R - rawLimit R ≤ C * fourthRoot (tailLimit R)) :
    Tendsto mean atTop (𝓝 target) := by
  have hRoot : Tendsto (fun R => fourthRoot (tailLimit R)) atTop (𝓝 0) := by
    simpa [fourthRoot] using hTailZero.sqrt.sqrt
  have hCutError : Tendsto (fun R => cutLimit R - rawLimit R) atTop (𝓝 0) := by
    exact squeeze_zero' (hHardEdge.mono fun _ h => h.1)
      (hHardEdge.mono fun _ h => h.2) (by simpa using hRoot.const_mul C)
  have hCutTarget : Tendsto cutLimit atTop (𝓝 target) := by
    simpa using hCutError.add hRawTarget
  apply tendsto_of_iterated_squeeze mean coreRaw
    (fun R n => coreCut R n + Real.sqrt (tailMass R n) / fourthRoot (tailLimit R))
    rawLimit (fun R => cutLimit R + fourthRoot (tailLimit R)) target
    hLower hUpper hRaw
  · intro R
    simpa [sqrt_div_fourthRoot (hTail R)] using
      (hCut R).add ((hMass R).sqrt.div_const (fourthRoot (tailLimit R)))
  · exact hRawTarget
  · simpa using hCutTarget.add hRoot

end CircularLawSection6
