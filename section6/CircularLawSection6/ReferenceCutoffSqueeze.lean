import CircularLawSection6.IteratedSqueeze

/-! # The reference-cutoff squeeze without an assumed cutoff limit

Only fixed-cutoff comparison to the finite reference model is required.
The reference's iterated lower-cutoff error replaces the stronger claim
that its limiting singular law has a linear hard-edge density bound.
-/

open Filter Topology

namespace CircularLawSection6

theorem mean_tendsto_of_reference_cutoff_squeeze
    (mean referenceRaw : ℕ → ℝ) (coreRaw coreCut referenceCut error : ℕ → ℕ → ℝ)
    (rawLimit errorLimit : ℕ → ℝ) (target : ℝ)
    (hLower : ∀ R, ∀ᶠ n in atTop, coreRaw R n ≤ mean n)
    (hUpper : ∀ R, ∀ᶠ n in atTop, mean n ≤ coreCut R n + error R n)
    (hRaw : ∀ R, Tendsto (coreRaw R) atTop (𝓝 (rawLimit R)))
    (hRawTarget : Tendsto rawLimit atTop (𝓝 target))
    (hReference : Tendsto referenceRaw atTop (𝓝 target))
    (hComparison : ∀ R, Tendsto (fun n => coreCut R n - referenceCut R n) atTop (𝓝 0))
    (hError : ∀ R, Tendsto (error R) atTop (𝓝 (errorLimit R)))
    (hErrorZero : Tendsto errorLimit atTop (𝓝 0))
    (hReferenceCutoff : ∀ ε : ℝ, 0 < ε → ∀ᶠ R in atTop, ∀ᶠ n in atTop,
      referenceCut R n ≤ referenceRaw n + ε) :
    Tendsto mean atTop (𝓝 target) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    obtain ⟨R, hR⟩ := (hRawTarget.eventually (lt_mem_nhds hb)).exists
    filter_upwards [(hRaw R).eventually (lt_mem_nhds hR), hLower R] with n hn hbound
    exact hn.trans_le hbound
  · intro b hb
    let ε : ℝ := (b - target) / 4
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hRsmall : ∀ᶠ R in atTop, errorLimit R < ε :=
      hErrorZero.eventually (gt_mem_nhds hε)
    obtain ⟨R, hRerror, hRcut⟩ := (hRsmall.and (hReferenceCutoff ε hε)).exists
    have hRawSmall := hReference.eventually (gt_mem_nhds (show target < target + ε by linarith))
    have hCmpSmall := (hComparison R).eventually (gt_mem_nhds hε)
    have hErrSmall := (hError R).eventually (gt_mem_nhds hRerror)
    filter_upwards [hUpper R, hRcut, hRawSmall, hCmpSmall, hErrSmall] with n hu hc hr hcmp herr
    dsimp [ε] at hc hr hcmp herr
    linarith

end CircularLawSection6
