import CircularLawSection6.GinibreDysonImaginary
import CircularLawSection6.UnequalGinibreCutoff
import Lean.Util.CollectAxioms

/-! Narrow transitive audit for the independent BBV-to-Ginibre bridges.
This batch does not yet assert a raw logarithmic-potential limit. -/
set_option autoImplicit false
set_option maxHeartbeats 0
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let prefixes : Array Name := #[
    `CircularLawSection6.GinibreBBV,
    `CircularLawSection6.GinibreDyson,
    `CircularLawSection6.unequal_matrix_grid_cdf_bound,
    `CircularLawSection6.compact_grid_compl_tendsto_zero,
    `CircularLawSection6.unequal_matrix_cdf_of_common_stieltjes,
    `CircularLawSection6.unequal_ginibre_cdf_of_bbv,
    `CircularLawSection6.cyclicSamples_unequal_cdf,
    `CircularLawSection6.unequal_ginibre_cutoff_of_bbv_ae,
    `Arxiv2410V3.normSq_mul_add_nonneg_le,
    `Arxiv2410V3.scalarDyson_strict_contraction,
    `Arxiv2410V3.scalarDysonEquation_unique,
    `Arxiv2410V3.eq_freeDysonStieltjes_of_scalarDysonEquation]
  let mut checked : Nat := 0
  for (name, _) in env.constants do
    if prefixes.any (fun p => p.isPrefixOf name) then
      checked := checked + 1
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do
          throwError "BBV/Ginibre audit failed: {name} depends on {axiomName}"
  if checked == 0 then
    throwError "BBV/Ginibre audit is empty"
  logInfo m!"BBV/Ginibre source axiom audit PASSED: {checked} declarations."

#check CircularLawSection6.GinibreBBV.ginibre_stieltjes_error_tri_of_bbv
#check CircularLawSection6.GinibreDyson.freeDysonStieltjes_re_eq_zero
#check CircularLawSection6.GinibreDyson.deriv_profileF_eq_profileV_mul_deriv_profileT
#check CircularLawSection6.unequal_ginibre_cdf_of_bbv
#check CircularLawSection6.unequal_ginibre_cutoff_of_bbv_ae
