import CircularLawSection6.GinibreDysonDerivative
import CircularLawSection6.BBVProfileEndpoint
import CircularLawSection6.GinibreLogMomentBounds
import CircularLawSection6.RegularizedMeanRemoval
import CircularLawSection6.GinibrePointwiseNonzero
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
    `CircularLawSection6.cyclicBlock_moving_ginibre_of_cdf_ae,
    `CircularLawSection6.periodicBlock_moving_cutoff_of_all_lengths,
    `CircularLawSection6.one_or_fullBlock_moving_cutoff_of_all_lengths,
    `CircularLawSection6.NoncompactProfile.unitCore_cutoff_comparison_of_local_cdf_ae,
    `CircularLawSection6.NoncompactProfile.canonical_core_cutoff_comparison_of_local_cdf,
    `CircularLawSection6.tendstoInProbabilityTri_of_tight_approximations,
    `CircularLawSection6.regularized_log_ge_log,
    `CircularLawSection6.regularized_log_le_cutoff,
    `CircularLawSection6.eventually_abs_center_le_of_tight_and_close,
    `CircularLawSection6.exists_uniform_secondMoment_of_tight_and_centered,
    `CircularLawSection6.CoreRadiusBounds.localCdf_of_bbv,
    `CircularLawSection6.CoreRadiusBounds.canonical_core_cutoff_comparison_of_bbv,
    `CircularLawSection6.NoncompactProfile.GaussianProfileBBVCoreSources,
    `CircularLawSection6.NoncompactProfile.sparse_profile_probability_of_bbv_section5,
    `CircularLawSection6.BoundedInProbabilityTri,
    `CircularLawSection6.boundedInProbabilityTri_of_integral_abs_bound,
    `CircularLawSection6.regularizedSquaredLog,
    `CircularLawSection6.matrixRegularizedPotential,
    `CircularLawSection6.hasDerivAt_regularizedSquaredLog,
    `CircularLawSection6.hasDerivAt_matrixRegularizedPotential,
    `CircularLawSection6.hasDerivAt_shifted_matrixRegularizedPotential,
    `CircularLawSection6.hasDerivAt_shifted_matrixRegularizedPotential_I_mul,
    `CircularLawSection6.continuous_matrixRegularizedPotential,
    `CircularLawSection6.measurable_matrixRegularizedPotential,
    `CircularLawSection6.integrable_matrixRegularizedPotential,
    `CircularLawSection6.sum_sq_singularValues_eq_hilbertSchmidtSq,
    `CircularLawSection6.matrixRegularizedPotential_highHeight,
    `CircularLawSection6.abs_matrixRegularizedPotential_sub_log_le,
    `CircularLawSection6.matrixRegularizedPotential_eq_sum_card,
    `CircularLawSection6.matrixRawPotential_le_regularized,
    `CircularLawSection6.matrixRegularizedPotential_le_cutoff,
    `CircularLawSection6.matrixRegularized_raw_error_le_negativeMoment,
    `CircularLawSection6.matrixRaw_probability_of_regularized_limits,
    `CircularLawSection6.abs_matrixRawPotential_le_energy_negativeMoment,
    `CircularLawSection6.matrixRawPotential_boundedInProbabilityTri_of_energy_negativeMoment,
    `CircularLawSection6.ginibre_shifted_det_ne_zero_ae,
    `CircularLawSection6.ginibre_raw_centered_tendsto,
    `CircularLawSection6.ginibre_raw_tight_of_bbv_ae,
    `CircularLawSection6.ginibre_raw_uniform_secondMoment_of_bbv_ae,
    `CircularLawSection6.ginibreLowerCutoff_L1_of_bbv_ae,
    `CircularLawSection6.ginibre_iterated_lowerCutoff_L1_of_bbv_ae,
    `CircularLawSection6.tendsto_of_iterated_approximations,
    `CircularLawSection6.expected_regularized_raw_error_le_cutoff,
    `CircularLawSection6.matrixRaw_mean_of_regularized_mean_limits,
    `CircularLawSection6.leastSingularValue_lt_of_shifted_det_eq_zero,
    `CircularLawSection6.ginibreOnSequence_shifted_det_ne_zero,
    `CircularLawSection6.ginibre_shifted_det_ne_zero,
    `CircularLawSection6.NoncompactProfile.profile_probability_along_sparse_subsequence_of_bbv_sources,
    `CircularLawSection6.NoncompactProfile.profile_spectral_limit_along_sparse_subsequence_of_bbv_sources,
    `CircularLawSection6.NoncompactProfile.gaussian_profile_circular_law_of_bbv_core_sources,
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
#check CircularLawSection6.NoncompactProfile.canonical_core_cutoff_comparison_of_local_cdf
#check CircularLawSection6.tendstoInProbabilityTri_of_tight_approximations
#check CircularLawSection6.GinibreDyson.tendsto_dysonPotential_nhdsGT_zero
#check CircularLawSection6.GinibreDyson.tendsto_dysonPotential_sub_log_atTop
#check CircularLawSection6.CoreRadiusBounds.canonical_core_cutoff_comparison_of_bbv
#check CircularLawSection6.NoncompactProfile.GaussianProfileBBVCoreSources
#check CircularLawSection6.matrixRaw_probability_of_regularized_limits
#check CircularLawSection6.GinibreDyson.hasDerivAt_dysonPotential
#check CircularLawSection6.ginibre_raw_uniform_secondMoment_of_bbv_ae
#check CircularLawSection6.ginibre_iterated_lowerCutoff_L1_of_bbv_ae
#check CircularLawSection6.NoncompactProfile.gaussian_profile_circular_law_of_bbv_core_sources
#check CircularLawSection6.ginibre_shifted_det_ne_zero
