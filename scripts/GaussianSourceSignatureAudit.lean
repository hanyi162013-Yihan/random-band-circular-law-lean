import ShortRingAnchor.BC12.GaussianMatrixLawBridge
import ShortRingAnchor.BC12.GinibreNegativeMoments

-- Print the actual model definitions, so a spectral-density conclusion
-- cannot be disguised as the definition of the matrix ensemble.
#print Ginibre.gaussianMatrixLaw
#print Ginibre.gaussianLabelledSpectralLaw
#print ShortRingAnchor.BC12.normalizedGinibreLaw

-- The upstream density and covariance theorems have only the displayed
-- scalar positivity and test-function domain conditions, not Schur inputs.
#print axioms Ginibre.gaussianLabelledSpectralLaw_eq_withDensity
#print axioms Ginibre.gaussian_matrix_density_and_correlations
#print axioms Ginibre.gaussianEigenvalueVariance_all_energy
#check @Ginibre.gaussianLabelledSpectralLaw_eq_withDensity
#check @Ginibre.gaussian_matrix_density_and_correlations
#check @Ginibre.gaussianMatrix_integral_linearStatistic_all
#check @Ginibre.gaussianEigenvalueVariance_all_energy
#check @ShortRingAnchor.BC12.verifiedGinibreProjection
#check @ShortRingAnchor.BC12.verifiedGinibreCorrelations
#check @ShortRingAnchor.BC12.normalizedGinibre_correlations
#check @ShortRingAnchor.BC12.ginibre_logdet_convergesInProbability_of_ginibreLaw
#check @ShortRingAnchor.BC12.negativeMomentTightness_of_ginibreLaw_and_v3
