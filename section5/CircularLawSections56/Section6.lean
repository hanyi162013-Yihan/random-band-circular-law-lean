import CircularLawSections56.Section6.CompactCoreAssembly
import CircularLawSections56.Section6.CyclicBand
import CircularLawSections56.Section6.DeterministicCentering
import CircularLawSections56.Section6.GaussianConcentration
import CircularLawSections56.Section6.GaussianProfileClosure
import CircularLawSections56.Section6.LiteralCompactCoreBridge
import CircularLawSections56.Section6.PhysicalReplacementBridge
import CircularLawSections56.Section6.TriangularReplacement
import CircularLawSections56.Section6.LiteralIndicatorModel
import CircularLawSections56.Section6.CompletedSection4Endpoint
import CircularLawSections56.Section6.LiteralModelIdentification
import CircularLawSections56.Section6.Potentials
import CircularLawSections56.Section6.ProfileMasses
import CircularLawSections56.Section6.RadialAndCutoff
import CircularLawSections56.Section6.Section5LongBranchBridge
import CircularLawSections56.Section6.SparseMean

/-!
# Section 6: Gaussian compact cores and non-compact profiles

This umbrella module collects the formalized deterministic, analytic, and asymptotic
proof chain of Section 6 of the combined circular-law manuscript.  The long raw
compact-core branch now consumes Section 5's quantitative `L¹` certificate, deriving
integrability and expectation convergence from observable measurability.  A constant
shift supports fixed-scale applications; the separate cutoff comparison inputs remain
explicit.
-/
