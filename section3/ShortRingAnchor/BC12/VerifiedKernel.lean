import ShortRingAnchor.BC12.KnownFormulas
import Ginibre.Projection

/-!
# The Section 3 kernel interface is a theorem

The pinned `GinibreCorrelationIdentities` dependency proves weighted
projection from the explicit Gaussian orthonormal basis. The definitions
below agree exactly, including planar volume and variance normalization.
No BC12 theorem is a hypothesis of this adapter.
-/

noncomputable section
open MeasureTheory
namespace ShortRingAnchor.BC12

/-- BC12 normalized one-point density: equality of the two explicit formulas. -/
theorem ginibreOnePointDensity_eq_verified (n : ℕ) :
    ginibreOnePointDensity n = Ginibre.onePointDensity n := rfl

/-- BC12 finite-rank kernel: the same Gaussian weight and variance convention. -/
theorem ginibreKernel_eq_verified (n : ℕ) : ginibreKernel n = Ginibre.kernel n := rfl

/-- BC12 covariance weight: definitional agreement with the proved projection. -/
theorem ginibreKernelWeight_eq_verified (n : ℕ) :
    ginibreKernelWeight n = Ginibre.kernelWeight n := rfl

/-- BC12 projection input, now discharged from explicit Gaussian integration. -/
theorem verifiedGinibreProjection (n : ℕ) : GinibreProjectionIntegralFormula n := by
  constructor
  intro g hg hg0 hi
  exact Ginibre.weighted_projection n hg hg0 hi

end ShortRingAnchor.BC12
