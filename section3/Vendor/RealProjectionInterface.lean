/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealProjectionInterface.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.LivshytsProjectionFormalization.ProjectionSmallBall

open scoped ENNReal
open MeasureTheory ProbabilityTheory Set

namespace HighBandLSV.Real

/-- A coordinate density hypothesis, not a projection probability hypothesis. -/
structure BoundedPDFInterface (Omega : Type*) [MeasurableSpace Omega]
    (P : Measure Omega) (X : Omega → Real) (rho : Real) where
  hasPDF : HasPDF X P (volume : Measure Real)
  rho_nonneg : 0 ≤ rho
  density_le : ∀ᵐ x ∂(volume : Measure Real), pdf X P volume x ≤ ENNReal.ofReal rho

theorem BoundedPDFInterface.real_small_ball
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : Omega → Real} {rho center radius : Real}
    (data : BoundedPDFInterface Omega P X rho) (hr : 0 ≤ radius) :
    P (X ⁻¹' Icc (center - radius) (center + radius)) ≤
      ENNReal.ofReal (2 * rho * radius) := by
  letI : HasPDF X P (volume : Measure Real) := data.hasPDF
  exact LivshytsProjectionFormalization.real_small_ball_of_bounded_pdf P X
    hr data.rho_nonneg data.density_le

end HighBandLSV.Real

