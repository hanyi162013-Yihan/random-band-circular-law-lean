/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealLSVAssembly.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RealMatrixColumnBound
import Vendor.LSVAssembly

/-! Distance-to-span assembly for the actual real-entry product model. -/

noncomputable section
open MeasureTheory LivshytsProjectionFormalization
open scoped ENNReal
namespace HighBandLSV

/-- The only probabilistic premise here is the bad-normal probability; the
column small-ball and distance-to-span steps are derived from the model.
The later model theorem supplies this premise by the proved anisotropic net. -/
theorem real_lsv_from_bad_normals
    {n W : Nat} {c C rho R d s Bbad : Real}
    (m : RealBandModel (n + 1) W c C rho)
    (hGBL : RealFiniteGeometricBrascampLieb) (hrho : 0 < rho)
    (hc : 0 < c) (hW : 0 < W) (z : Complex)
    (B : Fin (n + 1) → Finset (Fin (n + 1)))
    (hB : ∀ j i, i ∈ B j → Section5Formalization.cyclicDist (n + 1) i j ≤ W)
    (hd : 0 < d) (hs : 0 ≤ s)
    (hbad : m.law (hsEvent m.matrix R \ m.goodNormalEvent z B d) ≤ ENNReal.ofReal Bbad) :
    m.law (leastSingularBadEvent (fun omega => shifted (m.matrix omega) z) s ∩ hsEvent m.matrix R) ≤
      ENNReal.ofReal ((n + 1 : Nat) *
        ((2 * Real.sqrt 2 * Real.exp 1 * rho / Real.sqrt c) *
          Real.sqrt W * (s * Real.sqrt (n + 1 : Nat)) / d)) + ENNReal.ofReal Bbad := by
  have hcol : ∀ j : Fin (n + 1),
      m.law (closedColumnEvent (fun omega => shifted (m.matrix omega) z)
        (s * Real.sqrt (n + 1 : Nat)) j ∩ m.goodNormalEvent z B d) ≤
      ENNReal.ofReal ((2 * Real.sqrt 2 * Real.exp 1 * rho / Real.sqrt c) *
        Real.sqrt W * (s * Real.sqrt (n + 1 : Nat)) / d) := by
    intro j
    exact m.column_distance_small_ball hGBL hrho hc hW z B hB hd
      (mul_nonneg hs (Real.sqrt_nonneg _)) j
  exact lsv_probability_from_cover (by omega) m.law m.matrix z R s _ _
    (m.goodNormalEvent z B d) (hsEvent m.matrix R) Set.Subset.rfl hbad hcol

end HighBandLSV

#print axioms HighBandLSV.real_lsv_from_bad_normals

