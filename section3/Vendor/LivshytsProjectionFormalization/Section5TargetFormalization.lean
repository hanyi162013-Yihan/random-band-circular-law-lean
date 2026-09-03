/- Source snapshot: upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/Section5TargetFormalization.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.LivshytsProjectionFormalization.ProjectionSmallBall

open scoped ENNReal
open MeasureTheory ProbabilityTheory Set

namespace LivshytsProjectionFormalization

/-- Interface corresponding to Livshyts 2016 Theorem 1.1 for dimensions 1 and 2. -/
structure LivshytsSection5ProjectionInput
    (Omega : Type*) [MeasurableSpace Omega] (n : Nat) (P : Measure Omega)
    (x : Omega → EuclideanSpace Real (Fin n)) (K : Real) where
  h_one :
    ∀ p : EuclideanSpace Real (Fin n), ‖p‖ = 1 →
      BoundedPDFInterface Omega P (fun ω => inner Real (x ω) p) (Real.sqrt 2 * K)
  h_two :
    ∀ p r : EuclideanSpace Real (Fin n), ‖p‖ = 1 → ‖r‖ = 1 →
      inner Real p r = 0 →
      BoundedPlanePDFInterface Omega P
        (fun ω => (inner Real (x ω) p, inner Real (x ω) r))
        (2 * K ^ 2)

/-- Real 1D projection coordinate map. -/
noncomputable def projection1D
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (x : Omega → EuclideanSpace Real (Fin n)) (p : EuclideanSpace Real (Fin n)) :
    Omega → Real :=
  fun ω => inner Real (x ω) p

/-- Complex 2D projection coordinate map used in this model. -/
noncomputable def projection2DComplex
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (x : Omega → EuclideanSpace Real (Fin n))
    (p r : EuclideanSpace Real (Fin n)) : Omega → Complex :=
  fun ω => (inner Real (x ω) p : Complex) + Complex.I * (inner Real (x ω) r : Complex)

/-- Extracts the one-dimensional projected marginals and keeps the interface-supplied density bound. -/
theorem oneDim_projection_density_from_livshyts
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat} {P : Measure Omega}
    {x : Omega → EuclideanSpace Real (Fin n)} {K : Real}
    (h : LivshytsSection5ProjectionInput Omega n P x K)
    (p : EuclideanSpace Real (Fin n)) (hp : ‖p‖ = 1) :
    HasPDF (projection1D (x := x) p) P :=
  (h.h_one p hp).hasPDF

/-- The 1D essential upper density bound for a unit direction projection. -/
theorem oneDim_projection_esssup_bound
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat} {P : Measure Omega}
    {x : Omega → EuclideanSpace Real (Fin n)} {K : Real}
    (h : LivshytsSection5ProjectionInput Omega n P x K)
    (p : EuclideanSpace Real (Fin n)) (hp : ‖p‖ = 1) :
    ∀ᵐ t ∂(volume : Measure Real),
      pdf (projection1D (x := x) p) P volume t ≤
        ENNReal.ofReal (Real.sqrt 2 * K) :=
  (h.h_one p hp).density_le

/-- 1D density bound implies a small-ball probability bound (interval length 2ε). -/
theorem oneDim_projection_small_ball
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat} {P : Measure Omega}
    {x : Omega → EuclideanSpace Real (Fin n)} {K : Real}
    (h : LivshytsSection5ProjectionInput Omega n P x K)
    (p : EuclideanSpace Real (Fin n)) (hp : ‖p‖ = 1)
    (z : Real) (eps : Real) (heps : 0 ≤ eps) :
    P ((projection1D (x := x) p) ⁻¹' Icc (z - eps) (z + eps)) ≤
      ENNReal.ofReal (2 * (Real.sqrt 2 * K) * eps) := by
  let data := h.h_one p hp
  letI : HasPDF (projection1D (x := x) p) P := data.hasPDF
  exact real_small_ball_of_bounded_pdf P (projection1D (x := x) p)
    heps data.rho_nonneg data.density_le

/-- Rescaled 1D projection: density is diluted by `|a|`. -/
theorem oneDim_projection_scaled_small_ball
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat} {P : Measure Omega}
    {x : Omega → EuclideanSpace Real (Fin n)} {K : Real}
    (h : LivshytsSection5ProjectionInput Omega n P x K)
    (p : EuclideanSpace Real (Fin n)) (hp : ‖p‖ = 1)
    (a : Real) (ha : a ≠ 0)
    (z : Real) (eps : Real) (heps : 0 ≤ eps) :
    P ((fun ω => a * projection1D (x := x) p ω) ⁻¹' Icc (z - eps) (z + eps)) ≤
      ENNReal.ofReal (2 * (Real.sqrt 2 * K) * (eps / |a|)) := by
  let data := h.h_one p hp
  letI : HasPDF (projection1D (x := x) p) P := data.hasPDF
  exact real_scaled_small_ball_of_bounded_pdf P (projection1D (x := x) p)
    ha data.rho_nonneg heps data.density_le

/-- 2D projection through orthogonal pair `(p,r)` is controlled by the `scaledShear` complex estimate. -/
theorem twoDim_projection_complex_small_ball
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat} {P : Measure Omega}
    {x : Omega → EuclideanSpace Real (Fin n)} {K : Real}
    (h : LivshytsSection5ProjectionInput Omega n P x K)
    (p r : EuclideanSpace Real (Fin n))
    (hp : ‖p‖ = 1) (hr : ‖r‖ = 1) (hpr : inner Real p r = 0)
    (w : Complex) (eps : Real) (heps : 0 ≤ eps) :
    P {ω | ‖projection2DComplex (x := x) p r ω - w‖ ≤ eps} ≤
      ENNReal.ofReal (8 * (2 * K ^ 2) * eps ^ 2) := by
  have data := h.h_two p r hp hr hpr
  have hpre :
      {ω | ‖projection2DComplex (x := x) p r ω - w‖ ≤ eps} =
      {ω | ‖scaledShearToComplex 0 1 1 (inner Real (x ω) p, inner Real (x ω) r) - w‖ ≤ eps} := by
    ext ω
    have hpair :
        projection2DComplex (x := x) p r ω = (⟨inner Real (x ω) p, inner Real (x ω) r⟩ : Complex) := by
      rw [projection2DComplex, Complex.ext_iff]
      simp
    have hshear :
        (⟨inner Real (x ω) p, inner Real (x ω) r⟩ : Complex) =
          scaledShearToComplex 0 1 1 (inner Real (x ω) p, inner Real (x ω) r) := by
      simp [scaledShearToComplex]
    simp [hpair, hshear]
  rw [hpre]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (data.scaled_sheared_complex_small_ball 0 1 1 w eps
      (show (0 : Real) < 1 by norm_num) (show (0 : Real) < 1 by norm_num)
      heps (by norm_num))

/-- Conditional 1D bounded-density interface lifts to an a.e. small-ball bound. -/
theorem conditional_projection_small_ball_from_interface
    {Alpha Omega : Type*} [MeasurableSpace Alpha] [MeasurableSpace Omega]
    {mu : Measure Alpha} {kernel : Kernel Alpha Omega}
    {X : Alpha -> Omega -> Real} {rho : Alpha -> Real}
    (hcond : ConditionalBoundedPDFInterface Alpha Omega mu kernel X rho)
    (center radius : Alpha -> Real) (hradius : ∀ a, 0 ≤ radius a) :
    ∀ᵐ a ∂mu, kernel a ((X a) ⁻¹' Icc (center a - radius a) (center a + radius a)) ≤
      ENNReal.ofReal (2 * rho a * radius a) :=
  hcond.real_small_ball_ae center radius hradius

/-- A compact target statement for `π_E`-style projection claims in dimension 1/2.
For 1D this is projection onto a unit vector; for 2D the identified complex coordinates
`ω ↦ (x⋅p) + i*(x⋅r)` are used to represent the plane.
-/
theorem section5_target_projection_bound
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat} {P : Measure Omega}
    [IsProbabilityMeasure P]
    {x : Omega → EuclideanSpace Real (Fin n)} {K : Real}
    (h : LivshytsSection5ProjectionInput Omega n P x K)
    (p : EuclideanSpace Real (Fin n)) (hp : ‖p‖ = 1)
    (eps : Real) (heps : 0 ≤ eps) :
    P ((projection1D (x := x) p) ⁻¹' Icc (-eps) eps) ≤
      ENNReal.ofReal (2 * (Real.sqrt 2 * K) * eps) := by
  simpa using
    (oneDim_projection_small_ball (Omega := Omega) (n := n) (P := P) (x := x) (K := K)
      h p hp 0 eps heps)

end LivshytsProjectionFormalization

