/- Source snapshot: upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/ProjectionSmallBall.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.LivshytsProjectionFormalization.ProbabilityCore
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Data.Real.Basic

open scoped ENNReal
open MeasureTheory ProbabilityTheory Set

namespace LivshytsProjectionFormalization

/-- A measurable set with bounded density has a controlled probability on every measurable set. -/
theorem measurableSet_probability_of_bounded_pdf
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (nu : Measure E) (X : Omega -> E)
    [HasPDF X P nu] {rho : Real} (_hrho : 0 <= rho)
    (hdensity : ∀ᵐ x ∂nu, pdf X P nu x <= ENNReal.ofReal rho)
    (s : Set E) (hs : MeasurableSet s) :
    P (X ⁻¹' s) <= ENNReal.ofReal rho * nu s := by
  rw [← Measure.map_apply_of_aemeasurable
    (HasPDF.aemeasurable X P nu) hs]
  rw [map_eq_setLIntegral_pdf X P nu hs]
  calc
    (∫⁻ x in s, pdf X P nu x ∂nu) <=
        ∫⁻ _x in s, ENNReal.ofReal rho ∂nu :=
      lintegral_mono_ae (ae_restrict_of_ae hdensity)
    _ = ENNReal.ofReal rho * nu s := by simp

/-- Nonnegative Lebesgue product measure on `Real × Real`. -/
noncomputable abbrev realPlaneMeasure : Measure (Real × Real) :=
  (volume : Measure Real).prod (volume : Measure Real)

/-- Minimal bounded planar density interface used by the 2D complex small-ball step. -/
structure BoundedPlanePDFInterface
    (Omega : Type*) [MeasurableSpace Omega] (P : Measure Omega)
    (Y : Omega -> Real × Real) (rho : Real) where
  hasPDF : HasPDF Y P realPlaneMeasure
  rho_nonneg : 0 <= rho
  density_le :
    ∀ᵐ q ∂realPlaneMeasure,
      pdf Y P realPlaneMeasure q <= ENNReal.ofReal rho

/-- A bounded density data field used throughout both 1D/2D sections. -/
structure BoundedPDFInterface
    (Omega : Type*) [MeasurableSpace Omega] (P : Measure Omega)
    (X : Omega -> Real) (rho : Real) where
  hasPDF : HasPDF X P
  rho_nonneg : 0 <= rho
  density_le :
    ∀ᵐ x ∂(volume : Measure Real), pdf X P volume x <= ENNReal.ofReal rho

/-- The one-dimensional small-ball bound packaged in the interface. -/
theorem BoundedPDFInterface.real_small_ball
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : Omega -> Real} {rho center radius : Real}
    (data : BoundedPDFInterface Omega P X rho) (hradius : 0 <= radius) :
    P (X ⁻¹' Icc (center - radius) (center + radius)) <=
      ENNReal.ofReal (2 * rho * radius) := by
  letI : HasPDF X P := data.hasPDF
  exact real_small_ball_of_bounded_pdf P X hradius data.rho_nonneg data.density_le

/-- A measurable set in `Real × Real` associated to a real anisotropic shear/scale. -/
def scaledShearRectangle (alpha x y : Real) (w : Complex) (radius : Real) :
    Set (Real × Real) :=
  Icc (w.re / x - radius / x) (w.re / x + radius / x) ×ˢ
    Icc ((w.im - alpha * w.re) / y - 2 * radius / y)
      ((w.im - alpha * w.re) / y + 2 * radius / y)

/-- The shear map from coordinates `(q.1, q.2)` to `ℂ` used in scaled estimates. -/
def scaledShearToComplex (alpha x y : Real) (q : Real × Real) : Complex :=
  ⟨x * q.1, alpha * (x * q.1) + y * q.2⟩

@[simp] theorem scaledShearToComplex_re (alpha x y : Real) (q : Real × Real) :
    (scaledShearToComplex alpha x y q).re = x * q.1 := rfl

@[simp] theorem scaledShearToComplex_im (alpha x y : Real) (q : Real × Real) :
    (scaledShearToComplex alpha x y q).im = alpha * (x * q.1) + y * q.2 := rfl

/-- Sheared image small-ball events are measurable. -/
theorem measurableSet_scaledShearRectangle
    (alpha x y : Real) (w : Complex) (radius : Real) :
    MeasurableSet (scaledShearRectangle alpha x y w radius) :=
  measurableSet_Icc.prod measurableSet_Icc

/-- The preimage inclusion is the source of the Jacobian-lossless 2D bound. -/
theorem scaledShear_event_subset_rectangle
    {Omega : Type*} (Y : Omega -> Real × Real)
    (alpha x y : Real) (w : Complex) (radius : Real)
    (hx : 0 < x) (hy : 0 < y) (halpha : |alpha| <= 1) :
    {omega | ‖scaledShearToComplex alpha x y (Y omega) - w‖ <= radius} ⊆
      Y ⁻¹' scaledShearRectangle alpha x y w radius := by
  intro omega homega
  have hre0 :
      |(scaledShearToComplex alpha x y (Y omega) - w).re| <= radius :=
    (Complex.abs_re_le_norm _).trans homega
  have him0 :
      |(scaledShearToComplex alpha x y (Y omega) - w).im| <= radius :=
    (Complex.abs_im_le_norm _).trans homega
  have hre : |x * (Y omega).1 - w.re| <= radius := by
    simpa [scaledShearToComplex] using hre0
  have him : |alpha * (x * (Y omega).1) + y * (Y omega).2 - w.im| <= radius := by
    simpa [scaledShearToComplex] using him0
  have hrealIdentity :
      x * (Y omega).1 - w.re = x * ((Y omega).1 - w.re / x) := by
    field_simp [ne_of_gt hx]
  have hrealScaled : x * |(Y omega).1 - w.re / x| <= radius := by
    rw [hrealIdentity, abs_mul, abs_of_pos hx] at hre
    exact hre
  have hrealAbs : |(Y omega).1 - w.re / x| <= radius / x := by
    exact (le_div_iff₀ hx).2 (by simpa [mul_comm] using hrealScaled)
  have himResidual :
      |y * (Y omega).2 - (w.im - alpha * w.re)| <= 2 * radius := by
    calc
      |y * (Y omega).2 - (w.im - alpha * w.re)| =
          |(alpha * (x * (Y omega).1) + y * (Y omega).2 - w.im) -
            alpha * (x * (Y omega).1 - w.re)| := by
              congr 1
              ring
      _ <= |alpha * (x * (Y omega).1) + y * (Y omega).2 - w.im| +
            |alpha * (x * (Y omega).1 - w.re)| := by
        exact abs_sub _ _
      _ <= radius + radius := by
        apply add_le_add him
        rw [abs_mul]
        calc
          |alpha| * |x * (Y omega).1 - w.re| <=
              1 * |x * (Y omega).1 - w.re| := by
            exact mul_le_mul_of_nonneg_right halpha (abs_nonneg _)
          _ <= 1 * radius := by
            exact mul_le_mul_of_nonneg_left hre (zero_le_one)
          _ = radius := by ring
      _ = 2 * radius := by ring
  have himIdentity :
      y * (Y omega).2 - (w.im - alpha * w.re) =
        y * ((Y omega).2 - (w.im - alpha * w.re) / y) := by
    field_simp [ne_of_gt hy]
  have himScaled :
      y * |(Y omega).2 - (w.im - alpha * w.re) / y| <= 2 * radius := by
    rw [himIdentity, abs_mul, abs_of_pos hy] at himResidual
    exact himResidual
  have himAbs : |(Y omega).2 - (w.im - alpha * w.re) / y| <= 2 * radius / y := by
    exact (le_div_iff₀ hy).2 (by simpa [mul_comm] using himScaled)
  change (Y omega).1 ∈
      Icc (w.re / x - radius / x) (w.re / x + radius / x) ∧
    (Y omega).2 ∈
      Icc ((w.im - alpha * w.re) / y - 2 * radius / y)
        ((w.im - alpha * w.re) / y + 2 * radius / y)
  constructor
  · rcases abs_le.mp hrealAbs with ⟨hlower, hupper⟩
    constructor <;> linarith
  · rcases abs_le.mp himAbs with ⟨hlower, hupper⟩
    constructor <;> linarith

/-- Exact rectangle size under the shear map. -/
theorem realPlaneMeasure_scaledShearRectangle
    (alpha x y : Real) (w : Complex) (radius : Real)
    (hx : 0 < x) (hy : 0 < y) (hradius : 0 <= radius) :
    realPlaneMeasure (scaledShearRectangle alpha x y w radius) =
      ENNReal.ofReal (8 * radius ^ 2 / (x * y)) := by
  rw [realPlaneMeasure, scaledShearRectangle, Measure.prod_prod,
    Real.volume_Icc, Real.volume_Icc]
  have hfirst :
      0 <= (w.re / x + radius / x) - (w.re / x - radius / x) := by
    have hdiv : 0 <= radius / x := div_nonneg hradius hx.le
    linarith
  rw [<- ENNReal.ofReal_mul hfirst]
  congr 1
  field_simp [ne_of_gt hx, ne_of_gt hy]
  ring

/-- 2D complex-valued small-ball bound from planar density via a sheared linear map. -/
theorem BoundedPlanePDFInterface.scaled_sheared_complex_small_ball
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {Y : Omega -> Real × Real} {rho : Real}
    (data : BoundedPlanePDFInterface Omega P Y rho)
    (alpha x y : Real) (w : Complex) (radius : Real)
    (hx : 0 < x) (hy : 0 < y) (hradius : 0 <= radius)
    (halpha : |alpha| <= 1) :
    P {omega | ‖scaledShearToComplex alpha x y (Y omega) - w‖ <= radius} <=
      ENNReal.ofReal (8 * rho * radius ^ 2 / (x * y)) := by
  letI : HasPDF Y P realPlaneMeasure := data.hasPDF
  calc
    P {omega | ‖scaledShearToComplex alpha x y (Y omega) - w‖ <= radius} <=
        P (Y ⁻¹' scaledShearRectangle alpha x y w radius) :=
      measure_mono (scaledShear_event_subset_rectangle Y alpha x y w radius hx hy halpha)
    _ <= ENNReal.ofReal rho *
        realPlaneMeasure (scaledShearRectangle alpha x y w radius) :=
      measurableSet_probability_of_bounded_pdf P realPlaneMeasure Y
        data.rho_nonneg data.density_le _ (measurableSet_scaledShearRectangle alpha x y w radius)
    _ = ENNReal.ofReal (8 * rho * radius ^ 2 / (x * y)) := by
      rw [realPlaneMeasure_scaledShearRectangle alpha x y w radius hx hy hradius]
      rw [<- ENNReal.ofReal_mul data.rho_nonneg]
      congr 1
      ring

/-- Bounded density on `Real × Real` induces the analogous complex-event bound with a truncation. -/
theorem BoundedPlanePDFInterface.scaled_sheared_complex_small_ball_min
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P]
    {Y : Omega -> Real × Real} {rho : Real}
    (data : BoundedPlanePDFInterface Omega P Y rho)
    (alpha x y : Real) (w : Complex) (radius : Real)
    (hx : 0 < x) (hy : 0 < y) (hradius : 0 <= radius)
    (halpha : |alpha| <= 1) :
    P {omega | ‖scaledShearToComplex alpha x y (Y omega) - w‖ <= radius} <=
      ENNReal.ofReal (min 1 (8 * rho * radius ^ 2 / (x * y))) := by
  rw [ENNReal.ofReal_min]
  apply le_min
  · calc
      P {omega | ‖scaledShearToComplex alpha x y (Y omega) - w‖ <= radius} ≤
          P Set.univ := measure_mono (Set.subset_univ _)
      _ = ENNReal.ofReal 1 := by simp
  · exact data.scaled_sheared_complex_small_ball alpha x y w radius hx hy hradius halpha

/-- The exact external content of Theorem 1.1 for dimensions one and two. -/
structure OneTwoProjectionDensityInterface
    (Omega : Type*) [MeasurableSpace Omega] (m : Nat) (P : Measure Omega)
    (xi : Omega -> EuclideanSpace Real (Fin m)) (rho C1 C2 : Real) where
  one : ∀ p : EuclideanSpace Real (Fin m), ‖p‖ = 1 ->
    BoundedPDFInterface Omega P (fun omega => inner Real (xi omega) p) (C1 * rho)
  two : ∀ p r : EuclideanSpace Real (Fin m), ‖p‖ = 1 -> ‖r‖ = 1 ->
    inner Real p r = 0 ->
    BoundedPlanePDFInterface Omega P
      (fun omega => (inner Real (xi omega) p, inner Real (xi omega) r))
      (C2 * rho ^ 2)

/-- From the external one- and two-dimensional interface, derive the generic complex block estimate. -/
theorem OneTwoProjectionDensityInterface.generic_block_small_ball
    {Omega : Type*} [MeasurableSpace Omega] {m : Nat} {P : Measure Omega}
    [IsProbabilityMeasure P]
    {xi : Omega -> EuclideanSpace Real (Fin m)} {rho C1 C2 : Real}
    (data : OneTwoProjectionDensityInterface Omega m P xi rho C1 C2)
    (p r : EuclideanSpace Real (Fin m))
    (hp : ‖p‖ = 1) (hr : ‖r‖ = 1) (hpr : inner Real p r = 0)
    (alpha x y : Real) (w : Complex) (radius : Real)
    (hx : 0 < x) (hy : 0 < y) (hradius : 0 <= radius)
    (halpha : |alpha| <= 1) :
    P {omega |
        ‖scaledShearToComplex alpha x y
          (inner Real (xi omega) p, inner Real (xi omega) r) - w‖ <= radius} <=
      ENNReal.ofReal
        (min 1 (8 * (C2 * rho ^ 2) * radius ^ 2 / (x * y))) := by
  exact (data.two p r hp hr hpr).scaled_sheared_complex_small_ball_min
    alpha x y w radius hx hy hradius halpha

/-- Conditional 1D bounded density that is preserved almost everywhere in an outer index. -/
structure ConditionalBoundedPDFInterface
    (Alpha Omega : Type*) [MeasurableSpace Alpha] [MeasurableSpace Omega]
    (mu : Measure Alpha) (kernel : Kernel Alpha Omega)
    (X : Alpha -> Omega -> Real) (rho : Alpha -> Real) where
  rho_nonneg : forall a, 0 <= rho a
  hasPDF_ae : ∀ᵐ a ∂mu, HasPDF (X a) (kernel a)
  density_le_ae : ∀ᵐ a ∂mu,
    ∀ᵐ x ∂(volume : Measure Real), pdf (X a) (kernel a) volume x <= ENNReal.ofReal (rho a)

/-- Conditional one-dimensional small-ball estimate is available almost everywhere. -/
theorem ConditionalBoundedPDFInterface.real_small_ball_ae
    {Alpha Omega : Type*} [MeasurableSpace Alpha] [MeasurableSpace Omega]
    {mu : Measure Alpha} {kernel : Kernel Alpha Omega}
    {X : Alpha -> Omega -> Real} {rho : Alpha -> Real}
    (data : ConditionalBoundedPDFInterface Alpha Omega mu kernel X rho)
    (center radius : Alpha -> Real) (hradius : forall a, 0 <= radius a) :
    ∀ᵐ a ∂mu,
      kernel a ((X a) ⁻¹' Icc (center a - radius a) (center a + radius a)) <=
        ENNReal.ofReal (2 * rho a * radius a) := by
  filter_upwards [data.hasPDF_ae, data.density_le_ae] with a hpdf hdensity
  letI : HasPDF (X a) (kernel a) := hpdf
  exact real_small_ball_of_bounded_pdf (kernel a) (X a)
    (hradius a) (data.rho_nonneg a) hdensity

/-- `complexSmallBall` notation used by the 2D block argument. -/
def complexSmallBall {Ω : Type*} {m : ℕ}
    (ξ : Ω → EuclideanSpace ℂ (Fin m))
    (u : EuclideanSpace ℂ (Fin m)) (w : Complex) (t : ℝ) : Set Ω :=
  {ω | ‖inner ℂ (ξ ω) u - w‖ ≤ t}

/-- The bounded density one-dimensional projection bound in complex metric form. -/
theorem complex_disk_small_ball_of_bounded_pdf
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω -> Complex) (w : Complex) {radius rho : Real}
    (hradius : 0 <= radius) (hrho : 0 <= rho)
    [HasPDF (fun omega => (Z omega).re) P]
    (hdensity : ∀ᵐ x ∂(volume : Measure Real),
      pdf (fun omega => (Z omega).re) P volume x <= ENNReal.ofReal rho) :
    P {ω | ‖Z ω - w‖ <= radius} <=
      ENNReal.ofReal (2 * rho * radius) := by
  have hsubset :
      {ω | ‖Z ω - w‖ <= radius} ⊆
        (fun ω => (Z ω).re) ⁻¹' Icc (w.re - radius) (w.re + radius) := by
    intro ω hω
    have hle : |(Z ω - w).re| <= ‖Z ω - w‖ := by
      simpa [Complex.sub_re] using (Complex.abs_re_le_norm (Z ω - w))
    have habs : |(Z ω).re - w.re| <= radius := by
      exact le_trans hle hω
    rcases abs_le.mp habs with ⟨hlow, hhigh⟩
    constructor
    · linarith
    · linarith
  calc
    P {ω | ‖Z ω - w‖ <= radius} <=
        P ((fun ω => (Z ω).re) ⁻¹' Icc (w.re - radius) (w.re + radius)) :=
      measure_mono hsubset
    _ <= ENNReal.ofReal (2 * rho * radius) :=
      real_small_ball_of_bounded_pdf P (fun ω => (Z ω).re)
        hradius hrho hdensity

/-- Bounded density on a one-dimensional real projection gives a bounded complex disk bound. -/
theorem complexSmallBall_of_bounded_real_projection
    {Ω : Type*} [MeasurableSpace Ω] {m : Nat}
    (P : Measure Ω) (xi : Ω -> EuclideanSpace Complex (Fin m))
    (u : EuclideanSpace Complex (Fin m)) (w : Complex) {radius rho : Real}
    (hradius : 0 <= radius) (hrho : 0 <= rho)
    [HasPDF (fun ω => (inner Complex (xi ω) u).re) P]
    (hdensity : ∀ᵐ x ∂(volume : Measure Real),
      pdf (fun ω => (inner Complex (xi ω) u).re) P volume x <=
        ENNReal.ofReal rho) :
    P (complexSmallBall xi u w radius) <=
      ENNReal.ofReal (2 * rho * radius) := by
  simpa only [complexSmallBall] using
    (complex_disk_small_ball_of_bounded_pdf P (fun ω => inner Complex (xi ω) u) w
      hradius hrho hdensity)

end LivshytsProjectionFormalization

