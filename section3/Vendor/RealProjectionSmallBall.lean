/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealProjectionSmallBall.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RealProjectionInterface
import Mathlib.MeasureTheory.Measure.Prod

open scoped ENNReal
open MeasureTheory ProbabilityTheory Set

namespace HighBandLSV.Real

/-! # Projection-density consequences used by the block-net argument

The cited projection-density theorem is kept as a sharply stated input.  All
measure integration, anisotropic scaling, the real shear, and the complex
small-ball estimate are proved in this file.
-/

/-- A bounded density controls the probability of every measurable target set. -/
theorem measurableSet_probability_of_bounded_pdf
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (nu : Measure E) (X : Omega -> E)
    [HasPDF X P nu] {rho : Real} (hrho : 0 <= rho)
    (hdensity : ∀ᵐ x ∂nu,
      pdf X P nu x <= ENNReal.ofReal rho)
    (s : Set E) (hs : MeasurableSet s) :
    P (X ⁻¹' s) <= ENNReal.ofReal rho * nu s := by
  rw [<- Measure.map_apply_of_aemeasurable
    (HasPDF.aemeasurable X P nu) hs]
  rw [map_eq_setLIntegral_pdf X P nu hs]
  calc
    (∫⁻ x in s, pdf X P nu x ∂nu) <=
        ∫⁻ _x in s, ENNReal.ofReal rho ∂nu :=
      lintegral_mono_ae (ae_restrict_of_ae hdensity)
    _ = ENNReal.ofReal rho * nu s := by simp

/-- Lebesgue measure on the real coordinate plane. -/
noncomputable abbrev realPlaneMeasure : Measure (Real × Real) :=
  (volume : Measure Real).prod (volume : Measure Real)

/-- Minimal bounded-density data for a pair of real random variables. -/
structure BoundedPlanePDFInterface
    (Omega : Type*) [MeasurableSpace Omega] (P : Measure Omega)
    (Y : Omega -> Real × Real) (rho : Real) where
  hasPDF : HasPDF Y P realPlaneMeasure
  rho_nonneg : 0 <= rho
  density_le :
    ∀ᵐ q ∂realPlaneMeasure,
      pdf Y P realPlaneMeasure q <= ENNReal.ofReal rho

/-- The anisotropically scaled shear appearing in the corrected block lemma. -/
def scaledShearToComplex (alpha x y : Real) (q : Real × Real) : Complex :=
  ⟨x * q.1, alpha * (x * q.1) + y * q.2⟩

@[simp] theorem scaledShearToComplex_re (alpha x y : Real) (q : Real × Real) :
    (scaledShearToComplex alpha x y q).re = x * q.1 := rfl

@[simp] theorem scaledShearToComplex_im (alpha x y : Real) (q : Real × Real) :
    (scaledShearToComplex alpha x y q).im = alpha * (x * q.1) + y * q.2 := rfl

/-- A rectangle containing the inverse image of a complex disk under the shear. -/
def scaledShearRectangle (alpha x y : Real) (w : Complex) (radius : Real) :
    Set (Real × Real) :=
  Icc (w.re / x - radius / x) (w.re / x + radius / x) ×ˢ
    Icc ((w.im - alpha * w.re) / y - 2 * radius / y)
      ((w.im - alpha * w.re) / y + 2 * radius / y)

theorem measurableSet_scaledShearRectangle
    (alpha x y : Real) (w : Complex) (radius : Real) :
    MeasurableSet (scaledShearRectangle alpha x y w radius) :=
  measurableSet_Icc.prod measurableSet_Icc

/-- Disk membership implies membership in the explicit enclosing rectangle. -/
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
              1 * |x * (Y omega).1 - w.re| :=
            mul_le_mul_of_nonneg_right halpha (abs_nonneg _)
          _ <= 1 * radius := mul_le_mul_of_nonneg_left hre zero_le_one
          _ = radius := one_mul radius
      _ = 2 * radius := by ring
  have himIdentity :
      y * (Y omega).2 - (w.im - alpha * w.re) =
        y * ((Y omega).2 - (w.im - alpha * w.re) / y) := by
    field_simp [ne_of_gt hy]
  have himScaled :
      y * |(Y omega).2 - (w.im - alpha * w.re) / y| <= 2 * radius := by
    rw [himIdentity, abs_mul, abs_of_pos hy] at himResidual
    exact himResidual
  have himAbs :
      |(Y omega).2 - (w.im - alpha * w.re) / y| <= 2 * radius / y := by
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

/-- Exact area of the rectangle used in the anisotropic small-ball proof. -/
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

/-- The two-dimensional projection-density consequence used in the generic case. -/
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
        data.rho_nonneg data.density_le _
        (measurableSet_scaledShearRectangle alpha x y w radius)
    _ = ENNReal.ofReal (8 * rho * radius ^ 2 / (x * y)) := by
      rw [realPlaneMeasure_scaledShearRectangle alpha x y w radius hx hy hradius]
      rw [<- ENNReal.ofReal_mul data.rho_nonneg]
      congr 1
      ring

/-- Probability-measure form with the manuscript's explicit truncation by one. -/
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
      P {omega | ‖scaledShearToComplex alpha x y (Y omega) - w‖ <= radius} <=
          P Set.univ := measure_mono (Set.subset_univ _)
      _ = ENNReal.ofReal 1 := by simp
  · exact data.scaled_sheared_complex_small_ball alpha x y w radius
      hx hy hradius halpha

/-- Scaling a real random variable converts the density bound into the exact
`rho / |b|` small-ball factor, without postulating a density transformation. -/
theorem BoundedPDFInterface.scaled_real_small_ball
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : Omega -> Real} {rho b center radius : Real}
    (data : BoundedPDFInterface Omega P X rho)
    (hb : b ≠ 0) (hradius : 0 <= radius) :
    P ((fun omega => b * X omega) ⁻¹'
        Icc (center - radius) (center + radius)) <=
      ENNReal.ofReal (2 * rho * (radius / |b|)) := by
  have habs : 0 < |b| := abs_pos.mpr hb
  have hsubset :
      (fun omega => b * X omega) ⁻¹' Icc (center - radius) (center + radius) ⊆
        X ⁻¹' Icc (center / b - radius / |b|) (center / b + radius / |b|) := by
    intro omega homega
    have hball : |b * X omega - center| <= radius := by
      rw [abs_le]
      constructor <;> linarith [homega.1, homega.2]
    have hid : b * X omega - center = b * (X omega - center / b) := by
      field_simp [hb]
    have hscaled : |b| * |X omega - center / b| <= radius := by
      rw [hid, abs_mul] at hball
      exact hball
    have hdiv : |X omega - center / b| <= radius / |b| := by
      exact (le_div_iff₀ habs).2 (by simpa [mul_comm] using hscaled)
    rcases abs_le.mp hdiv with ⟨hlower, hupper⟩
    constructor <;> linarith
  calc
    P ((fun omega => b * X omega) ⁻¹'
        Icc (center - radius) (center + radius)) <=
        P (X ⁻¹' Icc (center / b - radius / |b|)
          (center / b + radius / |b|)) := measure_mono hsubset
    _ <= ENNReal.ofReal (2 * rho * (radius / |b|)) :=
      data.real_small_ball (div_nonneg hradius (abs_nonneg b))

/-- Exact external content of the cited one/two-dimensional projection theorem. -/
structure OneTwoProjectionDensityInterface
    (Omega : Type*) [MeasurableSpace Omega] (m : Nat) (P : Measure Omega)
    (xi : Omega -> EuclideanSpace Real (Fin m)) (rho C : Real) where
  one : forall p : EuclideanSpace Real (Fin m), ‖p‖ = 1 ->
    BoundedPDFInterface Omega P (fun omega => inner Real (xi omega) p) (C * rho)
  two : forall p r : EuclideanSpace Real (Fin m), ‖p‖ = 1 -> ‖r‖ = 1 ->
    inner Real p r = 0 ->
    BoundedPlanePDFInterface Omega P
      (fun omega => (inner Real (xi omega) p, inner Real (xi omega) r))
      (C * rho ^ 2)

/-- Once the cited two-dimensional density theorem is supplied, the corrected
generic block small-ball estimate is an internal theorem. -/
theorem OneTwoProjectionDensityInterface.generic_block_small_ball
    {Omega : Type*} [MeasurableSpace Omega] {m : Nat} {P : Measure Omega}
    [IsProbabilityMeasure P]
    {xi : Omega -> EuclideanSpace Real (Fin m)} {rho C : Real}
    (data : OneTwoProjectionDensityInterface Omega m P xi rho C)
    (p r : EuclideanSpace Real (Fin m))
    (hp : ‖p‖ = 1) (hr : ‖r‖ = 1) (hpr : inner Real p r = 0)
    (alpha x y : Real) (w : Complex) (radius : Real)
    (hx : 0 < x) (hy : 0 < y) (hradius : 0 <= radius)
    (halpha : |alpha| <= 1) :
    P {omega |
        ‖scaledShearToComplex alpha x y
          (inner Real (xi omega) p, inner Real (xi omega) r) - w‖ <= radius} <=
      ENNReal.ofReal
        (min 1 (8 * (C * rho ^ 2) * radius ^ 2 / (x * y))) := by
  exact (data.two p r hp hr hpr).scaled_sheared_complex_small_ball_min
    alpha x y w radius hx hy hradius halpha

end HighBandLSV.Real

