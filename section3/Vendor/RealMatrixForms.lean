/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealMatrixForms.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RealFormSmallBall
import Vendor.RealWeightedGeometry

/-! The real model's complex column forms, directly linked to proved projected densities. -/

noncomputable section
open MeasureTheory LivshytsProjectionFormalization
open scoped BigOperators ENNReal InnerProductSpace
namespace HighBandLSV.RealBandModel
open HighBandLSV.Anisotropic
variable {N W : Nat} {c C rho : Real} (m : RealBandModel N W c C rho)

def linearForm (j : Fin N) (u : CV (Fin N)) (x : AtomColumn N) : Complex :=
  ∑ i, star (u i) * ((m.sigma i j * x i : Real) : Complex)

def realCoefficients (j : Fin N) (u : CV (Fin N)) : RV (Fin N) :=
  weightReal (fun i => m.sigma i j) (realPart u)

def imagCoefficients (j : Fin N) (u : CV (Fin N)) : RV (Fin N) :=
  weightReal (fun i => m.sigma i j) (imagPart u)

def gram (j : Fin N) (u : CV (Fin N)) : Real :=
  ‖m.realCoefficients j u‖ * ‖residual (m.realCoefficients j u) (m.imagCoefficients j u)‖

theorem form_eq_star_linearForm (j : Fin N) (u : CV (Fin N)) (x : AtomColumn N) :
    form (m.realCoefficients j u) (m.imagCoefficients j u) (coordinateRV x) =
      star (m.linearForm j u x) := by
  apply Complex.ext <;>
    simp [form, realCoefficients, imagCoefficients, weightReal, Anisotropic.realPart, Anisotropic.imagPart,
      coordinateRV, linearForm, PiLp.inner_apply, Complex.mul_re, Complex.mul_im,
      mul_comm, mul_left_comm, mul_assoc]

theorem linearForm_one_small_ball
    (hGBL : RealFiniteGeometricBrascampLieb) (hrho : 0 < rho)
    (j : Fin N) (u : CV (Fin N)) (ha : 0 < ‖m.realCoefficients j u‖)
    (w : Complex) {s : Real} (hs : 0 ≤ s) :
    m.columnLaw j {x | ‖m.linearForm j u x - w‖ ≤ s} ≤
      ENNReal.ofReal (2 * (Real.exp 1 * rho) * (s / ‖m.realCoefficients j u‖)) := by
  have h := form_one_small_ball (m.projectionInterface hGBL hrho j)
    (m.realCoefficients j u) (m.imagCoefficients j u) ha (star w) hs
  simpa only [m.form_eq_star_linearForm, ← star_sub, norm_star] using h

theorem linearForm_two_small_ball
    (hGBL : RealFiniteGeometricBrascampLieb) (hrho : 0 < rho)
    (j : Fin N) (u : CV (Fin N)) (hg : 0 < m.gram j u)
    (w : Complex) {s : Real} (hs : 0 ≤ s) :
    m.columnLaw j {x | ‖m.linearForm j u x - w‖ ≤ s} ≤
      ENNReal.ofReal (min 1 (8 * (Real.exp 1 * rho ^ 2) * s ^ 2 / m.gram j u)) := by
  have h := form_two_small_ball (m.projectionInterface hGBL hrho j)
    (m.realCoefficients j u) (m.imagCoefficients j u) hg (star w) hs
  simpa only [m.form_eq_star_linearForm, ← star_sub, norm_star, gram] using h

theorem block_gram_lower (j : Fin N) (u : CV (Fin N)) (B : Finset (Fin N))
    (hc : 0 ≤ c) (hW : 0 < W)
    (hB : ∀ i ∈ B, Section5Formalization.cyclicDist N i j ≤ W) :
    (c / (W : Real)) * (‖restrictReal B (realPart u)‖ *
      ‖residual (restrictReal B (realPart u)) (restrictReal B (imagPart u))‖) ≤ m.gram j u := by
  exact weighted_block_gram_product (fun i => m.sigma i j) B (realPart u) (imagPart u)
    (by positivity) (fun i hi => m.local_floor i j (hB i hi))

end HighBandLSV.RealBandModel

#print axioms HighBandLSV.RealBandModel.linearForm_two_small_ball
#print axioms HighBandLSV.RealBandModel.block_gram_lower

