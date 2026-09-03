/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealColumnSmallBall.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RealRowBounds
import Vendor.NormalEvents

/-! Real-entry column concentration from a block mass lower bound. -/

noncomputable section
open MeasureTheory LivshytsProjectionFormalization
open scoped BigOperators ENNReal InnerProductSpace
namespace HighBandLSV.Anisotropic

variable {N : Nat}

theorem restrictComplex_norm_sq (B : Finset (Fin N)) (u : CV (Fin N)) :
    ‖restrictComplex B u‖ ^ 2 = NormalEvents.blockMass B u := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [restrictComplex, WithLp.ofLp_toLp, NormalEvents.blockMass]
  exact Finset.sum_coe_sort B (fun i => ‖u i‖ ^ 2)

theorem form_max_axis_small_ball {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P] {xi : Omega → RV (Fin N)} {rho C : Real}
    (data : HighBandLSV.Real.OneTwoProjectionDensityInterface Omega N P xi rho C)
    (a b : RV (Fin N)) (hmax : 0 < max ‖a‖ ‖b‖) (w : Complex) {s : Real} (hs : 0 ≤ s) :
    P {omega | ‖form a b (xi omega) - w‖ ≤ s} ≤
      ENNReal.ofReal (2 * (C * rho) * (s / max ‖a‖ ‖b‖)) := by
  by_cases h : ‖b‖ ≤ ‖a‖
  · rw [max_eq_left h] at hmax ⊢
    exact form_one_small_ball data a b hmax w hs
  · have h' : ‖a‖ ≤ ‖b‖ := by linarith
    rw [max_eq_right h'] at hmax ⊢
    have hb := form_one_small_ball data b a hmax (swapComplex w) hs
    have he : {omega | ‖form b a (xi omega) - swapComplex w‖ ≤ s} =
        {omega | ‖form a b (xi omega) - w‖ ≤ s} := by
      ext omega
      change ‖form b a (xi omega) - swapComplex w‖ ≤ s ↔ ‖form a b (xi omega) - w‖ ≤ s
      rw [form_swap, swapComplex_distance]
    rw [he] at hb
    exact hb

end HighBandLSV.Anisotropic

namespace HighBandLSV.RealBandModel
open HighBandLSV.Anisotropic HighBandLSV.RealSmallBallNumerics
variable {N W : Nat} {c C rho : Real} (m : RealBandModel N W c C rho)

theorem combined_block_energy (j : Fin N) (u : CV (Fin N)) (B : Finset (Fin N))
    (hc : 0 ≤ c) (hW : 0 < W)
    (hB : ∀ i ∈ B, Section5Formalization.cyclicDist N i j ≤ W) :
    (c / (W : Real)) * NormalEvents.blockMass B u ≤
      ‖m.realCoefficients j u‖ ^ 2 + ‖m.imagCoefficients j u‖ ^ 2 := by
  have ha := weighted_block_energy (fun i => m.sigma i j) B (realPart u)
    (by positivity : 0 ≤ c / (W : Real)) (fun i hi => m.local_floor i j (hB i hi))
  have hb := weighted_block_energy (fun i => m.sigma i j) B (imagPart u)
    (by positivity : 0 ≤ c / (W : Real)) (fun i hi => m.local_floor i j (hB i hi))
  have he : ‖restrictReal B (realPart u)‖ ^ 2 + ‖restrictReal B (imagPart u)‖ ^ 2 =
      NormalEvents.blockMass B u := by
    change ‖realPart (restrictComplex B u)‖ ^ 2 + ‖imagPart (restrictComplex B u)‖ ^ 2 = _
    rw [← parts_norm_sq, restrictComplex_norm_sq]
  rw [← he, mul_add]
  exact add_le_add ha hb

theorem linearForm_block_mass_small_ball
    (hGBL : RealFiniteGeometricBrascampLieb) (hrho : 0 < rho)
    (hc : 0 < c) (hW : 0 < W) (j : Fin N) (u : CV (Fin N)) (B : Finset (Fin N))
    (hB : ∀ i ∈ B, Section5Formalization.cyclicDist N i j ≤ W)
    {d s : Real} (hd : 0 < d) (hs : 0 ≤ s) (hmass : d ^ 2 ≤ NormalEvents.blockMass B u)
    (w : Complex) :
    m.columnLaw j {x | ‖m.linearForm j u x - w‖ ≤ s} ≤
      ENNReal.ofReal ((2 * Real.sqrt 2 * Real.exp 1 * rho / Real.sqrt c) *
        Real.sqrt W * s / d) := by
  have hq : 0 < c / (W : Real) := by positivity
  have he := (mul_le_mul_of_nonneg_left hmass hq.le).trans (m.combined_block_energy j u B hc.le hW hB)
  have haxis := one_axis_energy (norm_nonneg (m.realCoefficients j u))
    (norm_nonneg (m.imagCoefficients j u)) hq hd.le he
  have hqeq : c / (2 * (W : Real)) = (c / W) / 2 := by ring
  have haxis' : Real.sqrt (c / (2 * (W : Real))) * d ≤
      max ‖m.realCoefficients j u‖ ‖m.imagCoefficients j u‖ := by
    simpa only [hqeq] using haxis
  have hmax : 0 < max ‖m.realCoefficients j u‖ ‖m.imagCoefficients j u‖ :=
    (mul_pos (Real.sqrt_pos.2 (by positivity)) hd).trans_le haxis'
  have hp := form_max_axis_small_ball (m.projectionInterface hGBL hrho j)
    (m.realCoefficients j u) (m.imagCoefficients j u) hmax (star w) hs
  have hp' : m.columnLaw j {x | ‖m.linearForm j u x - w‖ ≤ s} ≤
      ENNReal.ofReal (2 * (Real.exp 1 * rho) *
        (s / max ‖m.realCoefficients j u‖ ‖m.imagCoefficients j u‖)) := by
    simpa only [m.form_eq_star_linearForm, ← star_sub, norm_star] using hp
  have hn := scaled_one_bound (by positivity : 0 ≤ 2 * (Real.exp 1 * rho))
    hs hc (by positivity : 0 < 2 * (W : Real)) hd haxis'
  rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2)] at hn
  apply hp'.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    2 * (Real.exp 1 * rho) * (s / max ‖m.realCoefficients j u‖ ‖m.imagCoefficients j u‖) =
      (2 * (Real.exp 1 * rho)) * s / max ‖m.realCoefficients j u‖ ‖m.imagCoefficients j u‖ := by ring
    _ ≤ ((2 * (Real.exp 1 * rho)) / Real.sqrt c) * (Real.sqrt 2 * Real.sqrt W) * s / d := hn
    _ = (2 * Real.sqrt 2 * Real.exp 1 * rho / Real.sqrt c) * Real.sqrt W * s / d := by ring

end HighBandLSV.RealBandModel

#print axioms HighBandLSV.RealBandModel.linearForm_block_mass_small_ball

