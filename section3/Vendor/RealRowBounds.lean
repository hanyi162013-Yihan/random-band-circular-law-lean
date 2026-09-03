/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealRowBounds.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RealMatrixForms
import Vendor.RealSmallBallNumerics
import Vendor.AnisotropicLabels

/-! All rank regimes of the real-entry block small-ball estimate. -/

noncomputable section
open MeasureTheory LivshytsProjectionFormalization
open scoped BigOperators ENNReal InnerProductSpace
namespace HighBandLSV.Anisotropic

variable {N : Nat}

def restrictComplex (B : Finset (Fin N)) (u : CV (Fin N)) : CV {i // i ∈ B} :=
  WithLp.toLp 2 (fun i => u i)

@[simp] theorem realPart_restrictRotate (B : Finset (Fin N)) (phase : Bool) (u : CV (Fin N)) :
    restrictReal B (realPart (rotate phase u)) = realPart (rotate phase (restrictComplex B u)) := by
  cases phase <;> rfl

@[simp] theorem imagPart_restrictRotate (B : Finset (Fin N)) (phase : Bool) (u : CV (Fin N)) :
    restrictReal B (imagPart (rotate phase u)) = imagPart (rotate phase (restrictComplex B u)) := by
  cases phase <;> rfl

theorem radius_dichotomy {h : Real} (hh : 0 < h) (q : RadiusLabel h) :
    radius h q = 0 ∨ h ≤ radius h q := by
  by_cases hq : q.val = 0
  · left; simp [radius, hq]
  · right
    have hk : (1 : Real) ≤ q.val := by exact_mod_cast (show 1 ≤ q.val by omega)
    simpa [radius] using mul_le_mul_of_nonneg_right hk hh.le

theorem sqrt_energy_lower {q x a : Real} (hq : 0 ≤ q) (hx : 0 ≤ x) (ha : 0 ≤ a)
    (he : q * x ^ 2 ≤ a ^ 2) : Real.sqrt q * x ≤ a := by
  have hs : (Real.sqrt q * x) ^ 2 = q * x ^ 2 := by rw [mul_pow, Real.sq_sqrt hq]
  nlinarith [mul_nonneg (Real.sqrt_nonneg q) hx]

end HighBandLSV.Anisotropic

namespace HighBandLSV.RealBandModel
open HighBandLSV.Anisotropic HighBandLSV.RealSmallBallNumerics
variable {N W : Nat} {c C rho : Real} (m : RealBandModel N W c C rho)

theorem linearForm_smul (j : Fin N) (u : CV (Fin N)) (x : AtomColumn N) (a : Complex) :
    m.linearForm j (a • u) x = star a * m.linearForm j u x := by
  simp only [linearForm, PiLp.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def rotatedCenter (phase : Bool) (w : Complex) : Complex := if phase then star Complex.I * w else w

theorem rotated_linearForm_distance (j : Fin N) (u : CV (Fin N)) (x : AtomColumn N)
    (phase : Bool) (w : Complex) :
    ‖m.linearForm j (rotate phase u) x - rotatedCenter phase w‖ = ‖m.linearForm j u x - w‖ := by
  cases phase
  · rfl
  · simp only [rotate, rotatedCenter, Bool.true_eq, if_true, m.linearForm_smul]
    rw [← mul_sub, norm_mul, norm_star, Complex.norm_I, one_mul]

theorem block_real_axis_lower (j : Fin N) (u : CV (Fin N)) (B : Finset (Fin N))
    (hc : 0 < c) (hW : 0 < W)
    (hB : ∀ i ∈ B, Section5Formalization.cyclicDist N i j ≤ W)
    {x : Real} (hx : 0 ≤ x) (haxis : x ≤ ‖restrictReal B (realPart u)‖) :
    Real.sqrt (c / W) * x ≤ ‖m.realCoefficients j u‖ := by
  have he := weighted_block_energy (fun i => m.sigma i j) B (realPart u)
    (by positivity : 0 ≤ c / (W : Real)) (fun i hi => m.local_floor i j (hB i hi))
  apply sqrt_energy_lower (by positivity) hx (norm_nonneg _)
  apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx haxis 2) (by positivity)).trans
  exact he

theorem anisotropic_row_probability
    (hGBL : RealFiniteGeometricBrascampLieb) (hrho : 0 < rho)
    (hc : 0 < c) (hW : 0 < W) {A h d : Real}
    (hA1 : 1 ≤ A) (hAone : 2 * (Real.exp 1 * rho) / Real.sqrt c ≤ A)
    (hAtwo : (8 * (Real.exp 1 * rho ^ 2)) / c ≤ A)
    (hh : 0 < h) (hhd : h ≤ d) (j : Fin N) (B : Finset (Fin N))
    (hB : ∀ i ∈ B, Section5Formalization.cyclicDist N i j ≤ W)
    (q : Label h) (hq : admissible q) (u : CV (Fin N))
    (hu : restrictComplex B u ∈ blockClass q) (w : Complex) :
    m.columnLaw j {x | ‖m.linearForm j u x - w‖ ≤ d} ≤
      ENNReal.ofReal (A * W * d ^ 2 / labelWeight q) := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA1
  have hWr : (1 : Real) ≤ W := by exact_mod_cast hW
  have hd : 0 < d := hh.trans_le hhd
  let v := rotate q.1 u
  let w' := rotatedCenter q.1 w
  have hevent : {x | ‖m.linearForm j v x - w'‖ ≤ d} =
      {x | ‖m.linearForm j u x - w‖ ≤ d} := by
    ext x
    change ‖m.linearForm j v x - w'‖ ≤ d ↔ ‖m.linearForm j u x - w‖ ≤ d
    rw [show ‖m.linearForm j v x - w'‖ = ‖m.linearForm j u x - w‖ from
      m.rotated_linearForm_distance j u x q.1 w]
  have hx0 : 0 ≤ xRadius q := radius_nonneg hh.le _
  have hy0 : 0 ≤ yRadius q := radius_nonneg hh.le _
  have haxis : xRadius q ≤ ‖restrictReal B (realPart v)‖ := by
    simpa only [v, realPart_restrictRotate] using hu.2.2.1
  have hres : yRadius q ≤ ‖residual (restrictReal B (realPart v)) (restrictReal B (imagPart v))‖ := by
    simpa only [v, realPart_restrictRotate, imagPart_restrictRotate] using hu.2.2.2.2.1
  rcases radius_dichotomy hh q.2.1 with hxzero | hxlarge
  · have hxz : xRadius q = 0 := hxzero
    have hyz : yRadius q = 0 := by linarith [hq.2.1]
    have hw : labelWeight q = h ^ 2 := by simp [labelWeight, hxz, hyz, hh.le, pow_two]
    have hb : 1 ≤ A * (W : Real) * d ^ 2 / labelWeight q := by
      rw [hw]
      apply (le_div_iff₀ (sq_pos_of_pos hh)).2
      have hAW : 1 ≤ A * (W : Real) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hAW (sq_nonneg d)]
    calc
      _ ≤ m.columnLaw j Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal (A * W * d ^ 2 / labelWeight q) := by
        simpa using ENNReal.ofReal_le_ofReal hb
  · have hxp : 0 < xRadius q := hh.trans_le hxlarge
    have ha := m.block_real_axis_lower j v B hc hW hB hx0 haxis
    have hap : 0 < ‖m.realCoefficients j v‖ :=
      (mul_pos (Real.sqrt_pos.2 (by positivity)) hxp).trans_le ha
    rcases radius_dichotomy hh q.2.2.1 with hyzero | hylarge
    · have hyz : yRadius q = 0 := hyzero
      have hw : labelWeight q = xRadius q * h := by
        rw [labelWeight, max_eq_left (show h ≤ xRadius q from hxlarge), hyz,
          max_eq_right hh.le]
      have hp := m.linearForm_one_small_ball hGBL hrho j v hap w' hd.le
      rw [hevent] at hp
      have hn := rank_one_to_mesh_bound (by positivity : 0 ≤ 2 * (Real.exp 1 * rho))
        hc hWr hxp hh hhd ha hAone
      apply hp.trans
      apply ENNReal.ofReal_le_ofReal
      rw [hw]
      convert hn using 1 <;> ring
    · have hyp : 0 < yRadius q := hh.trans_le hylarge
      have hg0 := m.block_gram_lower j v B hc.le hW hB
      have hg : (c / (W : Real)) * (xRadius q * yRadius q) ≤ m.gram j v := by
        apply (mul_le_mul_of_nonneg_left
          (mul_le_mul haxis hres hy0 (norm_nonneg _)) (by positivity)).trans
        exact hg0
      have hgp : 0 < m.gram j v := (by positivity : 0 < (c / (W : Real)) *
        (xRadius q * yRadius q)).trans_le hg
      have hp := m.linearForm_two_small_ball hGBL hrho j v hgp w' hd.le
      rw [hevent] at hp
      have hn := two_dimensional_bound (d := d)
        (by positivity : 0 ≤ 8 * (Real.exp 1 * rho ^ 2))
        hc (by exact_mod_cast hW) hxp hyp hg hAtwo
      have hw : labelWeight q = xRadius q * yRadius q := by
        rw [labelWeight, max_eq_left (show h ≤ xRadius q from hxlarge),
          max_eq_left (show h ≤ yRadius q from hylarge)]
      apply hp.trans
      apply ENNReal.ofReal_le_ofReal
      rw [hw]
      exact (min_le_right _ _).trans hn

end HighBandLSV.RealBandModel

#print axioms HighBandLSV.RealBandModel.anisotropic_row_probability

