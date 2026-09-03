/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/GaussianModelMoments.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.BVH.GaussianMoments
import Vendor.Arxiv2410.V3.BVH.ModelMoments

/-!
# Third moments of the Gaussian companion entries

This file derives the Gaussian-entry third-moment ledger needed by the specialized
Lindeberg proof of BVH Remark 6.13.  All probabilistic input comes from the joint
Gaussian law and the five first/second moment matches in `GaussianCompanionModelV3`.
In particular, no comparison principle is assumed here.
-/

namespace Arxiv2410V3.BVH

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable section

variable {Omega OmegaXi OmegaG : Type*}
  [MeasurableSpace Omega] [MeasurableSpace OmegaXi] [MeasurableSpace OmegaG]
  {mu : Measure Omega} {nu : Measure OmegaXi} {muG : Measure OmegaG}
  [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure muG]
  {n : ℕ}

variable
  (actual : RandomMatrixModelV3 n Omega OmegaXi mu nu)
  (gaussian : GaussianCompanionModelV3 n Omega OmegaXi OmegaG mu nu muG actual)

/-- The real part of every companion entry is Gaussian, by projection of the joint law. -/
theorem gaussian_entry_re_hasGaussianLaw (i j : Fin n) :
    HasGaussianLaw (fun omega ↦ (gaussian.matrix omega i j).re) muG :=
  (gaussian.entry_jointGaussian i j).fst

/-- The imaginary part of every companion entry is Gaussian, by projection of the joint law. -/
theorem gaussian_entry_im_hasGaussianLaw (i j : Fin n) :
    HasGaussianLaw (fun omega ↦ (gaussian.matrix omega i j).im) muG :=
  (gaussian.entry_jointGaussian i j).snd

/-- First-moment matching and the centered atom imply that every Gaussian real coordinate
is centered. -/
theorem integral_gaussian_entry_re_eq_zero (i j : Fin n) :
    (∫ omega, (gaussian.matrix omega i j).re ∂muG) = 0 := by
  rw [gaussian.re_mean_match, integral_entry_re_eq_zero actual]

theorem integral_gaussian_entry_im_eq_zero (i j : Fin n) :
    (∫ omega, (gaussian.matrix omega i j).im ∂muG) = 0 := by
  rw [gaussian.im_mean_match, integral_entry_im_eq_zero actual]

/-- Second-moment matching bounds each real-coordinate variance by `bᵢⱼ²`. -/
theorem variance_gaussian_entry_re_le_coefficient_sq (i j : Fin n) :
    Var[fun omega ↦ (gaussian.matrix omega i j).re; muG] ≤
      actual.profile.coefficient i j ^ 2 := by
  rw [variance_of_integral_eq_zero
    (gaussian_entry_re_hasGaussianLaw actual gaussian i j).aemeasurable
    (integral_gaussian_entry_re_eq_zero actual gaussian i j)]
  rw [gaussian.re_second_match]
  exact integral_entry_re_sq_le_coefficient_sq actual i j

theorem variance_gaussian_entry_im_le_coefficient_sq (i j : Fin n) :
    Var[fun omega ↦ (gaussian.matrix omega i j).im; muG] ≤
      actual.profile.coefficient i j ^ 2 := by
  rw [variance_of_integral_eq_zero
    (gaussian_entry_im_hasGaussianLaw actual gaussian i j).aemeasurable
    (integral_gaussian_entry_im_eq_zero actual gaussian i j)]
  rw [gaussian.im_second_match]
  exact integral_entry_im_sq_le_coefficient_sq actual i j

/-- The real part of one companion entry has the correct cubic scale. -/
theorem integral_abs_gaussian_entry_re_cube_le (i j : Fin n) :
    (∫ omega, |(gaussian.matrix omega i j).re| ^ 3 ∂muG) ≤
      realGaussianThirdMomentConstant * actual.profile.coefficient i j ^ 3 := by
  let c : ℝ≥0 :=
    ⟨actual.profile.coefficient i j ^ 2, sq_nonneg (actual.profile.coefficient i j)⟩
  have h := integral_abs_cube_le_of_centered_gaussian_of_variance_le
    (c := c) (gaussian_entry_re_hasGaussianLaw actual gaussian i j)
    (integral_gaussian_entry_re_eq_zero actual gaussian i j)
    (variance_gaussian_entry_re_le_coefficient_sq actual gaussian i j)
  change (∫ omega, |(gaussian.matrix omega i j).re| ^ 3 ∂muG) ≤
    realGaussianThirdMomentConstant *
      (Real.sqrt (actual.profile.coefficient i j ^ 2)) ^ 3 at h
  rwa [Real.sqrt_sq_eq_abs,
    abs_of_nonneg (actual.profile.coefficient_nonneg i j)] at h

/-- The imaginary part of one companion entry has the correct cubic scale. -/
theorem integral_abs_gaussian_entry_im_cube_le (i j : Fin n) :
    (∫ omega, |(gaussian.matrix omega i j).im| ^ 3 ∂muG) ≤
      realGaussianThirdMomentConstant * actual.profile.coefficient i j ^ 3 := by
  let c : ℝ≥0 :=
    ⟨actual.profile.coefficient i j ^ 2, sq_nonneg (actual.profile.coefficient i j)⟩
  have h := integral_abs_cube_le_of_centered_gaussian_of_variance_le
    (c := c) (gaussian_entry_im_hasGaussianLaw actual gaussian i j)
    (integral_gaussian_entry_im_eq_zero actual gaussian i j)
    (variance_gaussian_entry_im_le_coefficient_sq actual gaussian i j)
  change (∫ omega, |(gaussian.matrix omega i j).im| ^ 3 ∂muG) ≤
    realGaussianThirdMomentConstant *
      (Real.sqrt (actual.profile.coefficient i j ^ 2)) ^ 3 at h
  rwa [Real.sqrt_sq_eq_abs,
    abs_of_nonneg (actual.profile.coefficient_nonneg i j)] at h

/-- A deterministic two-coordinate estimate used to combine the real and imaginary
third moments.  The constant is chosen for a robust algebraic proof, not sharpness. -/
private theorem norm_complex_cube_le_abs_re_im_cube (z : ℂ) :
    ‖z‖ ^ 3 ≤ 4 * (|z.re| ^ 3 + |z.im| ^ 3) := by
  have hnorm : ‖z‖ ≤ |z.re| + |z.im| := by
    calc
      ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := by
        congr 1
        apply Complex.ext <;> simp
      _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |z.re| + |z.im| := by simp [Real.norm_eq_abs]
  have hpoly :
      0 ≤ 3 * (|z.re| + |z.im|) * (|z.re| - |z.im|) ^ 2 := by positivity
  calc
    ‖z‖ ^ 3 ≤ (|z.re| + |z.im|) ^ 3 :=
      pow_le_pow_left₀ (norm_nonneg z) hnorm 3
    _ ≤ 4 * (|z.re| ^ 3 + |z.im| ^ 3) := by nlinarith

/-- The cubic norm of every Gaussian companion entry is integrable. -/
theorem integrable_gaussian_entry_norm_cube (i j : Fin n) :
    Integrable (fun omega ↦ ‖gaussian.matrix omega i j‖ ^ 3) muG := by
  have hre : Integrable (fun omega ↦ |(gaussian.matrix omega i j).re| ^ 3) muG := by
    have hreLp : MemLp (fun omega ↦ (gaussian.matrix omega i j).re) 3 muG :=
      (gaussian_entry_re_hasGaussianLaw actual gaussian i j).memLp (by norm_num)
    simpa [Real.norm_eq_abs] using
      MemLp.integrable_norm_pow hreLp (by norm_num)
  have him : Integrable (fun omega ↦ |(gaussian.matrix omega i j).im| ^ 3) muG := by
    have himLp : MemLp (fun omega ↦ (gaussian.matrix omega i j).im) 3 muG :=
      (gaussian_entry_im_hasGaussianLaw actual gaussian i j).memLp (by norm_num)
    simpa [Real.norm_eq_abs] using
      MemLp.integrable_norm_pow himLp (by norm_num)
  have hmajorant : Integrable
      (fun omega ↦ 4 *
        (|(gaussian.matrix omega i j).re| ^ 3 +
          |(gaussian.matrix omega i j).im| ^ 3)) muG :=
    (hre.add him).const_mul 4
  apply hmajorant.mono'
    (((gaussian.entry_measurable i j).aestronglyMeasurable.norm.aemeasurable.pow_const 3).aestronglyMeasurable)
  filter_upwards [] with omega
  simpa [abs_of_nonneg (pow_nonneg (norm_nonneg _) 3)] using
    norm_complex_cube_le_abs_re_im_cube (gaussian.matrix omega i j)

/-- Explicit cubic-moment bound for one Gaussian companion entry:
`E ‖Gᵢⱼ‖³ ≤ C_G bᵢⱼ³`. -/
theorem integral_gaussian_entry_norm_cube_le (i j : Fin n) :
    (∫ omega, ‖gaussian.matrix omega i j‖ ^ 3 ∂muG) ≤
      complexGaussianThirdMomentConstant * actual.profile.coefficient i j ^ 3 := by
  have hre : Integrable (fun omega ↦ |(gaussian.matrix omega i j).re| ^ 3) muG := by
    have hreLp : MemLp (fun omega ↦ (gaussian.matrix omega i j).re) 3 muG :=
      (gaussian_entry_re_hasGaussianLaw actual gaussian i j).memLp (by norm_num)
    simpa [Real.norm_eq_abs] using
      MemLp.integrable_norm_pow hreLp (by norm_num)
  have him : Integrable (fun omega ↦ |(gaussian.matrix omega i j).im| ^ 3) muG := by
    have himLp : MemLp (fun omega ↦ (gaussian.matrix omega i j).im) 3 muG :=
      (gaussian_entry_im_hasGaussianLaw actual gaussian i j).memLp (by norm_num)
    simpa [Real.norm_eq_abs] using
      MemLp.integrable_norm_pow himLp (by norm_num)
  have hmajorant : Integrable
      (fun omega ↦ 4 *
        (|(gaussian.matrix omega i j).re| ^ 3 +
          |(gaussian.matrix omega i j).im| ^ 3)) muG :=
    (hre.add him).const_mul 4
  calc
    (∫ omega, ‖gaussian.matrix omega i j‖ ^ 3 ∂muG) ≤
        ∫ omega, 4 *
          (|(gaussian.matrix omega i j).re| ^ 3 +
            |(gaussian.matrix omega i j).im| ^ 3) ∂muG := by
      apply integral_mono (integrable_gaussian_entry_norm_cube actual gaussian i j)
        hmajorant
      exact fun omega ↦
        norm_complex_cube_le_abs_re_im_cube (gaussian.matrix omega i j)
    _ = 4 * ((∫ omega, |(gaussian.matrix omega i j).re| ^ 3 ∂muG) +
          ∫ omega, |(gaussian.matrix omega i j).im| ^ 3 ∂muG) := by
      rw [integral_const_mul, integral_add hre him]
    _ ≤ 4 *
        (realGaussianThirdMomentConstant * actual.profile.coefficient i j ^ 3 +
          realGaussianThirdMomentConstant * actual.profile.coefficient i j ^ 3) := by
      gcongr
      · exact integral_abs_gaussian_entry_re_cube_le actual gaussian i j
      · exact integral_abs_gaussian_entry_im_cube_le actual gaussian i j
    _ = complexGaussianThirdMomentConstant * actual.profile.coefficient i j ^ 3 := by
      simp only [complexGaussianThirdMomentConstant]
      ring

/-- The normalized double sum of companion-entry cubic moments has the bandwidth scale
`C_G / √B`.  This is the Gaussian half of the third-moment ledger in v3 (3.12). -/
theorem normalized_sum_integral_gaussian_entry_norm_cube_le
    [NeZero n] {B : ℝ} (hB : IsBandwidth actual.profile B) :
    (∑ i : Fin n, ∑ j : Fin n,
        ∫ omega, ‖gaussian.matrix omega i j‖ ^ 3 ∂muG) / (n : ℝ) ≤
      complexGaussianThirdMomentConstant / Real.sqrt B := by
  have hsum :
      (∑ i : Fin n, ∑ j : Fin n,
          ∫ omega, ‖gaussian.matrix omega i j‖ ^ 3 ∂muG) ≤
        ∑ i : Fin n, ∑ j : Fin n,
          complexGaussianThirdMomentConstant * actual.profile.coefficient i j ^ 3 :=
    Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
      integral_gaussian_entry_norm_cube_le actual gaussian i j
  have hnNat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnNat
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        ∫ omega, ‖gaussian.matrix omega i j‖ ^ 3 ∂muG) / (n : ℝ) ≤
        (∑ i : Fin n, ∑ j : Fin n,
          complexGaussianThirdMomentConstant * actual.profile.coefficient i j ^ 3) /
            (n : ℝ) := (div_le_div_iff_of_pos_right hnpos).2 hsum
    _ = complexGaussianThirdMomentConstant *
        ((∑ i : Fin n, ∑ j : Fin n, actual.profile.coefficient i j ^ 3) /
          (n : ℝ)) := by
      simp_rw [← Finset.mul_sum]
      ring
    _ ≤ complexGaussianThirdMomentConstant / Real.sqrt B := by
      simpa [Fintype.card_fin] using
        third_moment_mul_normalized_sum_cube_le actual.profile hB
          (show 0 ≤ complexGaussianThirdMomentConstant by
            simp only [complexGaussianThirdMomentConstant,
              realGaussianThirdMomentConstant]
            positivity)

end

end Arxiv2410V3.BVH

