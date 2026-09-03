/- Source snapshot: upstream-sources/i-2/work/ginibre-lsv-lean/GinibreLSV/GaussianSmallBall.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# One-dimensional Gaussian small-ball estimates

The square argument ultimately needs only a one-dimensional density estimate:
a real Gaussian places at most its peak density times the interval length in
any interval.  This file isolates that analytic fact.
-/

open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace RealInnerProductSpace ComplexInnerProductSpace

noncomputable section

namespace GinibreLSV

/-- The peak value of the density of a real Gaussian with variance `v`. -/
def gaussianPeak (v : NNReal) : ENNReal :=
  ENNReal.ofReal (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹

theorem gaussianPDF_le_peak (m : ℝ) (v : NNReal) (x : ℝ) :
    gaussianPDF m v x ≤ gaussianPeak v := by
  rw [gaussianPDF, gaussianPeak, gaussianPDFReal]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_of_le_one_right
  · positivity
  · rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
      (show 0 ≤ (2 : ℝ) * (v : ℝ) by positivity)

theorem gaussianReal_le_peak_smul_volume (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    gaussianReal m v ≤ gaussianPeak v • volume := by
  rw [gaussianReal_of_var_ne_zero m hv, ← withDensity_const]
  exact withDensity_mono (ae_of_all _ fun x => gaussianPDF_le_peak m v x)

/-- A real Gaussian interval has mass at most peak-density times interval
length.  The center `a` is arbitrary. -/
theorem gaussianReal_Ioo_le (m a r : ℝ) {v : NNReal} (hv : v ≠ 0) (_hr : 0 ≤ r) :
    gaussianReal m v (Ioo (a - r) (a + r)) ≤
      gaussianPeak v * ENNReal.ofReal (2 * r) := by
  calc
    gaussianReal m v (Ioo (a - r) (a + r)) ≤
        (gaussianPeak v • volume) (Ioo (a - r) (a + r)) :=
      gaussianReal_le_peak_smul_volume m hv (Ioo (a - r) (a + r))
    _ = gaussianPeak v * ENNReal.ofReal (2 * r) := by
      rw [Measure.smul_apply, Real.volume_Ioo]
      change gaussianPeak v * ENNReal.ofReal ((a + r) - (a - r)) = _
      rw [show (a + r) - (a - r) = 2 * r by ring]

/-- Every nonzero real linear functional of a standard Gaussian vector obeys
the corresponding one-dimensional interval small-ball estimate. -/
theorem stdGaussian_linear_Ioo_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : StrongDual ℝ E) (hL : L ≠ 0) (a r : ℝ) (hr : 0 ≤ r) :
    stdGaussian E (L ⁻¹' Ioo (a - r) (a + r)) ≤
      gaussianPeak ((‖L‖ ^ 2).toNNReal) * ENNReal.ofReal (2 * r) := by
  have hv : (‖L‖ ^ 2).toNNReal ≠ 0 := by
    simp [hL]
  calc
    stdGaussian E (L ⁻¹' Ioo (a - r) (a + r)) =
        (stdGaussian E).map L (Ioo (a - r) (a + r)) := by
      rw [Measure.map_apply (by fun_prop) measurableSet_Ioo]
    _ = gaussianReal 0 ((‖L‖ ^ 2).toNNReal) (Ioo (a - r) (a + r)) := by
      rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
        variance_dual_stdGaussian]
    _ ≤ gaussianPeak ((‖L‖ ^ 2).toNNReal) * ENNReal.ofReal (2 * r) :=
      gaussianReal_Ioo_le 0 a r hv hr

/-- A standard Gaussian vector lies within distance `r` of any fixed proper
subspace with probability at most the one-dimensional Gaussian interval
bound.  This is the fixed-fiber estimate used after exposing all other
columns of a square Ginibre matrix. -/
theorem stdGaussian_subspace_smallBall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (H : Submodule ℝ E) (hH : H ≠ ⊤) (r : ℝ) (hr : 0 ≤ r) :
    stdGaussian E {x | ‖Hᗮ.starProjection x‖ < r} ≤
      gaussianPeak 1 * ENNReal.ofReal (2 * r) := by
  have horth : Hᗮ ≠ ⊥ := by
    intro hbot
    exact hH (Submodule.orthogonal_eq_bot_iff.mp hbot)
  obtain ⟨u₀, hu₀H, hu₀⟩ := (Submodule.ne_bot_iff Hᗮ).mp horth
  let u : E := ‖u₀‖⁻¹ • u₀
  have huH : u ∈ Hᗮ := Hᗮ.smul_mem _ hu₀H
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, hu₀]
  let L : StrongDual ℝ E := innerSL ℝ u
  have hLnorm : ‖L‖ = 1 := by
    simp [L, innerSL_apply_norm, hu]
  have hL : L ≠ 0 := by
    intro hzero
    have : ‖L‖ = 0 := by rw [hzero, norm_zero]
    linarith
  have hsubset : {x : E | ‖Hᗮ.starProjection x‖ < r} ⊆
      L ⁻¹' Ioo (-r) r := by
    intro x hx
    have hinner : ⟪u, x⟫ = ⟪u, Hᗮ.starProjection x⟫ := by
      calc
        ⟪u, x⟫ = ⟪Hᗮ.starProjection u, x⟫ := by
          rw [Hᗮ.starProjection_eq_self_iff.mpr huH]
        _ = ⟪u, Hᗮ.starProjection x⟫ :=
          Hᗮ.inner_starProjection_left_eq_right u x
    have habs : |L x| < r := by
      change |⟪u, x⟫| < r
      rw [hinner]
      calc
        |⟪u, Hᗮ.starProjection x⟫| ≤ ‖u‖ * ‖Hᗮ.starProjection x‖ :=
          abs_real_inner_le_norm _ _
        _ = ‖Hᗮ.starProjection x‖ := by rw [hu, one_mul]
        _ < r := hx
    exact (abs_lt.mp habs)
  calc
    stdGaussian E {x | ‖Hᗮ.starProjection x‖ < r} ≤
        stdGaussian E (L ⁻¹' Ioo (-r) r) := measure_mono hsubset
    _ ≤ gaussianPeak ((‖L‖ ^ 2).toNNReal) * ENNReal.ofReal (2 * r) := by
      simpa only [zero_sub, zero_add] using stdGaussian_linear_Ioo_le L hL 0 r hr
    _ = gaussianPeak 1 * ENNReal.ofReal (2 * r) := by simp [hLnorm]

set_option maxHeartbeats 4000000 in
/-- A fixed proper complex subspace has a linear small-ball bound under the
standard real Gaussian on complex Euclidean space.  We only use one real
normal direction, which is enough for the square least-singular-value bound. -/
theorem stdGaussian_complexSubspace_smallBall
    {ι : Type*} [Fintype ι]
    (K : Submodule ℂ (EuclideanSpace ℂ ι)) (hK : K ≠ ⊤)
    (r : ℝ) (hr : 0 ≤ r) :
    stdGaussian (EuclideanSpace ℂ ι)
        {x | ‖Kᗮ.starProjection x‖ < r} ≤
      gaussianPeak 1 * ENNReal.ofReal (2 * r) := by
  have horth : Kᗮ ≠ ⊥ := by
    intro hbot
    exact hK (Submodule.orthogonal_eq_bot_iff.mp hbot)
  obtain ⟨u₀, hu₀K, hu₀⟩ := (Submodule.ne_bot_iff Kᗮ).mp horth
  let u : EuclideanSpace ℂ ι := ((‖u₀‖⁻¹ : ℝ) : ℂ) • u₀
  have huK : u ∈ Kᗮ := Kᗮ.smul_mem ((‖u₀‖⁻¹ : ℝ) : ℂ) hu₀K
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, hu₀]
  let L : StrongDual ℝ (EuclideanSpace ℂ ι) := innerSL ℝ u
  have hLnorm : ‖L‖ = 1 := by
    simp [L, innerSL_apply_norm, hu]
  have hL : L ≠ 0 := by
    intro hzero
    have : ‖L‖ = 0 := by rw [hzero, norm_zero]
    linarith
  have hsubset : {x : EuclideanSpace ℂ ι | ‖Kᗮ.starProjection x‖ < r} ⊆
      L ⁻¹' Ioo (-r) r := by
    intro x hx
    have hinnerC : ⟪u, x⟫_ℂ = ⟪u, Kᗮ.starProjection x⟫_ℂ := by
      calc
        ⟪u, x⟫_ℂ = ⟪Kᗮ.starProjection u, x⟫_ℂ := by
          rw [Kᗮ.starProjection_eq_self_iff.mpr huK]
        _ = ⟪u, Kᗮ.starProjection x⟫_ℂ :=
          Kᗮ.inner_starProjection_left_eq_right u x
    have hinnerR : ⟪u, x⟫_ℝ = ⟪u, Kᗮ.starProjection x⟫_ℝ := by
      have hre (z : ℂ) : RCLike.re z = z.re := rfl
      simpa only [PiLp.inner_apply, Complex.inner, RCLike.inner_apply, map_sum,
        RCLike.reCLM_apply, hre] using
        congrArg (RCLike.reCLM : ℂ →L[ℝ] ℝ) hinnerC
    have habs : |L x| < r := by
      change |⟪u, x⟫_ℝ| < r
      rw [hinnerR]
      calc
        |⟪u, Kᗮ.starProjection x⟫_ℝ| ≤ ‖u‖ * ‖Kᗮ.starProjection x‖ :=
          abs_real_inner_le_norm _ _
        _ = ‖Kᗮ.starProjection x‖ := by rw [hu, one_mul]
        _ < r := hx
    exact abs_lt.mp habs
  calc
    stdGaussian (EuclideanSpace ℂ ι)
        {x | ‖Kᗮ.starProjection x‖ < r} ≤
        stdGaussian (EuclideanSpace ℂ ι) (L ⁻¹' Ioo (-r) r) :=
      measure_mono hsubset
    _ ≤ gaussianPeak ((‖L‖ ^ 2).toNNReal) * ENNReal.ofReal (2 * r) := by
      simpa only [zero_sub, zero_add] using stdGaussian_linear_Ioo_le L hL 0 r hr
    _ = gaussianPeak 1 * ENNReal.ofReal (2 * r) := by simp [hLnorm]

/-- Translation-uniform version of the complex subspace small-ball bound.
The deterministic center is arbitrary; only the fresh Gaussian direction is
used in the proof. -/
theorem stdGaussian_complexSubspace_shift_smallBall
    {ι : Type*} [Fintype ι]
    (K : Submodule ℂ (EuclideanSpace ℂ ι)) (hK : K ≠ ⊤)
    (b : EuclideanSpace ℂ ι) (r : ℝ) (hr : 0 ≤ r) :
    stdGaussian (EuclideanSpace ℂ ι)
        {x | ‖Kᗮ.starProjection (b + x)‖ < r} ≤
      gaussianPeak 1 * ENNReal.ofReal (2 * r) := by
  have horth : Kᗮ ≠ ⊥ := by
    intro hbot
    exact hK (Submodule.orthogonal_eq_bot_iff.mp hbot)
  obtain ⟨u₀, hu₀K, hu₀⟩ := (Submodule.ne_bot_iff Kᗮ).mp horth
  let u : EuclideanSpace ℂ ι := ((‖u₀‖⁻¹ : ℝ) : ℂ) • u₀
  have huK : u ∈ Kᗮ := Kᗮ.smul_mem ((‖u₀‖⁻¹ : ℝ) : ℂ) hu₀K
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, hu₀]
  let L : StrongDual ℝ (EuclideanSpace ℂ ι) := innerSL ℝ u
  have hLnorm : ‖L‖ = 1 := by
    simp [L, innerSL_apply_norm, hu]
  have hL : L ≠ 0 := by
    intro hzero
    have : ‖L‖ = 0 := by rw [hzero, norm_zero]
    linarith
  have hsubset :
      {x : EuclideanSpace ℂ ι | ‖Kᗮ.starProjection (b + x)‖ < r} ⊆
        L ⁻¹' Ioo (-L b - r) (-L b + r) := by
    intro x hx
    have hinnerC : ⟪u, b + x⟫_ℂ =
        ⟪u, Kᗮ.starProjection (b + x)⟫_ℂ := by
      calc
        ⟪u, b + x⟫_ℂ = ⟪Kᗮ.starProjection u, b + x⟫_ℂ := by
          rw [Kᗮ.starProjection_eq_self_iff.mpr huK]
        _ = ⟪u, Kᗮ.starProjection (b + x)⟫_ℂ :=
          Kᗮ.inner_starProjection_left_eq_right u (b + x)
    have hinnerR : ⟪u, b + x⟫_ℝ =
        ⟪u, Kᗮ.starProjection (b + x)⟫_ℝ := by
      have hre (z : ℂ) : RCLike.re z = z.re := rfl
      simpa only [PiLp.inner_apply, Complex.inner, RCLike.inner_apply, map_sum,
        RCLike.reCLM_apply, hre] using
        congrArg (RCLike.reCLM : ℂ →L[ℝ] ℝ) hinnerC
    have habs : |L b + L x| < r := by
      change |⟪u, b⟫_ℝ + ⟪u, x⟫_ℝ| < r
      rw [← inner_add_right, hinnerR]
      calc
        |⟪u, Kᗮ.starProjection (b + x)⟫_ℝ| ≤
            ‖u‖ * ‖Kᗮ.starProjection (b + x)‖ :=
          abs_real_inner_le_norm _ _
        _ = ‖Kᗮ.starProjection (b + x)‖ := by rw [hu, one_mul]
        _ < r := hx
    change -L b - r < L x ∧ L x < -L b + r
    rcases abs_lt.mp habs with ⟨hlower, hupper⟩
    constructor <;> linarith
  calc
    stdGaussian (EuclideanSpace ℂ ι)
        {x | ‖Kᗮ.starProjection (b + x)‖ < r} ≤
        stdGaussian (EuclideanSpace ℂ ι)
          (L ⁻¹' Ioo (-L b - r) (-L b + r)) := measure_mono hsubset
    _ ≤ gaussianPeak ((‖L‖ ^ 2).toNNReal) * ENNReal.ofReal (2 * r) := by
      simpa only using stdGaussian_linear_Ioo_le L hL (-L b) r hr
    _ = gaussianPeak 1 * ENNReal.ofReal (2 * r) := by simp [hLnorm]

/-- Translation- and scale-uniform subspace small-ball bound.  This is the
one-column input for smoothed analysis of `M + ρ G`. -/
theorem stdGaussian_complexSubspace_shift_scale_smallBall
    {ι : Type*} [Fintype ι]
    (K : Submodule ℂ (EuclideanSpace ℂ ι)) (hK : K ≠ ⊤)
    (b : EuclideanSpace ℂ ι) (ρ r : ℝ) (hρ : 0 < ρ) (hr : 0 ≤ r) :
    stdGaussian (EuclideanSpace ℂ ι)
        {x | ‖Kᗮ.starProjection (b + (ρ : ℂ) • x)‖ < r} ≤
      gaussianPeak 1 * ENNReal.ofReal (2 * (r / ρ)) := by
  have hevent :
      {x : EuclideanSpace ℂ ι |
          ‖Kᗮ.starProjection (b + (ρ : ℂ) • x)‖ < r} =
        {x | ‖Kᗮ.starProjection (((ρ⁻¹ : ℝ) : ℂ) • b + x)‖ < r / ρ} := by
    ext x
    have hfactor : b + (ρ : ℂ) • x =
        (ρ : ℂ) • (((ρ⁻¹ : ℝ) : ℂ) • b + x) := by
      rw [smul_add, smul_smul]
      simp [hρ.ne']
    change (‖Kᗮ.starProjection (b + (ρ : ℂ) • x)‖ < r ↔
      ‖Kᗮ.starProjection (((ρ⁻¹ : ℝ) : ℂ) • b + x)‖ < r / ρ)
    rw [hfactor, map_smul, norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    simpa [mul_comm] using (lt_div_iff₀ hρ).symm
  rw [hevent]
  exact stdGaussian_complexSubspace_shift_smallBall K hK
    (((ρ⁻¹ : ℝ) : ℂ) • b) (r / ρ) (div_nonneg hr hρ.le)

end GinibreLSV

