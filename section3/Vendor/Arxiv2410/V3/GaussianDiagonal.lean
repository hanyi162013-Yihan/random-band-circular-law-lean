/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/GaussianDiagonal.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.DiagonalCorrection
import Vendor.Arxiv2410.V3.TraceMeasurability
import Vendor.Arxiv2410.V3.VarianceProfile
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-!
# Gaussian diagonal correction in v3 Proposition 3.4

This file formalizes the Gaussian maximum estimate used in proof step (4) of
arXiv:2410.16457v3, Proposition 3.4.  In the notation of that proof,
`D = X - Xᵒ = diag(d)` and

`Δ = hermitization X z - hermitization Xᵒ z = [[0,D],[Dᴴ,0]]`.

The proof below derives the required first-moment estimate from the actual
one-dimensional Gaussian laws.  It does not assume a Gaussian-maximal or
`L¹` estimate as an external input, and it does not require independence of
the diagonal coordinates.
-/

namespace ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- A centered real Gaussian with variance at most `c` has sub-Gaussian MGF
with proxy `c`. -/
theorem HasGaussianLaw.hasSubgaussianMGF_of_integral_eq_zero_of_variance_le
    {X : Omega → ℝ} {c : ℝ≥0}
    (hG : HasGaussianLaw X mu)
    (hmean : ∫ omega, X omega ∂mu = 0)
    (hvar : Var[X; mu] ≤ c) :
    HasSubgaussianMGF X c mu := by
  rw [← Function.id_comp X]
  apply HasSubgaussianMGF.of_map hG.aemeasurable
  rw [hG.map_eq_gaussianReal, hmean]
  constructor
  · intro t
    exact integrable_exp_mul_gaussianReal t
  · intro t
    rw [mgf_id_gaussianReal]
    apply Real.exp_le_exp.mpr
    have hv0 : 0 ≤ Var[X; mu] := variance_nonneg X mu
    simp only [zero_mul, zero_add]
    rw [Real.coe_toNNReal _ hv0]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hvar (sq_nonneg t)) (by norm_num)

end ProbabilityTheory

namespace Arxiv2410V3

open scoped BigOperators

variable {Omega I : Type*} [MeasurableSpace Omega]
  {mu : Measure Omega} [IsProbabilityMeasure mu] [Fintype I] [Nonempty I]

omit [IsProbabilityMeasure mu] [Fintype I] [Nonempty I] in
private theorem integrable_finset_sup'
    {s : Finset I} (hs : s.Nonempty) {X : I → Omega → ℝ}
    (hX : ∀ i ∈ s, Integrable (X i) mu) :
    Integrable (fun omega ↦ s.sup' hs (fun i ↦ X i omega)) mu := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert i s hi ih =>
      by_cases hs' : s.Nonempty
      · simp_rw [Finset.sup'_insert hs']
        exact (hX i (by simp)).sup
          (ih hs' (fun j hj ↦ hX j (Finset.mem_insert_of_mem hj)))
      · rw [Finset.not_nonempty_iff_eq_empty] at hs'
        subst s
        simpa using hX i (by simp)

/-- Expected maximum of a finite family of centered sub-Gaussians, proved by
the exponential-moment/log-sum-exp argument. No independence is required. -/
theorem integral_fintype_sup_le_of_hasSubgaussianMGF
    (X : I → Omega → ℝ) {c : ℝ≥0}
    (hX : ∀ i, HasSubgaussianMGF (X i) c mu)
    {t : ℝ} (ht : 0 < t) :
    (∫ omega, Finset.univ.sup' Finset.univ_nonempty
        (fun i ↦ X i omega) ∂mu) ≤
      Real.log (Fintype.card I) / t + (c : ℝ) * t / 2 := by
  let M : Omega → ℝ := fun omega ↦
    Finset.univ.sup' Finset.univ_nonempty (fun i ↦ X i omega)
  have hMint : Integrable M mu :=
    integrable_finset_sup' Finset.univ_nonempty
      (fun i _ ↦ (hX i).integrable)
  have hsumint : Integrable (fun omega ↦ ∑ i : I, Real.exp (t * X i omega)) mu := by
    exact integrable_finsetSum Finset.univ
      (fun i _ ↦ (hX i).integrable_exp_mul t)
  have hexpM_le (omega : Omega) :
      Real.exp (t * M omega) ≤ ∑ i : I, Real.exp (t * X i omega) := by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup'
      Finset.univ_nonempty (fun i ↦ X i omega)
    change Real.exp (t * Finset.univ.sup' Finset.univ_nonempty
      (fun i ↦ X i omega)) ≤ _
    rw [hi]
    exact Finset.single_le_sum
      (f := fun j ↦ Real.exp (t * X j omega))
      (fun _ _ ↦ (Real.exp_pos _).le)
      (Finset.mem_univ i)
  have hexpMint : Integrable (fun omega ↦ Real.exp (t * M omega)) mu := by
    apply hsumint.mono
    · fun_prop
    · filter_upwards [] with omega
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ (Real.exp_pos _).le)]
        using hexpM_le omega
  let tM : Omega → ℝ := fun omega ↦ t * M omega
  have htMint : Integrable tM mu := hMint.const_mul t
  have hJensen :
      Real.exp (∫ omega, tM omega ∂mu) ≤
        ∫ omega, Real.exp (tM omega) ∂mu := by
    exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (by simp) htMint hexpMint
  have hmoment :
      (∫ omega, Real.exp (tM omega) ∂mu) ≤
        (Fintype.card I : ℝ) * Real.exp ((c : ℝ) * t ^ 2 / 2) := by
    calc
      (∫ omega, Real.exp (tM omega) ∂mu) ≤
          ∫ omega, ∑ i : I, Real.exp (t * X i omega) ∂mu :=
        integral_mono hexpMint hsumint hexpM_le
      _ = ∑ i : I, ∫ omega, Real.exp (t * X i omega) ∂mu := by
        rw [integral_finsetSum]
        exact fun i _ ↦ (hX i).integrable_exp_mul t
      _ ≤ ∑ _i : I, Real.exp ((c : ℝ) * t ^ 2 / 2) := by
        exact Finset.sum_le_sum fun i _ ↦ (hX i).mgf_le t
      _ = (Fintype.card I : ℝ) * Real.exp ((c : ℝ) * t ^ 2 / 2) := by
        simp
  have hcardpos : 0 < (Fintype.card I : ℝ) := by positivity
  have hExp :
      Real.exp (∫ omega, tM omega ∂mu) ≤
        Real.exp (Real.log (Fintype.card I) + (c : ℝ) * t ^ 2 / 2) := by
    calc
      Real.exp (∫ omega, tM omega ∂mu) ≤
          ∫ omega, Real.exp (tM omega) ∂mu := hJensen
      _ ≤ (Fintype.card I : ℝ) * Real.exp ((c : ℝ) * t ^ 2 / 2) := hmoment
      _ = Real.exp (Real.log (Fintype.card I) + (c : ℝ) * t ^ 2 / 2) := by
        rw [Real.exp_add, Real.exp_log hcardpos]
  have hlinear := Real.exp_le_exp.mp hExp
  rw [show (∫ omega, tM omega ∂mu) =
      t * ∫ omega, M omega ∂mu by
        exact integral_const_mul t M] at hlinear
  rw [show Real.log (Fintype.card I) / t + (c : ℝ) * t / 2 =
      (Real.log (Fintype.card I) + (c : ℝ) * t ^ 2 / 2) / t by
        field_simp]
  exact (le_div_iff₀ ht).2 (by simpa [mul_comm] using hlinear)

end Arxiv2410V3

namespace Arxiv2410V3


open Matrix Complex MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The four signed real coordinates used to dominate the modulus of a
complex variable: `re`, `-re`, `im`, `-im`. -/
def signedReImCoordinate {Omega : Type*} {n : ℕ}
    (d : Fin n → Omega → ℂ) (k : Fin n × Bool × Bool) (omega : Omega) : ℝ :=
  let x := if k.2.1 then (d k.1 omega).im else (d k.1 omega).re
  if k.2.2 then -x else x

theorem hasSubgaussianMGF_signedReImCoordinate
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {n : ℕ} (d : Fin n → Omega → ℂ) {c : ℝ≥0}
    (hre : ∀ i, HasSubgaussianMGF (fun omega ↦ (d i omega).re) c mu)
    (him : ∀ i, HasSubgaussianMGF (fun omega ↦ (d i omega).im) c mu)
    (k : Fin n × Bool × Bool) :
    HasSubgaussianMGF (signedReImCoordinate d k) c mu := by
  rcases k with ⟨i, b, s⟩
  cases b <;> cases s
  · change HasSubgaussianMGF (fun omega ↦ (d i omega).re) c mu
    exact hre i
  · change HasSubgaussianMGF (- fun omega ↦ (d i omega).re) c mu
    exact (hre i).neg
  · change HasSubgaussianMGF (fun omega ↦ (d i omega).im) c mu
    exact him i
  · change HasSubgaussianMGF (- fun omega ↦ (d i omega).im) c mu
    exact (him i).neg

theorem norm_pi_le_two_mul_signedReImSup
    {Omega : Type*} {n : ℕ} [NeZero n]
    (d : Fin n → Omega → ℂ) (omega : Omega) :
    ‖fun i ↦ d i omega‖ ≤
      2 * Finset.univ.sup' Finset.univ_nonempty
        (fun k : Fin n × Bool × Bool ↦ signedReImCoordinate d k omega) := by
  let M := Finset.univ.sup' Finset.univ_nonempty
    (fun k : Fin n × Bool × Bool ↦ signedReImCoordinate d k omega)
  have hle (k : Fin n × Bool × Bool) :
      signedReImCoordinate d k omega ≤ M := by
    exact Finset.le_sup' (fun k : Fin n × Bool × Bool ↦
      signedReImCoordinate d k omega) (Finset.mem_univ k)
  have hM0 : 0 ≤ M := by
    let i : Fin n := Classical.choice inferInstance
    have hp := hle (i, false, false)
    have hn := hle (i, false, true)
    change (d i omega).re ≤ M at hp
    change -(d i omega).re ≤ M at hn
    linarith
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) hM0)).2
  intro i
  have hrePos := hle (i, false, false)
  have hreNeg := hle (i, false, true)
  have himPos := hle (i, true, false)
  have himNeg := hle (i, true, true)
  change (d i omega).re ≤ M at hrePos
  change -(d i omega).re ≤ M at hreNeg
  change (d i omega).im ≤ M at himPos
  change -(d i omega).im ≤ M at himNeg
  calc
    ‖d i omega‖ ≤ |(d i omega).re| + |(d i omega).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ M + M := by
      gcongr <;> rw [abs_le] <;> constructor <;> linarith
    _ = 2 * M := by ring

/-- Fully proved complex Gaussian maximum estimate at arbitrary exponential
parameter `t`. This is the probabilistic core of v3 proof step (4). -/
theorem integral_norm_pi_le_of_re_im_hasSubgaussianMGF
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {n : ℕ} [NeZero n]
    (d : Fin n → Omega → ℂ) {c : ℝ≥0}
    (hre : ∀ i, HasSubgaussianMGF (fun omega ↦ (d i omega).re) c mu)
    (him : ∀ i, HasSubgaussianMGF (fun omega ↦ (d i omega).im) c mu)
    {t : ℝ} (ht : 0 < t) :
    (∫ omega, ‖fun i ↦ d i omega‖ ∂mu) ≤
      2 * (Real.log (4 * n) / t + (c : ℝ) * t / 2) := by
  let M : Omega → ℝ := fun omega ↦
    Finset.univ.sup' Finset.univ_nonempty
      (fun k : Fin n × Bool × Bool ↦ signedReImCoordinate d k omega)
  have hMInt : Integrable M mu :=
    integrable_finset_sup' Finset.univ_nonempty
      (fun k _ ↦ (hasSubgaussianMGF_signedReImCoordinate d hre him k).integrable)
  have hdInt : Integrable (fun omega i ↦ d i omega) mu := by
    apply Integrable.of_eval
    intro i
    exact Integrable.re_im_iff.mp ⟨(hre i).integrable, (him i).integrable⟩
  have hnormInt : Integrable (fun omega ↦ ‖fun i ↦ d i omega‖) mu := hdInt.norm
  calc
    (∫ omega, ‖fun i ↦ d i omega‖ ∂mu) ≤
        ∫ omega, 2 * M omega ∂mu :=
      integral_mono hnormInt (hMInt.const_mul 2)
        (norm_pi_le_two_mul_signedReImSup d)
    _ = 2 * ∫ omega, M omega ∂mu := integral_const_mul 2 M
    _ ≤ 2 * (Real.log (4 * n) / t + (c : ℝ) * t / 2) := by
      gcongr
      simpa [M, mul_comm] using
        (integral_fintype_sup_le_of_hasSubgaussianMGF
          (fun k : Fin n × Bool × Bool ↦ signedReImCoordinate d k)
          (fun k ↦ hasSubgaussianMGF_signedReImCoordinate d hre him k) ht)

/-- The v3 scale for a diagonal complex Gaussian family. If every real and
imaginary coordinate is centered Gaussian with variance at most `2 / B`, then
for `n ≥ 2` the expected sup norm is at most
`8 * sqrt(log n) / sqrt B`. The numerical constant is deliberately explicit. -/
theorem integral_norm_pi_le_eight_mul_sqrt_log_div_sqrt
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {n : ℕ} (hn : 2 ≤ n)
    (d : Fin n → Omega → ℂ) {B : ℝ} (hB : 0 < B)
    (hreG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).re) mu)
    (himG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).im) mu)
    (hreMean : ∀ i, ∫ omega, (d i omega).re ∂mu = 0)
    (himMean : ∀ i, ∫ omega, (d i omega).im ∂mu = 0)
    (hreVar : ∀ i, Var[fun omega ↦ (d i omega).re; mu] ≤ 2 / B)
    (himVar : ∀ i, Var[fun omega ↦ (d i omega).im; mu] ≤ 2 / B) :
    (∫ omega, ‖fun i ↦ d i omega‖ ∂mu) ≤
      8 * Real.sqrt (Real.log (n : ℝ)) / Real.sqrt B := by
  let _ : NeZero n := ⟨by omega⟩
  let c : ℝ≥0 := ⟨2 / B, by positivity⟩
  have hre (i : Fin n) :
      HasSubgaussianMGF (fun omega ↦ (d i omega).re) c mu := by
    apply (hreG i).hasSubgaussianMGF_of_integral_eq_zero_of_variance_le
      (hreMean i)
    change Var[fun omega ↦ (d i omega).re; mu] ≤ 2 / B
    exact hreVar i
  have him (i : Fin n) :
      HasSubgaussianMGF (fun omega ↦ (d i omega).im) c mu := by
    apply (himG i).hasSubgaussianMGF_of_integral_eq_zero_of_variance_le
      (himMean i)
    change Var[fun omega ↦ (d i omega).im; mu] ≤ 2 / B
    exact himVar i
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnRpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  have hnRone : 1 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hnRone
  have hsqrtBpos : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have hsqrtLogpos : 0 < Real.sqrt (Real.log (n : ℝ)) :=
    Real.sqrt_pos.2 hlogpos
  let t := Real.sqrt B * Real.sqrt (Real.log (n : ℝ))
  have ht : 0 < t := mul_pos hsqrtBpos hsqrtLogpos
  have hraw := integral_norm_pi_le_of_re_im_hasSubgaussianMGF
    d hre him ht
  have hfour : (4 : ℝ) * n ≤ (n : ℝ) ^ 3 := by
    have hnonneg : 0 ≤ (n : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) + 2) := by positivity
    nlinarith
  have hlog4n : Real.log ((4 * n : ℕ) : ℝ) ≤ 3 * Real.log (n : ℝ) := by
    calc
      Real.log ((4 * n : ℕ) : ℝ) = Real.log ((4 : ℝ) * n) := by norm_num
      _ ≤ Real.log ((n : ℝ) ^ 3) := Real.log_le_log (by positivity) hfour
      _ = 3 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num
  have hsqrtBsq : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB.le
  have hsqrtLogsq : Real.sqrt (Real.log (n : ℝ)) ^ 2 = Real.log (n : ℝ) :=
    Real.sq_sqrt hlogpos.le
  have hfirst :
      Real.log ((4 * n : ℕ) : ℝ) / t ≤
        3 * Real.sqrt (Real.log (n : ℝ)) / Real.sqrt B := by
    apply (div_le_iff₀ ht).2
    calc
      Real.log ((4 * n : ℕ) : ℝ) ≤ 3 * Real.log (n : ℝ) := hlog4n
      _ = (3 * Real.sqrt (Real.log (n : ℝ)) / Real.sqrt B) * t := by
        dsimp [t]
        field_simp [hsqrtBpos.ne']
        nlinarith
  have hsecond : (c : ℝ) * t / 2 =
      Real.sqrt (Real.log (n : ℝ)) / Real.sqrt B := by
    change (2 / B) * t / 2 = _
    dsimp [t]
    field_simp [hB.ne', hsqrtBpos.ne']
    nlinarith [hsqrtBsq]
  have hsum :
      Real.log ((4 * n : ℕ) : ℝ) / t + (c : ℝ) * t / 2 ≤
        3 * Real.sqrt (Real.log (n : ℝ)) / Real.sqrt B +
          Real.sqrt (Real.log (n : ℝ)) / Real.sqrt B :=
    add_le_add hfirst hsecond.le
  calc
    (∫ omega, ‖fun i ↦ d i omega‖ ∂mu) ≤
        2 * (Real.log (4 * n) / t + (c : ℝ) * t / 2) := hraw
    _ ≤ 2 * (3 * Real.sqrt (Real.log (n : ℝ)) / Real.sqrt B +
        Real.sqrt (Real.log (n : ℝ)) / Real.sqrt B) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsum
    _ = 8 * Real.sqrt (Real.log (n : ℝ)) / Real.sqrt B := by ring

end Arxiv2410V3

namespace Arxiv2410V3

open Matrix Complex
open scoped Matrix.Norms.L2Operator

theorem hermitization_sub_of_sub_eq_diagonal {n : ℕ}
    (X Xo : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (d : Fin n → ℂ)
    (hdiag : X - Xo = Matrix.diagonal d) :
    hermitization X z - hermitization Xo z =
      Matrix.fromBlocks 0 (Matrix.diagonal d)
        (Matrix.diagonal d)ᴴ 0 := by
  have hshift : shiftedMatrix X z - shiftedMatrix Xo z = Matrix.diagonal d := by
    ext i j
    have hij := congrFun (congrFun hdiag i) j
    simpa [shiftedMatrix, Matrix.sub_apply] using hij
  simp only [hermitization]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp
  · have hij := congrFun (congrFun hshift i) j
    simpa [Matrix.sub_apply] using hij
  · have hij := congrFun (congrFun hshift j) i
    convert congrArg star hij using 1 <;>
      simp [Matrix.conjTranspose_apply, Matrix.sub_apply,
        Matrix.diagonal_apply, eq_comm]
    all_goals split_ifs with h <;> simp_all
  · simp

private def sumSwapPerm (n : ℕ) : Equiv.Perm (Fin n ⊕ Fin n) :=
  Equiv.sumComm (Fin n) (Fin n)

theorem fromBlocks_zero_diagonal_conjTranspose_norm_le {n : ℕ}
    (d : Fin n → ℂ) :
    ‖Matrix.fromBlocks 0 (Matrix.diagonal d)
        (Matrix.diagonal d)ᴴ 0‖ ≤ ‖d‖ := by
  let q : (Fin n ⊕ Fin n) → ℂ := Sum.elim (fun i ↦ star (d i)) d
  let P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    (sumSwapPerm n).permMatrix ℂ
  have hfactor :
      Matrix.fromBlocks 0 (Matrix.diagonal d) (Matrix.diagonal d)ᴴ 0 =
        P * Matrix.diagonal q := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [P, q, sumSwapPerm, Matrix.mul_apply, Equiv.toPEquiv,
        PEquiv.toMatrix, Matrix.diagonal_apply]
    all_goals split_ifs with h <;> simp_all
  rw [hfactor]
  calc
    ‖P * Matrix.diagonal q‖ ≤ ‖P‖ * ‖Matrix.diagonal q‖ :=
      Matrix.l2_opNorm_mul P (Matrix.diagonal q)
    _ ≤ 1 * ‖Matrix.diagonal q‖ := by
      gcongr
      exact Matrix.permMatrix_l2_opNorm_le (sumSwapPerm n)
    _ = ‖q‖ := by simp
    _ ≤ ‖d‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg d)).2
      intro i
      rcases i with i | i <;> simp [q, norm_le_pi_norm]

theorem norm_hermitization_sub_le_pi_norm_of_sub_eq_diagonal {n : ℕ}
    (X Xo : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (d : Fin n → ℂ)
    (hdiag : X - Xo = Matrix.diagonal d) :
    ‖hermitization X z - hermitization Xo z‖ ≤ ‖d‖ := by
  rw [hermitization_sub_of_sub_eq_diagonal X Xo z d hdiag]
  exact fromBlocks_zero_diagonal_conjTranspose_norm_le d

end Arxiv2410V3


namespace Arxiv2410V3

open Matrix Complex MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

local instance gaussianDiagonalMatrixMeasurableSpace {m n : Type*} :
    MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

local instance gaussianDiagonalMatrixBorelSpace
    {m n : Type*} [Countable m] [Countable n] :
    BorelSpace (Matrix m n ℂ) :=
  inferInstanceAs (BorelSpace (m → n → ℂ))

section GaussianDiagonalCorrection

variable {Omega : Type*} [MeasurableSpace Omega]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  {n : ℕ}

omit [IsProbabilityMeasure mu] in
/-- Integrability needed in v3 Proposition 3.4, proof step (4): the norm of
the actual Hermitization correction `Δ` is integrable whenever the real and
imaginary parts of its diagonal coordinates have Gaussian laws. -/
theorem integrable_norm_hermitization_diagonal_difference
    (X Xo : Omega → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → Omega → ℂ) (z : ℂ)
    (hX : ∀ i j, Measurable (fun omega ↦ X omega i j))
    (hXo : ∀ i j, Measurable (fun omega ↦ Xo omega i j))
    (hdiag : ∀ omega,
      X omega - Xo omega = Matrix.diagonal (fun i ↦ d i omega))
    (hreG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).re) mu)
    (himG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).im) mu) :
    Integrable (fun omega ↦
      ‖hermitization (X omega) z - hermitization (Xo omega) z‖) mu := by
  have hdInt : Integrable (fun omega i ↦ d i omega) mu := by
    apply Integrable.of_eval
    intro i
    exact Integrable.re_im_iff.mp ⟨(hreG i).integrable, (himG i).integrable⟩
  have hdNormInt : Integrable (fun omega ↦ ‖fun i ↦ d i omega‖) mu := hdInt.norm
  have hHermX := measurable_hermitization hX z
  have hHermXo := measurable_hermitization hXo z
  have hDeltaMatrix : Measurable (fun omega ↦
      hermitization (X omega) z - hermitization (Xo omega) z) := by
    apply measurable_matrix_of_apply
    intro i j
    exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hHermX)).sub
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hHermXo))
  have hDeltaMeas : Measurable (fun omega ↦
      ‖hermitization (X omega) z - hermitization (Xo omega) z‖) :=
    hDeltaMatrix.norm
  refine hdNormInt.mono hDeltaMeas.aestronglyMeasurable ?_
  filter_upwards [] with omega
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    norm_hermitization_sub_le_pi_norm_of_sub_eq_diagonal
      (X omega) (Xo omega) z (fun i ↦ d i omega) (hdiag omega)

/-- v3 Proposition 3.4, proof step (4), Gaussian diagonal maximum estimate
at the Hermitization level:

`E ‖Δ‖ ≤ 8 sqrt(log n) / sqrt B`.

This theorem assumes only the concrete centered Gaussian laws and coordinate
variance bounds; it has no Gaussian-maximum or `L¹` hypothesis. -/
theorem integral_norm_hermitization_diagonal_gaussian_le_eight
    (X Xo : Omega → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → Omega → ℂ) (z : ℂ)
    (hn : 2 ≤ n) {B : ℝ} (hB : 0 < B)
    (hX : ∀ i j, Measurable (fun omega ↦ X omega i j))
    (hXo : ∀ i j, Measurable (fun omega ↦ Xo omega i j))
    (hdiag : ∀ omega,
      X omega - Xo omega = Matrix.diagonal (fun i ↦ d i omega))
    (hreG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).re) mu)
    (himG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).im) mu)
    (hreMean : ∀ i, ∫ omega, (d i omega).re ∂mu = 0)
    (himMean : ∀ i, ∫ omega, (d i omega).im ∂mu = 0)
    (hreVar : ∀ i, Var[fun omega ↦ (d i omega).re; mu] ≤ 2 / B)
    (himVar : ∀ i, Var[fun omega ↦ (d i omega).im; mu] ≤ 2 / B) :
    (∫ omega,
      ‖hermitization (X omega) z - hermitization (Xo omega) z‖ ∂mu) ≤
      8 * Real.sqrt (Real.log (n : ℝ)) / Real.sqrt B := by
  let _ : NeZero n := ⟨by omega⟩
  have hDeltaInt := integrable_norm_hermitization_diagonal_difference
    X Xo d z hX hXo hdiag hreG himG
  have hdInt : Integrable (fun omega i ↦ d i omega) mu := by
    apply Integrable.of_eval
    intro i
    exact Integrable.re_im_iff.mp ⟨(hreG i).integrable, (himG i).integrable⟩
  have hdNormInt : Integrable (fun omega ↦ ‖fun i ↦ d i omega‖) mu := hdInt.norm
  calc
    (∫ omega,
        ‖hermitization (X omega) z - hermitization (Xo omega) z‖ ∂mu) ≤
        ∫ omega, ‖fun i ↦ d i omega‖ ∂mu :=
      integral_mono hDeltaInt hdNormInt (fun omega ↦
        norm_hermitization_sub_le_pi_norm_of_sub_eq_diagonal
          (X omega) (Xo omega) z (fun i ↦ d i omega) (hdiag omega))
    _ ≤ 8 * Real.sqrt (Real.log (n : ℝ)) / Real.sqrt B :=
      integral_norm_pi_le_eight_mul_sqrt_log_div_sqrt
        hn d hB hreG himG hreMean himMean hreVar himVar

/-- A concrete construction of the former `L¹` input for v3 Proposition 3.4,
proof step (4).  The structure is now an output derived from Gaussian laws,
not an external assumption. -/
theorem gaussianDiagonalPseudovarianceL1Input_v3
    (X Xo : Omega → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → Omega → ℂ) (z : ℂ) {eta : ℂ} (heta : 0 < eta.im)
    (hn : 2 ≤ n) {B : ℝ} (hB : 0 < B)
    (hX : ∀ i j, Measurable (fun omega ↦ X omega i j))
    (hXo : ∀ i j, Measurable (fun omega ↦ Xo omega i j))
    (hdiag : ∀ omega,
      X omega - Xo omega = Matrix.diagonal (fun i ↦ d i omega))
    (hreG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).re) mu)
    (himG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).im) mu)
    (hreMean : ∀ i, ∫ omega, (d i omega).re ∂mu = 0)
    (himMean : ∀ i, ∫ omega, (d i omega).im ∂mu = 0)
    (hreVar : ∀ i, Var[fun omega ↦ (d i omega).re; mu] ≤ 2 / B)
    (himVar : ∀ i, Var[fun omega ↦ (d i omega).im; mu] ≤ 2 / B) :
    DiagonalPseudovarianceL1Input mu X Xo z eta
      (8 * Real.sqrt (Real.log (n : ℝ)) / Real.sqrt B) := by
  let _ : NeZero n := ⟨by omega⟩
  refine ⟨integrable_stieltjesTrace hX z heta,
    integrable_stieltjesTrace hXo z heta,
    integrable_norm_hermitization_diagonal_difference
      X Xo d z hX hXo hdiag hreG himG, ?_⟩
  exact integral_norm_hermitization_diagonal_gaussian_le_eight
    X Xo d z hn hB hX hXo hdiag hreG himG hreMean himMean hreVar himVar

/-- The strongest direct form of v3 Proposition 3.4, proof step (4):

`|E m_z^G(eta) - E m_z^{G,o}(eta)|
    ≤ 8 sqrt(log n) / (sqrt B * (Im eta)^2)`.

Unlike the compatibility theorem below, the conclusion is the trace-norm
inequality itself and mentions no external interface structure. -/
theorem norm_expected_stieltjesTrace_sub_le_of_gaussianDiagonal_v3
    (X Xo : Omega → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → Omega → ℂ) (z : ℂ) {eta : ℂ} (heta : 0 < eta.im)
    (hn : 2 ≤ n) {B : ℝ} (hB : 0 < B)
    (hX : ∀ i j, Measurable (fun omega ↦ X omega i j))
    (hXo : ∀ i j, Measurable (fun omega ↦ Xo omega i j))
    (hdiag : ∀ omega,
      X omega - Xo omega = Matrix.diagonal (fun i ↦ d i omega))
    (hreG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).re) mu)
    (himG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).im) mu)
    (hreMean : ∀ i, ∫ omega, (d i omega).re ∂mu = 0)
    (himMean : ∀ i, ∫ omega, (d i omega).im ∂mu = 0)
    (hreVar : ∀ i, Var[fun omega ↦ (d i omega).re; mu] ≤ 2 / B)
    (himVar : ∀ i, Var[fun omega ↦ (d i omega).im; mu] ≤ 2 / B) :
    ‖(∫ omega, stieltjesTrace (X omega) z eta ∂mu) -
        ∫ omega, stieltjesTrace (Xo omega) z eta ∂mu‖ ≤
      8 * Real.sqrt (Real.log (n : ℝ)) /
        (Real.sqrt B * eta.im ^ 2) := by
  let _ : NeZero n := ⟨by omega⟩
  let input := gaussianDiagonalPseudovarianceL1Input_v3
    X Xo d z heta hn hB hX hXo hdiag hreG himG
      hreMean himMean hreVar himVar
  calc
    ‖(∫ omega, stieltjesTrace (X omega) z eta ∂mu) -
        ∫ omega, stieltjesTrace (Xo omega) z eta ∂mu‖ ≤
        (8 * Real.sqrt (Real.log (n : ℝ)) / Real.sqrt B) / eta.im ^ 2 :=
      norm_expected_stieltjesTrace_sub_le_of_integral_hermitization_norm
        X Xo z heta input.trace_integrable input.circular_trace_integrable
          input.perturbation_norm_integrable input.perturbation_norm_mean_le
    _ = 8 * Real.sqrt (Real.log (n : ℝ)) /
        (Real.sqrt B * eta.im ^ 2) := by ring

/-- Compatibility name for the same direct v3 formula (3.11) inequality, with the Gaussian
input fully reconstructed:

`|E m_z^G(eta) - E m_z^{G,o}(eta)|
    ≤ 8 sqrt(log n) / (sqrt B * (Im eta)^2)`.

Only the two van Handel comparisons remain external to the surrounding argument. -/
theorem diagonalPseudovarianceCorrectionHypothesis_v3_of_gaussianDiagonal
    (X Xo : Omega → Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → Omega → ℂ) (z : ℂ) {eta : ℂ} (heta : 0 < eta.im)
    (hn : 2 ≤ n) {B : ℝ} (hB : 0 < B)
    (hX : ∀ i j, Measurable (fun omega ↦ X omega i j))
    (hXo : ∀ i j, Measurable (fun omega ↦ Xo omega i j))
    (hdiag : ∀ omega,
      X omega - Xo omega = Matrix.diagonal (fun i ↦ d i omega))
    (hreG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).re) mu)
    (himG : ∀ i, HasGaussianLaw (fun omega ↦ (d i omega).im) mu)
    (hreMean : ∀ i, ∫ omega, (d i omega).re ∂mu = 0)
    (himMean : ∀ i, ∫ omega, (d i omega).im ∂mu = 0)
    (hreVar : ∀ i, Var[fun omega ↦ (d i omega).re; mu] ≤ 2 / B)
    (himVar : ∀ i, Var[fun omega ↦ (d i omega).im; mu] ≤ 2 / B) :
    ‖(∫ omega, stieltjesTrace (X omega) z eta ∂mu) -
        ∫ omega, stieltjesTrace (Xo omega) z eta ∂mu‖ ≤
      8 * Real.sqrt (Real.log (n : ℝ)) /
        (Real.sqrt B * eta.im ^ 2) := by
  let _ : NeZero n := ⟨by omega⟩
  exact diagonalPseudovarianceCorrectionHypothesis_v3_of_l1Input
    X Xo z heta
    (gaussianDiagonalPseudovarianceL1Input_v3
      X Xo d z heta hn hB hX hXo hdiag hreG himG
      hreMean himMean hreVar himVar)

end GaussianDiagonalCorrection

end

end Arxiv2410V3

