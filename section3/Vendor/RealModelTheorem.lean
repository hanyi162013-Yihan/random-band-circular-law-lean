/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealModelTheorem.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RealNormalTheorem
import Vendor.RealLSVAssembly
import Vendor.ModelPartition

/-! Model-level high-band least-singular-value bounds for real entry laws. -/

noncomputable section
open MeasureTheory LivshytsProjectionFormalization
open scoped ENNReal
namespace HighBandLSV

theorem real_model_lsv_of_numerics
    {n W : Nat} {c C rho kappa R Kz A C1 Cw : Real}
    (m : RealBandModel (n + 1) W c C rho) (hGBL : RealFiniteGeometricBrascampLieb)
    (hseed : 8 ≤ seedSize (n + 1) W)
    (num : NumericalCertificate (n + 1) (blockCount (n + 1) W) (retainedRows (n + 1) W)
      W kappa R Kz A C1 (1 / (64 * Cw)) Cw)
    (entropy : CorrectedSection5NumericalConditions (n + 1 : Nat) W kappa
      (blockCount (n + 1) W) 28 (1 / (64 * Cw)))
    (gap : Real.log (dimensionLossColumnPrefactor (n + 1 : Nat) W) ≤
      Section5Formalization.finalExponentGap (n + 1 : Nat) W kappa)
    (hc : 0 < c) (hrho : 0 < rho) (hA : 1024 ≤ A)
    (hAone : 2 * (Real.exp 1 * rho) / Real.sqrt c ≤ A)
    (hAtwo : 8 * (Real.exp 1 * rho ^ 2) / c ≤ A)
    (hC1 : 4 ≤ C1) (hAC1 : 4 * C1 ≤ A)
    (z : Complex) (hz : ‖z‖ ≤ Kz) (t : Real) (ht : 0 ≤ t) :
    m.law (leastSingularBadEvent (fun omega => shifted (m.matrix omega) z)
        (tau (n + 1 : Nat) W kappa t) ∩ hsEvent m.matrix R) ≤
      ENNReal.ofReal ((2 * Real.sqrt 2 * Real.exp 1 * rho / Real.sqrt c) * t) +
        ENNReal.ofReal (Real.exp (-((n + 1 : Nat) : Real) ^ (1 + kappa / 4))) := by
  let p := ModelPartition.actual hseed
  let B := ModelPartition.columnBlock hseed
  let d := delta (n + 1 : Nat) W kappa
  let D := 2 * Real.sqrt 2 * Real.exp 1 * rho / Real.sqrt c
  have hd : 0 < d := delta_pos _ _ _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hW : 0 < W := by exact_mod_cast entropy.W_pos
  have hB : ∀ j i, i ∈ B j → Section5Formalization.cyclicDist (n + 1) i j ≤ W :=
    fun j i hi => ModelPartition.columnBlock_local hseed j i hi
  have hbadspread := real_bad_normals_from_numerics m hGBL p
    (ModelPartition.local_band hseed) (ModelPartition.retained_rows_fit hseed)
    num entropy hc hrho hA hAone hAtwo hC1 hAC1 z
  have hbad : m.law (hsEvent m.matrix R \ m.goodNormalEvent z B d) ≤
      ENNReal.ofReal (Real.exp (-((n + 1 : Nat) : Real) ^ (1 + kappa / 4))) := by
    apply (measure_mono ?_).trans hbadspread
    intro omega homega
    refine ⟨?_, ?_⟩
    · intro j
      exact MatrixGeometry.hs_cutoff_column_bound (m.matrix omega) z homega.1 hz j
    · intro hspread
      apply homega.2
      intro j
      exact hspread j (Classical.choose (p.cover j))
  have hratio : 0 ≤ tau (n + 1 : Nat) W kappa t / d := by
    dsimp [d]
    rw [threshold_ratio]
    positivity
  have htau : 0 ≤ tau (n + 1 : Nat) W kappa t := by
    have hm := mul_nonneg hratio hd.le
    simpa only [div_mul_cancel₀ _ hd.ne'] using hm
  have hroot : 1 ≤ Real.sqrt (n + 1 : Nat) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  have hDscale : D ≤ D * Real.sqrt (n + 1 : Nat) := by
    nlinarith [mul_nonneg hD (sub_nonneg.mpr hroot)]
  have hcolscale : D * Real.sqrt W *
      (tau (n + 1 : Nat) W kappa t * Real.sqrt (n + 1 : Nat)) / d ≤
      D * Real.sqrt (n + 1 : Nat) * Real.sqrt W *
        (tau (n + 1 : Nat) W kappa t * Real.sqrt (n + 1 : Nat)) / d :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hDscale (Real.sqrt_nonneg _))
        (mul_nonneg htau (Real.sqrt_nonneg _))) hd.le
  have hsum : ((n + 1 : Nat) : Real) *
      (D * Real.sqrt W * (tau (n + 1 : Nat) W kappa t * Real.sqrt (n + 1 : Nat)) / d) ≤ D * t := by
    apply (mul_le_mul_of_nonneg_left hcolscale (Nat.cast_nonneg (n + 1))).trans
    exact dimension_loss_column_union_bound (by exact_mod_cast num.N_pos)
      entropy.W_pos ht hD gap
  calc
    _ ≤ ENNReal.ofReal (((n + 1 : Nat) : Real) *
        (D * Real.sqrt W * (tau (n + 1 : Nat) W kappa t * Real.sqrt (n + 1 : Nat)) / d)) +
        ENNReal.ofReal (Real.exp (-((n + 1 : Nat) : Real) ^ (1 + kappa / 4))) :=
      real_lsv_from_bad_normals m hGBL hrho hc hW z B hB hd htau hbad
    _ ≤ _ := add_le_add (ENNReal.ofReal_le_ofReal hsum) le_rfl

/-- The full real-entry model theorem. The sole external analytic input is
the accepted real finite geometric Brascamp--Lieb inequality; its projection
density consequences and all random-matrix interfaces are proved here. -/
theorem eventually_real_band_lsv
    {c C rho chi kappa R Kz Cw : Real}
    (hGBL : RealFiniteGeometricBrascampLieb) (hc : 0 < c) (hrho : 0 < rho)
    (hchi : 0 < chi) (hk : 0 < kappa) (hR : 0 ≤ R) (hKz : 0 ≤ Kz) (hCw : 1 ≤ Cw)
    (W : Nat → Nat) (m : ∀ n, RealBandModel n (W n) c C rho)
    (hWp : ∀ᶠ (n : Nat) in Filter.atTop, 0 < W n)
    (hband : ∀ᶠ (n : Nat) in Filter.atTop, (n : Real) ^ (1 / 2 + chi) ≤ W n)
    (hupper : ∀ᶠ (n : Nat) in Filter.atTop, (W n : Real) ≤ Cw * n) :
    ∀ᶠ (n : Nat) in Filter.atTop, ∀ z : Complex, ‖z‖ ≤ Kz → ∀ t : Real, 0 ≤ t →
      (m n).law (leastSingularBadEvent (fun omega => shifted ((m n).matrix omega) z)
          (tau n (W n) kappa t) ∩ hsEvent (m n).matrix R) ≤
        ENNReal.ofReal ((2 * Real.sqrt 2 * Real.exp 1 * rho / Real.sqrt c) * t) +
          ENNReal.ofReal (Real.exp (-(n : Real) ^ (1 + kappa / 4))) := by
  let A := 1024 + 2 * (Real.exp 1 * rho) / Real.sqrt c + 8 * (Real.exp 1 * rho ^ 2) / c
  have hone0 : 0 ≤ 2 * (Real.exp 1 * rho) / Real.sqrt c := by positivity
  have htwo0 : 0 ≤ 8 * (Real.exp 1 * rho ^ 2) / c := by positivity
  have hA : 1024 ≤ A := by dsimp [A]; linarith
  have hA0 : 0 < A := by linarith
  have hAone : 2 * (Real.exp 1 * rho) / Real.sqrt c ≤ A := by dsimp [A]; linarith
  have hAtwo : 8 * (Real.exp 1 * rho ^ 2) / c ≤ A := by dsimp [A]; linarith
  have he := eventually_model_numerics hchi hk hR hKz hA0
    (by norm_num : 0 < (64 : Real)) hCw W hWp hband hupper
  filter_upwards [he] with N hnum
  rcases hnum with ⟨hseed, num, entropy, gap⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt num.N_pos)
  intro z hz t ht
  exact real_model_lsv_of_numerics (m (n + 1)) hGBL hseed num entropy gap hc hrho
    hA hAone hAtwo (by norm_num) (by norm_num; linarith) z hz t ht

end HighBandLSV

#print axioms HighBandLSV.real_model_lsv_of_numerics
#print axioms HighBandLSV.eventually_real_band_lsv

