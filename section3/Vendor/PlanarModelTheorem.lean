/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/PlanarModelTheorem.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.PlanarNormalTheorem
import Vendor.MatrixGeometry
import Vendor.LSVAssembly

/-! Main least-singular-value theorem for the actual independent complex-entry band model.
There is no small-ball, conditional-density, normal-net, or GBL hypothesis in this theorem. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace HighBandLSV

theorem planar_model_lsv_of_numerics
    {n W : Nat} {c C L kappa R Kz A C1 Cw : Real}
    (m : PlanarBandModel (n + 1 : Nat) W c C L)
    (hseed : 8 ≤ seedSize (n + 1 : Nat) W)
    (num : NumericalCertificate (n + 1 : Nat) (blockCount (n + 1 : Nat) W) (retainedRows (n + 1 : Nat) W)
      W kappa R Kz A C1 (1 / (64 * Cw)) Cw)
    (entropy : CorrectedSection5NumericalConditions (n + 1 : Nat) W kappa
      (blockCount (n + 1 : Nat) W) 28 (1 / (64 * Cw)))
    (gap : Real.log (dimensionLossColumnPrefactor (n + 1 : Nat) W) ≤
      Section5Formalization.finalExponentGap (n + 1 : Nat) W kappa)
    (hc : 0 < c) (hL : 0 ≤ L) (hA25 : 25 ≤ A) (hA : Real.pi * L / c ≤ A)
    (hC1 : 2 ≤ C1) (z : Complex) (hz : ‖z‖ ≤ Kz) (t : Real) (ht : 0 ≤ t) :
    m.law (leastSingularBadEvent (fun omega => shifted (m.matrix omega) z)
      (tau (n + 1 : Nat) W kappa t) ∩ hsEvent m.matrix R) ≤
      ENNReal.ofReal (Real.sqrt (Real.pi * L / c) * t) +
        ENNReal.ofReal (Real.exp (-((n + 1 : Nat) : Real) ^ (1 + kappa / 4))) := by
  classical
  let p := ModelPartition.actual hseed
  let d := delta (n + 1 : Nat) W kappa
  let s := tau (n + 1 : Nat) W kappa t * Real.sqrt (n + 1 : Nat)
  let D := Real.sqrt (Real.pi * L / c)
  let B := ModelPartition.columnBlock hseed
  let good : Set (MatrixSample (n + 1 : Nat)) :=
    (fun omega => shifted (m.matrix omega) z) ⁻¹' NormalNetEvents.normalSpread p d
  let cap : Set (MatrixSample (n + 1 : Nat)) :=
    (fun omega => shifted (m.matrix omega) z) ⁻¹' NormalNetEvents.columnCap (hsCap (n + 1 : Nat) R Kz)
  have hW : 0 < W := by exact_mod_cast num.entropy.W_pos
  have hd : 0 < d := delta_pos _ _ _
  have hratio : 0 ≤ tau (n + 1 : Nat) W kappa t / d := by
    dsimp [d]
    rw [threshold_ratio]
    positivity
  have htau : 0 ≤ tau (n + 1 : Nat) W kappa t := by
    have hm := mul_nonneg hratio hd.le
    simpa only [div_mul_cancel₀ _ hd.ne'] using hm
  have hs : 0 ≤ s := mul_nonneg htau (Real.sqrt_nonneg _)
  have hgood : good ⊆ m.goodNormalEvent z B d := by
    intro omega homega j
    exact homega j (Classical.choose (p.cover j))
  have hcap : hsEvent m.matrix R ⊆ cap := by
    intro omega homega j
    exact MatrixGeometry.hs_cutoff_column_bound (m.matrix omega) z homega hz j
  have hbad : m.law (cap \ good) ≤
      ENNReal.ofReal (Real.exp (-((n + 1 : Nat) : Real) ^ (1 + kappa / 4))) := by
    exact planar_bad_normals_from_numerics m p (ModelPartition.local_band hseed)
      (ModelPartition.retained_rows_fit hseed) num entropy hc hL hA25 hA hC1 z
  have hcol : ∀ j, m.law (closedColumnEvent (fun omega => shifted (m.matrix omega) z) s j ∩ good) ≤
      ENNReal.ofReal (D * Real.sqrt (n + 1 : Nat) * Real.sqrt W * s / d) := by
    intro j
    have hb := m.column_distance_small_ball hL hc hW z B
      (ModelPartition.columnBlock_local hseed) hd hs j
    have hlin : min 1 (Real.pi * (((n + 1 : Nat) : Real) * L / (c / W * d ^ 2)) * s ^ 2) ≤
        D * Real.sqrt (n + 1 : Nat) * Real.sqrt W * s / d := by
      dsimp [D]
      exact QuadraticLinearization.planar_column_linearization (n + 1 : Nat) W hc hW hL hd hs
    calc
      m.law (closedColumnEvent (fun omega => shifted (m.matrix omega) z) s j ∩ good) ≤
          m.law (closedColumnEvent (fun omega => shifted (m.matrix omega) z) s j ∩
            m.goodNormalEvent z B d) := measure_mono (Set.inter_subset_inter_right _ hgood)
      _ ≤ ENNReal.ofReal (min 1 (Real.pi *
          (((n + 1 : Nat) : Real) * L / (c / W * d ^ 2)) * s ^ 2)) := hb
      _ ≤ ENNReal.ofReal (D * Real.sqrt (n + 1 : Nat) * Real.sqrt W * s / d) :=
        ENNReal.ofReal_le_ofReal hlin
  have hsum := dimension_loss_column_union_bound
    (by positivity : (0 : Real) < (n + 1 : Nat)) num.entropy.W_pos ht (Real.sqrt_nonneg (Real.pi * L / c)) gap
  calc
    m.law (leastSingularBadEvent (fun omega => shifted (m.matrix omega) z)
        (tau (n + 1 : Nat) W kappa t) ∩ hsEvent m.matrix R) ≤
        ENNReal.ofReal (((n + 1 : Nat) : Real) *
          (D * Real.sqrt (n + 1 : Nat) * Real.sqrt W * s / d)) +
        ENNReal.ofReal (Real.exp (-((n + 1 : Nat) : Real) ^ (1 + kappa / 4))) :=
      lsv_probability_from_cover (by omega) m.law m.matrix z R (tau (n + 1 : Nat) W kappa t)
        _ _ good cap hcap hbad hcol
    _ ≤ ENNReal.ofReal (Real.sqrt (Real.pi * L / c) * t) +
        ENNReal.ofReal (Real.exp (-((n + 1 : Nat) : Real) ^ (1 + kappa / 4))) :=
      add_le_add (ENNReal.ofReal_le_ofReal hsum) le_rfl

/-- Uniform in the bounded spectral parameter and in the small-ball parameter.
Every numerical and probabilistic interface is discharged from the actual model. -/
theorem eventually_planar_band_lsv
    {c C L chi kappa R Kz Cw : Real}
    (hc : 0 < c) (hL : 0 ≤ L) (hchi : 0 < chi) (hk : 0 < kappa)
    (hR : 0 ≤ R) (hKz : 0 ≤ Kz) (hCw : 1 ≤ Cw)
    (W : Nat → Nat) (m : (n : Nat) → PlanarBandModel n (W n) c C L)
    (hWp : ∀ᶠ n : Nat in atTop, 0 < W n)
    (hband : ∀ᶠ n : Nat in atTop, (n : Real) ^ (1 / 2 + chi) ≤ W n)
    (hupper : ∀ᶠ n : Nat in atTop, (W n : Real) ≤ Cw * n) :
    ∀ᶠ n : Nat in atTop, ∀ z : Complex, ‖z‖ ≤ Kz → ∀ t : Real, 0 ≤ t →
      (m n).law (leastSingularBadEvent (fun omega => shifted ((m n).matrix omega) z)
        (tau n (W n) kappa t) ∩ hsEvent (m n).matrix R) ≤
        ENNReal.ofReal (Real.sqrt (Real.pi * L / c) * t) +
          ENNReal.ofReal (Real.exp (-(n : Real) ^ (1 + kappa / 4))) := by
  let A := 25 + Real.pi * L / c
  have hbase : 0 ≤ Real.pi * L / c := by positivity
  have hA25 : 25 ≤ A := by dsimp [A]; linarith
  have hA : Real.pi * L / c ≤ A := by dsimp [A]; linarith
  have hAp : 0 < A := by linarith
  have hn := eventually_model_numerics hchi hk hR hKz hAp
    (by norm_num : (0 : Real) < 64) hCw W hWp hband hupper
  filter_upwards [hn] with N hN
  intro z hz t ht
  cases N with
  | zero => have h := hN.2.1.N_pos; omega
  | succ n =>
      exact planar_model_lsv_of_numerics (m (n + 1 : Nat)) hN.1 hN.2.1 hN.2.2.1 hN.2.2.2
        hc hL hA25 hA (by norm_num) z hz t ht

end HighBandLSV

#print axioms HighBandLSV.planar_model_lsv_of_numerics
#print axioms HighBandLSV.eventually_planar_band_lsv

