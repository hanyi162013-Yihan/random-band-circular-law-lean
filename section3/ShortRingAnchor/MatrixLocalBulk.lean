import ShortRingAnchor.MatrixStieltjesSmoothing
import Vendor.Arxiv2410.V3.FreeDysonExistence
import ShortRingAnchor.CompactStieltjesGoodEvent
import Vendor.Arxiv2410.V3.EtaUniformization

/-!
# Lemma 3.5: deterministic matrix estimates on a compact good event

These deterministic results do not assume a random-matrix comparison theorem.
The actual trace identity, finite net, free-transform bound and CDF smoothing
supply the compact estimate on the explicitly defined good event.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace ShortRingAnchor
open Arxiv2410V3

/-- Lemma 3.5: horizontal continuity of the actual normalized matrix trace. -/
theorem matrix_stieltjesTrace_horizontal_lipschitz {n : ℕ} [NeZero n]
    (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) {v : ℝ} (hv : 0 < v)
    (u w : ℝ) :
    ‖stieltjesTrace X z (spectralParameter u v) -
      stieltjesTrace X z (spectralParameter w v)‖ ≤ v⁻¹ ^ 2 * |u - w| := by
  have h := norm_stieltjesTrace_sub_eta_le_of_im_ge X z hv
    (show v ≤ (spectralParameter u v).im by simp [spectralParameter])
    (show v ≤ (spectralParameter w v).im by simp [spectralParameter])
  have hd : dist (spectralParameter u v) (spectralParameter w v) = |u - w| := by
    rw [dist_eq_norm]
    simp [spectralParameter, add_sub_add_right_eq_sub, ← Complex.ofReal_sub]
  simpa only [hd] using h

/-- Lemma 3.5: the concrete good event for the two actual matrices. -/
def matrixLocalBulkGood {Omega : Type*} {n : ℕ}
    (X Y : Omega → Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (v R d : ℝ) : Set Omega :=
  compactStieltjesGridGood
    (fun sample u => stieltjesTrace (X sample) z (spectralParameter u v))
    (fun sample u => stieltjesTrace (Y sample) z (spectralParameter u v))
    (fun u => freeDysonStieltjes z (spectralParameter u v)) n (R + 1) d

/-- Lemma 3.5: actual squared-singular-value CDF bound on the concrete
event, including zero singular values and every finite fixed shift. -/
theorem matrixLocalBulkGood_cdf_bound {Omega : Type*} {n : ℕ} (hn : 2 ≤ n)
    (X Y : Omega → Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) {v R d : ℝ} (hR : 0 ≤ R) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hvlower : (n : ℝ) ^ (-(1 / 8 : ℝ)) ≤ v)
    (hsmall : 3 * Real.sqrt v ≤ 1)
    {sample : Omega} (hgood : sample ∈ matrixLocalBulkGood X Y z v R d) :
    empiricalCdfDistanceOn 0 (R ^ 2)
      (fun i => shiftedSingularValueFamily (X sample) z i ^ 2)
      (fun i => shiftedSingularValueFamily (Y sample) z i ^ 2) ≤
        ((8 * R + 40) * (n : ℝ) ^ (-d) + 32 * Real.sqrt v) / Real.pi := by
  let _ : NeZero n := ⟨by omega⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hv : 0 < v := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hnR) _).trans_le hvlower
  have hL := inverse_height_sq_le_dimension hnR hvlower
  have hf := fun sample => matrix_stieltjesTrace_horizontal_lipschitz (X sample) z hv
  have hg := fun sample => matrix_stieltjesTrace_horizontal_lipschitz (Y sample) z hv
  have href : ∀ u, ‖freeDysonStieltjes z (spectralParameter u v)‖ ≤ 1 := by
    intro u
    exact (freeDysonStieltjes_norm_lt_one z _ (by simpa [spectralParameter] using hv)).le
  have hc (u : ℝ) (hu : u ∈ Icc (-(R + 1)) (R + 1)) :=
    compactStieltjesGridGood_comparison _ _ _ hnR (sq_nonneg _) hL hd1 hf hg hgood hu
  have hi (u : ℝ) (hu : u ∈ Icc (-(R + 1)) (R + 1)) :=
    compactStieltjesGridGood_reference_im_le_three _ _ _ hnR
      (sq_nonneg _) hL hd0 hd1 hg href hgood hu
  have h := matrix_squaredCdfDistanceOn_le_of_stieltjes (X sample) (Y sample) z
    hv hR hsmall (show 0 ≤ 4 * (n : ℝ) ^ (-d) by positivity)
    (fun u hu => hc u (by simpa only [neg_add, sub_eq_add_neg] using hu))
    (fun u hu => hi u (by simpa only [neg_add, sub_eq_add_neg] using hu))
  convert h using 1 <;> ring

end ShortRingAnchor
