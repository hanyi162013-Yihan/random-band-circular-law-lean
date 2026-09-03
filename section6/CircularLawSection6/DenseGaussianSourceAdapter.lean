import CircularLawSection6.ProfileReplacement
import CircularLawSection6.ProfileComparability
import CircularLawSections56.Section5.DiskReferenceLaw
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The dense profile satisfies Han's Gaussian variance threshold

Han, arXiv:2410.16457v3, Theorem 1.5 is an explicit external input, here
specialized to Gaussian cyclic variances and exponent 11/12 = 5/6 + 1/12.
The profile-dependent bounds and the eventual exponent inequality are
proved. The cited theorem is not introduced as a Lean axiom.
-/

open MeasureTheory Filter Topology TaoVuReplacement ShortRingAnchor
open CircularLawSections56.Section5 CircularLawSections56.Section6
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem eventually_dense_variance_threshold (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (C : ℝ) :
    ∀ᶠ n in atTop, C / (N n : ℝ) ≤ (N n : ℝ) ^ (-(11 / 12 : ℝ)) := by
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp
    (tendsto_natCast_atTop_atTop.comp hN)
  filter_upwards [hp.eventually_ge_atTop C] with n hn
  calc
    _ ≤ (N n : ℝ) ^ (1 / 12 : ℝ) / (N n : ℝ) :=
      div_le_div_of_nonneg_right hn (Nat.cast_nonneg _)
    _ = _ := by
      rw [← Real.rpow_sub_one (Nat.cast_ne_zero.mpr (NeZero.ne (N n)))]
      norm_num

def HanGaussianDenseInput : Prop :=
  ∀ (φ : ℕ → ℕ), StrictMono φ →
    ∀ q : ∀ n, ZMod (φ n + 1) → ℝ,
      (∀ n s, 0 ≤ q n s) → (∀ n, ∑ s, q n s = 1) →
      (∀ᶠ n in atTop, ∀ s, q n s ≤ ((φ n + 1 : ℕ) : ℝ) ^ (-(11 / 12 : ℝ))) →
      ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
        TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
          (fun n ω => realEsdTest (cyclicPhysicalMatrix (φ n)
            (weightedCyclicMatrix (φ n + 1) (q n) (ω (φ n)).1)) f)
          atTop (fun _ => ∫ z, f z ∂circularMeasure)

namespace NoncompactProfile

theorem dense_profile_spectral_limit_of_Han (p : NoncompactProfile)
    (W : ℕ → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hdense : ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ W (φ n) / (φ n + 1 : ℕ))
    (hHan : HanGaussianDenseInput) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix (φ n)
          (p.matrix (φ n + 1) (W (φ n)) (ω (φ n)).1)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) := by
  obtain ⟨c, hc, hratio⟩ := hdense
  obtain ⟨c₀, C, _, _, hweights⟩ := p.dense_weights_comparable hc
  have hbound (n : ℕ) (s : ZMod (φ n + 1)) : p.weight (φ n + 1) (W (φ n)) s ≤ C / (φ n + 1 : ℕ) :=
    (hweights (φ n + 1) (W (φ n)) ((le_div_iff₀ (by positivity)).mp (hratio n)) s).2
  have hthreshold : ∀ᶠ n in atTop, ∀ s,
      p.weight (φ n + 1) (W (φ n)) s ≤ ((φ n + 1 : ℕ) : ℝ) ^ (-(11 / 12 : ℝ)) := by
    filter_upwards [eventually_dense_variance_threshold (fun n => φ n + 1)
      ((tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop) C] with n hn
    exact fun s => (hbound n s).trans hn
  simpa only [matrix] using hHan φ hφ (fun n => p.weight (φ n + 1) (W (φ n)))
    (fun n s => (p.weight_pos _ _ s).le) (fun n => p.sum_weight _ _) hthreshold

end NoncompactProfile
end CircularLawSection6
