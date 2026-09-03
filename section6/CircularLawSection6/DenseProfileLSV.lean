import CircularLawSection6.DenseProfilePublishedModel
import ShortRingAnchor.HighBandLSVProbability

/-! # The proved Section 3 least-value bound for actual dense profile matrices

The full profile, with variances comparable to `1/N`, is a planar model
with geometric width `N`. The already proved high-band theorem supplies
its least-value estimate. Equality of the actual and planar matrix laws
transports the bad event, and the exact row moments remove the HS cutoff.
No least-value estimate, logarithmic limit, or Han result is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology ShortRingAnchor HighBandLSV
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CircularLawSection6.DenseProfile

theorem actualMatrix_minimumInput (M : ℕ → ℕ) [∀ n, NeZero (M n)]
    (q : ∀ n, ZMod (M n) → ℝ) (hq : ∀ n s, 0 < q n s)
    (hsum : ∀ n, ∑ s, q n s = 1)
    {c C : ℝ} (hc : 0 < c)
    (hlower : ∀ n s, c / (M n : ℝ) ≤ q n s)
    (hupper : ∀ n s, q n s ≤ C / (M n : ℝ))
    (hM : Tendsto M atTop atTop) (z : ℂ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ good, Theorem31MinimumSingularValueInput (fun n => NeZero.pos (M n)) law
      (fun n => actualMatrix (M n) (q n)) z (sourceHardEdgeScale M M κ) good := by
  let m (n : ℕ) := planarModel (M n) (q n) (hq n) (hsum n) (hlower n) (hupper n)
  have hlaw (n : ℕ) : IdentDistrib (actualMatrix (M n) (q n)) (m n).matrix law (m n).law :=
    planarModel_identDistrib (M n) (q n) (hq n) (hsum n) (hlower n) (hupper n)
  apply theorem31MinimumInput_of_truncated_estimate
    (W := M) (fun n => NeZero.pos (M n)) hM (fun n => actualMatrix (M n) (q n)) z hκ
    (D := Real.sqrt (Real.pi * 2 / c)) (actualMatrix_rowMoments M q hq hsum)
  intro R hR
  have hband : ∀ᶠ n in atTop, (M n : ℝ) ^ (1 / 2 + (1 / 2 : ℝ)) ≤ (M n : ℝ) := by
    apply Eventually.of_forall
    intro n
    norm_num
  filter_upwards [eventually_planar_lsv_along_dimensions
    (chi := (1 / 2 : ℝ)) m hM hc (by norm_num) (by norm_num) le_rfl hκ hR (norm_nonneg z)
    (Eventually.of_forall (fun n => NeZero.pos (M n))) hband
    (Eventually.of_forall (fun _ => le_rfl))] with n hn
  exact (highBand_strict_bad_le_of_identDistrib (NeZero.pos (M n)) (hlaw n) z _ R).trans
    (hn z le_rfl _ (Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem actualMatrix_eq_profile (p : NoncompactProfile) (N : ℕ) [NeZero N]
    (W : ℝ) (ω : CircularLawSections56.Section5.PublishedSection3Concrete.Sample) :
    actualMatrix N (p.weight N W) ω = (p.matrix N W (cyclicSamples N ω)).submatrix
      (ZMod.finEquiv N) (ZMod.finEquiv N) :=
  actualMatrix_eq_weightedCyclicMatrix N (p.weight N W) ω

theorem profile_minimumInput (p : NoncompactProfile) (M : ℕ → ℕ)
    [∀ n, NeZero (M n)] (W : ℕ → ℝ) (hM : Tendsto M atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) (hdense : ∀ n, δ * (M n : ℝ) ≤ W n)
    (z : ℂ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ good, Theorem31MinimumSingularValueInput (fun n => NeZero.pos (M n)) law
      (fun n => actualMatrix (M n) (p.weight (M n) (W n))) z
      (sourceHardEdgeScale M M κ) good := by
  obtain ⟨c, C, hc, _hC, hb⟩ := p.dense_weights_comparable hδ
  exact actualMatrix_minimumInput M (fun n => p.weight (M n) (W n))
    (fun n s => p.weight_pos _ _ s) (fun n => p.sum_weight _ _) hc
    (fun n s => (hb (M n) (W n) (hdense n) s).1)
    (fun n s => (hb (M n) (W n) (hdense n) s).2) hM z hκ

end CircularLawSection6.DenseProfile
