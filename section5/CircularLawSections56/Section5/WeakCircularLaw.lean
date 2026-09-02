import CircularLawSections56.Section5.CircularLawFromPotential
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-! # From compactly supported spectral tests to bounded continuous tests

The target is a probability measure supported in the unit disk. A fixed compact
cutoff equal to one there prevents escape of spectral mass. Thus the Section 5
endpoint is weak convergence in probability, not merely vague convergence.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section
set_option maxHeartbeats 1400000
set_option autoImplicit false

namespace CircularLawSections56.Section5
open Section6 TaoVuReplacement ShortRingAnchor

def circularTestCutoff : ContDiffBump (0 : ℂ) :=
  { rIn := 1
    rOut := 2
    rIn_pos := by norm_num
    rIn_lt_rOut := by norm_num }

theorem circularTestCutoff_ae_one :
    ∀ᵐ z ∂circularMeasure, circularTestCutoff z = 1 := by
  filter_upwards [circularMeasure_norm_lt_one] with z hz
  apply circularTestCutoff.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, dist_zero_right, circularTestCutoff] using hz.le

theorem circularTestCutoff_integral :
    (∫ z, circularTestCutoff z ∂circularMeasure) = 1 := by
  rw [integral_congr_ae circularTestCutoff_ae_one]
  simp

theorem realEsdTest_subtract
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (f g : ℂ → ℝ) :
    realEsdTest A (fun z => f z - g z) = realEsdTest A f - realEsdTest A g := by
  have he : (fun z => f z - g z) = (fun z => f z + (-1 : ℝ) • g z) := by
    funext z
    simp only [smul_eq_mul]
    ring
  rw [he, realEsdTest_add, realEsdTest_smul]
  simp only [smul_eq_mul]
  ring

theorem abs_realEsdTest_sub_le_spectral_error
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (f g error : ℂ → ℝ)
    (h : ∀ z, |f z - g z| ≤ error z) :
    |realEsdTest A f - realEsdTest A g| ≤ realEsdTest A error := by
  have hsum (s : Multiset ℂ) :
      |(s.map f).sum - (s.map g).sum| ≤ (s.map error).sum := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      calc
        |f a + (s.map f).sum - (g a + (s.map g).sum)| =
          |(f a - g a) + ((s.map f).sum - (s.map g).sum)| := by ring_nf
        _ ≤ |f a - g a| + |(s.map f).sum - (s.map g).sum| := abs_add_le _ _
        _ ≤ error a + (s.map error).sum := add_le_add (h a) ih
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  simp only [realEsdTest, realSpectralSum, ← sub_div, abs_div, abs_of_pos hcard]
  exact div_le_div_of_nonneg_right (hsum _) hcard.le

theorem realEsdTest_cutoff_error
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (g χ : ℂ → ℝ) (M : ℝ)
    (hBound : ∀ z, |g z| ≤ M) (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) :
    |realEsdTest A g - realEsdTest A (fun z => χ z * g z)| ≤
      M * (1 - realEsdTest A χ) := by
  have he := abs_realEsdTest_sub_le_spectral_error A g (fun z => χ z * g z)
    (fun z => M * (1 - χ z)) (by
      intro z
      have hpos : 0 ≤ 1 - χ z := sub_nonneg.2 (hχ z).2
      rw [show g z - χ z * g z = g z * (1 - χ z) by ring,
        abs_mul, abs_of_nonneg hpos]
      exact mul_le_mul_of_nonneg_right (hBound z) hpos)
  have hid : realEsdTest A (fun z => M * (1 - χ z)) =
      M * (1 - realEsdTest A χ) := by
    change realEsdTest A (fun z => M • (1 - χ z)) = _
    rw [realEsdTest_smul, realEsdTest_subtract, realEsdTest_const]
    rfl
  exact he.trans_eq hid

theorem tendstoInProbabilityTri_of_cutoff_error
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Z : ℕ → Ω → ℝ) (a M : ℝ) (hM : 0 ≤ M)
    (hY : TendstoInProbabilityTri (fun _ => P) Y a)
    (hZ : TendstoInProbabilityTri (fun _ => P) Z 1)
    (hError : ∀ n ω, |X n ω - Y n ω| ≤ M * |Z n ω - 1|) :
    TendstoInProbabilityTri (fun _ => P) X a := by
  intro ε hε
  let δ := ε / (2 * (M + 1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδeq : (M + 1) * δ = ε / 2 := by
    dsimp only [δ]
    field_simp
  have hMδ : M * δ ≤ ε / 2 := by nlinarith
  have hupper (n : ℕ) :
      P.real {ω | ε ≤ |X n ω - a|} ≤
        P.real {ω | ε / 2 ≤ |Y n ω - a|} + P.real {ω | δ ≤ |Z n ω - 1|} := by
    have hs : {ω | ε ≤ |X n ω - a|} ⊆
        {ω | ε / 2 ≤ |Y n ω - a|} ∪ {ω | δ ≤ |Z n ω - 1|} := by
      intro ω hω
      by_contra hbad
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hbad
      have hc : |X n ω - Y n ω| ≤ ε / 2 :=
        (hError n ω).trans ((mul_le_mul_of_nonneg_left hbad.2.le hM).trans hMδ)
      have ht : |X n ω - a| ≤ |X n ω - Y n ω| + |Y n ω - a| := by
        simpa only [sub_add_sub_cancel] using abs_add_le (X n ω - Y n ω) (Y n ω - a)
      change ε ≤ |X n ω - a| at hω
      linarith
    exact (measureReal_mono hs).trans (measureReal_union_le _ _)
  apply squeeze_zero (fun _ => measureReal_nonneg) hupper
  simpa only [zero_add] using (hY (ε / 2) (by positivity)).add (hZ δ hδ)

/-- Every bounded continuous test is covered, without a separate tightness or
comparison-model assumption. -/
theorem circularLaw_boundedContinuous_of_compactSupport
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ∀ n, Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hCompact : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      TendstoInMeasure P (fun n ω => realEsdTest (X n ω) g) atTop
        (fun _ => ∫ z, g z ∂circularMeasure))
    (g : ℂ → ℝ) (hg : Continuous g) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ z, |g z| ≤ M) :
    TendstoInMeasure P (fun n ω => realEsdTest (X n ω) g) atTop
      (fun _ => ∫ z, g z ∂circularMeasure) := by
  let χ : ℂ → ℝ := circularTestCutoff
  have hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1 := fun _ =>
    ⟨circularTestCutoff.nonneg, circularTestCutoff.le_one⟩
  have hχg : (∫ z, χ z * g z ∂circularMeasure) = ∫ z, g z ∂circularMeasure := by
    apply integral_congr_ae
    filter_upwards [circularTestCutoff_ae_one] with z hz
    simp only [χ, hz, one_mul]
  have hy := hCompact (fun z => χ z * g z)
    (circularTestCutoff.continuous.mul hg) circularTestCutoff.hasCompactSupport.mul_right
  rw [hχg] at hy
  have hz := hCompact χ circularTestCutoff.continuous circularTestCutoff.hasCompactSupport
  rw [show (∫ z, χ z ∂circularMeasure) = 1 from circularTestCutoff_integral] at hz
  apply (tendstoInMeasure_iff_tri P _ _).2
  apply tendstoInProbabilityTri_of_cutoff_error P _
    (fun n ω => realEsdTest (X n ω) (fun z => χ z * g z))
    (fun n ω => realEsdTest (X n ω) χ) _ M hM
    ((tendstoInMeasure_iff_tri P _ _).1 hy) ((tendstoInMeasure_iff_tri P _ _).1 hz)
  intro n ω
  exact (realEsdTest_cutoff_error (X n ω) g χ M hBound hχ).trans
    (mul_le_mul_of_nonneg_left (by
      simpa only [abs_sub_comm] using (le_abs_self (1 - realEsdTest (X n ω) χ))) hM)

theorem circularLaw_boundedContinuousMap_of_compactSupport
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ∀ n, Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hCompact : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      TendstoInMeasure P (fun n ω => realEsdTest (X n ω) g) atTop
        (fun _ => ∫ z, g z ∂circularMeasure))
    (g : BoundedContinuousFunction ℂ ℝ) :
    TendstoInMeasure P (fun n ω => realEsdTest (X n ω) g) atTop
      (fun _ => ∫ z, g z ∂circularMeasure) := by
  apply circularLaw_boundedContinuous_of_compactSupport P X hCompact g g.continuous
    ‖g‖ (norm_nonneg g)
  intro z
  simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm z

end CircularLawSections56.Section5
