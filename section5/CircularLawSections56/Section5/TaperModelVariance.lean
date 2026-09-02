import CircularLawSections56.Section5.TaperVarianceProfile
import CircularLawSections56.Section5.LiteralEnergyIdentity

/-! # Identification of the taper variance matrix with actual entry moments

The doubly stochastic array is not a separately supplied comparison profile:
it is exactly the expected squared modulus of the entries of the literal
cyclic random matrix, with the manuscript's sampled and normalized weights.
-/

open Filter MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
set_option maxHeartbeats 1200000
set_option autoImplicit false

namespace CircularLawSections56.Section5
open Section6 CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

theorem paperScalarBandMatrix_entry_slot
    (N d : ℕ) [NeZero N] (hfit : d + 2 ≤ N) (center : Fin (d + 1))
    (x : ZMod N → Fin (d + 2) → ℂ) (i : ZMod N) (s : Fin (d + 2)) :
    paperScalarBandMatrix N d center x i (i - (center.val : ZMod N) + (s.val : ZMod N)) = x i s := by
  have hinj : Function.Injective (fun t : Fin (d + 2) => (t.val : ZMod N)) := by
    intro a b hab
    apply Fin.ext
    exact CharP.natCast_injOn_Iio (ZMod N) N
      (lt_of_lt_of_le a.isLt hfit) (lt_of_lt_of_le b.isLt hfit) hab
  have he (t : Fin (d + 2)) :
      i - (center.val : ZMod N) + (s.val : ZMod N) =
        i - (center.val : ZMod N) + (t.val : ZMod N) ↔ s = t :=
    add_left_cancel_iff.trans hinj.eq_iff
  unfold paperScalarBandMatrix
  simp_rw [he]
  simp

theorem paperIndicatorX_entry_second_moment
    (N d : ℕ) [NeZero N] (hfit : d + 2 ≤ N) (center : Fin (d + 1))
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν = 1) (i j : ZMod N) :
    Integrable (fun ω => ‖paperIndicatorX N d center profile.b ω i j‖ ^ 2)
      (iidMeasure ν (N * (d + 2))) ∧
    (∫ ω, ‖paperIndicatorX N d center profile.b ω i j‖ ^ 2 ∂iidMeasure ν (N * (d + 2))) =
      cyclicVarianceProfile N (d + 2) (center.val : ZMod N) profile.q i j := by
  classical
  by_cases hslot : ∃ s : Fin (d + 2), j = i - (center.val : ZMod N) + (s.val : ZMod N)
  · obtain ⟨s, rfl⟩ := hslot
    have hMP : MeasurePreserving (fun ω => ω (paperIndicatorFlatIndex N d i s))
        (iidMeasure ν (N * (d + 2))) ν :=
      ⟨measurable_pi_apply _, iidMeasure_map_coordinate ν _⟩
    have hpoint (ω : Fin (N * (d + 2)) → ℂ) :
        ‖paperIndicatorX N d center profile.b ω i
          (i - (center.val : ZMod N) + (s.val : ZMod N))‖ ^ 2 =
          profile.q s * ‖ω (paperIndicatorFlatIndex N d i s)‖ ^ 2 := by
      rw [paperIndicatorX, paperScalarBandMatrix_entry_slot N d hfit]
      simp only [paperIndicatorXi_apply, norm_mul, mul_pow, profile.norm_b,
        Real.sq_sqrt (profile.q_pos hc₀ s).le]
    simp_rw [hpoint]
    refine ⟨?_, ?_⟩
    · simpa only [Function.comp_apply] using
        (hMP.integrable_comp_of_integrable hInt).const_mul (profile.q s)
    · rw [integral_const_mul, integral_comp_measurePreserving_eq hMP _ hInt,
        hSecond, mul_one, cyclicVarianceProfile_slot N (d + 2) hfit]
  · have hs : ∀ s : Fin (d + 2), j ≠ i - (center.val : ZMod N) + (s.val : ZMod N) := by
      simpa only [not_exists] using hslot
    have he (ω : Fin (N * (d + 2)) → ℂ) : paperIndicatorX N d center profile.b ω i j = 0 := by
      simp only [paperIndicatorX, paperScalarBandMatrix, hs, if_false, Finset.sum_const_zero]
    simp only [he, norm_zero, zero_pow (by decide : 2 ≠ 0), integral_zero,
      cyclicVarianceProfile, hs, if_false, Finset.sum_const_zero]
    exact ⟨integrable_zero _ _ _, trivial⟩

theorem literalIndicatorMatrix_entry_second_moment
    (k d : ℕ) (hfit : d + 2 ≤ k + 1) (center : Fin (d + 1))
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν = 1) (i j : Fin (k + 1)) :
    (∫ ω, ‖literalIndicatorMatrix k d center profile.b ω i j‖ ^ 2
      ∂iidMeasure ν ((k + 1) * (d + 2))) =
      cyclicVarianceProfile (k + 1) (d + 2) (center.val : ZMod (k + 1)) profile.q
        ((ZMod.finEquiv (k + 1)) i) ((ZMod.finEquiv (k + 1)) j) :=
  (paperIndicatorX_entry_second_moment (k + 1) d hfit center profile hc₀ ν hInt hSecond _ _).2

theorem taperedMatrix_entry_second_moment
    (p : PolynomialTaperProfile) (k W : ℕ) (hW : 0 < W) (hfit : 2 * W + 1 ≤ k + 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν = 1) (i j : Fin (k + 1)) :
    (∫ ω, ‖p.literalMatrix k W hW ω i j‖ ^ 2
      ∂iidMeasure ν ((k + 1) * (taperStateDimension W + 2))) =
      cyclicVarianceProfile (k + 1) (taperStateDimension W + 2)
        (W : ZMod (k + 1)) (p.literalWeights W hW).q
        ((ZMod.finEquiv (k + 1)) i) ((ZMod.finEquiv (k + 1)) j) := by
  exact literalIndicatorMatrix_entry_second_moment k (taperStateDimension W)
    ((PolynomialTaperProfile.literalMatrix_band_fits k W hW).2 hfit)
    (taperCenter W hW) (p.literalWeights W hW) (p.lowerParameter_pos W) ν hInt hSecond i j

theorem cyclicVarianceProfile_cast
    (N : ℕ) [NeZero N] {D E : ℕ} (h : D = E)
    (center : ZMod N) (q : Fin E → ℝ) (i j : ZMod N) :
    cyclicVarianceProfile N D center (fun s => q (Fin.cast h s)) i j =
      cyclicVarianceProfile N E center q i j := by
  subst E
  rfl

theorem PolynomialTaperProfile.literalVarianceMatrix_eq
    (p : PolynomialTaperProfile) (N W : ℕ) [NeZero N] (hW : 0 < W) (i j : ZMod N) :
    cyclicVarianceProfile N (taperStateDimension W + 2) (W : ZMod N)
      (p.literalWeights W hW).q i j = p.varianceMatrix N W i j := by
  have hq : (p.literalWeights W hW).q = fun s =>
      p.weight W (Fin.cast (congrArg (· + 1) (taperStateDimension_succ W hW)) s) := by
    funext s
    exact p.literalWeights_q W hW s
  rw [hq]
  exact cyclicVarianceProfile_cast N _ _ _ i j

/-- The manuscript's normalized sampled taper is precisely the variance of each
actual matrix entry, not merely an admissible auxiliary profile. -/
theorem taperedMatrix_expected_entry_eq_varianceMatrix
    (p : PolynomialTaperProfile) (k W : ℕ) (hW : 0 < W) (hfit : 2 * W + 1 ≤ k + 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν = 1) (i j : Fin (k + 1)) :
    (∫ ω, ‖p.literalMatrix k W hW ω i j‖ ^ 2
      ∂iidMeasure ν ((k + 1) * (taperStateDimension W + 2))) =
      p.varianceMatrix (k + 1) W ((ZMod.finEquiv (k + 1)) i) ((ZMod.finEquiv (k + 1)) j) := by
  rw [taperedMatrix_entry_second_moment p k W hW hfit ν hInt hSecond]
  exact p.literalVarianceMatrix_eq _ _ hW _ _

end CircularLawSections56.Section5
