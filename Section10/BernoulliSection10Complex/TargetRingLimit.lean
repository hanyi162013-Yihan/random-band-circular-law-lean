import BernoulliSection10Complex.LongRingLimit

/-! # Log-determinant convergence for every growing bandwidth, (10.56) -/

open Filter MeasureTheory Set Topology

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open SourceInputs ShortRingAnchor ProbabilityLimits

def densityDirectCondition (W s : ℕ) : Prop :=
  (((s + 3) * W : ℕ) : ℝ) ≤ (W : ℝ) ^ (101 / 100 : ℝ)

instance (W s : ℕ) : Decidable (densityDirectCondition W s) :=
  inferInstanceAs (Decidable ((((s + 3) * W : ℕ) : ℝ) ≤ (W : ℝ) ^ (101 / 100 : ℝ)))

def densityDirectAuxSites (W s : ℕ) : ℕ :=
  if densityDirectCondition W s then s else densityCoreSites W

def densityLongAuxSites (W s : ℕ) : ℕ :=
  if densityDirectCondition W s then W else s

theorem densityLongAuxSites_long (W s : ℕ) (hW : 0 < W) :
    (W : ℝ) ^ (101 / 100 : ℝ) ≤ (((densityLongAuxSites W s + 3) * W : ℕ) : ℝ) := by
  classical
  by_cases h : densityDirectCondition W s
  · simp only [densityLongAuxSites, if_pos h, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    have hp := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hW : (1 : ℝ) ≤ W)
      (by norm_num : (101 / 100 : ℝ) ≤ 2)
    norm_num at hp
    nlinarith [Nat.cast_nonneg (α := ℝ) W]
  · simp only [densityLongAuxSites, if_neg h]
    exact (lt_of_not_ge h).le

theorem densityDirectAuxSites_highBand
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop) :
    ∀ᶠ n in atTop,
      (((densityDirectAuxSites (W n) (s n) + 3) * W n : ℕ) : ℝ) ^
        (8 / 9 + 1 / 20 : ℝ) ≤ W n := by
  classical
  filter_upwards [hWtop.eventually eventually_density_anchor_highBand] with n hn
  by_cases h : densityDirectCondition (W n) (s n)
  · simp only [densityDirectAuxSites, if_pos h]
    exact density_direct_highBand (hW n) h
  · simp only [densityDirectAuxSites, if_neg h]
    exact hn

/-- The full log-potential conclusion retains only the atom assumptions
and the exact permitted Section 3 theorem statements. -/
theorem density_profile_log_limit
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (h3 : Integrable (fun x : ℂ => ‖x‖ ^ 3) μ) (hSource : Section3Inputs μ L)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (z : ℂ) :
    ConvergesInProbability (inputLaw μ)
      (fun n ω => normalizedShiftLogDet (profileMatrix (physicalProfile (W n) (s n)) ω) z)
      (circularLogPotential z) := by
  classical
  have hshort := fullBlockHighBand_profile_log_limit hμ h3 hSource W
    (fun n => densityDirectAuxSites (W n) (s n)) hW hWtop (1 / 20)
    (by norm_num) (by norm_num) (densityDirectAuxSites_highBand W s hW hWtop) z
  have hlong := density_long_profile_log_limit hμ h3 hSource W
    (fun n => densityLongAuxSites (W n) (s n)) hW hWtop
    (Eventually.of_forall fun n => densityLongAuxSites_long (W n) (s n) (hW n)) z
  rw [convergesInProbability_iff_norm] at hshort hlong ⊢
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using (hshort ε hε).add (hlong ε hε))
    (fun _ => zero_le)
  intro n
  apply (measure_mono ?_).trans (measure_union_le _ _)
  intro sample hsample
  have hsame (t : ℕ) (ht : t = s n) :
      ε ≤ ‖normalizedShiftLogDet (profileMatrix (physicalProfile (W n) t) sample) z -
        circularLogPotential z‖ := by
    subst t
    exact hsample
  by_cases h : densityDirectCondition (W n) (s n)
  · apply Or.inl
    exact hsame (densityDirectAuxSites (W n) (s n)) (by simp [densityDirectAuxSites, h])
  · apply Or.inr
    exact hsame (densityLongAuxSites (W n) (s n)) (by simp [densityLongAuxSites, h])

/-- The same result for the literal finite physical-row probability spaces;
there is no infinite-array or auxiliary-Gaussian premise on the caller. -/
theorem density_ring_log_limit
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (h3 : Integrable (fun x : ℂ => ‖x‖ ^ 3) μ) (hSource : Section3Inputs μ L)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWtop : Tendsto W atTop atTop)
    (z : ℂ) :
    letI := hμ.toIsProbabilityMeasure
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) μ)
      (fun n x => densityCyclicLogDet (W n) (s n) z x / (((s n + 3) * W n : ℕ) : ℝ))
      (circularLogPotential z) := by
  letI := hμ.toIsProbabilityMeasure
  exact (profile_log_converges_iff_physical_rows μ W s z _).mp
    (density_profile_log_limit hμ h3 hSource W s hW hWtop z)

end BernoulliSection10Complex
