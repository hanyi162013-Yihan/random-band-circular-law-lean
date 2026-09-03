/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Corollary35.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.HermitianStieltjes
import Vendor.Arxiv2410.V3.ProbabilityEvent
import Vendor.Arxiv2410.V3.RateArithmetic

/-!
# v3 Corollary 3.5 from a uniform Stieltjes bound

The deterministic Poisson-kernel argument is complete.  The probability theorem transfers the
same good event by set inclusion, so no unproved measurability claim about ordered Hermitian
eigenvalues is needed.
-/

namespace Arxiv2410V3

open MeasureTheory

/-- The midpoint Stieltjes information actually used for intervals of length at most four. -/
def UniformMidpointStieltjesBound
    {ι : Type*} [Fintype ι]
    (eigenvalue : ι → ℝ) (scale C1 : ℝ) : Prop :=
  ∀ a b, -5 ≤ a → b ≤ 5 → scale ≤ b - a → b - a ≤ 4 →
    ‖empiricalStieltjes eigenvalue
      (spectralParameter ((a + b) / 2) (b - a))‖ ≤ C1

/-- The full deterministic content of v3 Corollary 3.5 for a `2n`-point real spectrum.

The explicit universal constant is `C₂ = 4 C₁ + 1`.  Intervals of length at most four use
the Poisson kernel; longer intervals use the trivial total count `2n`.
-/
theorem corollary35_finite_spectrum
    {n : ℕ} [NeZero n]
    (eigenvalue : HermitizationIndex n → ℝ)
    {scale C1 a b : ℝ}
    (hscale : 0 < scale) (hC1 : 0 ≤ C1)
    (huniform : UniformMidpointStieltjesBound eigenvalue scale C1)
    (ha : -5 ≤ a) (hb : b ≤ 5) (hthreshold : scale ≤ b - a) :
    ((eigenvaluesInInterval eigenvalue a b).card : ℝ) ≤
      (4 * C1 + 1) * (n : ℝ) * (b - a) := by
  let v := b - a
  have hv : 0 < v := lt_of_lt_of_le hscale hthreshold
  have hab : a < b := sub_pos.mp hv
  by_cases hv4 : v ≤ 4
  · have htrace := huniform a b ha hb hthreshold hv4
    have hcount := interval_count_le_of_midpoint_stieltjes_bound eigenvalue hab htrace
    have hcard : (Fintype.card (HermitizationIndex n) : ℝ) = 2 * (n : ℝ) := by
      simp [HermitizationIndex]
      ring
    rw [hcard] at hcount
    dsimp [v] at hv
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hv0 : 0 ≤ b - a := hv.le
    have hextra : 0 ≤ (n : ℝ) * (b - a) := mul_nonneg hn0 hv0
    nlinarith only [hcount, hextra]
  · have hv4' : 4 < v := lt_of_not_ge hv4
    have hcardNat :
        (eigenvaluesInInterval eigenvalue a b).card ≤
          Fintype.card (HermitizationIndex n) := by
      rw [eigenvaluesInInterval]
      simpa only [Finset.card_univ] using Finset.card_le_card
        (Finset.filter_subset
          (fun i : HermitizationIndex n =>
            a ≤ eigenvalue i ∧ eigenvalue i ≤ b)
          (Finset.univ : Finset (HermitizationIndex n)))
    have hcardReal :
        ((eigenvaluesInInterval eigenvalue a b).card : ℝ) ≤
          (Fintype.card (HermitizationIndex n) : ℝ) := by exact_mod_cast hcardNat
    have hcard : (Fintype.card (HermitizationIndex n) : ℝ) = 2 * (n : ℝ) := by
      simp [HermitizationIndex]
      ring
    rw [hcard] at hcardReal
    have hnNat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hn : 0 < (n : ℝ) := by exact_mod_cast hnNat
    dsimp [v] at hv4'
    have htwo_v : 2 ≤ b - a := by linarith
    have htwo_n_le : 2 * (n : ℝ) ≤ (n : ℝ) * (b - a) := by
      calc
        2 * (n : ℝ) = (n : ℝ) * 2 := by ring
        _ ≤ (n : ℝ) * (b - a) :=
          mul_le_mul_of_nonneg_left htwo_v hn.le
    have hcoefficient : 1 ≤ 4 * C1 + 1 := by linarith
    have hnv : 0 ≤ (n : ℝ) * (b - a) :=
      mul_nonneg hn.le (le_trans (by norm_num) htwo_v)
    calc
      ((eigenvaluesInInterval eigenvalue a b).card : ℝ)
          ≤ 2 * (n : ℝ) := hcardReal
      _ ≤ (n : ℝ) * (b - a) := htwo_n_le
      _ = 1 * ((n : ℝ) * (b - a)) := by ring
      _ ≤ (4 * C1 + 1) * ((n : ℝ) * (b - a)) :=
        mul_le_mul_of_nonneg_right hcoefficient hnv
      _ = (4 * C1 + 1) * (n : ℝ) * (b - a) := by ring

/-- The deterministic v3 Corollary 3.5 for the actual Hermitization `𝒴_z`.

The hypothesis is exactly the uniform trace-bound consequence (3.10) needed at the fixed `z`.
It is stated for all parameters in the v3 domain, and the spectral bridge is proved internally.
-/
theorem corollary35_of_uniform_trace_bound
    {n : ℕ} [NeZero n]
    (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {scale C1 a b : ℝ}
    (hscale : 0 < scale) (hC1 : 0 ≤ C1)
    (htrace : ∀ eta, InUpperHalfPlane eta → ‖eta‖ ≤ 5 → scale ≤ eta.im →
      ‖stieltjesTrace X z eta‖ ≤ C1)
    (ha : -5 ≤ a) (hb : b ≤ 5) (hthreshold : scale ≤ b - a) :
    ((eigenvaluesInInterval (hermitization_isHermitian X z).eigenvalues a b).card : ℝ) ≤
      (4 * C1 + 1) * (n : ℝ) * (b - a) := by
  apply corollary35_finite_spectrum
    (hermitization_isHermitian X z).eigenvalues hscale hC1 _ ha hb hthreshold
  intro a b ha hb hthreshold hlen
  have hab : a < b := by linarith
  have him : InUpperHalfPlane (spectralParameter ((a + b) / 2) (b - a)) := by
    simp [InUpperHalfPlane, spectralParameter]
    linarith
  have hnorm := norm_midpoint_parameter_le_five ha hb hab.le hlen
  have hpaper := htrace (spectralParameter ((a + b) / 2) (b - a))
    him hnorm (by simp [spectralParameter]; exact hthreshold)
  rw [stieltjesTrace_eq_empiricalHermitizationSpectrum X z him] at hpaper
  exact hpaper

/-- v3 Corollary 3.5 with its printed mesoscopic scale
`B^(-1/8) n^c`, for the actual Hermitization `𝒴_z` at a fixed `z`.

The only analytic input is the uniform trace estimate (3.10); the scale positivity and the
entire Poisson-kernel deduction are proved internally.
-/
theorem corollary35_v3_scale_of_uniform_trace_bound
    {n : ℕ} [NeZero n]
    (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {B c C1 a b : ℝ}
    (hB : 0 < B) (_hc : 0 < c) (hC1 : 0 ≤ C1)
    (htrace : ∀ eta, InUpperHalfPlane eta → ‖eta‖ ≤ 5 →
      Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c ≤ eta.im →
        ‖stieltjesTrace X z eta‖ ≤ C1)
    (ha : -5 ≤ a) (hb : b ≤ 5)
    (hthreshold : Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c ≤ b - a) :
    ((eigenvaluesInInterval (hermitization_isHermitian X z).eigenvalues a b).card : ℝ) ≤
      (4 * C1 + 1) * (n : ℝ) * (b - a) := by
  have hnNat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn : 0 < (n : ℝ) := by exact_mod_cast hnNat
  exact corollary35_of_uniform_trace_bound X z
    (corollary35_scale_pos hB hn) hC1 htrace ha hb hthreshold

/-- The event asserting the interval-count conclusion of v3 Corollary 3.5 for a fixed `z`. -/
def Corollary35CountGood
    {Omega : Type*} {n : ℕ} [NeZero n]
    (matrix : Omega → Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (scale C2 : ℝ) : Set Omega :=
  {omega | ∀ a b, -5 ≤ a → b ≤ 5 → scale ≤ b - a →
    ((eigenvaluesInInterval
      (hermitization_isHermitian (matrix omega) z).eigenvalues a b).card : ℝ) ≤
        C2 * (n : ℝ) * (b - a)}

/-- Probability form of v3 Corollary 3.5.  The good event from Proposition 3.4 is included in
the count-good event by the fully verified deterministic theorem, so its probability lower bound
is inherited unchanged.
-/
theorem corollary35_probability_from_uniform_trace_event
    {Omega : Type*} [MeasurableSpace Omega]
    {n : ℕ} [NeZero n]
    (mu : Measure Omega)
    (matrix : Omega → Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {scale C1 nReal : ℝ} (hscale : 0 < scale) (hC1 : 0 ≤ C1)
    (good : Set Omega)
    (hprob : ProbabilityAtLeast mu good (1 - nReal ^ (-10 : ℤ)))
    (htrace : ∀ omega ∈ good, ∀ eta,
      InUpperHalfPlane eta → ‖eta‖ ≤ 5 → scale ≤ eta.im →
        ‖stieltjesTrace (matrix omega) z eta‖ ≤ C1) :
    ProbabilityAtLeast mu
      (Corollary35CountGood matrix z scale (4 * C1 + 1))
      (1 - nReal ^ (-10 : ℤ)) := by
  apply hprob.trans
  apply measure_mono
  intro omega homega a b ha hb hthreshold
  exact corollary35_of_uniform_trace_bound (matrix omega) z hscale hC1
    (htrace omega homega) ha hb hthreshold

/-- The probability statement of v3 Corollary 3.5 at a fixed `z`, with exactly the printed
scale `B^(-1/8) n^c` and probability lower bound `1 - n^(-10)`.

The unresolved `z`-range mismatch in the paper is not hidden: a caller must supply (3.10) at
the chosen `z`.
-/
theorem corollary35_probability_v3_scale
    {Omega : Type*} [MeasurableSpace Omega]
    {n : ℕ} [NeZero n]
    (mu : Measure Omega)
    (matrix : Omega → Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {B c C1 : ℝ} (hB : 0 < B) (_hc : 0 < c) (hC1 : 0 ≤ C1)
    (good : Set Omega)
    (hprob : ProbabilityAtLeast mu good (1 - (n : ℝ) ^ (-10 : ℤ)))
    (htrace : ∀ omega ∈ good, ∀ eta,
      InUpperHalfPlane eta → ‖eta‖ ≤ 5 →
        Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c ≤ eta.im →
          ‖stieltjesTrace (matrix omega) z eta‖ ≤ C1) :
    ProbabilityAtLeast mu
      (Corollary35CountGood matrix z
        (Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c) (4 * C1 + 1))
      (1 - (n : ℝ) ^ (-10 : ℤ)) := by
  have hnNat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn : 0 < (n : ℝ) := by exact_mod_cast hnNat
  exact corollary35_probability_from_uniform_trace_event mu matrix z
    (corollary35_scale_pos hB hn) hC1 good hprob htrace

/-- Arbitrary fixed-`z` form of v3 Corollary 3.5, with the counting constant chosen only after
`z` has been fixed.

There is no norm restriction on `z`.  The witness is `C₂(z) = 4 C₁(z) + 1`; here `C₁` is an
input attached to this fixed `z`, so no uniformity in `z` is asserted. -/
theorem corollary35_probability_v3_scale_fixed_z_constant
    {Omega : Type*} [MeasurableSpace Omega]
    {n : ℕ} [NeZero n]
    (mu : Measure Omega)
    (matrix : Omega → Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {B c C1 : ℝ} (hB : 0 < B) (hc : 0 < c) (hC1 : 0 ≤ C1)
    (good : Set Omega)
    (hprob : ProbabilityAtLeast mu good (1 - (n : ℝ) ^ (-10 : ℤ)))
    (htrace : ∀ omega ∈ good, ∀ eta,
      InUpperHalfPlane eta → ‖eta‖ ≤ 5 →
        Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c ≤ eta.im →
          ‖stieltjesTrace (matrix omega) z eta‖ ≤ C1) :
    ∃ C2 : ℝ, 0 ≤ C2 ∧
      ProbabilityAtLeast mu
        (Corollary35CountGood matrix z
          (Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c) C2)
        (1 - (n : ℝ) ^ (-10 : ℤ)) := by
  refine ⟨4 * C1 + 1, by linarith, ?_⟩
  exact corollary35_probability_v3_scale mu matrix z hB hc hC1 good hprob htrace

/-- Fixed-`z` interpretation of v3 Corollary 3.5 with constants and good events allowed to
depend on `z`.

This theorem makes the quantifier order explicit:

`∀ z, ℙ(Corollary35CountGood at z with C₂(z)) ≥ 1 - n⁻¹⁰`,

where `C₂(z) = 4 C₁(z) + 1` and the input event is `good z`.  It does **not** assert a single
event or a single constant valid simultaneously on the unbounded `z`-plane, and it has no
assumption such as `‖z‖ ≤ 3`.  This is the arbitrary-fixed-`z` version requested by the printed
wording “for any `z ∈ ℂ`”. -/
theorem corollary35_probability_v3_scale_zDependent
    {Omega : Type*} [MeasurableSpace Omega]
    {n : ℕ} [NeZero n]
    (mu : Measure Omega)
    (matrix : Omega → Matrix (Fin n) (Fin n) ℂ)
    {B c : ℝ} (hB : 0 < B) (hc : 0 < c)
    (C1 : ℂ → ℝ) (good : ℂ → Set Omega)
    (hC1 : ∀ z, 0 ≤ C1 z)
    (hprob : ∀ z,
      ProbabilityAtLeast mu (good z) (1 - (n : ℝ) ^ (-10 : ℤ)))
    (htrace : ∀ z, ∀ omega ∈ good z, ∀ eta,
      InUpperHalfPlane eta → ‖eta‖ ≤ 5 →
        Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c ≤ eta.im →
          ‖stieltjesTrace (matrix omega) z eta‖ ≤ C1 z) :
    ∀ z, ProbabilityAtLeast mu
      (Corollary35CountGood matrix z
        (Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c) (4 * C1 z + 1))
      (1 - (n : ℝ) ^ (-10 : ℤ)) := by
  intro z
  exact corollary35_probability_v3_scale mu matrix z hB hc (hC1 z)
    (good z) (hprob z) (htrace z)

end Arxiv2410V3

