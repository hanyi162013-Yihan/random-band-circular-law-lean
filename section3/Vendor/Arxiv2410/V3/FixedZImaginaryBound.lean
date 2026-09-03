/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/FixedZImaginaryBound.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.Corollary35

/-!
# Fixed-`z` Corollary 3.5 from an imaginary-part bound

The Poisson-kernel proof of v3 Corollary 3.5 does not need a bound on the full modulus of the
Stieltjes transform.  Its exact analytic input is only an upper bound on the imaginary part.
This file records that weaker form, with no restriction on `z`; constants and good events may
depend on the fixed `z`.

It also proves the deterministic bridge used after v3 formula (3.9): a norm comparison with a
free Stieltjes transform, together with an upper bound on the imaginary part of the free
transform, gives the required random imaginary-part bound.
-/

namespace Arxiv2410V3

open MeasureTheory

/-- The midpoint imaginary-part information actually used by the Poisson-kernel argument. -/
def UniformMidpointStieltjesImBound
    {ι : Type*} [Fintype ι]
    (eigenvalue : ι → ℝ) (scale C : ℝ) : Prop :=
  ∀ a b, -5 ≤ a → b ≤ 5 → scale ≤ b - a → b - a ≤ 4 →
    (empiricalStieltjes eigenvalue
      (spectralParameter ((a + b) / 2) (b - a))).im ≤ C

/-- Imaginary-part-only form of the central Poisson-kernel counting implication used after
v3 Corollary 3.5. -/
theorem interval_count_le_of_stieltjes_im_bound_at
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (eigenvalue : ι → ℝ) {a b E v C : ℝ}
    (hv : 0 < v)
    (hcover : ∀ i, a ≤ eigenvalue i → eigenvalue i ≤ b →
      |eigenvalue i - E| ≤ v)
    (himBound :
      (empiricalStieltjes eigenvalue (spectralParameter E v)).im ≤ C) :
    ((eigenvaluesInInterval eigenvalue a b).card : ℝ) ≤
      2 * (Fintype.card ι : ℝ) * C * v := by
  have hcount := interval_count_le_two_v_poissonSum eigenvalue hv hcover
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have him := empiricalStieltjes_im eigenvalue E v
  have hsum :
      (∑ i, poissonKernel v (eigenvalue i - E)) =
        (Fintype.card ι : ℝ) *
          (empiricalStieltjes eigenvalue (spectralParameter E v)).im := by
    have hdiv := (div_eq_iff hcard).mp him.symm
    nlinarith
  rw [hsum] at hcount
  have hfactor : 0 ≤ 2 * v * (Fintype.card ι : ℝ) := by positivity
  calc
    ((eigenvaluesInInterval eigenvalue a b).card : ℝ)
        ≤ 2 * v * ((Fintype.card ι : ℝ) *
          (empiricalStieltjes eigenvalue (spectralParameter E v)).im) := hcount
    _ ≤ 2 * v * ((Fintype.card ι : ℝ) * C) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left himBound (by positivity)) (by positivity)
    _ = 2 * (Fintype.card ι : ℝ) * C * v := by ring

/-- Midpoint specialization of the imaginary-part-only Poisson-kernel bound. -/
theorem interval_count_le_of_midpoint_stieltjes_im_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (eigenvalue : ι → ℝ) {a b C : ℝ}
    (hab : a < b)
    (himBound :
      (empiricalStieltjes eigenvalue
        (spectralParameter ((a + b) / 2) (b - a))).im ≤ C) :
    ((eigenvaluesInInterval eigenvalue a b).card : ℝ) ≤
      2 * (Fintype.card ι : ℝ) * C * (b - a) := by
  apply interval_count_le_of_stieltjes_im_bound_at eigenvalue
    (sub_pos.mpr hab) _ himBound
  intro i hai hib
  rw [abs_le]
  constructor <;> linarith

/-- Full deterministic content of v3 Corollary 3.5 from only an imaginary-part bound.

The explicit count constant is `4 C + 1`, exactly as in the stronger norm-bound version. -/
theorem corollary35_finite_spectrum_of_im_bound
    {n : ℕ} [NeZero n]
    (eigenvalue : HermitizationIndex n → ℝ)
    {scale C a b : ℝ}
    (hscale : 0 < scale) (hC : 0 ≤ C)
    (huniform : UniformMidpointStieltjesImBound eigenvalue scale C)
    (ha : -5 ≤ a) (hb : b ≤ 5) (hthreshold : scale ≤ b - a) :
    ((eigenvaluesInInterval eigenvalue a b).card : ℝ) ≤
      (4 * C + 1) * (n : ℝ) * (b - a) := by
  let v := b - a
  have hv : 0 < v := lt_of_lt_of_le hscale hthreshold
  have hab : a < b := sub_pos.mp hv
  by_cases hv4 : v ≤ 4
  · have himBound := huniform a b ha hb hthreshold hv4
    have hcount :=
      interval_count_le_of_midpoint_stieltjes_im_bound eigenvalue hab himBound
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
          (Fintype.card (HermitizationIndex n) : ℝ) := by
      exact_mod_cast hcardNat
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
    have hcoefficient : 1 ≤ 4 * C + 1 := by linarith
    have hnv : 0 ≤ (n : ℝ) * (b - a) :=
      mul_nonneg hn.le (le_trans (by norm_num) htwo_v)
    calc
      ((eigenvaluesInInterval eigenvalue a b).card : ℝ)
          ≤ 2 * (n : ℝ) := hcardReal
      _ ≤ (n : ℝ) * (b - a) := htwo_n_le
      _ = 1 * ((n : ℝ) * (b - a)) := by ring
      _ ≤ (4 * C + 1) * ((n : ℝ) * (b - a)) :=
        mul_le_mul_of_nonneg_right hcoefficient hnv
      _ = (4 * C + 1) * (n : ℝ) * (b - a) := by ring

/-- Fixed arbitrary-`z` deterministic form of v3 Corollary 3.5.  There is no norm restriction
on `z`, and the analytic hypothesis controls only `Im m_z(eta)`. -/
theorem corollary35_of_uniform_trace_im_bound
    {n : ℕ} [NeZero n]
    (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {scale C a b : ℝ}
    (hscale : 0 < scale) (hC : 0 ≤ C)
    (htrace : ∀ eta, InUpperHalfPlane eta → ‖eta‖ ≤ 5 → scale ≤ eta.im →
      (stieltjesTrace X z eta).im ≤ C)
    (ha : -5 ≤ a) (hb : b ≤ 5) (hthreshold : scale ≤ b - a) :
    ((eigenvaluesInInterval (hermitization_isHermitian X z).eigenvalues a b).card : ℝ) ≤
      (4 * C + 1) * (n : ℝ) * (b - a) := by
  apply corollary35_finite_spectrum_of_im_bound
    (hermitization_isHermitian X z).eigenvalues hscale hC _ ha hb hthreshold
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

/-- Fixed arbitrary-`z` deterministic Corollary 3.5 at the printed v3 mesoscopic scale,
using only an imaginary-part bound. -/
theorem corollary35_v3_scale_of_uniform_trace_im_bound
    {n : ℕ} [NeZero n]
    (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {B c C a b : ℝ}
    (hB : 0 < B) (_hc : 0 < c) (hC : 0 ≤ C)
    (htrace : ∀ eta, InUpperHalfPlane eta → ‖eta‖ ≤ 5 →
      Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c ≤ eta.im →
        (stieltjesTrace X z eta).im ≤ C)
    (ha : -5 ≤ a) (hb : b ≤ 5)
    (hthreshold : Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c ≤ b - a) :
    ((eigenvaluesInInterval (hermitization_isHermitian X z).eigenvalues a b).card : ℝ) ≤
      (4 * C + 1) * (n : ℝ) * (b - a) := by
  have hnNat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn : 0 < (n : ℝ) := by exact_mod_cast hnNat
  exact corollary35_of_uniform_trace_im_bound X z
    (corollary35_scale_pos hB hn) hC htrace ha hb hthreshold

/-- A norm comparison with a reference transform needs only an upper bound on the reference
imaginary part to control the random imaginary part. -/
theorem im_le_of_norm_sub_le
    (m mfree : ℂ) {delta Cfree : ℝ}
    (hcomparison : ‖m - mfree‖ ≤ delta)
    (hfreeIm : mfree.im ≤ Cfree) :
    m.im ≤ Cfree + delta := by
  have hdiff : (m - mfree).im ≤ delta :=
    (Complex.im_le_norm (m - mfree)).trans hcomparison
  have him : m.im = (m - mfree).im + mfree.im := by
    simp
  linarith

/-- Uniform fixed-`z` version of the preceding bridge over the eta-domain used in v3
Corollary 3.5. -/
theorem uniform_trace_im_bound_of_free_comparison
    {Omega : Type*} {good : Set Omega}
    {n : ℕ} {B c delta Cfree : ℝ}
    (trace : Omega → ℂ → ℂ) (freeTrace : ℂ → ℂ)
    (hcomparison : ∀ omega ∈ good, ∀ eta,
      InUpperHalfPlane eta → ‖eta‖ ≤ 5 →
        Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c ≤ eta.im →
          ‖trace omega eta - freeTrace eta‖ ≤ delta)
    (hfreeIm : ∀ eta, InUpperHalfPlane eta → ‖eta‖ ≤ 5 →
      Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c ≤ eta.im →
        (freeTrace eta).im ≤ Cfree) :
    ∀ omega ∈ good, ∀ eta, InUpperHalfPlane eta → ‖eta‖ ≤ 5 →
      Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c ≤ eta.im →
        (trace omega eta).im ≤ Cfree + delta := by
  intro omega homega eta hetaUpper hetaNorm hetaScale
  exact im_le_of_norm_sub_le (trace omega eta) (freeTrace eta)
    (hcomparison omega homega eta hetaUpper hetaNorm hetaScale)
    (hfreeIm eta hetaUpper hetaNorm hetaScale)

/-- Probability form of fixed-`z` Corollary 3.5 from an imaginary-part good event. -/
theorem corollary35_probability_from_uniform_trace_im_event
    {Omega : Type*} [MeasurableSpace Omega]
    {n : ℕ} [NeZero n]
    (mu : Measure Omega)
    (matrix : Omega → Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {scale C p : ℝ} (hscale : 0 < scale) (hC : 0 ≤ C)
    (good : Set Omega)
    (hprob : ProbabilityAtLeast mu good p)
    (htrace : ∀ omega ∈ good, ∀ eta,
      InUpperHalfPlane eta → ‖eta‖ ≤ 5 → scale ≤ eta.im →
        (stieltjesTrace (matrix omega) z eta).im ≤ C) :
    ProbabilityAtLeast mu
      (Corollary35CountGood matrix z scale (4 * C + 1)) p := by
  apply hprob.trans
  apply measure_mono
  intro omega homega a b ha hb hthreshold
  exact corollary35_of_uniform_trace_im_bound (matrix omega) z hscale hC
    (htrace omega homega) ha hb hthreshold

/-- Printed v3 scale and probability, for any fixed `z`, using only an imaginary-part bound. -/
theorem corollary35_probability_v3_scale_from_im_event
    {Omega : Type*} [MeasurableSpace Omega]
    {n : ℕ} [NeZero n]
    (mu : Measure Omega)
    (matrix : Omega → Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {B c C : ℝ} (hB : 0 < B) (_hc : 0 < c) (hC : 0 ≤ C)
    (good : Set Omega)
    (hprob : ProbabilityAtLeast mu good (1 - (n : ℝ) ^ (-10 : ℤ)))
    (htrace : ∀ omega ∈ good, ∀ eta,
      InUpperHalfPlane eta → ‖eta‖ ≤ 5 →
        Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c ≤ eta.im →
          (stieltjesTrace (matrix omega) z eta).im ≤ C) :
    ProbabilityAtLeast mu
      (Corollary35CountGood matrix z
        (Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c) (4 * C + 1))
      (1 - (n : ℝ) ^ (-10 : ℤ)) := by
  have hnNat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn : 0 < (n : ℝ) := by exact_mod_cast hnNat
  exact corollary35_probability_from_uniform_trace_im_event mu matrix z
    (corollary35_scale_pos hB hn) hC good hprob htrace

/-- Fixed-`z` probability statement with the count constant existentially chosen after `z`.
There is no restriction on `z`; the witness is `4 C(z) + 1`. -/
theorem corollary35_probability_v3_scale_fixed_z_im_constant
    {Omega : Type*} [MeasurableSpace Omega]
    {n : ℕ} [NeZero n]
    (mu : Measure Omega)
    (matrix : Omega → Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {B c C : ℝ} (hB : 0 < B) (hc : 0 < c) (hC : 0 ≤ C)
    (good : Set Omega)
    (hprob : ProbabilityAtLeast mu good (1 - (n : ℝ) ^ (-10 : ℤ)))
    (htrace : ∀ omega ∈ good, ∀ eta,
      InUpperHalfPlane eta → ‖eta‖ ≤ 5 →
        Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c ≤ eta.im →
          (stieltjesTrace (matrix omega) z eta).im ≤ C) :
    ∃ C2 : ℝ, 0 ≤ C2 ∧
      ProbabilityAtLeast mu
        (Corollary35CountGood matrix z
          (Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c) C2)
        (1 - (n : ℝ) ^ (-10 : ℤ)) := by
  refine ⟨4 * C + 1, by linarith, ?_⟩
  exact corollary35_probability_v3_scale_from_im_event
    mu matrix z hB hc hC good hprob htrace

/-- Explicit quantifier-order version with both the imaginary-part constant and the good event
allowed to depend on `z`.  It asserts pointwise-in-`z` probability, not one simultaneous event
on the unbounded complex plane. -/
theorem corollary35_probability_v3_scale_zDependent_im
    {Omega : Type*} [MeasurableSpace Omega]
    {n : ℕ} [NeZero n]
    (mu : Measure Omega)
    (matrix : Omega → Matrix (Fin n) (Fin n) ℂ)
    {B c : ℝ} (hB : 0 < B) (hc : 0 < c)
    (C : ℂ → ℝ) (good : ℂ → Set Omega)
    (hC : ∀ z, 0 ≤ C z)
    (hprob : ∀ z,
      ProbabilityAtLeast mu (good z) (1 - (n : ℝ) ^ (-10 : ℤ)))
    (htrace : ∀ z, ∀ omega ∈ good z, ∀ eta,
      InUpperHalfPlane eta → ‖eta‖ ≤ 5 →
        Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c ≤ eta.im →
          (stieltjesTrace (matrix omega) z eta).im ≤ C z) :
    ∀ z, ProbabilityAtLeast mu
      (Corollary35CountGood matrix z
        (Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c) (4 * C z + 1))
      (1 - (n : ℝ) ^ (-10 : ℤ)) := by
  intro z
  exact corollary35_probability_v3_scale_from_im_event
    mu matrix z hB hc (hC z) (good z) (hprob z) (htrace z)

/-- The complete fixed-`z` bridge requested for Corollary 3.5: on a common good event, norm
comparison with a free trace plus a free imaginary-part bound imply the count conclusion.
The constants may depend on the already fixed `z`. -/
theorem corollary35_probability_v3_scale_from_free_im_comparison
    {Omega : Type*} [MeasurableSpace Omega]
    {n : ℕ} [NeZero n]
    (mu : Measure Omega)
    (matrix : Omega → Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {B c delta Cfree : ℝ}
    (hB : 0 < B) (hc : 0 < c) (hdelta : 0 ≤ delta) (hCfree : 0 ≤ Cfree)
    (freeTrace : ℂ → ℂ) (good : Set Omega)
    (hprob : ProbabilityAtLeast mu good (1 - (n : ℝ) ^ (-10 : ℤ)))
    (hcomparison : ∀ omega ∈ good, ∀ eta,
      InUpperHalfPlane eta → ‖eta‖ ≤ 5 →
        Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c ≤ eta.im →
          ‖stieltjesTrace (matrix omega) z eta - freeTrace eta‖ ≤ delta)
    (hfreeIm : ∀ eta, InUpperHalfPlane eta → ‖eta‖ ≤ 5 →
      Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c ≤ eta.im →
        (freeTrace eta).im ≤ Cfree) :
    ProbabilityAtLeast mu
      (Corollary35CountGood matrix z
        (Real.rpow B (-(1 / 8 : ℝ)) * Real.rpow n c)
        (4 * (Cfree + delta) + 1))
      (1 - (n : ℝ) ^ (-10 : ℤ)) := by
  apply corollary35_probability_v3_scale_from_im_event
    mu matrix z hB hc (add_nonneg hCfree hdelta) good hprob
  intro omega homega eta hetaUpper hetaNorm hetaScale
  apply im_le_of_norm_sub_le
    (stieltjesTrace (matrix omega) z eta) (freeTrace eta)
  · exact hcomparison omega homega eta hetaUpper hetaNorm hetaScale
  · exact hfreeIm eta hetaUpper hetaNorm hetaScale

end Arxiv2410V3

