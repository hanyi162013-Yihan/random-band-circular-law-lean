/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/EtaUniformization.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.ResolventPerturbation
import Vendor.Arxiv2410.V3.ProbabilityEvent
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Finite-net uniformization in the spectral parameter

This file supplies the deterministic resolvent-continuity and finite-union-bound steps that
are implicit in the passage from pointwise control in `eta` to the uniform clause of v3
Proposition 3.4.  It does not postulate a net: a finite family of centres together with an
explicit covering proof is carried as data.
-/

namespace Arxiv2410V3

open Matrix Complex MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

section ResolventContinuity

variable {n : ℕ}

/-- Resolvent identity with the matrix fixed and only the upper-half-plane parameter changed. -/
theorem greenFunction_sub_greenFunction_eta
    (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {eta theta : ℂ} (heta : 0 < eta.im) (htheta : 0 < theta.im) :
    greenFunction X z eta - greenFunction X z theta =
      (eta - theta) • (greenFunction X z eta * greenFunction X z theta) := by
  have hleft := (shiftedHermitian_inv_mul_and_mul_inv
    (hermitization X z) (hermitization_isHermitian X z) heta).1
  have hright := (shiftedHermitian_inv_mul_and_mul_inv
    (hermitization X z) (hermitization_isHermitian X z) htheta).2
  rw [greenFunction, greenFunction]
  rw [inverse_sub_inverse_of_mul_eq_one
    (hermitization X z - eta • (1 : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ))
    (hermitization X z - theta • (1 : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ))
    _ _ hleft hright]
  simp only [sub_sub_sub_cancel_left]
  rw [← sub_smul]
  simp only [mul_smul_comm, smul_mul_assoc, mul_one]

/-- Explicit upper-half-plane Lipschitz bound for the normalized Stieltjes trace:
`|m_z(eta)-m_z(theta)| <= |eta-theta| /(Im eta Im theta)`.

This is the continuity estimate needed for a finite `eta`-net.  The bound is independent of
`X`, `z`, and the dimension. -/
theorem norm_stieltjesTrace_sub_eta_le
    [NeZero n]
    (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {eta theta : ℂ} (heta : 0 < eta.im) (htheta : 0 < theta.im) :
    ‖stieltjesTrace X z eta - stieltjesTrace X z theta‖ ≤
      ‖eta - theta‖ / (eta.im * theta.im) := by
  rw [stieltjesTrace, stieltjesTrace, ← normalizedTrace_sub]
  calc
    ‖normalizedTrace (greenFunction X z eta - greenFunction X z theta)‖ ≤
        ‖greenFunction X z eta - greenFunction X z theta‖ :=
      norm_normalizedTrace_le_l2Operator _
    _ = ‖(eta - theta) •
        (greenFunction X z eta * greenFunction X z theta)‖ := by
      rw [greenFunction_sub_greenFunction_eta X z heta htheta]
    _ = ‖eta - theta‖ * ‖greenFunction X z eta * greenFunction X z theta‖ :=
      norm_smul _ _
    _ ≤ ‖eta - theta‖ *
        ((eta.im)⁻¹ * (theta.im)⁻¹) := by
      gcongr
      calc
        ‖greenFunction X z eta * greenFunction X z theta‖ ≤
            ‖greenFunction X z eta‖ * ‖greenFunction X z theta‖ := norm_mul_le _ _
        _ ≤ (eta.im)⁻¹ * (theta.im)⁻¹ := by
          gcongr
          · exact norm_shiftedHermitian_inv_le_inv_im
              (hermitization X z) (hermitization_isHermitian X z) heta
          · exact norm_shiftedHermitian_inv_le_inv_im
              (hermitization X z) (hermitization_isHermitian X z) htheta
    _ = ‖eta - theta‖ / (eta.im * theta.im) := by
      field_simp

end ResolventContinuity

section FiniteNet

/-- A finite covering certificate for a set of spectral parameters.  No particular grid
construction is baked into the theorem: an application may use a rectangular rational grid,
or any other finite family for which the two elementary fields can be proved. -/
structure FiniteEtaNet (κ : Type*) [Fintype κ] (domain : Set ℂ) where
  center : κ → ℂ
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  center_mem : ∀ i, center i ∈ domain
  cover : ∀ eta ∈ domain, ∃ i, dist eta (center i) ≤ radius

/-- The simultaneous event on the finitely many centres of a net. -/
def FiniteEtaNet.gridGood
    {κ Ω : Type*} [Fintype κ] {domain : Set ℂ}
    (net : FiniteEtaNet κ domain) (trace : Ω → ℂ → ℂ) (C : ℝ) : Set Ω :=
  {omega | ∀ i, ‖trace omega (net.center i)‖ ≤ C}

/-- The desired event on every parameter in the domain. -/
def UniformEtaGood
    {Ω : Type*} (domain : Set ℂ) (trace : Ω → ℂ → ℂ) (C : ℝ) : Set Ω :=
  {omega | ∀ eta ∈ domain, ‖trace omega eta‖ ≤ C}

/-- Abstract finite-net closure.  A bound `L * dist` between parameters, a covering radius
`r`, and the explicit budget `L*r <= margin` turn a grid bound `C` into the uniform bound
`C+margin`. -/
theorem finiteEtaNet_gridGood_subset_uniformEtaGood
    {κ Ω : Type*} [Fintype κ] {domain : Set ℂ}
    (net : FiniteEtaNet κ domain) (trace : Ω → ℂ → ℂ)
    {L margin C : ℝ}
    (hL : 0 ≤ L)
    (hcontinuity : ∀ omega eta theta,
      eta ∈ domain → theta ∈ domain →
        ‖trace omega eta - trace omega theta‖ ≤ L * dist eta theta)
    (hmargin : L * net.radius ≤ margin) :
    net.gridGood trace C ⊆ UniformEtaGood domain trace (C + margin) := by
  intro omega homega eta heta
  obtain ⟨i, hi⟩ := net.cover eta heta
  calc
    ‖trace omega eta‖ ≤
        ‖trace omega eta - trace omega (net.center i)‖ +
          ‖trace omega (net.center i)‖ := by
      simpa only [sub_add_cancel] using
        norm_add_le (trace omega eta - trace omega (net.center i))
          (trace omega (net.center i))
    _ ≤ L * dist eta (net.center i) + C := by
      gcongr
      · exact hcontinuity omega eta (net.center i) heta (net.center_mem i)
      · exact homega i
    _ ≤ L * net.radius + C := by
      simpa only [add_comm] using
        add_le_add_right (mul_le_mul_of_nonneg_left hi hL) C
    _ ≤ C + margin := by linarith

/-- On a domain bounded away from the real axis, the preceding resolvent estimate has the
ordinary Lipschitz constant `v0⁻²`. -/
theorem norm_stieltjesTrace_sub_eta_le_of_im_ge
    {n : ℕ} [NeZero n]
    (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {v0 : ℝ} (hv0 : 0 < v0) {eta theta : ℂ}
    (heta : v0 ≤ eta.im) (htheta : v0 ≤ theta.im) :
    ‖stieltjesTrace X z eta - stieltjesTrace X z theta‖ ≤
      v0⁻¹ ^ 2 * dist eta theta := by
  have heta_pos : 0 < eta.im := hv0.trans_le heta
  have htheta_pos : 0 < theta.im := hv0.trans_le htheta
  have hprod : v0 * v0 ≤ eta.im * theta.im :=
    mul_le_mul heta htheta hv0.le (hv0.le.trans heta)
  calc
    ‖stieltjesTrace X z eta - stieltjesTrace X z theta‖ ≤
        ‖eta - theta‖ / (eta.im * theta.im) :=
      norm_stieltjesTrace_sub_eta_le X z heta_pos htheta_pos
    _ ≤ ‖eta - theta‖ / (v0 * v0) := by
      exact div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hv0 hv0) hprod
    _ = v0⁻¹ ^ 2 * dist eta theta := by
      rw [dist_eq]
      field_simp

/-- Concrete finite-net closure for the paper's normalized Hermitized resolvent trace.

It is pointwise in `z`: neither the net nor the conclusion asks for any uniformity in `z`.
The margin is exactly `v0⁻² * radius`. -/
theorem stieltjesTrace_gridGood_subset_uniformEtaGood
    {κ Ω : Type*} [Fintype κ] {domain : Set ℂ}
    (net : FiniteEtaNet κ domain)
    {n : ℕ} [NeZero n]
    (matrix : Ω → Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    {v0 C : ℝ} (hv0 : 0 < v0)
    (hdomain : ∀ eta ∈ domain, v0 ≤ eta.im) :
    net.gridGood (fun omega eta => stieltjesTrace (matrix omega) z eta) C ⊆
      UniformEtaGood domain
        (fun omega eta => stieltjesTrace (matrix omega) z eta)
        (C + v0⁻¹ ^ 2 * net.radius) := by
  apply finiteEtaNet_gridGood_subset_uniformEtaGood net
    (L := v0⁻¹ ^ 2) (margin := v0⁻¹ ^ 2 * net.radius)
  · positivity
  · intro omega eta theta heta htheta
    exact norm_stieltjesTrace_sub_eta_le_of_im_ge
      (matrix omega) z hv0 (hdomain eta heta) (hdomain theta htheta)
  · exact le_rfl

end FiniteNet

section FiniteUnionBound

variable {κ Ω : Type*} [Fintype κ]
  [MeasurableSpace Ω] (mu : Measure Ω)

/-- The complement of a finite intersection obeys the exact finite union bound. -/
theorem measure_compl_iInter_le_sum
    (good : κ → Set Ω) :
    mu (⋂ i, good i)ᶜ ≤ ∑ i, mu (good i)ᶜ := by
  rw [Set.compl_iInter]
  exact measure_iUnion_fintype_le mu (fun i => (good i)ᶜ)

/-- A finite family of pointwise failure bounds gives a failure bound for their common event. -/
theorem measure_compl_iInter_le_nsmul
    (good : κ → Set Ω) (q : ENNReal)
    (hpoint : ∀ i, mu (good i)ᶜ ≤ q) :
    mu (⋂ i, good i)ᶜ ≤ Fintype.card κ • q := by
  calc
    mu (⋂ i, good i)ᶜ ≤ ∑ i, mu (good i)ᶜ :=
      measure_compl_iInter_le_sum mu good
    _ ≤ ∑ _i : κ, q := Finset.sum_le_sum fun i _ => hpoint i
    _ = Fintype.card κ • q := by simp

/-- Probability form of the finite union bound.  If the sum of all pointwise failure budgets
is at most `epsilon`, then the finite grid-good event has probability at least `1-epsilon`.
This is the probability-preserving part of `eta`-uniformization. -/
theorem probabilityAtLeast_iInter_of_finite_failure_bounds
    [IsProbabilityMeasure mu]
    (good : κ → Set Ω) (hmeas : ∀ i, MeasurableSet (good i))
    (q : ENNReal) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hpoint : ∀ i, mu (good i)ᶜ ≤ q)
    (htotal : Fintype.card κ • q ≤ ENNReal.ofReal epsilon) :
    ProbabilityAtLeast mu (⋂ i, good i) (1 - epsilon) := by
  have hgrid_meas : MeasurableSet (⋂ i, good i) := MeasurableSet.iInter hmeas
  have hfailure : mu (⋂ i, good i)ᶜ ≤ ENNReal.ofReal epsilon :=
    (measure_compl_iInter_le_nsmul mu good q hpoint).trans htotal
  have hprob : mu (⋂ i, good i) = 1 - mu (⋂ i, good i)ᶜ := by
    simpa only [compl_compl] using
      (prob_compl_eq_one_sub (μ := mu) hgrid_meas.compl)
  rw [ProbabilityAtLeast, ENNReal.ofReal_sub _ hepsilon,
    ENNReal.ofReal_one, hprob]
  exact tsub_le_tsub_left hfailure 1

omit [MeasurableSpace Ω] in
/-- The finite intersection of the pointwise centre events is exactly `gridGood`. -/
theorem iInter_centerGood_eq_gridGood
    {domain : Set ℂ} (net : FiniteEtaNet κ domain)
    (trace : Ω → ℂ → ℂ) (C : ℝ) :
    (⋂ i, {omega | ‖trace omega (net.center i)‖ ≤ C}) = net.gridGood trace C := by
  ext omega
  simp [FiniteEtaNet.gridGood]

end FiniteUnionBound

end Arxiv2410V3

