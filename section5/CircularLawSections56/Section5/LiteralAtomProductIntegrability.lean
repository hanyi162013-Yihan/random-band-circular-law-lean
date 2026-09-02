import CircularLawSections56.Section5.LiteralAtomRowCost

/-! # Integrable actual products from one-atom logarithmic moments

This removes the need for a separate planar-density integrability theorem in
the real and tapered branches.  No independence is needed until identifying
the product law: one-coordinate marginals suffice for the finite-product bound.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1200000

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

theorem matrix_pathwise_remainder_right
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (R P : Matrix ι ι ℂ) (hR : IsUnit R) (hP : P ≠ 0) :
    |Real.log ‖P * R‖ - Real.log ‖P‖| ≤ matrixInverseRowCost R := by
  have hRh : IsUnit Rᴴ := hR.star
  have hPh : Pᴴ ≠ 0 := by
    intro hz
    apply hP
    apply norm_eq_zero.1
    rw [← Matrix.l2_opNorm_conjTranspose P, hz, norm_zero]
  have h := matrix_pathwise_remainder Rᴴ Pᴴ hRh hPh
  simpa only [← Matrix.conjTranspose_mul, Matrix.l2_opNorm_conjTranspose,
    matrixInverseRowCost, ← Matrix.conjTranspose_nonsing_inv] using h

theorem abs_log_chronologicalProduct_le_sum_cost
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (xs : List (Matrix ι ι ℂ))
    (hUnit : ∀ A ∈ xs, IsUnit A) :
    |Real.log ‖chronologicalProduct xs‖| ≤ (xs.map matrixInverseRowCost).sum := by
  induction xs with
  | nil => simp [chronologicalProduct]
  | cons A xs ih =>
      have hu : ∀ B ∈ xs, IsUnit B := fun B hB => hUnit B (List.mem_cons_of_mem A hB)
      have h := matrix_pathwise_remainder_right A (chronologicalProduct xs)
        (hUnit A List.mem_cons_self) (chronologicalProduct_isUnit_of_forall_mem xs hu).ne_zero
      rw [chronologicalProduct_cons, List.map_cons, List.sum_cons]
      have ht := abs_add_le (Real.log ‖chronologicalProduct xs * A‖ -
        Real.log ‖chronologicalProduct xs‖) (Real.log ‖chronologicalProduct xs‖)
      rw [sub_add_cancel] at ht
      linarith [ih hu]

theorem literal_open_product_integrable_of_atom_log
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n d : ℕ) {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (hcenter : center ≠ 0)
    (z : ℂ) (q : ExteriorDegree (d + 1))
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (rows : Ω → Fin n → PaperIndicatorAtomRow d) (hRows : Measurable rows)
    (hMarginal : ∀ t s, MeasurePreserving (fun ω => rows ω t s) μ ν)
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1)
    (K : ℝ) (hzero : ∀ᵐ u : ℂ ∂ν, u ≠ 0)
    (hNegInt : Integrable (fun u : ℂ => negativeLog ‖u‖) ν)
    (hNeg : ∫ u : ℂ, negativeLog ‖u‖ ∂ν ≤ K) :
    Integrable (fun ω => profile.paperIndicatorOpenPressure center z q (rows ω)) μ ∧
      ∀ᵐ ω ∂μ, IsUnit (profile.paperIndicatorOpenExteriorProduct center z q (rows ω)) := by
  classical
  let : Nonempty (ExteriorIndex (d + 1) q) := exteriorIndex_nonempty_bridge _ _
  let R := fun row : PaperIndicatorAtomRow d => profile.paperIndicatorOpenExteriorRow center z q row
  let cost := fun t ω => literalRowLogMajorant d profile center z q (rows ω t)
  have hc : ∀ t, Integrable (cost t) μ := fun t =>
    (literalRowLogMajorant_integrable_and_bound μ d profile hc₀ center z q ν
      (fun ω => rows ω t) ((measurable_pi_apply t).comp hRows) (hMarginal t)
      hInt hSecond K hzero hNegInt hNeg).1
  have he : ∀ᵐ ω ∂μ, ∀ t : Fin n,
      IsUnit (R (rows ω t)) ∧ matrixInverseRowCost (R (rows ω t)) ≤ cost t ω := by
    rw [ae_all_iff]
    intro t
    filter_upwards [(hMarginal t 0).quasiMeasurePreserving.ae hzero,
      (hMarginal t (Fin.last (d + 1))).quasiMeasurePreserving.ae hzero] with ω hl hr
    have hleft := mul_ne_zero (profile.b_ne_zero hc₀ 0) hl
    have hright := mul_ne_zero (profile.b_ne_zero hc₀ (Fin.last (d + 1))) hr
    exact ⟨literal_exterior_row_isUnit_of_edges d profile center hcenter z q (rows ω t) hleft hright,
      matrixInverseRowCost_le_literalRowLogMajorant d profile center hcenter z q (rows ω t)
        hleft hright⟩
  have hu : ∀ᵐ ω ∂μ, IsUnit (profile.paperIndicatorOpenExteriorProduct center z q (rows ω)) := by
    filter_upwards [he] with ω hω
    apply chronologicalProduct_isUnit_of_forall_mem
    intro A hA
    simp only [List.mem_ofFn] at hA
    obtain ⟨t, rfl⟩ := hA
    exact (hω t).1
  have hdom : ∀ᵐ ω ∂μ, |profile.paperIndicatorOpenPressure center z q (rows ω)| ≤ ∑ t, cost t ω := by
    filter_upwards [he] with ω hω
    have h := abs_log_chronologicalProduct_le_sum_cost (List.ofFn (fun t => R (rows ω t))) (by
      intro A hA
      simp only [List.mem_ofFn] at hA
      obtain ⟨t, rfl⟩ := hA
      exact (hω t).1)
    have hs : ((List.ofFn (fun t => R (rows ω t))).map matrixInverseRowCost).sum =
        ∑ t, matrixInverseRowCost (R (rows ω t)) := by
      rw [List.map_ofFn, List.sum_ofFn]
      rfl
    rw [hs] at h
    exact h.trans (Finset.sum_le_sum fun t _ => (hω t).2)
  have hm : Measurable (fun ω => profile.paperIndicatorOpenPressure center z q (rows ω)) :=
    Real.measurable_log.comp
      ((profile.continuous_paperIndicatorOpenExteriorProduct center z q n).norm.measurable.comp hRows)
  exact ⟨(integrable_finsetSum Finset.univ (fun t _ => hc t)).mono'
    hm.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hdom), hu⟩

end CircularLawSections56.Section5
