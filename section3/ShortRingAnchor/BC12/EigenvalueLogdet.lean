import ShortRingAnchor.BC12.KnownFormulas
import ShortRingAnchor.SourceStatement
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# From eigenvalue statistics to the actual matrix logarithmic determinant

The algebraic premise says that the supplied list enumerates the roots of
the characteristic polynomial with multiplicity.  It is a representation
condition, not an asymptotic or probabilistic estimate.  The one-point
formula itself proves avoidance of every fixed point, so no extra a.s.
nonsingularity assumption is needed in the logarithmic expansion.
-/

open Filter Set MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace ShortRingAnchor.BC12

/-- Exact algebraic meaning of an eigenvalue enumeration, with algebraic
multiplicity.  This does not require any ordering or distinctness. -/
def IsEigenvalueEnumeration {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (eigenvalue : Fin n → ℂ) : Prop :=
  A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (eigenvalue i))

/-- Every complex matrix admits such an enumeration: the characteristic
polynomial splits and has exactly its degree many roots with multiplicity.
Thus the representation condition is not an external mathematical input. -/
theorem exists_eigenvalueEnumeration {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ eigenvalue : Fin n → ℂ, IsEigenvalueEnumeration A eigenvalue := by
  classical
  let roots := A.charpoly.roots.toList
  have hlength : roots.length = n := by
    dsimp only [roots]
    rw [Multiset.length_toList, ← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let eigenvalue : Fin n → ℂ := fun i => roots[(finCongr hlength.symm i).val]
  refine ⟨eigenvalue, ?_⟩
  unfold IsEigenvalueEnumeration
  rw [(IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic A.charpoly_monic]
  have hprod : (∏ i : Fin n, (Polynomial.X - Polynomial.C (eigenvalue i))) =
      ∏ i : Fin roots.length, (Polynomial.X - Polynomial.C roots[i.val]) :=
    Fintype.prod_equiv (finCongr hlength.symm) _ _ (fun _ => rfl)
  rw [hprod, Fin.prod_univ_fun_getElem roots
    (fun x => (Polynomial.X : Polynomial ℂ) - Polynomial.C x)]
  simp [roots, ← Multiset.prod_coe, ← Multiset.map_coe]

/-- A fixed choice of an algebraic-multiplicity enumeration.  Only symmetric
statistics are used; no measurability of this arbitrary ordering is claimed. -/
def matrixEigenvalues {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Fin n → ℂ :=
  Classical.choose (exists_eigenvalueEnumeration A)

/-- The chosen enumeration has its proved algebraic meaning. -/
theorem matrixEigenvalues_spec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    IsEigenvalueEnumeration A (matrixEigenvalues A) :=
  Classical.choose_spec (exists_eigenvalueEnumeration A)

/-- The first correlation formula rules out a fixed eigenvalue by applying
it to a singleton indicator.  No independent geometric null-set premise is
being smuggled into the use of `Real.log`. -/
theorem eigenvalues_ne_fixed_ae_of_firstMoment
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {n : ℕ} (hn : 0 < n)
    {eigenvalue : Omega → Fin n → ℂ}
    (hcorrelation : GinibreCorrelationFormulas mu eigenvalue) (z : ℂ) :
    ∀ᵐ sample ∂mu, ∀ i, eigenvalue sample i ≠ z := by
  let f : ℂ → ℝ := ({z} : Set ℂ).indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator (measurableSet_singleton z)
  have hzero : (fun w => f w * ginibreOnePointDensity n w) =ᵐ[volume] 0 := by
    filter_upwards [(volume : Measure ℂ).ae_ne z] with w hw
    simp [f, hw]
  have hint : Integrable (fun w => f w * ginibreOnePointDensity n w) :=
    (integrable_zero ℂ ℝ volume).congr hzero.symm
  obtain ⟨hstatInt, hstatMean⟩ := hcorrelation.firstMoment f hf hint
  have hmean0 : (∫ sample, eigenvalueStatistic eigenvalue f sample ∂mu) = 0 := by
    rw [hstatMean, integral_congr_ae hzero]
    simp only [Pi.zero_apply, integral_zero]
  have hnonneg (sample : Omega) : 0 ≤ eigenvalueStatistic eigenvalue f sample := by
    apply div_nonneg _ (Nat.cast_nonneg n)
    exact Finset.sum_nonneg fun i _ => indicator_nonneg (fun _ _ => zero_le_one) _
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg hstatInt).mp hmean0
  filter_upwards [hae] with sample hsample
  have hdim : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum : (∑ i, f (eigenvalue sample i)) = 0 := by
    change (∑ i, f (eigenvalue sample i)) / (n : ℝ) = 0 at hsample
    exact (div_eq_zero_iff).mp hsample |>.resolve_right hdim
  intro i hi
  have hi0 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ Finset.univ) =>
      show 0 ≤ f (eigenvalue sample j) from indicator_nonneg (fun _ _ => zero_le_one) _)).mp hsum
      i (Finset.mem_univ i)
  simp [f, hi] at hi0

/-- The characteristic-polynomial factorization implies the norm of the
shifted determinant is the product of distances to the eigenvalues. -/
theorem norm_shifted_det_eq_prod_of_enumeration
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {eigenvalue : Fin n → ℂ}
    (henum : IsEigenvalueEnumeration A eigenvalue) (z : ℂ) :
    ‖(A - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det‖ =
      ∏ i, ‖eigenvalue i - z‖ := by
  have hscalar : Matrix.scalar (Fin n) z = z • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have hnorm : ‖(A - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det‖ = ‖A.charpoly.eval z‖ := by
    rw [Matrix.eval_charpoly, hscalar, ← neg_sub A (z • (1 : Matrix (Fin n) (Fin n) ℂ)),
      Matrix.det_neg, norm_mul]
    simp
  rw [hnorm, henum]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, norm_prod, norm_sub_rev]

/-- Source formula (3.8) as an eigenvalue statistic, on the event proved
above.  The nonvanishing guard is essential for a product logarithm. -/
theorem normalizedShiftLogDet_eq_eigenvalueStatistic
    {Omega : Type*} {n : ℕ}
    {A : Omega → Matrix (Fin n) (Fin n) ℂ}
    {eigenvalue : Omega → Fin n → ℂ} {sample : Omega} {z : ℂ}
    (henum : IsEigenvalueEnumeration (A sample) (eigenvalue sample))
    (hne : ∀ i, eigenvalue sample i ≠ z) :
    normalizedShiftLogDet (A sample) z =
      eigenvalueStatistic eigenvalue (fun w => Real.log ‖w - z‖) sample := by
  unfold normalizedShiftLogDet eigenvalueStatistic
  rw [norm_shifted_det_eq_prod_of_enumeration henum z,
    Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hne i)))]

end ShortRingAnchor.BC12
