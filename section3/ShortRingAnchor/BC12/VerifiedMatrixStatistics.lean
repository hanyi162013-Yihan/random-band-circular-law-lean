import ShortRingAnchor.BC12.VerifiedStatistics
import ShortRingAnchor.BC12.EigenvalueLogdet
import ShortRingAnchor.BC12.LogdetConvergence

/-!
# Correlation formulas for the existing Section 3 matrix enumeration

The Schur enumeration is only used on the proved full-measure simple
spectrum locus. Equality of characteristic-polynomial root multisets
identifies every symmetric statistic with Section 3's arbitrary root
enumeration. No measurability of that arbitrary ordering is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace ShortRingAnchor.BC12

/-- Characteristic roots counted with multiplicity do not depend on ordering. -/
theorem roots_eq_multiset_of_enumeration {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} {e : Fin n → ℂ}
    (he : IsEigenvalueEnumeration A e) :
    A.charpoly.roots = Finset.univ.val.map e := by
  rw [he, Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.mpr
    (fun i _ => Polynomial.X_sub_C_ne_zero (e i)))]
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]

/-- The statistic of any test agrees for two genuine eigenvalue enumerations. -/
theorem sum_test_eq_of_enumerations {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    {e d : Fin n → ℂ} (he : IsEigenvalueEnumeration A e)
    (hd : IsEigenvalueEnumeration A d) (f : ℂ → ℝ) :
    (∑ i, f (e i)) = ∑ i, f (d i) := by
  have hr := (roots_eq_multiset_of_enumeration he).symm.trans
    (roots_eq_multiset_of_enumeration hd)
  have hs := congrArg (fun s : Multiset ℂ => (s.map f).sum) hr
  simpa only [Multiset.map_map, Function.comp_def, Finset.sum_eq_multiset_sum] using hs

/-- Correlation identities transfer across a.e. equal symmetric statistics;
the eigenvalue orderings themselves need not be measurable or equal. -/
theorem GinibreCorrelationFormulas.congr_statistics
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    {e d : Ω → Fin n → ℂ} (h : GinibreCorrelationFormulas μ e)
    (heq : ∀ f : ℂ → ℝ, eigenvalueStatistic e f =ᵐ[μ] eigenvalueStatistic d f) :
    GinibreCorrelationFormulas μ d := by
  constructor
  · intro f hf hi
    obtain ⟨hint, hmean⟩ := h.firstMoment f hf hi
    exact ⟨hint.congr (heq f), (integral_congr_ae (heq f).symm).trans hmean⟩
  · intro f hf hi
    obtain ⟨hint, hmean⟩ := h.secondMoment f hf hi
    have hcent : (fun x => (eigenvalueStatistic e f x - ∫ y, eigenvalueStatistic e f y ∂μ)^2)
        =ᵐ[μ] (fun x => (eigenvalueStatistic d f x - ∫ y, eigenvalueStatistic d f y ∂μ)^2) := by
      have hm := integral_congr_ae (heq f)
      filter_upwards [heq f] with x hx
      rw [hx, hm]
    exact ⟨hint.congr hcent, (integral_congr_ae hcent.symm).trans hmean⟩

/-- BC12 one- and two-point formulas for an actual matrix process whose
flattened entries have the specified independent complex Gaussian law. -/
theorem verifiedGinibreMatrixCorrelations
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : ℕ} (hn : 0 < n) (G : Ω → Matrix (Fin n) (Fin n) ℂ)
    (hG : HasLaw (fun sample (ij : Fin n × Fin n) => G sample ij.1 ij.2)
      (Ginibre.gaussianMatrixLaw n n) μ) :
    GinibreCorrelationFormulas μ (fun sample => matrixEigenvalues (G sample)) := by
  have hc := GinibreCorrelationFormulas.comp_hasLaw hG hn (verifiedGinibreCorrelations hn)
  apply hc.congr_statistics
  intro f
  have hs : ∀ᵐ sample ∂μ, (G sample).charpoly.Separable := by
    have h := Ginibre.gaussianMatrix_charpoly_separable_ae n (by exact_mod_cast hn : (0 : ℝ) < n)
    rw [← hG.map_eq] at h
    exact ae_of_ae_map hG.aemeasurable h
  filter_upwards [hs] with sample hsample
  apply congrArg (fun x : ℝ => x / (n : ℝ))
  exact sum_test_eq_of_enumerations
    (Ginibre.charpoly_eq_prod_schurSpectrum (G sample) hsample)
    (matrixEigenvalues_spec (G sample)) f

/-- BC12 full logarithmic-potential convergence with no BC12 input:
all finite formulas now follow from the explicit Gaussian entry law. -/
theorem ginibre_logdet_convergesInProbability_of_entryLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {N : ℕ → ℕ} (hNpos : ∀ k, 0 < N k) (hN : Tendsto N atTop atTop)
    (G : ∀ k, Ω → Matrix (Fin (N k)) (Fin (N k)) ℂ)
    (hG : ∀ k, HasLaw (fun sample (ij : Fin (N k) × Fin (N k)) => G k sample ij.1 ij.2)
      (Ginibre.gaussianMatrixLaw (N k) (N k)) μ) (z : ℂ) :
    ConvergesInProbability μ (fun k sample => normalizedShiftLogDet (G k sample) z)
      (circularLogPotential z) :=
  ginibre_matrix_logdet_convergesInProbability_of_formulas hNpos hN G
    (fun k => verifiedGinibreProjection (N k))
    (fun k => verifiedGinibreMatrixCorrelations (hNpos k) (G k) (hG k)) z

end ShortRingAnchor.BC12
