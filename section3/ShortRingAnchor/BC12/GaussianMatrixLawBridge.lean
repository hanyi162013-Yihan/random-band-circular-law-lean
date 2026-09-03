import ShortRingAnchor.BC12.GaussianEntryLawBridge
import ShortRingAnchor.BC12.GinibreSmallBall
import ShortRingAnchor.BC12.VerifiedMatrixStatistics

/-!
# One Gaussian model for both Section 3 estimates

The Gaussian-column least-singular-value theorem and the Gaussian-entry
correlation theorem are connected by equality of their actual laws.
There is no second, unrelated Gaussian-law hypothesis.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace ShortRingAnchor.BC12

local instance gaussianBridgeMatrixMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := borel _
local instance gaussianBridgeMatrixBorelSpace (n : ℕ) :
    BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩

/-- BC12 model coordinates: reading matrix entries is Borel measurable. -/
theorem measurable_matrixEntries (n : ℕ) :
    Measurable (fun A : Matrix (Fin n) (Fin n) ℂ =>
      fun ij : Fin n × Fin n => A ij.1 ij.2) := by
  apply Continuous.measurable
  exact continuous_pi (fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

/-- The two normalization factors give real variance `1/(2n)`. -/
theorem normalizedGinibre_real_scale {n : ℕ} (hn : 0 < n) :
    0 < (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt 2)⁻¹ ∧
      2 * ((Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt 2)⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
  constructor
  · positivity
  · rw [mul_pow, inv_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring

/-- A normalized Gaussian column has independent planar Gaussian coordinates. -/
theorem normalizedGinibre_column_map {n : ℕ} (hn : 0 < n) :
    (stdGaussian (GinibreLSV.ComplexColumn n)).map
      (fun C i => (((Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt 2)⁻¹ : ℝ) : ℂ) * C i) =
        Measure.pi (fun _ : Fin n => Ginibre.gaussianEntryLaw n) := by
  let r : ℝ := (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt 2)⁻¹
  have hs := normalizedGinibre_real_scale hn
  have hentry := scaled_stdGaussian_complex_eq_entryLaw
    (by exact_mod_cast hn : (0 : ℝ) < n) hs.1 hs.2
  letI : IsProbabilityMeasure ((stdGaussian ℂ).map (fun z => (r : ℂ) * z)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [stdGaussian_complexColumn_eq_pi, Measure.map_map (by fun_prop) (by fun_prop)]
  change (Measure.pi (fun _ : Fin n => stdGaussian ℂ)).map (fun C i => (r : ℂ) * C i) = _
  rw [Measure.pi_map_pi (fun _ => by fun_prop)]
  exact congrArg Measure.pi (funext (fun _ => hentry))

/-- Flattening a family of independent columns produces the independent-entry law.
The transpose in the index map is only a finite coordinate permutation. -/
theorem pi_columns_flatten_map (n : ℕ) {ν : Measure ℂ} [IsProbabilityMeasure ν] :
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => ν))).map
      (fun C (ij : Fin n × Fin n) => C ij.2 ij.1) =
        Measure.pi (fun _ : Fin n × Fin n => ν) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have he : (fun C : Fin n → Fin n → ℂ => fun ij : Fin n × Fin n => C ij.2 ij.1) ⁻¹'
      univ.pi s = univ.pi (fun j => univ.pi (fun i => s (i, j))) := by
    ext C
    simp only [mem_preimage, mem_univ_pi]
    exact ⟨fun h j i => h (i, j), fun h ij => h ij.2 ij.1⟩
  rw [he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Finset.prod_comm, Fintype.prod_prod_type]

/-- The earlier normalized column law equals the normalized iid entry law
after reading the actual matrix entries. This discharges the model bridge. -/
theorem normalizedGinibreLaw_flatten {n : ℕ} (hn : 0 < n) :
    (normalizedGinibreLaw n).map (fun A (ij : Fin n × Fin n) => A ij.1 ij.2) =
      Ginibre.gaussianMatrixLaw n n := by
  letI := Ginibre.gaussianEntryLaw_isProbability (by exact_mod_cast hn : (0 : ℝ) < n)
  let r : ℝ := (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt 2)⁻¹
  let columnMap : GinibreLSV.ComplexColumn n → Fin n → ℂ := fun C i => (r : ℂ) * C i
  have hc : MeasurePreserving columnMap (stdGaussian (GinibreLSV.ComplexColumn n))
      (Measure.pi (fun _ : Fin n => Ginibre.gaussianEntryLaw n)) :=
    ⟨by fun_prop, normalizedGinibre_column_map hn⟩
  have hp := measurePreserving_pi
    (fun _ : Fin n => stdGaussian (GinibreLSV.ComplexColumn n))
    (fun _ : Fin n => Measure.pi (fun _ : Fin n => Ginibre.gaussianEntryLaw n))
    (fun _ => hc)
  have hflat := pi_columns_flatten_map n (ν := Ginibre.gaussianEntryLaw n)
  rw [← hp.map_eq, Measure.map_map (by fun_prop) hp.measurable] at hflat
  rw [normalizedGinibreLaw,
    Measure.map_map (measurable_matrixEntries n) (continuous_normalizedGinibreMatrix n).measurable]
  convert hflat using 1
  · congr 1
    funext C ij
    dsimp only [Function.comp_def, columnMap]
    simp only [normalizedGinibreMatrix, GinibreLSV.normalizedComplexGinibreMatrix,
      GinibreLSV.matrixOfColumns, Matrix.smul_apply, smul_eq_mul]
    dsimp only [r]
    push_cast
    ring
  · rfl

/-- A matrix with the existing Section 3 Ginibre law satisfies the proved
independent-entry law, with no correlation or density premise. -/
theorem normalizedGinibre_hasEntryLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : ℕ} (hn : 0 < n) {G : Ω → Matrix (Fin n) (Fin n) ℂ}
    (hG : HasLaw G (normalizedGinibreLaw n) μ) :
    HasLaw (fun sample (ij : Fin n × Fin n) => G sample ij.1 ij.2)
      (Ginibre.gaussianMatrixLaw n n) μ :=
  HasLaw.fun_comp ⟨(measurable_matrixEntries n).aemeasurable, normalizedGinibreLaw_flatten hn⟩ hG

/-- BC12 finite formulas on precisely the Gaussian law already used by
the proved Section 3 least-singular-value estimate. -/
theorem normalizedGinibre_correlations
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : ℕ} (hn : 0 < n) {G : Ω → Matrix (Fin n) (Fin n) ℂ}
    (hG : HasLaw G (normalizedGinibreLaw n) μ) :
    GinibreCorrelationFormulas μ (fun sample => matrixEigenvalues (G sample)) :=
  verifiedGinibreMatrixCorrelations hn G (normalizedGinibre_hasEntryLaw hn hG)

/-- BC12 finite formulas on the concrete Gaussian-column probability space.
No law, density, correlation, or projection hypothesis is supplied here. -/
theorem canonical_normalizedGinibre_correlations {n : ℕ} (hn : 0 < n) :
    GinibreCorrelationFormulas (GinibreLSV.complexGinibreColumns n)
      (fun C => matrixEigenvalues (normalizedGinibreMatrix n C)) :=
  normalizedGinibre_correlations hn (normalizedGinibreMatrix_hasLaw n)

/-- BC12 full-logdet input eliminated: one genuine Gaussian model premise
implies the required log-potential limit for every fixed finite shift. -/
theorem ginibre_logdet_convergesInProbability_of_ginibreLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {N : ℕ → ℕ} (hNpos : ∀ k, 0 < N k) (hN : Tendsto N atTop atTop)
    (G : ∀ k, Ω → Matrix (Fin (N k)) (Fin (N k)) ℂ)
    (hG : ∀ k, HasLaw (G k) (normalizedGinibreLaw (N k)) μ) (z : ℂ) :
    ConvergesInProbability μ (fun k sample => normalizedShiftLogDet (G k sample) z)
      (circularLogPotential z) :=
  ginibre_logdet_convergesInProbability_of_entryLaw hNpos hN G
    (fun k => normalizedGinibre_hasEntryLaw (hNpos k) (hG k)) z

end ShortRingAnchor.BC12
