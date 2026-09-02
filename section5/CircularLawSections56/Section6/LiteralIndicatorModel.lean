import CircularLawSections56.Section6.PhysicalReplacementBridge
import CircularLawSections56.Section6.TriangularReplacement
import CircularLawSections56.Section5.LiteralPhysicalDeterminantSeam

/-!
# The literal band matrix as a replacement-principle model

This is the actual Section 4 matrix, reindexed from `ZMod N` to `Fin N`.
The non-aliasing condition is `d + 2 ≤ N`, because a row has `d + 2` slots.
Its normalized expected Hilbert--Schmidt square is at most one directly from
the normalized variance profile and the atom second moment, not a new premise.
-/

open Filter MeasureTheory Topology
open scoped ENNReal BigOperators

noncomputable section

namespace CircularLawSections56.Section6

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights TaoVuReplacement

theorem sparse_row_norm_square_sum
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f : κ → ι) (hf : Function.Injective f) (a : κ → ℂ) :
    (∑ j, ‖∑ k, if j = f k then a k else 0‖ ^ 2) = ∑ k, ‖a k‖ ^ 2 := by
  classical
  have hpoint : ∀ j, ‖∑ k, if j = f k then a k else 0‖ ^ 2 =
      ∑ k, if j = f k then ‖a k‖ ^ 2 else 0 := by
    intro j
    by_cases hj : ∃ k, j = f k
    · obtain ⟨k, rfl⟩ := hj
      simp only [hf.eq_iff]
      simp
    · have hj' : ∀ k, j ≠ f k := by simpa only [not_exists] using hj
      simp [hj']
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  simp

theorem paperScalarBandMatrix_hilbertSchmidtSq
    (N d : ℕ) [NeZero N] (hsize : d + 2 ≤ N)
    (center : Fin (d + 1)) (x : ZMod N → Fin (d + 2) → ℂ) :
    hilbertSchmidtSq (paperScalarBandMatrix N d center x) = ∑ i, ∑ k, ‖x i k‖ ^ 2 := by
  unfold hilbertSchmidtSq paperScalarBandMatrix
  apply Finset.sum_congr rfl
  intro i _
  apply sparse_row_norm_square_sum
  intro a b hab
  apply Fin.ext
  exact CharP.natCast_injOn_Iio (ZMod N) N
    (lt_of_lt_of_le a.isLt hsize) (lt_of_lt_of_le b.isLt hsize) (add_left_cancel hab)

theorem hilbertSchmidtSq_reindex
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (X : Matrix ι ι ℂ) :
    hilbertSchmidtSq (X.submatrix e e) = hilbertSchmidtSq X := by
  unfold hilbertSchmidtSq
  change (∑ i, ∑ j, ‖X (e i) (e j)‖ ^ 2) = ∑ i, ∑ j, ‖X i j‖ ^ 2
  calc
    _ = ∑ i, ∑ j, ‖X (e i) j‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact e.sum_comp (fun j => ‖X (e i) j‖ ^ 2)
    _ = _ := e.sum_comp (fun i => ∑ j, ‖X i j‖ ^ 2)

def literalIndicatorMatrix (k d : ℕ) (center : Fin (d + 1))
    (b : Fin (d + 2) → ℂ) (ω : Fin ((k + 1) * (d + 2)) → ℂ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  (paperIndicatorX (k + 1) d center b ω).submatrix
    (ZMod.finEquiv (k + 1)).toEquiv (ZMod.finEquiv (k + 1)).toEquiv

theorem literalIndicatorMatrix_logPotential (k d : ℕ) (center : Fin (d + 1))
    (b : Fin (d + 2) → ℂ) (ω : Fin ((k + 1) * (d + 2)) → ℂ) (z : ℂ) :
    physicalLogPotential (literalIndicatorMatrix k d center b ω) z =
      Real.log ‖(paperIndicatorXSubZI (k + 1) d center b ω z).det‖ / (k + 1 : ℝ) := by
  rfl

theorem literalIndicatorMatrix_measurable (k d : ℕ) (center : Fin (d + 1))
    (b : Fin (d + 2) → ℂ) (i j : Fin (k + 1)) :
    Measurable (fun ω : Fin ((k + 1) * (d + 2)) → ℂ =>
      literalIndicatorMatrix k d center b ω i j) := by
  classical
  change Measurable (fun ω : Fin ((k + 1) * (d + 2)) → ℂ => ∑ s : Fin (d + 2),
    if (ZMod.finEquiv (k + 1)) j = (ZMod.finEquiv (k + 1)) i -
        (center.val : ZMod (k + 1)) + (s.val : ZMod (k + 1))
      then b s * ω (paperIndicatorFlatIndex (k + 1) d ((ZMod.finEquiv (k + 1)) i) s) else 0)
  apply Finset.measurable_sum
  intro s _
  split_ifs
  · exact measurable_const.mul (measurable_pi_apply _)
  · exact measurable_const

theorem literalIndicatorMatrix_energy_eq
    (k d : ℕ) (hsize : d + 2 ≤ k + 1) (center : Fin (d + 1))
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (ω : Fin ((k + 1) * (d + 2)) → ℂ) :
    physicalEnergy (literalIndicatorMatrix k d center profile.b ω) =
      (∑ i : ZMod (k + 1), ∑ s : Fin (d + 2),
        profile.q s * ‖ω (paperIndicatorFlatIndex (k + 1) d i s)‖ ^ 2) / (k + 1 : ℝ) := by
  unfold physicalEnergy literalIndicatorMatrix
  rw [hilbertSchmidtSq_reindex (ZMod.finEquiv (k + 1)).toEquiv]
  rw [paperIndicatorX, paperScalarBandMatrix_hilbertSchmidtSq _ _ hsize]
  simp only [paperIndicatorXi_apply, norm_mul, mul_pow, profile.norm_b,
    Real.sq_sqrt (le_of_lt (profile.q_pos hc₀ _))]

/-- Exact model-level second-moment input for the replacement bridge. -/
theorem literalIndicatorMatrix_energy_integrable_and_le_one
    (k d : ℕ) (hsize : d + 2 ≤ k + 1) (center : Fin (d + 1))
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (ν : Measure ℂ) [SFinite ν] [IsProbabilityMeasure ν]
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    Integrable (fun ω => physicalEnergy (literalIndicatorMatrix k d center profile.b ω))
      (iidMeasure ν ((k + 1) * (d + 2))) ∧
    (∫ ω, physicalEnergy (literalIndicatorMatrix k d center profile.b ω)
      ∂iidMeasure ν ((k + 1) * (d + 2))) ≤ 1 := by
  let μ := iidMeasure ν ((k + 1) * (d + 2))
  have hcoord := fun i s => iidMeasure_coordinate_norm_sq_integrable_and_integral_le_one
    (paperIndicatorFlatIndex (k + 1) d i s) hνInt hνSecond
  have hterm : ∀ i s, Integrable
      (fun ω => profile.q s * ‖ω (paperIndicatorFlatIndex (k + 1) d i s)‖ ^ 2) μ :=
    fun i s => (hcoord i s).1.const_mul _
  have hsum : Integrable (fun ω => ∑ i : ZMod (k + 1), ∑ s : Fin (d + 2),
      profile.q s * ‖ω (paperIndicatorFlatIndex (k + 1) d i s)‖ ^ 2) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun s _ => hterm i s
  simp_rw [literalIndicatorMatrix_energy_eq k d hsize center profile hc₀]
  refine ⟨hsum.div_const _, ?_⟩
  rw [integral_div, integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun s _ => hterm i s))]
  apply (div_le_one (by positivity : (0 : ℝ) < k + 1)).2
  calc
    _ ≤ ∑ _i : ZMod (k + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [integral_finsetSum _ (fun s _ => hterm i s)]
      calc
        _ = ∑ s : Fin (d + 2), profile.q s *
            ∫ ω, ‖ω (paperIndicatorFlatIndex (k + 1) d i s)‖ ^ 2 ∂μ := by
          simp only [integral_const_mul]
        _ ≤ ∑ s, profile.q s := by
          apply Finset.sum_le_sum
          intro s _
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (hcoord i s).2
            (profile.q_pos hc₀ s).le
        _ = 1 := profile.normalized
    _ = _ := by simp

/-- A harmless zero-matrix filler before the band fits in the circle. This makes
the all-index energy bound available without an impossible size-one band premise. -/
def filledLiteralIndicatorMatrix (k d : ℕ) (center : Fin (d + 1))
    (b : Fin (d + 2) → ℂ) (ω : Fin ((k + 1) * (d + 2)) → ℂ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  if d + 2 ≤ k + 1 then literalIndicatorMatrix k d center b ω else 0

theorem filledLiteralIndicatorMatrix_measurable (k d : ℕ) (center : Fin (d + 1))
    (b : Fin (d + 2) → ℂ) (i j : Fin (k + 1)) :
    Measurable (fun ω => filledLiteralIndicatorMatrix k d center b ω i j) := by
  unfold filledLiteralIndicatorMatrix
  split_ifs
  · exact literalIndicatorMatrix_measurable _ _ _ _ _ _
  · exact measurable_const

theorem filledLiteralIndicatorMatrix_energy_integrable_and_le_one
    (k d : ℕ) (center : Fin (d + 1))
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (ν : Measure ℂ) [SFinite ν] [IsProbabilityMeasure ν]
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    Integrable (fun ω => physicalEnergy (filledLiteralIndicatorMatrix k d center profile.b ω))
      (iidMeasure ν ((k + 1) * (d + 2))) ∧
    (∫ ω, physicalEnergy (filledLiteralIndicatorMatrix k d center profile.b ω)
      ∂iidMeasure ν ((k + 1) * (d + 2))) ≤ 1 := by
  by_cases hsize : d + 2 ≤ k + 1
  · simpa only [filledLiteralIndicatorMatrix, if_pos hsize] using
      literalIndicatorMatrix_energy_integrable_and_le_one k d hsize center profile hc₀ ν hνInt hνSecond
  · simp [filledLiteralIndicatorMatrix, hsize, physicalEnergy, hilbertSchmidtSq]

/-- The filler disappears eventually whenever the physical band eventually fits. -/
theorem filledLiteralIndicatorMatrix_eventually_eq
    (d : ℕ → ℕ) (center : ∀ k, Fin (d k + 1)) (b : ∀ k, Fin (d k + 2) → ℂ)
    (hsize : ∀ᶠ k in atTop, d k + 2 ≤ k + 1) :
    ∀ᶠ k in atTop, ∀ ω,
      filledLiteralIndicatorMatrix k (d k) (center k) (b k) ω =
        literalIndicatorMatrix k (d k) (center k) (b k) ω := by
  filter_upwards [hsize] with k hk ω
  simp only [filledLiteralIndicatorMatrix, if_pos hk]

/-- Literal band-model instantiation. Only the comparison model's energy and
log-potential limit remain inputs; the band-model energy bound, common-space
realization, square-root normalization, and replacement theorem are supplied here. -/
theorem literal_indicator_replacement_of_certificate
    (d : ℕ → ℕ) (center : ∀ k, Fin (d k + 1))
    {c₀ C₀ : ℝ} (profile : ∀ k, PaperIndicatorWeights (d k + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (ν : ℕ → Measure ℂ) [∀ k, SFinite (ν k)] [∀ k, IsProbabilityMeasure (ν k)]
    (hνInt : ∀ k, Integrable (fun u : ℂ => ‖u‖ ^ 2) (ν k))
    (hνSecond : ∀ k, ∫ u : ℂ, ‖u‖ ^ 2 ∂ν k ≤ 1)
    (Y : ∀ k, (Fin ((k + 1) * (d k + 2)) → ℂ) → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hY : ∀ k i j, Measurable fun ω => Y k ω i j)
    (comparisonEnergyBound : ℝ) (hComparisonEnergyBound : 0 ≤ comparisonEnergyBound)
    (hYEnergyInt : ∀ k, Integrable (fun ω => physicalEnergy (Y k ω))
      (iidMeasure (ν k) ((k + 1) * (d k + 2))))
    (hYEnergy : ∀ k, ∫ ω, physicalEnergy (Y k ω)
      ∂iidMeasure (ν k) ((k + 1) * (d k + 2)) ≤ comparisonEnergyBound)
    (meanPressure : ℂ → ℕ → ℝ) (target : ℂ → ℝ)
    (hCertificate : ∀ᵐ z ∂(volume : Measure ℂ), Nonempty
      (CircularLawSections56.Section5.LiteralFinalClosureCertificateTri
        (fun k => iidMeasure (ν k) ((k + 1) * (d k + 2)))
        (fun k ω => physicalLogPotential
          (filledLiteralIndicatorMatrix k (d k) (center k) (profile k).b ω) z)
        (meanPressure z) (target z)))
    (hLogY :
      let : ∀ k, IsProbabilityMeasure (iidMeasure (ν k) ((k + 1) * (d k + 2))) :=
        fun k => iidMeasure_isProbability (ν k) _
      ∀ᵐ z ∂(volume : Measure ℂ), CircularLawSections56.Section5.TendstoInProbabilityTri
        (fun k => iidMeasure (ν k) ((k + 1) * (d k + 2)))
        (fun k ω => physicalLogPotential (Y k ω) z) (target z)) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi (fun k => iidMeasure (ν k) ((k + 1) * (d k + 2))))
        (fun k ω => esdDifference
          (filledLiteralIndicatorMatrix k (d k) (center k) (profile k).b (ω k)) (Y k (ω k)) f)
        atTop 0 := by
  let : ∀ k, IsProbabilityMeasure (iidMeasure (ν k) ((k + 1) * (d k + 2))) :=
    fun k => iidMeasure_isProbability (ν k) _
  have hXEnergy := fun k => filledLiteralIndicatorMatrix_energy_integrable_and_le_one
    k (d k) (center k) (profile k) hc₀ (ν k) (hνInt k) (hνSecond k)
  apply triangular_physical_replacement
    (fun k => iidMeasure (ν k) ((k + 1) * (d k + 2)))
    (fun k ω => filledLiteralIndicatorMatrix k (d k) (center k) (profile k).b ω) Y
    (fun k => filledLiteralIndicatorMatrix_measurable k (d k) (center k) (profile k).b) hY
    (1 + comparisonEnergyBound) (by positivity)
    (fun k => (hXEnergy k).1.add (hYEnergyInt k)) ?_ target ?_ hLogY
  · intro k
    rw [integral_add (hXEnergy k).1 (hYEnergyInt k)]
    exact add_le_add (hXEnergy k).2 (hYEnergy k)
  · filter_upwards [hCertificate] with z hz
    exact hz.some.tendstoInProbability

end CircularLawSections56.Section6
