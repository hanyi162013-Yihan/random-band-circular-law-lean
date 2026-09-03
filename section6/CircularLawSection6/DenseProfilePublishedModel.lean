import CircularLawSection6.PublishedGaussianDensity
import CircularLawSection6.ProfileComparability
import CircularLawSections56.Section5.PublishedSection3ConcreteSampling
import ShortRingAnchor.CyclicPlanarHighBandModel
import Vendor.Arxiv2410.V3.BVH.ModelMoments

/-! # Actual full cyclic Gaussian profiles on the common Section 5 sample space

The first infinite Gaussian array supplies the full profile matrix; the
second remains available for `PublishedSection3Concrete.actualGinibre`.
All entries, laws, row/column normalizations and the exact maximum-variance
bandwidth are constructed here. The planar high-band model uses geometric
width equal to the full dimension, with no artificial off-band zero entries.
-/

open MeasureTheory ProbabilityTheory Filter Topology ShortRingAnchor Arxiv2410V3
open CircularLawSections56.Section5
open CircularLawSections56.Section5.PublishedSection3Concrete
  (Sample sampleLaw gaussianSequenceLaw denseCoordinate denseCoordinate_injective
    selectedCoordinates_measurePreserving)
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CircularLawSection6.DenseProfile

abbrev law : Measure Sample := sampleLaw circularComplexGaussian

def firstDenseSamples (N : ℕ) (ω : Sample) (ij : Fin N × Fin N) : ℂ :=
  ω.1 (denseCoordinate ij)

theorem firstDenseSamples_measurePreserving (N : ℕ) :
    MeasurePreserving (firstDenseSamples N) law
      (Measure.pi fun _ : Fin N × Fin N => circularComplexGaussian) :=
  (selectedCoordinates_measurePreserving circularComplexGaussian denseCoordinate
    (denseCoordinate_injective N)).comp
    (measurePreserving_fst (μ := Measure.infinitePi fun _ : ℕ => circularComplexGaussian)
      (ν := gaussianSequenceLaw))

theorem firstDenseSamples_copies (N : ℕ) :
    IndependentAtomCopies21 law circularComplexGaussian id
      (fun ij : Fin N × Fin N => fun ω => firstDenseSamples N ω ij) :=
  independentAtomCopies21_of_jointLaw law circularComplexGaussian _
    (firstDenseSamples_measurePreserving N)

def offset (N : ℕ) [NeZero N] (i j : Fin N) : ZMod N :=
  ZMod.finEquiv N j - ZMod.finEquiv N i

def rowOffsetEquiv (N : ℕ) [NeZero N] (i : Fin N) : Fin N ≃ ZMod N :=
  (ZMod.finEquiv N).toEquiv.trans (cyclicOffsetEquiv N (ZMod.finEquiv N i))

def colOffsetEquiv (N : ℕ) [NeZero N] (j : Fin N) : Fin N ≃ ZMod N where
  toFun i := offset N i j
  invFun s := (ZMod.finEquiv N).symm (ZMod.finEquiv N j - s)
  left_inv i := by simp [offset]
  right_inv s := by simp [offset]

def varianceProfile (N : ℕ) [NeZero N] (q : ZMod N → ℝ)
    (hq : ∀ s, 0 < q s) (hsum : ∑ s, q s = 1) :
    DoublyStochasticVarianceProfile (Fin N) where
  coefficient i j := Real.sqrt (q (offset N i j))
  coefficient_nonneg _ _ := Real.sqrt_nonneg _
  row_sq_sum i := by
    simp_rw [Real.sq_sqrt (hq _).le]
    exact ((rowOffsetEquiv N i).sum_comp q).trans hsum
  col_sq_sum j := by
    simp_rw [Real.sq_sqrt (hq _).le]
    exact ((colOffsetEquiv N j).sum_comp q).trans hsum

theorem varianceProfile_coefficient_sq (N : ℕ) [NeZero N] (q : ZMod N → ℝ)
    (hq : ∀ s, 0 < q s) (hsum : ∑ s, q s = 1) (i j : Fin N) :
    (varianceProfile N q hq hsum).coefficient i j ^ 2 = q (offset N i j) :=
  Real.sq_sqrt (hq _).le

def actualMatrix (N : ℕ) [NeZero N] (q : ZMod N → ℝ) (ω : Sample) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (Real.sqrt (q (offset N i j)) : ℂ) * firstDenseSamples N ω (i, j)

def v3Model (N : ℕ) [NeZero N] (q : ZMod N → ℝ)
    (hq : ∀ s, 0 < q s) (hsum : ∑ s, q s = 1) :
    RandomMatrixModelV3 N Sample ℂ law circularComplexGaussian where
  matrix := actualMatrix N q
  atom := id
  profile := varianceProfile N q hq hsum
  entry_measurable i j := measurable_const.mul ((firstDenseSamples_copies N).measurable (i, j))
  entries_independent := (firstDenseSamples_copies N).independent.comp
    (fun ij x => (Real.sqrt (q (offset N ij.1 ij.2)) : ℂ) * x)
    (fun _ => measurable_const.mul measurable_id)
  entry_law i j := ((firstDenseSamples_copies N).law (i, j)).const_mul _
  atom_integrable := circularComplexGaussian_publishedMoments.integrable
  atom_mean_zero := circularComplexGaussian_publishedMoments.centered
  atom_variance_one := circularComplexGaussian_publishedMoments.unitSecondMoment
  atom_third_moment_finite := circularComplexGaussian_publishedMoments.thirdMomentIntegrable

def maxWeight (N : ℕ) [NeZero N] (q : ZMod N → ℝ) : ℝ :=
  (Finset.univ : Finset (ZMod N)).sup' ⟨0, Finset.mem_univ _⟩ q

def bandwidth (N : ℕ) [NeZero N] (q : ZMod N → ℝ) : ℝ := (maxWeight N q)⁻¹

theorem le_maxWeight (N : ℕ) [NeZero N] (q : ZMod N → ℝ) (s : ZMod N) :
    q s ≤ maxWeight N q := Finset.le_sup' q (Finset.mem_univ s)

theorem maxWeight_pos (N : ℕ) [NeZero N] (q : ZMod N → ℝ) (hq : ∀ s, 0 < q s) :
    0 < maxWeight N q := (hq 0).trans_le (le_maxWeight N q 0)

theorem isBandwidth (N : ℕ) [NeZero N] (q : ZMod N → ℝ)
    (hq : ∀ s, 0 < q s) (hsum : ∑ s, q s = 1) :
    IsBandwidth (v3Model N q hq hsum).profile (bandwidth N q) := by
  classical
  refine ⟨inv_pos.mpr (maxWeight_pos N q hq), ?_, ?_⟩
  · intro i j
    rw [show (v3Model N q hq hsum).profile = varianceProfile N q hq hsum from rfl,
      varianceProfile_coefficient_sq]
    simpa only [bandwidth, inv_inv] using le_maxWeight N q (offset N i j)
  · obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_sup'
      (show (Finset.univ : Finset (ZMod N)).Nonempty from ⟨0, Finset.mem_univ _⟩) q
    refine ⟨0, (rowOffsetEquiv N 0).symm s, ?_⟩
    rw [show (v3Model N q hq hsum).profile = varianceProfile N q hq hsum from rfl,
      varianceProfile_coefficient_sq]
    change q ((rowOffsetEquiv N 0) ((rowOffsetEquiv N 0).symm s)) = _
    rw [Equiv.apply_symm_apply]
    simpa only [bandwidth, inv_inv, maxWeight] using hs.symm

theorem bandwidth_lower (N : ℕ) [NeZero N] (q : ZMod N → ℝ)
    (hq : ∀ s, 0 < q s) {C : ℝ} (hC : 0 < C)
    (hupper : ∀ s, q s ≤ C / (N : ℝ)) : (N : ℝ) / C ≤ bandwidth N q := by
  have hmax : maxWeight N q ≤ C / (N : ℝ) := by
    apply Finset.sup'_le
    intro s _
    exact hupper s
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hmpos := maxWeight_pos N q hq
  change (N : ℝ) / C ≤ (maxWeight N q)⁻¹
  apply (div_le_iff₀ hC).2
  calc
    (N : ℝ) = (maxWeight N q)⁻¹ * (maxWeight N q * (N : ℝ)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hmpos.ne', one_mul]
    _ ≤ (maxWeight N q)⁻¹ * C :=
      mul_le_mul_of_nonneg_left ((le_div_iff₀ hN).mp hmax) (inv_nonneg.mpr hmpos.le)

def cyclicCoordinate (N : ℕ) [NeZero N] (is : ZMod N × ZMod N) : ℕ :=
  denseCoordinate ((ZMod.finEquiv N).symm is.1, (ZMod.finEquiv N).symm (is.1 + is.2))

theorem cyclicCoordinate_injective (N : ℕ) [NeZero N] :
    Function.Injective (cyclicCoordinate N) := by
  intro x y h
  have hp := denseCoordinate_injective N h
  have hi : x.1 = y.1 := (ZMod.finEquiv N).symm.injective (congrArg Prod.fst hp)
  have hs : x.1 + x.2 = y.1 + y.2 :=
    (ZMod.finEquiv N).symm.injective (congrArg Prod.snd hp)
  rw [hi] at hs
  exact Prod.ext hi (add_left_cancel hs)

def cyclicSamples (N : ℕ) [NeZero N] (ω : Sample) : ZMod N × ZMod N → ℂ :=
  fun is => ω.1 (cyclicCoordinate N is)

theorem cyclicSamples_measurePreserving (N : ℕ) [NeZero N] :
    MeasurePreserving (cyclicSamples N) law (cyclicAtomLaw N circularComplexGaussian) :=
  (selectedCoordinates_measurePreserving circularComplexGaussian (cyclicCoordinate N)
    (cyclicCoordinate_injective N)).comp
    (measurePreserving_fst (μ := Measure.infinitePi fun _ : ℕ => circularComplexGaussian)
      (ν := gaussianSequenceLaw))

theorem actualMatrix_eq_weightedCyclicMatrix (N : ℕ) [NeZero N] (q : ZMod N → ℝ)
    (ω : Sample) :
    actualMatrix N q ω = (weightedCyclicMatrix N q (cyclicSamples N ω)).submatrix
      (ZMod.finEquiv N) (ZMod.finEquiv N) := by
  ext i j
  simp [actualMatrix, weightedCyclicMatrix, offset, firstDenseSamples,
    cyclicSamples, cyclicCoordinate]

theorem actualMatrix_rowMoments (M : ℕ → ℕ) [∀ n, NeZero (M n)]
    (q : ∀ n, ZMod (M n) → ℝ) (hq : ∀ n s, 0 < q n s) (hsum : ∀ n, ∑ s, q n s = 1) :
    CenteredMatrixRowSecondMomentInputs law (fun n => actualMatrix (M n) (q n)) 1 where
  C_nonneg := zero_le_one
  entry_integrable n i j := BVH.entry_integrable (v3Model (M n) (q n) (hq n) (hsum n)) i j
  entry_sq_integrable n i j := BVH.integrable_entry_norm_square (v3Model (M n) (q n) (hq n) (hsum n)) i j
  centered n i j := BVH.integral_entry_eq_zero (v3Model (M n) (q n) (hq n) (hsum n)) i j
  row_secondMoment n i := by
    change (∑ j, ∫ ω, ‖(v3Model (M n) (q n) (hq n) (hsum n)).matrix ω i j‖ ^ 2 ∂law) = 1
    simp_rw [BVH.integral_entry_norm_square_eq]
    exact (varianceProfile (M n) (q n) (hq n) (hsum n)).row_sq_sum i

def planarModel (N : ℕ) [NeZero N] (q : ZMod N → ℝ)
    (hq : ∀ s, 0 < q s) (hsum : ∑ s, q s = 1) {c C : ℝ}
    (hlower : ∀ s, c / (N : ℝ) ≤ q s) (hupper : ∀ s, q s ≤ C / (N : ℝ)) :
    HighBandLSV.PlanarBandModel N N c C 2 where
  sigma := (varianceProfile N q hq hsum).coefficient
  sigma_nonneg := (varianceProfile N q hq hsum).coefficient_nonneg
  local_floor i j _ := by rw [varianceProfile_coefficient_sq]; exact hlower _
  upper i j := by rw [varianceProfile_coefficient_sq]; exact hupper _
  row_normalization := (varianceProfile N q hq hsum).row_sq_sum
  atomLaw := fun _ _ => circularComplexGaussian
  atom_probability := fun _ _ => inferInstance
  atom_density := fun _ _ => by simpa only [ENNReal.ofReal_ofNat] using circularComplexGaussian_le_two_volume

theorem planarModel_identDistrib (N : ℕ) [NeZero N] (q : ZMod N → ℝ)
    (hq : ∀ s, 0 < q s) (hsum : ∑ s, q s = 1) {c C : ℝ}
    (hlower : ∀ s, c / (N : ℝ) ≤ q s) (hupper : ∀ s, q s ≤ C / (N : ℝ)) :
    IdentDistrib (actualMatrix N q) (planarModel N q hq hsum hlower hupper).matrix
      law (planarModel N q hq hsum hlower hupper).law := by
  let v := v3Model N q hq hsum
  let m := planarModel N q hq hsum hlower hupper
  apply identDistrib_matrix_of_independent_entries _ _ v.entry_measurable
    (fun i j => by unfold HighBandLSV.PlanarBandModel.matrix; fun_prop)
    v.entries_independent (planarBandModel_entries_independent m)
  intro i j
  exact (v.entry_law i j).trans
    (planarBandModel_entry_law m id measurable_id (fun _ _ => (Measure.map_id).symm) i j).symm

end CircularLawSection6.DenseProfile
