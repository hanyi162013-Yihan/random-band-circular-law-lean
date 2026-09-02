import CircularLawSections56.Section5.TaperInnerBand

/-! # Effective bandwidth identified with actual matrix entry moments

The reciprocal of the largest entry second moment is exactly the reciprocal
of the largest sampled normalized taper weight. This connects the discrete
weight estimate to the random-matrix bandwidth used in the short-ring input.
-/

open MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace CircularLawSections56.Section5
open CircularLawSection4

theorem finiteSignedMax_univ_comp_equiv
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (e : ι ≃ κ) (f : κ → ℝ) :
    finiteSignedMax Finset.univ Finset.univ_nonempty (fun i => f (e i)) =
      finiteSignedMax Finset.univ Finset.univ_nonempty f := by
  apply le_antisymm
  · exact finiteSignedMax_le Finset.univ_nonempty _
      (fun i _ => le_finiteSignedMax Finset.univ_nonempty f (Finset.mem_univ (e i)))
  · apply finiteSignedMax_le Finset.univ_nonempty f
    intro j _
    simpa only [e.apply_symm_apply] using
      le_finiteSignedMax Finset.univ_nonempty (fun i => f (e i)) (Finset.mem_univ (e.symm j))

def PolynomialTaperProfile.maximumVariance
    (p : PolynomialTaperProfile) (N W : ℕ) [NeZero N] : ℝ :=
  finiteSignedMax (Finset.univ : Finset (ZMod N × ZMod N)) Finset.univ_nonempty
    (fun ij => p.varianceMatrix N W ij.1 ij.2)

theorem PolynomialTaperProfile.maximumVariance_eq_maxWeight
    (p : PolynomialTaperProfile) (N W : ℕ) [NeZero N]
    (hfit : 2 * W + 1 ≤ N) : p.maximumVariance N W = p.maxWeight W := by
  have hmax : 0 ≤ p.maxWeight W :=
    (p.weight_pos W 0).le.trans
      (le_finiteSignedMax Finset.univ_nonempty (p.weight W) (Finset.mem_univ 0))
  apply le_antisymm
  · apply finiteSignedMax_le Finset.univ_nonempty _
    intro ij _
    exact cyclicVarianceProfile_entry_le N _ hfit _ _ _ hmax
      (fun s => le_finiteSignedMax Finset.univ_nonempty (p.weight W) (Finset.mem_univ s))
      ij.1 ij.2
  · apply finiteSignedMax_le Finset.univ_nonempty (p.weight W)
    intro s _
    calc
      p.weight W s = p.varianceMatrix N W 0 (0 - (W : ZMod N) + (s.val : ZMod N)) :=
        (cyclicVarianceProfile_slot N _ hfit _ _ 0 s).symm
      _ ≤ p.maximumVariance N W :=
        le_finiteSignedMax Finset.univ_nonempty
          (fun ij : ZMod N × ZMod N => p.varianceMatrix N W ij.1 ij.2)
          (Finset.mem_univ ((0 : ZMod N), 0 - (W : ZMod N) + (s.val : ZMod N)))

def matrixMaxExpectedEntryNormSq {Ω : Type*} [MeasurableSpace Ω]
    (k : ℕ) (μ : Measure Ω) (X : Ω → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ℝ :=
  finiteSignedMax (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1))) Finset.univ_nonempty
    (fun ij => ∫ ω, ‖X ω ij.1 ij.2‖ ^ 2 ∂μ)

theorem taperedMatrix_maxExpectedEntry_eq_maxWeight
    (p : PolynomialTaperProfile) (k W : ℕ) (hW : 0 < W) (hfit : 2 * W + 1 ≤ k + 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν = 1) :
    matrixMaxExpectedEntryNormSq k (iidMeasure ν ((k + 1) * (taperStateDimension W + 2)))
      (p.literalMatrix k W hW) = p.maxWeight W := by
  unfold matrixMaxExpectedEntryNormSq
  simp_rw [taperedMatrix_expected_entry_eq_varianceMatrix p k W hW hfit ν hInt hSecond]
  have he := finiteSignedMax_univ_comp_equiv
    ((ZMod.finEquiv (k + 1)).toEquiv.prodCongr (ZMod.finEquiv (k + 1)).toEquiv)
    (fun ij => p.varianceMatrix (k + 1) W ij.1 ij.2)
  exact he.trans (p.maximumVariance_eq_maxWeight (k + 1) W hfit)

theorem taperedMatrix_effectiveBandwidth_comparable
    (p : PolynomialTaperProfile) (k W : ℕ) (hW : 0 < W) (hfit : 2 * W + 1 ≤ k + 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν = 1) :
    let b := (matrixMaxExpectedEntryNormSq k
      (iidMeasure ν ((k + 1) * (taperStateDimension W + 2))) (p.literalMatrix k W hW))⁻¹
    (W : ℝ) / p.upperWeightConstant ≤ b ∧ b ≤ (W : ℝ) / p.lowerWeightConstant := by
  dsimp only
  rw [taperedMatrix_maxExpectedEntry_eq_maxWeight p k W hW hfit ν hInt hSecond]
  exact p.effectiveBandwidth_comparable W hW

end CircularLawSections56.Section5
