import ShortRingAnchor.Proposition38.Assembly
import ShortRingAnchor.BC12.GaussianMatrixLawBridge
import ShortRingAnchor.BC12.GinibreNegativeMoments

/-!
# Proposition 3.8 without BC12 hypotheses

The earlier assembly is retained as a reusable conditional lemma.
This public endpoint constructs every BC12 input. Its only reference-law
premise is the ordinary model definition: the reference is complex Ginibre.
The explicitly permitted Proposition 3.2, Cook 1.12, and BBV comparisons
remain visible theorem arguments.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Arxiv2410V3
open scoped Topology
namespace ShortRingAnchor.Proposition38

local instance (n : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := borel _
local instance (n : ℕ) : BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩

/-- **Proposition 3.8 / (3.19), with every BC12 input discharged.**
The negative-moment exponent is constructed as `1/128`; the exact kernel
and correlation identities follow from the actual Gaussian entry law.
All fixed complex shifts are allowed. -/
theorem proposition38_withoutBC12
    {Ω ΞG : Type*} [MeasurableSpace Ω] [MeasurableSpace ΞG]
    {μ : Measure Ω} {νG : Measure ΞG} [IsProbabilityMeasure μ] [IsProbabilityMeasure νG]
    (A : Atom) {s W : ℕ → ℕ} (hW : ∀ k, 0 < W k) (hs : ∀ k, 0 < s k)
    (S : ∀ k, AtomArray μ A (Fin ((s k + 3) * W k) × Fin ((s k + 3) * W k)))
    (denseAtom : ∀ k, Ω → Fin ((s k + 3) * W k) → Fin ((s k + 3) * W k) → ℂ)
    (atomG : ΞG → ℂ) (hatomG : AtomMomentAssumption21 νG atomG)
    (hcopiesG : ∀ k, IndependentAtomCopies21 μ νG atomG
      (fun ij : Fin ((s k + 3) * W k) × Fin ((s k + 3) * W k) =>
        fun sample => denseAtom k sample ij.1 ij.2))
    (hGinibre : ∀ k, HasLaw (normalizedDenseMatrixProcess denseAtom k)
      (BC12.normalizedGinibreLaw ((s k + 3) * W k)) μ)
    (z : ℂ) (omega comparisonConstant : ℝ)
    (homega : 0 < omega ∧ omega < 1 / 9)
    (hN : Tendsto (fun k => (s k + 3) * W k) atTop atTop)
    (hWtop : Tendsto W atTop atTop)
    (hband : ∀ᶠ k in atTop,
      (((s k + 3) * W k : ℕ) : ℝ) ^ (8 / 9 + omega) ≤ W k)
    (known32 : Proposition32Input μ A z) (knownCook : Cook112Input μ A)
    (bbvA : ∀ k eta, 0 < eta.im → CanonicalBBVAt
      (fullBlockV3Model (hW k) (S k)) z eta (3 * (W k : ℝ))
      (max comparisonConstant (sourceV3MomentBudget A.law νG (fun x : ℝ => (x : ℂ)) atomG)))
    (bbvG : ∀ k eta, 0 < eta.im → CanonicalBBVAt
      (denseV3Model (Nat.mul_pos (show 0 < s k + 3 by omega) (hW k))
        (denseAtom k) atomG hatomG (hcopiesG k))
      z eta (((s k + 3) * W k : ℕ) : ℝ)
      (max comparisonConstant (sourceV3MomentBudget A.law νG (fun x : ℝ => (x : ℂ)) atomG))) :
    Conclusion μ (fun k => (s k + 3) * W k) (fun k => fullBlockMatrix (S k)) z := by
  have hNpos (k) : 0 < (s k + 3) * W k := Nat.mul_pos (by omega) (hW k)
  let C := max comparisonConstant (sourceV3MomentBudget A.law νG (fun x : ℝ => (x : ℂ)) atomG)
  have hC : 8 ≤ C := (sourceV3MomentBudget_ge_eight (fun x : ℝ => (x : ℂ)) atomG).trans
    (le_max_right comparisonConstant _)
  have hthird : (∫ x, ‖atomG x‖ ^ 3 ∂νG) + BVH.complexGaussianThirdMomentConstant ≤ C :=
    (sourceV3MomentBudget_ge_right (fun x : ℝ => (x : ℂ)) atomG).trans
      (le_max_right comparisonConstant _)
  have hnegative := BC12.negativeMomentTightness_normalizedDenseMatrixProcess
    hNpos hN denseAtom atomG hatomG hcopiesG hGinibre z hC hthird
    (fun k v hv => bbvG k (spectralParameter 0 v) (by simpa [spectralParameter] using hv))
  exact proposition38 A hW hs S denseAtom atomG hatomG hcopiesG z omega comparisonConstant
    (1 / 128) homega hN hWtop hband known32 knownCook bbvA bbvG
    (by norm_num) hnegative (fun k => BC12.verifiedGinibreProjection _)
    (fun k => BC12.normalizedGinibre_correlations (hNpos k) (hGinibre k))

end ShortRingAnchor.Proposition38
