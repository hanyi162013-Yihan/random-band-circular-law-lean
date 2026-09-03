import ShortRingAnchor.HermitizationSingularTrace
import Vendor.Arxiv2410.V3.ResolventPerturbation

/-!
# Lemma 3.5: the actual matrix trace is connected to the proved CDF smoothing

This file instantiates the inverse identities with the actual Hermitian
resolvent. Thus no spectral enumeration, trace formula, or nonsingularity
premise remains in the public matrix identities below.
-/

open Set Matrix

noncomputable section
namespace ShortRingAnchor

/-- v3 (3.1) and manuscript Lemma 3.5: exact equality of the normalized
matrix resolvent trace and the symmetric shifted-singular-value transform.
It holds for every square matrix, including singular matrices. -/
theorem matrix_stieltjesTrace_eq_symmetric_singularValues {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) {eta : ℂ} (heta : 0 < eta.im) :
    Arxiv2410V3.stieltjesTrace X z eta =
      Arxiv2410V3.empiricalStieltjes
        (symmetrizedSpectrum (shiftedSingularValueFamily X z)) eta := by
  let B : Matrix (Fin n) (Fin n) ℂ := X - z • 1
  have hinv := Arxiv2410V3.shiftedHermitian_inv_mul_and_mul_inv
    (hermitization B) (hermitization_isHermitian B) heta
  exact normalizedTrace_hermitization_inverse_eq_singularStieltjes B heta
    ((hermitization B - eta • 1)⁻¹) hinv.2 hinv.1

/-- Manuscript Lemma 3.5: the finite-spectrum smoothing theorem applied
to the actual shifted matrix singular values. The only analytic premises
are compact estimates for the genuine v3 matrix traces. -/
theorem matrix_squaredCdfDistanceOn_le_of_stieltjes {n m : ℕ}
    [NeZero n] [NeZero m]
    (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ)
    (z : ℂ) {v R C E : ℝ}
    (hv : 0 < v) (hR : 0 ≤ R) (hsmall : 3 * Real.sqrt v ≤ 1) (hE : 0 ≤ E)
    (hcompare : ∀ u ∈ Icc (-R - 1) (R + 1),
      ‖Arxiv2410V3.stieltjesTrace X z (Arxiv2410V3.spectralParameter u v) -
        Arxiv2410V3.stieltjesTrace Y z (Arxiv2410V3.spectralParameter u v)‖ ≤ E)
    (hreference : ∀ u ∈ Icc (-R - 1) (R + 1),
      (Arxiv2410V3.stieltjesTrace Y z (Arxiv2410V3.spectralParameter u v)).im ≤ C) :
    empiricalCdfDistanceOn 0 (R ^ 2)
      (fun i => shiftedSingularValueFamily X z i ^ 2)
      (fun j => shiftedSingularValueFamily Y z j ^ 2) ≤
        ((2 * R + 10) * E + (8 * C + 8) * Real.sqrt v) / Real.pi := by
  have heta (u : ℝ) : 0 < (Arxiv2410V3.spectralParameter u v).im := by
    simpa [Arxiv2410V3.spectralParameter] using hv
  apply squaredCdfDistanceOn_le_of_stieltjes
    (shiftedSingularValueFamily X z) (shiftedSingularValueFamily Y z) hv hR hsmall hE
  · intro u hu
    rw [← matrix_stieltjesTrace_eq_symmetric_singularValues X z (heta u),
      ← matrix_stieltjesTrace_eq_symmetric_singularValues Y z (heta u)]
    exact hcompare u hu
  · intro u hu
    rw [← matrix_stieltjesTrace_eq_symmetric_singularValues Y z (heta u)]
    exact hreference u hu

end ShortRingAnchor
