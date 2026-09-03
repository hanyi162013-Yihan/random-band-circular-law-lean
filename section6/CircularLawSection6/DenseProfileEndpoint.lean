import CircularLawSection6.DenseProfileConclusion
import CircularLawSection6.GinibreReducedSources

/-! # Removing Han from the actual noncompact Gaussian profile endpoint

The dense subsequence uses the checked general Section 3 estimates for the
actual full variance profile. The sparse subsequence retains the existing
Section 4/5 core argument. No assertion of Han's more general theorem is
made or needed. The logarithmic and squared-singular Ginibre literature
sources remain explicit in `GaussianProfileReducedSources`.
-/

open MeasureTheory Filter Topology ShortRingAnchor TaoVuReplacement
open CircularLawSections56.Section5 CircularLawSections56.Section6
open CircularLawSections56.Section5.PublishedSection3Concrete
  (BBVComparisonInput provedGinibreInput Sample)
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6
namespace DenseProfile

theorem profile_cyclicSamples_raw (p : NoncompactProfile) (N : ℕ) [NeZero N]
    (W : ℝ) (ω : Sample) (z : ℂ) :
    matrixRawPotential (p.matrix N W (cyclicSamples N ω) - z • 1) =
      normalizedShiftLogDet (actualMatrix N (p.weight N W) ω) z := by
  have hscalar : (z • (1 : Matrix (ZMod N) (ZMod N) ℂ)).submatrix
      (ZMod.finEquiv N) (ZMod.finEquiv N) = z • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply,
      (ZMod.finEquiv N).injective.eq_iff]
  have hm : (p.matrix N W (cyclicSamples N ω) - z • 1).submatrix
      (ZMod.finEquiv N) (ZMod.finEquiv N) = actualMatrix N (p.weight N W) ω - z • 1 := by
    change (p.matrix N W (cyclicSamples N ω)).submatrix (ZMod.finEquiv N)
      (ZMod.finEquiv N) - (z • (1 : Matrix (ZMod N) (ZMod N) ℂ)).submatrix
        (ZMod.finEquiv N) (ZMod.finEquiv N) = _
    rw [← actualMatrix_eq_profile p N W ω, hscalar]
  have hdet : (actualMatrix N (p.weight N W) ω - z • 1).det =
      (p.matrix N W (cyclicSamples N ω) - z • 1).det :=
    (congrArg Matrix.det hm.symm).trans
      (Matrix.det_submatrix_equiv_self (ZMod.finEquiv N).toEquiv
        (p.matrix N W (cyclicSamples N ω) - z • 1))
  unfold matrixRawPotential normalizedShiftLogDet
  rw [hdet, ZMod.card]

theorem profile_raw_limit
    (hBBV : BBVComparisonInput)
    (p : NoncompactProfile) (M : ℕ → ℕ) [∀ n, NeZero (M n)]
    (W : ℕ → ℝ) (hM : Tendsto M atTop atTop) {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ n, δ * (M n : ℝ) ≤ W n) (z : ℂ) :
    TendstoInProbabilityTri (fun n => gaussianProfileLaw (M n))
      (fun n ω => matrixRawPotential (p.matrix (M n) (W n) ω - z • 1))
      (circularRadialPotential ‖z‖) := by
  have h := (tendstoInMeasure_iff_tri law _ _).1
    (profile_conclusion hBBV p M W hM hδ hdense z)
  intro ε hε
  apply (h ε hε).congr'
  apply Eventually.of_forall
  intro n
  have hA : Measurable (fun ω => p.matrix (M n) (W n) ω - z • 1) :=
    (weightedCyclicMatrix_measurable_matrix (M n) (p.weight (M n) (W n))).sub
      measurable_const
  have hraw : Measurable (fun ω => matrixRawPotential (p.matrix (M n) (W n) ω - z • 1)) :=
    (measurable_log_norm_matrix_det _ (fun i j =>
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA))).div_const _
  have he := (cyclicSamples_measurePreserving (M n)).measureReal_preimage
    (measurableSet_le (measurable_const (a := ε))
      ((hraw.sub_const (circularRadialPotential ‖z‖)).abs)).nullMeasurableSet
  simpa only [Set.preimage_ofPred_eq, profile_cyclicSamples_raw,
    circularRadialPotential, circularLogPotential, gaussianProfileLaw] using he

end DenseProfile
namespace NoncompactProfile

theorem dense_profile_spectral_limit_of_section3 (p : NoncompactProfile)
    (W : ℕ → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hdense : ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ W (φ n) / (φ n + 1 : ℕ))
    (hBBV : BBVComparisonInput) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix (φ n)
          (p.matrix (φ n + 1) (W (φ n)) (ω (φ n)).1)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) := by
  obtain ⟨c, hc, hratio⟩ := hdense
  have hM : Tendsto (fun n => φ n + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop
  have hprofile : ∀ᵐ z ∂(volume : Measure ℂ),
      TendstoInProbabilityTri (fun n => gaussianProfileLaw (φ n + 1))
        (fun n ω => matrixRawPotential (p.matrix (φ n + 1) (W (φ n)) ω - z • 1))
        (circularRadialPotential ‖z‖) :=
    ae_of_all _ fun z => DenseProfile.profile_raw_limit hBBV p
      (fun n => φ n + 1) (fun n => W (φ n)) hM hc
      (fun n => (le_div_iff₀ (by positivity)).mp (hratio n)) z
  have hrep := p.profile_ginibre_replacement_along_subsequence W φ hφ
    (fun z => circularRadialPotential ‖z‖) hprofile
    (ae_of_all _ fun z => ginibre_raw_of_bc12 (provedGinibreInput hBBV) (fun n => n + 1)
      (tendsto_add_atTop_nat 1) z)
  intro f hf hcpt
  have hdiff := (tendstoInMeasure_iff_tri (Measure.infinitePi profileGinibrePairLaw) _ 0).1
    (hrep f hf hcpt)
  have hgin := (tendstoInMeasure_iff_tri (Measure.infinitePi profileGinibrePairLaw) _
    (∫ z, f z ∂circularMeasure)).1
    ((ginibre_spectral_of_bc12 (provedGinibreInput hBBV) f hf hcpt).comp hφ.tendsto_atTop)
  apply (tendstoInMeasure_iff_tri (Measure.infinitePi profileGinibrePairLaw) _ _).2
  simpa only [esdDifference, Function.comp_apply, sub_add_cancel, zero_add] using
    hdiff.add (fun _ => Measure.infinitePi profileGinibrePairLaw) hgin

theorem gaussian_profile_circular_law_without_Han (p : NoncompactProfile)
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsource : GaussianProfileReducedSources p W) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi profileGinibrePairLaw)
        (fun n ω => realEsdTest (cyclicPhysicalMatrix n (p.matrix (n + 1) (W n) (ω n).1)) f)
        atTop (fun _ => ∫ z, f z ∂circularMeasure) := by
  have hconcrete := GaussianProfileReducedSources.toConcrete p W hsource
  have h34 := GaussianProfileConcreteSources.toSection34 p W hW hWlim hconcrete
  have hsources := GaussianProfileSection34Inputs.toSourceInputs p W hW hWlim h34
  intro f hf hc
  apply tendstoInMeasure_of_sparse_dense_subsequences (Measure.infinitePi profileGinibrePairLaw)
    (fun n ω => realEsdTest (cyclicPhysicalMatrix n (p.matrix (n + 1) (W n) (ω n).1)) f)
    (fun _ => ∫ z, f z ∂circularMeasure) (fun n => W n / (n + 1 : ℕ))
    (fun n => div_nonneg (hW n).le (Nat.cast_nonneg _))
  · intro φ hφ hsparse
    exact p.profile_spectral_limit_along_sparse_subsequence W hW hWlim hsources
      φ hφ hsparse f hf hc
  · intro φ hφ hdense
    exact p.dense_profile_spectral_limit_of_section3 W φ hφ hdense
      hsource.bbv f hf hc

end NoncompactProfile
end CircularLawSection6
