import CircularLawSection6.ClampedSection5Source
import CircularLawSection6.SubsequenceSourceEndpoint

/-! # The direct Section 5 call supplies every canonical core input

The finite fit premises in CanonicalCoreSection5Input already ensure that
the global clamp is inactive. Thus the same Section 3/4 source package
supplies the core limit on all increasing dimension sequences and after
every allowed finite prefix. No extra core probability limit is assumed.
-/

open MeasureTheory Filter Topology
open CircularLawSection4
open CircularLawSections56.Section5 CircularLawSections56.Section6

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

def literalCoreBadProbability (p : NoncompactProfile) (n H : ℕ) (hH : 0 < H)
    (W : ℝ) (z : ℂ) (a ε : ℝ) : ℝ :=
  (paperIndicatorSampleMeasure (n + 1) (canonicalCoreBand H) circularComplexGaussian).real
    {ω | ε ≤ |physicalLogPotential
      (literalIndicatorMatrix n (canonicalCoreBand H) (canonicalCoreCenter H hH)
        (fun s => (Real.sqrt (p.coreBandWeight (n + 1) (canonicalCoreBand H)
          (canonicalCoreCenter H hH) W s) : ℂ)) ω) z - a|}

theorem literalCoreBadProbability_dimension (p : NoncompactProfile) {n m : ℕ}
    (hnm : n = m) (H : ℕ) (hH : 0 < H) (W : ℝ) (z : ℂ) (a ε : ℝ) :
    literalCoreBadProbability p n H hH W z a ε = literalCoreBadProbability p m H hH W z a ε := by
  subst m
  rfl

theorem literalCoreBadProbability_halfWidth (p : NoncompactProfile) (n : ℕ) {H J : ℕ}
    (hHJ : H = J) (hH : 0 < H) (hJ : 0 < J) (W : ℝ) (z : ℂ) (a ε : ℝ) :
    literalCoreBadProbability p n H hH W z a ε = literalCoreBadProbability p n J hJ W z a ε := by
  subst J
  rfl

def clampedCoreBadProbability {p : NoncompactProfile} {R : ℝ}
    (B : CoreRadiusBounds p R) (W : ℕ → ℝ) (n : ℕ) (z : ℂ) (a ε : ℝ) : ℝ :=
  (clampedCoreSampleLaw R W n).real
    {ω | ε ≤ |physicalLogPotential (literalIndicatorMatrix n (clampedCoreBand R W n)
      (clampedCoreCenter R W n) (B.clampedWeights (W n) n).b ω) z - a|}

namespace CoreRadiusBounds

variable {p : NoncompactProfile} {R : ℝ}

theorem clampedCoreBadProbability_eq_literal (B : CoreRadiusBounds p R)
    (W : ℕ → ℝ) (n : ℕ) (hW : 0 < W n) (hH : 0 < ⌊R * W n⌋₊)
    (hfit : 2 * ⌊R * W n⌋₊ + 1 ≤ n + 1) (z : ℂ) (a ε : ℝ) :
    clampedCoreBadProbability B W n z a ε =
      literalCoreBadProbability p n ⌊R * W n⌋₊ hH (W n) z a ε := by
  have hn : 2 ≤ n := by omega
  have hb : (B.clampedWeights (W n) n).b =
      (fun s => (Real.sqrt (p.coreBandWeight (n + 1) (clampedCoreBand R W n)
        (clampedCoreCenter R W n) (W n) s) : ℂ)) := by
    funext s
    change (Real.sqrt ((B.clampedWeights (W n) n).q s) : ℂ) = _
    rw [B.clampedWeights_q (W n) n hn hW hH]
    rfl
  have hfirst : clampedCoreBadProbability B W n z a ε =
      literalCoreBadProbability p n (clampedCoreHalfWidth R (W n) n)
        (clampedCoreHalfWidth_pos R (W n) n) (W n) z a ε := by
    unfold clampedCoreBadProbability
    rw [hb]
    rfl
  exact hfirst.trans (literalCoreBadProbability_halfWidth p n
    (clampedCoreHalfWidth_eq_floor R (W n) n hH hfit)
    (clampedCoreHalfWidth_pos R (W n) n) hH (W n) z a ε)

theorem Section34Input.toCanonical (B : CoreRadiusBounds p R) (W : ℕ → ℝ)
    (hR : 0 < R) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsource : B.Section34Input W) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    p.CanonicalCoreSection5Input (subsequenceCoreSize φ) (fun n => W (φ (n + 1))) R := by
  intro K hH hfit
  have h5 := Section34Input.logPotential B W hR hWlim hsource
  have hψ : Tendsto (fun n => φ (n + K + 1)) atTop atTop :=
    hφ.tendsto_atTop.comp ((tendsto_add_atTop_nat 1).comp (tendsto_add_atTop_nat K))
  filter_upwards [h5] with z hz
  intro ε hε
  apply ((hz ε hε).comp hψ).congr'
  apply Eventually.of_forall
  intro n
  have hidx : subsequenceCoreSize φ (n + K) + 1 = φ (n + K + 1) := by
    have h := subsequenceCoreSize_dimension φ hφ (n + K)
    omega
  have hfit' : 2 * ⌊R * W (φ (n + K + 1))⌋₊ + 1 ≤ φ (n + K + 1) + 1 := by
    simpa only [subsequenceCoreSize_dimension φ hφ] using hfit n
  change clampedCoreBadProbability B W (φ (n + K + 1)) z (circularRadialPotential ‖z‖) ε =
    literalCoreBadProbability p (subsequenceCoreSize φ (n + K) + 1)
      ⌊R * W (φ (n + K + 1))⌋₊ (hH n) (W (φ (n + K + 1))) z (circularRadialPotential ‖z‖) ε
  exact (B.clampedCoreBadProbability_eq_literal W (φ (n + K + 1))
    (hW _) (hH n) hfit' z (circularRadialPotential ‖z‖) ε).trans
    (literalCoreBadProbability_dimension p hidx.symm _ (hH n) (W (φ (n + K + 1))) z
      (circularRadialPotential ‖z‖) ε)

end CoreRadiusBounds
end CircularLawSection6
