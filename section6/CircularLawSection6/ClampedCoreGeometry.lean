import CircularLawSection6.CanonicalCoreBand

/-! # A globally defined band for the direct Section 5 application

The positive half-width is clamped at half the physical dimension. It tends
to infinity for every diverging positive bandwidth, fits all dimensions
after the first two, and is eventually the original floor-radius core on
every sparse subsequence. Thus Section 5 can be applied once to a full
dimension sequence before extracting sparse subsequences.
-/

open Filter Topology

noncomputable section

namespace CircularLawSection6

def clampedCoreHalfWidth (R W : ℝ) (n : ℕ) : ℕ :=
  max 1 (min ⌊R * W⌋₊ (n / 2))

theorem clampedCoreHalfWidth_pos (R W : ℝ) (n : ℕ) :
    0 < clampedCoreHalfWidth R W n := by
  unfold clampedCoreHalfWidth
  omega

theorem clampedCoreHalfWidth_fits (R W : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    2 * clampedCoreHalfWidth R W n + 1 ≤ n + 1 := by
  unfold clampedCoreHalfWidth
  omega

theorem clampedCoreHalfWidth_le_floor (R W : ℝ) (n : ℕ)
    (h : 0 < ⌊R * W⌋₊) : clampedCoreHalfWidth R W n ≤ ⌊R * W⌋₊ := by
  unfold clampedCoreHalfWidth
  omega

theorem clampedCoreHalfWidth_eq_floor (R W : ℝ) (n : ℕ)
    (h : 0 < ⌊R * W⌋₊) (hfit : 2 * ⌊R * W⌋₊ + 1 ≤ n + 1) :
    clampedCoreHalfWidth R W n = ⌊R * W⌋₊ := by
  unfold clampedCoreHalfWidth
  omega

theorem clampedCoreHalfWidth_atTop (W : ℕ → ℝ)
    (hW : Tendsto W atTop atTop) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun n => clampedCoreHalfWidth R (W n) n) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [(floor_radius_atTop W hW hR).eventually_ge_atTop b,
    eventually_ge_atTop (2 * b)] with n hf hn
  unfold clampedCoreHalfWidth
  omega

theorem clampedCoreHalfWidth_eq_floor_along_sparse
    (W : ℕ → ℝ) (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hsparse : Tendsto (fun n => W (φ n) / (φ n + 1 : ℕ)) atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ n in atTop, clampedCoreHalfWidth R (W (φ n)) (φ n) = ⌊R * W (φ n)⌋₊ := by
  have hgeom := canonical_floor_core_eventually_fits (fun n => φ n + 1)
    ((tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop)
    (fun n => W (φ n)) (fun n => hW (φ n)) (hWlim.comp hφ.tendsto_atTop) hsparse hR
  filter_upwards [hgeom] with n hn
  apply clampedCoreHalfWidth_eq_floor R (W (φ n)) (φ n) hn.1
  simpa only [canonicalCoreBand_width hn.1] using hn.2

end CircularLawSection6
