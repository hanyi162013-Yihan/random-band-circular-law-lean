import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite pressure maxima and the deterministic optimizing degree

These elementary statements underlie (10.33)--(10.36), (10.42), and
(10.46). The maximizing degree is the least maximizing index, as in the
paper, not an additional datum supplied by a caller. The bounds hold for
negative as well as positive pressures.
-/

noncomputable section

namespace BernoulliSection10

/-- Maximum of a nonempty finite family of real pressures. -/
def finitePressureMax {d : ℕ} (F : Fin (d + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty F

theorem le_finitePressureMax {d : ℕ} (F : Fin (d + 1) → ℝ) (r : Fin (d + 1)) :
    F r ≤ finitePressureMax F :=
  Finset.le_sup' F (Finset.mem_univ r)

theorem finitePressureMax_le {d : ℕ} {F : Fin (d + 1) → ℝ} {c : ℝ}
    (h : ∀ r, F r ≤ c) : finitePressureMax F ≤ c :=
  Finset.sup'_le Finset.univ_nonempty F (fun r _ => h r)

theorem finitePressureMax_attained {d : ℕ} (F : Fin (d + 1) → ℝ) :
    ∃ r, F r = finitePressureMax F := by
  obtain ⟨r, _, hr⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty F
  exact ⟨r, hr.symm⟩

/-- All maximizing degrees. This definition involves only a finite family. -/
def pressureMaximizers {d : ℕ} (F : Fin (d + 1) → ℝ) : Finset (Fin (d + 1)) := by
  classical
  exact Finset.univ.filter (fun r => F r = finitePressureMax F)

theorem mem_pressureMaximizers {d : ℕ} (F : Fin (d + 1) → ℝ)
    (r : Fin (d + 1)) : r ∈ pressureMaximizers F ↔ F r = finitePressureMax F := by
  classical
  simp [pressureMaximizers]

theorem pressureMaximizers_nonempty {d : ℕ} (F : Fin (d + 1) → ℝ) :
    (pressureMaximizers F).Nonempty := by
  obtain ⟨r, hr⟩ := finitePressureMax_attained F
  exact ⟨r, (mem_pressureMaximizers F r).mpr hr⟩

/-- The least maximizing degree, equation (10.36). -/
def pressureOptimizingDegree {d : ℕ} (F : Fin (d + 1) → ℝ) : Fin (d + 1) :=
  (pressureMaximizers F).min' (pressureMaximizers_nonempty F)

theorem pressureOptimizingDegree_maximizes {d : ℕ} (F : Fin (d + 1) → ℝ) :
    F (pressureOptimizingDegree F) = finitePressureMax F := by
  apply (mem_pressureMaximizers F _).mp
  exact Finset.min'_mem _ _

theorem pressureOptimizingDegree_le {d : ℕ} (F : Fin (d + 1) → ℝ)
    {r : Fin (d + 1)} (hr : F r = finitePressureMax F) :
    pressureOptimizingDegree F ≤ r :=
  Finset.min'_le _ _ ((mem_pressureMaximizers F r).mpr hr)

theorem finitePressureMax_mono {d : ℕ} {F G : Fin (d + 1) → ℝ}
    (h : ∀ r, F r ≤ G r) : finitePressureMax F ≤ finitePressureMax G :=
  finitePressureMax_le (fun r => (h r).trans (le_finitePressureMax G r))

/-- A common perturbation bound passes to the maximum with no cardinality
factor and, in a probabilistic application, no union bound. -/
theorem abs_finitePressureMax_sub_le {d : ℕ} {F G : Fin (d + 1) → ℝ} {c : ℝ}
    (h : ∀ r, |F r - G r| ≤ c) :
    |finitePressureMax F - finitePressureMax G| ≤ c := by
  have hFG : finitePressureMax F ≤ finitePressureMax G + c := by
    apply finitePressureMax_le
    intro r
    have h1 := (abs_le.mp (h r)).2
    have h2 := le_finitePressureMax G r
    linarith
  have hGF : finitePressureMax G ≤ finitePressureMax F + c := by
    apply finitePressureMax_le
    intro r
    have h1 := (abs_le.mp (h r)).1
    have h2 := le_finitePressureMax F r
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The precise maximum-of-deviations form used with row concentration. -/
theorem abs_finitePressureMax_sub_le_max_deviation {d : ℕ}
    (F G : Fin (d + 1) → ℝ) :
    |finitePressureMax F - finitePressureMax G| ≤
      finitePressureMax (fun r => |F r - G r|) :=
  abs_finitePressureMax_sub_le (le_finitePressureMax _)

theorem finitePressureMax_const {d : ℕ} (c : ℝ) :
    finitePressureMax (fun _ : Fin (d + 1) => c) = c :=
  Finset.sup'_const Finset.univ_nonempty c

theorem finitePressureMax_add_const {d : ℕ} (F : Fin (d + 1) → ℝ) (c : ℝ) :
    finitePressureMax (fun r => F r + c) = finitePressureMax F + c := by
  apply le_antisymm
  · apply finitePressureMax_le
    intro r
    linarith [le_finitePressureMax F r]
  · have h := le_finitePressureMax (fun r => F r + c) (pressureOptimizingDegree F)
    rwa [pressureOptimizingDegree_maximizes F] at h

theorem finitePressureMax_mul_nonneg {d : ℕ} (F : Fin (d + 1) → ℝ)
    {c : ℝ} (hc : 0 ≤ c) :
    finitePressureMax (fun r => c * F r) = c * finitePressureMax F := by
  apply le_antisymm
  · exact finitePressureMax_le
      (fun r => mul_le_mul_of_nonneg_left (le_finitePressureMax F r) hc)
  · have h := le_finitePressureMax (fun r => c * F r) (pressureOptimizingDegree F)
    rwa [pressureOptimizingDegree_maximizes F] at h

end BernoulliSection10
