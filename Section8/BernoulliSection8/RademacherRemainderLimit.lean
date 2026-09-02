import BernoulliSection8.RademacherRemainder
import BernoulliSection8.CellPressureLimit
import BernoulliSection10.AsymptoticErrors

/-! # Vanishing incomplete-cell error on the actual cyclic sample space

The terminal three sites are reserved first. The observable compares the
remaining literal prefix with its complete cells, both read from the same
`IntervalRows W (s+3)` sample. The sole exceptional event is the constructed
Nguyen all-interface event.
-/

open Filter MeasureTheory Set Topology
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10 BernoulliSection10.ProbabilityLimits

theorem rademacher_prefix_maxPressure_change_le
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s p : ℕ) (hp : p ≤ s) (hW : interfaceCanonicalLargeWThreshold I ≤ W)
    (z : ℂ) (x : IntervalRows W s)
    (hx : x ∈ rademacherInterfaceGoodEvent I W s) :
    |intervalMaxDegreeLog W s z x -
      intervalMaxDegreeLog W p z (intervalRestriction (Fin.castLEEmb hp) x)| ≤
      rademacherTransferLogConstant I z * (((s - p) * W : ℕ) : ℝ) * densityLogScale W := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp
  have he : (Fin.castLEEmb hp : Fin p ↪ Fin (p + q)) = Fin.castAddEmb q := by
    ext i
    rfl
  simpa only [he, Nat.add_sub_cancel_left] using
    rademacher_remainder_maxPressure_change_le I hI W p q hW z x hx

theorem targetCompleteCells_le_outside (W s : ℕ) :
    targetCells (s + 3) W * (3 + coreSites W) ≤ s := by
  simpa only [targetCells, Nat.add_sub_cancel_right, cellSites, Nat.add_comm 3] using
    Nat.div_mul_le_self s (cellSites W)

theorem targetCompleteCells_outside_restriction (W s : ℕ) (x : IntervalRows W (s + 3)) :
    intervalRestriction (Fin.castLEEmb (targetCompleteCells_le_outside W s))
      (intervalRestriction (Fin.castAddEmb 3) x) =
      intervalRestriction (targetCompleteCellsEmbedding W (s + 3)) x := by
  ext i a
  change x (intervalRowEmbedding (Fin.castAddEmb 3)
    (intervalRowEmbedding (Fin.castLEEmb (targetCompleteCells_le_outside W s)) i)) a =
      x (intervalRowEmbedding (targetCompleteCellsEmbedding W (s + 3)) i) a
  change x (intervalRowEmbedding (Fin.castAddEmb 3)
    (intervalRowIndex ((Fin.castLEEmb (targetCompleteCells_le_outside W s))
      (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2)) a = _
  rw [intervalRowEmbedding_rowIndex]
  rfl

/-- Outside pressure minus complete-cell pressure, normalized by the full
cyclic scalar dimension. The sample space and both embeddings are literal. -/
def rademacherRemainderDifference (W s : ℕ) (z : ℂ)
    (x : IntervalRows W (s + 3)) : ℝ :=
  (intervalMaxDegreeLog W s z (intervalRestriction (Fin.castAddEmb 3) x) -
    intervalMaxDegreeLog W (targetCells (s + 3) W * (3 + coreSites W)) z
      (intervalRestriction (targetCompleteCellsEmbedding W (s + 3)) x)) /
    (((s + 3) * W : ℕ) : ℝ)

theorem rademacherRemainderDifference_abs_le_on_good
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ) (hW : interfaceCanonicalLargeWThreshold I ≤ W) (z : ℂ)
    (x : IntervalRows W (s + 3))
    (hx : x ∈ rademacherInterfaceGoodEvent I W (s + 3)) :
    |rademacherRemainderDifference W s z x| ≤
      rademacherTransferLogConstant I z *
        ((densityAnchorSize W : ℝ) * densityLogScale W / (((s + 3) * W : ℕ) : ℝ)) := by
  have hWpos := (interfaceCanonicalLargeWConditions I hW).1
  have hprefix := rademacherInterfaceGoodEvent_subset_subinterval I (Fin.castAddEmb 3) hx
  have hchange := rademacher_prefix_maxPressure_change_le I hI W s
    (targetCells (s + 3) W * (3 + coreSites W)) (targetCompleteCells_le_outside W s)
    hW z (intervalRestriction (Fin.castAddEmb 3) x) hprefix
  rw [targetCompleteCells_outside_restriction] at hchange
  have hrem : s - targetCells (s + 3) W * (3 + coreSites W) = remainderSites (s + 3) W := by
    simpa only [Nat.add_sub_cancel_right, cellSites, Nat.add_comm 3] using
      (remainderSites_eq_sub (s + 3) W).symm
  rw [hrem] at hchange
  have hlen : ((remainderSites (s + 3) W * W : ℕ) : ℝ) ≤ densityAnchorSize W := by
    have h := Nat.mul_le_mul_right W (remainderSites_lt (s + 3) W).le
    have heq : cellSites W * W = densityAnchorSize W := rfl
    rw [heq] at h
    exact_mod_cast h
  have hnum := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlen (rademacherTransferLogConstant_nonneg I z))
    (densityLogScale_nonneg hWpos)
  unfold rademacherRemainderDifference
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ (rademacherTransferLogConstant I z *
      ((remainderSites (s + 3) W * W : ℕ) : ℝ) * densityLogScale W) /
        (((s + 3) * W : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hchange (Nat.cast_nonneg _)
    _ ≤ (rademacherTransferLogConstant I z * densityAnchorSize W * densityLogScale W) /
        (((s + 3) * W : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hnum (Nat.cast_nonneg _)
    _ = _ := by ring

/-- In the long branch, the incomplete-cell contribution vanishes in
probability under the actual global interface estimate and bandwidth law. -/
theorem rademacherRemainderDifference_tendsto
    (I : NguyenBottomSingularInput) (hI : 1 ≤ I.subgaussianBound)
    (W s : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (hlong : ∀ᶠ n in atTop, anchorSize (W n) ≤ (s n + 3) * W n)
    (hlog : Tendsto (fun n => Real.log (((s n + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0)) (z : ℂ) :
    TendstoInProbabilityTri (fun n => intervalRowsLaw (W n) (s n + 3) rademacherLaw)
      (fun n => rademacherRemainderDifference (W n) (s n) z) 0 := by
  have hlarge : ∀ᶠ n in atTop,
      (W n : ℝ) ^ (101 / 100 : ℝ) ≤ (((s n + 3) * W n : ℕ) : ℝ) := by
    filter_upwards [hW.eventually (eventually_gt_atTop 0), hlong] with n hn hln
    exact (rpow_le_anchorSize hn).trans (by exact_mod_cast hln)
  have hscale := (tendsto_densityRemainderErrorScale hW hlarge).const_mul
    (rademacherTransferLogConstant I z)
  have hbad := rademacherInterfaceGoodEvent_compl_probability_tendsto_zero
    I hI W (fun n => s n + 3) hW hlog
  intro ε hε
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => measureReal_nonneg) _ hbad
  have hsmall : ∀ᶠ n in atTop, rademacherTransferLogConstant I z *
      ((densityAnchorSize (W n) : ℝ) * densityLogScale (W n) /
        (((s n + 3) * W n : ℕ) : ℝ)) < ε :=
    hscale.eventually (eventually_lt_nhds (by simpa using hε))
  filter_upwards [hW.eventually (eventually_ge_atTop (interfaceCanonicalLargeWThreshold I)),
    hsmall] with n hn hεn
  refine measureReal_mono ?_ (measure_ne_top
    (intervalRowsLaw (W n) (s n + 3) rademacherLaw) _)
  intro x hx hgood
  have hb := rademacherRemainderDifference_abs_le_on_good I hI (W n) (s n) hn z x hgood
  exact (not_le_of_gt (hb.trans_lt hεn)) (by simpa only [sub_zero] using hx)

end BernoulliSection8
