import BernoulliSection10.MultiAffine

/-!
# Recursive second moment for multiaffine logarithms

This module iterates the one-row `L²` estimate from Lemma 10.2.  The explicit
recursive cost is deliberately coarse; its role in Section 10 is to prove the
finite `L²` input required by Efron--Stein without exposing a certificate to
callers.
-/

open scoped ENNReal NNReal Topology BigOperators
open Set MeasureTheory

noncomputable section

namespace BernoulliSection10

def multiAffineLogSqCost (L : ℝ) : List ℕ → ℝ≥0∞
  | [] => 0
  | p :: ps =>
      ENNReal.ofReal 2 * multiAffineLogSqCost L ps +
        ENNReal.ofReal 2 * ENNReal.ofReal
          (lemma10_2Constant L *
            Real.log (Real.exp 1 * (p : ℝ)) ^ 2)

theorem multiAffineEval_log_lintegral_sq_le
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ps : List ℕ} (hpos : ∀ p ∈ ps, 0 < p)
    (c : MultiAffineTensor E ps) :
    ∫⁻ x, ENNReal.ofReal
        (|Real.log ‖multiAffineEval c x‖ - Real.log ‖c‖| ^ 2)
        ∂(multiAffineRowLaw μ ps) ≤
      multiAffineLogSqCost L ps := by
  letI := hμ.toIsProbabilityMeasure
  induction ps with
  | nil =>
      have hf : (fun x : MultiAffineRows [] ↦
          ENNReal.ofReal
            (|Real.log ‖multiAffineEval c x‖ - Real.log ‖c‖| ^ 2)) = 0 := by
        funext x
        change ENNReal.ofReal (|Real.log ‖c‖ - Real.log ‖c‖| ^ 2) = 0
        rw [sub_self, abs_zero, zero_pow (by norm_num), ENNReal.ofReal_zero]
      rw [hf]
      change (∫⁻ _ : MultiAffineRows [], (0 : ℝ≥0∞)
        ∂multiAffineRowLaw μ []) ≤ 0
      exact le_of_eq lintegral_zero
  | cons p ps ih =>
      have hp : 0 < p := hpos p (by simp)
      have htail : ∀ q ∈ ps, 0 < q := by
        intro q hq
        exact hpos q (by simp [hq])
      let νp : Measure (Fin p → ℝ) := Measure.pi fun _ : Fin p => μ
      let νtail : Measure (MultiAffineRows ps) := multiAffineRowLaw μ ps
      let headDiff : (Fin p → ℝ) → ℝ := fun x ↦
        Real.log ‖multiAffineHeadEval c x‖ - Real.log ‖c‖
      let tailDiff : (Fin p → ℝ) → MultiAffineRows ps → ℝ := fun x y ↦
        Real.log ‖multiAffineEval (multiAffineHeadEval c x) y‖ -
          Real.log ‖multiAffineHeadEval c x‖
      have hheadCont : Continuous (multiAffineHeadEval c) := by
        change Continuous fun x : Fin p → ℝ ↦
          multiAffineTensorHead c 0 +
            ∑ s : Fin p, x s • multiAffineTensorHead c s.succ
        fun_prop
      have hevalCont : Continuous fun z :
          (Fin p → ℝ) × MultiAffineRows ps ↦
          multiAffineEval (multiAffineHeadEval c z.1) z.2 := by
        exact (continuous_multiAffineEval_uncurry ps).comp
          ((hheadCont.comp continuous_fst).prodMk continuous_snd)
      have htotalMeas : Measurable fun z :
          (Fin p → ℝ) × MultiAffineRows ps ↦
          ENNReal.ofReal
            (|Real.log ‖multiAffineEval c z‖ - Real.log ‖c‖| ^ 2) := by
        change Measurable fun z : (Fin p → ℝ) × MultiAffineRows ps ↦
          ENNReal.ofReal
            (|Real.log
                ‖multiAffineEval (multiAffineHeadEval c z.1) z.2‖ -
              Real.log ‖c‖| ^ 2)
        exact (((Real.measurable_log.comp hevalCont.norm.measurable).sub_const _).norm
          |>.pow_const 2).ennreal_ofReal
      change
        (∫⁻ z : (Fin p → ℝ) × MultiAffineRows ps,
          ENNReal.ofReal
            (|Real.log ‖multiAffineEval c z‖ - Real.log ‖c‖| ^ 2)
          ∂νp.prod νtail) ≤ multiAffineLogSqCost L (p :: ps)
      rw [MeasureTheory.lintegral_prod _ htotalMeas.aemeasurable]
      have hinner (x : Fin p → ℝ) :
          (∫⁻ y, ENNReal.ofReal
              (|Real.log ‖multiAffineEval c (x, y)‖ - Real.log ‖c‖| ^ 2)
              ∂νtail) ≤
            ENNReal.ofReal 2 * multiAffineLogSqCost L ps +
              ENNReal.ofReal 2 * ENNReal.ofReal (|headDiff x| ^ 2) := by
        have htailMeas : Measurable fun y : MultiAffineRows ps ↦
            ENNReal.ofReal (|tailDiff x y| ^ 2) := by
          exact ((((Real.measurable_log.comp
            (measurable_norm_multiAffineEval
              (multiAffineHeadEval c x))).sub_const _).norm).pow_const 2).ennreal_ofReal
        calc
          (∫⁻ y, ENNReal.ofReal
              (|Real.log ‖multiAffineEval c (x, y)‖ - Real.log ‖c‖| ^ 2)
              ∂νtail) ≤
              ∫⁻ y, ENNReal.ofReal 2 *
                  ENNReal.ofReal (|tailDiff x y| ^ 2) +
                ENNReal.ofReal 2 * ENNReal.ofReal (|headDiff x| ^ 2)
                ∂νtail := by
            apply lintegral_mono
            intro y
            change
              ENNReal.ofReal
                  (|Real.log ‖multiAffineEval (multiAffineHeadEval c x) y‖ -
                    Real.log ‖c‖| ^ 2) ≤ _
            have hdecomp :
                Real.log ‖multiAffineEval (multiAffineHeadEval c x) y‖ -
                    Real.log ‖c‖ = tailDiff x y + headDiff x := by
              simp only [tailDiff, headDiff]
              ring
            rw [hdecomp]
            have hreal : |tailDiff x y + headDiff x| ^ 2 ≤
                2 * |tailDiff x y| ^ 2 + 2 * |headDiff x| ^ 2 := by
              simp only [sq_abs]
              nlinarith [add_sq_le (a := tailDiff x y) (b := headDiff x)]
            apply le_trans (ENNReal.ofReal_le_ofReal hreal)
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          _ = ENNReal.ofReal 2 *
                (∫⁻ y, ENNReal.ofReal (|tailDiff x y| ^ 2) ∂νtail) +
              ENNReal.ofReal 2 * ENNReal.ofReal (|headDiff x| ^ 2) := by
            calc
              (∫⁻ y, ENNReal.ofReal 2 *
                    ENNReal.ofReal (|tailDiff x y| ^ 2) +
                  ENNReal.ofReal 2 * ENNReal.ofReal (|headDiff x| ^ 2)
                  ∂νtail) =
                  (∫⁻ y, ENNReal.ofReal 2 *
                    ENNReal.ofReal (|tailDiff x y| ^ 2) ∂νtail) +
                  ∫⁻ _y, ENNReal.ofReal 2 *
                    ENNReal.ofReal (|headDiff x| ^ 2) ∂νtail :=
                lintegral_add_left (measurable_const.mul htailMeas) _
              _ = ENNReal.ofReal 2 *
                    (∫⁻ y, ENNReal.ofReal (|tailDiff x y| ^ 2) ∂νtail) +
                  ENNReal.ofReal 2 * ENNReal.ofReal (|headDiff x| ^ 2) := by
                rw [lintegral_const_mul _ htailMeas]
                simp [νtail]
          _ ≤ ENNReal.ofReal 2 * multiAffineLogSqCost L ps +
              ENNReal.ofReal 2 * ENNReal.ofReal (|headDiff x| ^ 2) := by
            gcongr
            simpa [tailDiff, νtail] using
              ih htail (multiAffineHeadEval c x)
      have hheadSqMeas : Measurable fun x : Fin p → ℝ ↦
          ENNReal.ofReal (|headDiff x| ^ 2) := by
        exact ((((Real.measurable_log.comp hheadCont.norm.measurable).sub_const _).norm
          |>.pow_const 2).ennreal_ofReal)
      calc
        (∫⁻ x, ∫⁻ y, ENNReal.ofReal
            (|Real.log ‖multiAffineEval c (x, y)‖ - Real.log ‖c‖| ^ 2)
            ∂νtail ∂νp) ≤
            ∫⁻ x, ENNReal.ofReal 2 * multiAffineLogSqCost L ps +
              ENNReal.ofReal 2 * ENNReal.ofReal (|headDiff x| ^ 2) ∂νp :=
          lintegral_mono hinner
        _ = ENNReal.ofReal 2 * multiAffineLogSqCost L ps +
            ENNReal.ofReal 2 *
              (∫⁻ x, ENNReal.ofReal (|headDiff x| ^ 2) ∂νp) := by
          calc
            (∫⁻ x, ENNReal.ofReal 2 * multiAffineLogSqCost L ps +
                ENNReal.ofReal 2 * ENNReal.ofReal (|headDiff x| ^ 2)
                ∂νp) =
                (∫⁻ _x, ENNReal.ofReal 2 * multiAffineLogSqCost L ps
                  ∂νp) +
                ∫⁻ x, ENNReal.ofReal 2 *
                  ENNReal.ofReal (|headDiff x| ^ 2) ∂νp :=
              lintegral_add_left measurable_const _
            _ = ENNReal.ofReal 2 * multiAffineLogSqCost L ps +
                ENNReal.ofReal 2 *
                  (∫⁻ x, ENNReal.ofReal (|headDiff x| ^ 2) ∂νp) := by
              rw [lintegral_const_mul _ hheadSqMeas]
              simp [νp]
        _ ≤ ENNReal.ofReal 2 * multiAffineLogSqCost L ps +
            ENNReal.ofReal 2 * ENNReal.ofReal
              (lemma10_2Constant L *
                Real.log (Real.exp 1 * (p : ℝ)) ^ 2) := by
          gcongr
          simpa [headDiff, νp] using
            multiAffineHead_log_lintegral_sq_le hμ hp c
        _ = multiAffineLogSqCost L (p :: ps) := rfl

theorem multiAffineLogSqCost_ne_top (L : ℝ) (ps : List ℕ) :
    multiAffineLogSqCost L ps ≠ ∞ := by
  induction ps with
  | nil => simp [multiAffineLogSqCost]
  | cons p ps ih =>
      change ENNReal.ofReal 2 * multiAffineLogSqCost L ps +
        ENNReal.ofReal 2 * ENNReal.ofReal
          (lemma10_2Constant L *
            Real.log (Real.exp 1 * (p : ℝ)) ^ 2) ≠ ∞
      exact ENNReal.add_ne_top.2 ⟨
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ih,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩

theorem multiAffineEval_log_memLp_two
    {μ : Measure ℝ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ps : List ℕ} (hpos : ∀ p ∈ ps, 0 < p)
    (c : MultiAffineTensor E ps) :
    MemLp (fun x ↦
        Real.log ‖multiAffineEval c x‖ - Real.log ‖c‖)
      2 (multiAffineRowLaw μ ps) := by
  letI := hμ.toIsProbabilityMeasure
  let f : MultiAffineRows ps → ℝ := fun x ↦
    Real.log ‖multiAffineEval c x‖ - Real.log ‖c‖
  have hf : Measurable f := by
    exact (Real.measurable_log.comp
      (measurable_norm_multiAffineEval c)).sub_const _
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
  have hfinite :
      (∫⁻ x, ENNReal.ofReal (f x ^ 2)
        ∂multiAffineRowLaw μ ps) < ∞ := by
    apply lt_of_le_of_lt
    · simpa only [f, sq_abs] using
        multiAffineEval_log_lintegral_sq_le hμ hpos c
    · exact (multiAffineLogSqCost_ne_top L ps).lt_top
  refine ⟨(hf.pow_const 2).aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (ae_of_all _ fun x ↦ sq_nonneg (f x))).2 hfinite

end BernoulliSection10
