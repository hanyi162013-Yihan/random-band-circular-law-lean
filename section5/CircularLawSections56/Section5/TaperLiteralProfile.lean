import CircularLawSections56.Section5.TaperedPaperWeights
import CircularLawSections56.Section5.UniformLogarithmicWeights
import CircularLawSections56.Section6.LiteralIndicatorModel

/-! # The exact polynomial taper in the literal band-model coordinates -/

open scoped BigOperators ENNReal

noncomputable section
set_option autoImplicit false

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

def reindexPaperWeights {D E : ℕ} {c C : ℝ} (h : D = E)
    (profile : PaperIndicatorWeights E c C) : PaperIndicatorWeights D c C := by
  subst E
  exact profile

@[simp] theorem reindexPaperWeights_q {D E : ℕ} {c C : ℝ} (h : D = E)
    (profile : PaperIndicatorWeights E c C) (i : Fin (D + 1)) :
    (reindexPaperWeights h profile).q i = profile.q (Fin.cast (congrArg (· + 1) h) i) := by
  subst E
  rfl

@[simp] theorem reindexPaperWeights_b {D E : ℕ} {c C : ℝ} (h : D = E)
    (profile : PaperIndicatorWeights E c C) (i : Fin (D + 1)) :
    (reindexPaperWeights h profile).b i = profile.b (Fin.cast (congrArg (· + 1) h) i) := by
  subst E
  rfl

def taperStateDimension (W : ℕ) : ℕ := 2 * W - 1

theorem taperStateDimension_succ (W : ℕ) (hW : 0 < W) :
    taperStateDimension W + 1 = 2 * W := by unfold taperStateDimension; omega

def taperCenter (W : ℕ) (hW : 0 < W) : Fin (taperStateDimension W + 1) :=
  ⟨W, by unfold taperStateDimension; omega⟩

theorem taperCenter_ne_zero (W : ℕ) (hW : 0 < W) : taperCenter W hW ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  simp only [taperCenter, Fin.val_zero] at hv
  omega

namespace PolynomialTaperProfile

def literalWeights (p : PolynomialTaperProfile) (W : ℕ) (hW : 0 < W) :
    PaperIndicatorWeights (taperStateDimension W + 1) (p.lowerParameter W) p.upperParameter :=
  reindexPaperWeights (taperStateDimension_succ W hW) (p.paperWeights W)

@[simp] theorem literalWeights_q (p : PolynomialTaperProfile) (W : ℕ) (hW : 0 < W)
    (i : Fin (taperStateDimension W + 2)) :
    (p.literalWeights W hW).q i =
      p.weight W (Fin.cast (congrArg (· + 1) (taperStateDimension_succ W hW)) i) := by
  rw [literalWeights, reindexPaperWeights_q]
  rfl

/-- The entries are precisely the square roots of the normalized sampled taper. -/
theorem literalWeights_amplitude (p : PolynomialTaperProfile) (W : ℕ) (hW : 0 < W)
    (i : Fin (taperStateDimension W + 2)) :
    (p.literalWeights W hW).b i =
      (Real.sqrt (p.f (((i.val : ℝ) - W) / (W + 1 : ℝ)) / p.mass W) : ℂ) := by
  rw [literalWeights, reindexPaperWeights_b]
  rfl

def logarithmicWeightConstant (p : PolynomialTaperProfile) : ℝ :=
  |Real.log (p.lower / p.upper)| + p.exponent

theorem logarithmicWeightConstant_nonneg (p : PolynomialTaperProfile) :
    0 ≤ p.logarithmicWeightConstant := add_nonneg (abs_nonneg _) p.exponent_nonneg

theorem lowerParameter_logarithmic (p : PolynomialTaperProfile) (d W : ℕ)
    (hd : d + 1 = 2 * W) :
    |Real.log (p.lowerParameter W)| ≤ p.logarithmicWeightConstant * dimensionLogScale d := by
  have hH := one_le_dimensionLogScale d
  have hdim : (W + 1 : ℝ) ≤ d + 2 := by
    have hn : W + 1 ≤ d + 2 := by omega
    exact_mod_cast hn
  have hlog : Real.log (W + 1 : ℝ) ≤ dimensionLogScale d := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < W + 1) hdim
    unfold dimensionLogScale
    linarith
  have ha := mul_le_mul_of_nonneg_left hH (abs_nonneg (Real.log (p.lower / p.upper)))
  have hk := mul_le_mul_of_nonneg_left hlog p.exponent_nonneg
  have hp := p.abs_log_lowerParameter_le W
  unfold logarithmicWeightConstant
  nlinarith only [ha, hk, hp]

theorem literalWeights_logarithmic (p : PolynomialTaperProfile) (W : ℕ) (hW : 0 < W) :
    |Real.log (p.lowerParameter W)| ≤
      p.logarithmicWeightConstant * dimensionLogScale (taperStateDimension W) :=
  p.lowerParameter_logarithmic _ W (taperStateDimension_succ W hW)

/-- The manuscript's actual cyclic matrix, with the exact normalized taper. -/
def literalMatrix (p : PolynomialTaperProfile) (k W : ℕ) (hW : 0 < W)
    (ω : Fin ((k + 1) * (taperStateDimension W + 2)) → ℂ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Section6.literalIndicatorMatrix k (taperStateDimension W) (taperCenter W hW)
    (p.literalWeights W hW).b ω

theorem literalMatrix_band_fits (k W : ℕ) (hW : 0 < W) :
    taperStateDimension W + 2 ≤ k + 1 ↔ 2 * W + 1 ≤ k + 1 := by
  have h := taperStateDimension_succ W hW
  omega

def dimensions (W : ℕ → ℕ) : ℕ → ℕ := fun n => taperStateDimension (W n)

def centers (W : ℕ → ℕ) (hW : ∀ n, 0 < W n) : ∀ n, Fin (dimensions W n + 1) :=
  fun n => taperCenter (W n) (hW n)

def profiles (p : PolynomialTaperProfile) (W : ℕ → ℕ) (hW : ∀ n, 0 < W n) :
    ∀ n, PaperIndicatorWeights (dimensions W n + 1) (p.lowerParameter (W n)) p.upperParameter :=
  fun n => p.literalWeights (W n) (hW n)

end PolynomialTaperProfile

end CircularLawSections56.Section5
