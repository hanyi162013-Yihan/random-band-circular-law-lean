import CircularLawSections56.Section5.LiteralNearEndToEndAssembly
import TaoVuReplacement.ReplacementPrinciple

/-!
# Replacement for already-normalized physical matrices

The local Tao--Vu library is used as a proved theorem, not a replacement axiom.
Physical matrices in Sections 3--5 already include their variance normalization.
We undo and redo the Tao--Vu square-root normalization explicitly, and prove its
Hilbert--Schmidt hypothesis from a uniform expected energy bound.  A common
probability space and an a.e.-in-z comparison limit remain explicit model inputs.
-/

open Filter MeasureTheory Topology
open scoped ENNReal BigOperators

noncomputable section

namespace CircularLawSections56.Section6

open CircularLawSections56.Section5 TaoVuReplacement

variable {Ω : Type*} [MeasurableSpace Ω]

def physicalLogPotential {k : ℕ}
    (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (z : ℂ) : ℝ :=
  Real.log ‖(X - z • 1).det‖ / (k + 1 : ℝ)

def physicalEnergy {k : ℕ}
    (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ℝ :=
  hilbertSchmidtSq X / (k + 1 : ℝ)

def undoPhysicalNormalization {k : ℕ}
    (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  (Real.sqrt (k + 1 : ℝ) : ℂ) • X

@[simp] theorem normalizedMatrix_undoPhysicalNormalization {k : ℕ}
    (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    normalizedMatrix (undoPhysicalNormalization X) = X := by
  have hs : Real.sqrt (k + 1 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  unfold normalizedMatrix inverseSqrtDimension undoPhysicalNormalization
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, smul_smul]
  rw [← Complex.ofReal_mul, inv_mul_cancel₀ hs, Complex.ofReal_one, one_smul]

@[simp] theorem normalizedLogDet_undoPhysicalNormalization {k : ℕ}
    (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (z : ℂ) :
    normalizedLogDet (undoPhysicalNormalization X) z = physicalLogPotential X z := by
  simp [normalizedLogDet, physicalLogPotential]

@[simp] theorem normalizedEnergy_undoPhysicalNormalization {k : ℕ}
    (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    normalizedHilbertSchmidtSq (undoPhysicalNormalization X) = physicalEnergy X := by
  have hn : (k + 1 : ℝ) ≠ 0 := by positivity
  unfold normalizedHilbertSchmidtSq undoPhysicalNormalization physicalEnergy
  rw [hilbertSchmidtSq_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ k + 1), Nat.cast_add, Nat.cast_one]
  field_simp

theorem tendstoInMeasure_iff_tri (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (a : ℝ) :
    TendstoInMeasure P X atTop (fun _ => a) ↔
      TendstoInProbabilityTri (fun _ => P) X a := by
  simp only [TendstoInProbabilityTri, tendstoInMeasure_iff_measureReal_norm,
    Real.norm_eq_abs]

theorem tendstoInProbabilityTri_neg (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {a : ℝ}
    (h : TendstoInProbabilityTri (fun _ => P) X a) :
    TendstoInProbabilityTri (fun _ => P) (fun k ω => -X k ω) (-a) := by
  intro ε hε
  simpa only [neg_sub_neg, abs_sub_comm] using h ε hε

theorem tendstoInMeasure_sub_same_constant (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : ℕ → Ω → ℝ} {a : ℝ}
    (hX : TendstoInProbabilityTri (fun _ => P) X a)
    (hY : TendstoInProbabilityTri (fun _ => P) Y a) :
    TendstoInMeasure P (fun k ω => X k ω - Y k ω) atTop 0 := by
  apply (tendstoInMeasure_iff_tri P _ 0).2
  simpa only [add_neg_cancel, sub_eq_add_neg] using
    hX.add (fun _ => P) (tendstoInProbabilityTri_neg P hY)

/-- Markov supplies Tao--Vu's tightness assumption; it is not a model premise. -/
theorem boundedInProbability_of_uniform_integral
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hNonneg : ∀ k ω, 0 ≤ X k ω)
    (hInt : ∀ k, Integrable (X k) P)
    (hBound : ∀ k, ∫ ω, X k ω ∂P ≤ C) :
    BoundedInProbability P X := by
  intro ε hε
  obtain ⟨r, hr0, hrpos, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hr : 0 < r := ENNReal.ofReal_pos.1 hrpos
  let cutoff : ℝ := (C + 1) / r
  have hcutoff : 0 < cutoff := div_pos (by positivity) hr
  refine ⟨cutoff, hcutoff.le, Filter.Eventually.of_forall fun k => ?_⟩
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (hNonneg k)) (hInt k) cutoff
  have htail : P.real {ω | cutoff < ‖X k ω‖} < r := by
    have hsub : P.real {ω | cutoff < ‖X k ω‖} ≤ P.real {ω | cutoff ≤ X k ω} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      change cutoff < ‖X k ω‖ at hω
      have hlt : cutoff < X k ω := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hNonneg k ω)] using hω
      exact hlt.le
    have hmul := mul_le_mul_of_nonneg_left hsub hcutoff.le
    have heq : cutoff * r = C + 1 := by dsimp only [cutoff]; field_simp
    nlinarith [hBound k]
  calc
    P {ω | cutoff < ‖X k ω‖} = ENNReal.ofReal (P.real {ω | cutoff < ‖X k ω‖}) := by
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ < ENNReal.ofReal r := ENNReal.ofReal_lt_ofReal_iff hr |>.2 htail
    _ < ε := hrε

/-- Replacement applied to the actual, already-normalized matrix observables. -/
theorem physical_replacement_of_logPotential_limits
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ∀ k, Ω → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hX : ∀ k i j, Measurable fun ω => X k ω i j)
    (hY : ∀ k i j, Measurable fun ω => Y k ω i j)
    (energyBound : ℝ) (hEnergyBound : 0 ≤ energyBound)
    (hEnergyInt : ∀ k, Integrable
      (fun ω => physicalEnergy (X k ω) + physicalEnergy (Y k ω)) P)
    (hEnergy : ∀ k, ∫ ω, physicalEnergy (X k ω) + physicalEnergy (Y k ω) ∂P ≤ energyBound)
    (target : ℂ → ℝ)
    (hLogX : ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri (fun _ => P)
      (fun k ω => physicalLogPotential (X k ω) z) (target z))
    (hLogY : ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri (fun _ => P)
      (fun k ω => physicalLogPotential (Y k ω) z) (target z)) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure P (fun k ω => esdDifference (X k ω) (Y k ω) f) atTop 0 := by
  let A := fun k ω => undoPhysicalNormalization (X k ω)
  let B := fun k ω => undoPhysicalNormalization (Y k ω)
  have hA : ∀ k i j, Measurable fun ω => A k ω i j := by
    intro k i j
    exact measurable_const.mul (hX k i j)
  have hB : ∀ k i j, Measurable fun ω => B k ω i j := by
    intro k i j
    exact measurable_const.mul (hY k i j)
  have hHS : BoundedInProbability P
      (fun k ω => normalizedHilbertSchmidtPairSq (A k ω) (B k ω)) := by
    simp only [A, B, normalizedHilbertSchmidtPairSq, normalizedEnergy_undoPhysicalNormalization]
    apply boundedInProbability_of_uniform_integral P _ energyBound hEnergyBound
      (fun k ω => ?_) hEnergyInt hEnergy
    exact add_nonneg (div_nonneg (hilbertSchmidtSq_nonneg _) (by positivity))
      (div_nonneg (hilbertSchmidtSq_nonneg _) (by positivity))
  have hlog : ∀ᵐ z ∂(volume : Measure ℂ), TendstoInMeasure P
      (fun k ω => normalizedLogDetDifference (A k ω) (B k ω) z) atTop 0 := by
    filter_upwards [hLogX, hLogY] with z hzx hzy
    simpa only [A, B, normalizedLogDetDifference, normalizedLogDet_undoPhysicalNormalization] using
      tendstoInMeasure_sub_same_constant P hzx hzy
  simpa only [A, B, normalizedMatrix_undoPhysicalNormalization] using
    taoVuReplacementPrinciple_inProbability P A B hA hB hHS hlog

/-- The Section 5 literal certificate is used, rather than assuming its probability
conclusion again. The comparison model supplies its own a.e.-in-z log-potential limit. -/
theorem physical_replacement_of_literalCertificate
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ∀ k, Ω → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hX : ∀ k i j, Measurable fun ω => X k ω i j)
    (hY : ∀ k i j, Measurable fun ω => Y k ω i j)
    (energyBound : ℝ) (hEnergyBound : 0 ≤ energyBound)
    (hEnergyInt : ∀ k, Integrable
      (fun ω => physicalEnergy (X k ω) + physicalEnergy (Y k ω)) P)
    (hEnergy : ∀ k, ∫ ω, physicalEnergy (X k ω) + physicalEnergy (Y k ω) ∂P ≤ energyBound)
    (meanPressure : ℂ → ℕ → ℝ) (target : ℂ → ℝ)
    (hCertificate : ∀ᵐ z ∂(volume : Measure ℂ), Nonempty
      (LiteralFinalClosureCertificateTri (fun _ => P)
        (fun k ω => physicalLogPotential (X k ω) z) (meanPressure z) (target z)))
    (hLogY : ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri (fun _ => P)
      (fun k ω => physicalLogPotential (Y k ω) z) (target z)) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure P (fun k ω => esdDifference (X k ω) (Y k ω) f) atTop 0 := by
  apply physical_replacement_of_logPotential_limits P X Y hX hY energyBound
    hEnergyBound hEnergyInt hEnergy target ?_ hLogY
  filter_upwards [hCertificate] with z hz
  exact hz.some.tendstoInProbability

end CircularLawSections56.Section6
