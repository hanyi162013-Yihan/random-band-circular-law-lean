import CircularLawSection4.DirectionalOperatorAffine
import CircularLawSection4.PaperFreshClosureFull

/-!
# Directional-density closure for the actual fresh determinant

This file transports the heterogeneous conditional-product estimate back to
the actual rotated IID complex atoms.  The orthogonal coordinates are never
given a fictitious uniform conditional moment bound: the negative logarithmic
half is proved conditionally, while positive moments are taken only after
returning to the unconditional atom law.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory Set ProbabilityTheory

noncomputable section

namespace CircularLawSection4

set_option maxHeartbeats 4000000

namespace MultiAffine

/-- Substitute `a * xᵢ` for every variable of a recursive multiaffine
polynomial. -/
def rescaleAllVariables {R : Type*} [CommSemiring R] (a : R) :
    {n : ℕ} → MultiAffine R n → MultiAffine R n
  | 0, .const c => .const c
  | _ + 1, .affine p₀ p₁ =>
      .affine (rescaleAllVariables a p₀)
        (.scale a (rescaleAllVariables a p₁))

@[simp] theorem eval_rescaleAllVariables {R : Type*} [CommSemiring R]
    (a : R) : ∀ {n : ℕ} (p : MultiAffine R n) (x : Fin n → R),
      eval (rescaleAllVariables a p) x = eval p (fun i => a * x i)
  | 0, .const c, x => by simp [rescaleAllVariables]
  | n + 1, .affine p₀ p₁, x => by
      simp only [rescaleAllVariables, eval_affine, eval_scale,
        eval_rescaleAllVariables]
      change
        eval p₀ (fun i => a * x i.castSucc) +
            x (Fin.last n) * (a * eval p₁ (fun i => a * x i.castSucc)) =
          eval p₀ (fun i => a * x i.castSucc) +
            (a * x (Fin.last n)) * eval p₁ (fun i => a * x i.castSucc)
      ring

@[simp] theorem topCoeff_rescaleAllVariables {R : Type*} [CommSemiring R]
    (a : R) : ∀ {n : ℕ} (p : MultiAffine R n),
      topCoeff (rescaleAllVariables a p) = a ^ n * topCoeff p
  | 0, .const c => by simp [rescaleAllVariables]
  | n + 1, .affine p₀ p₁ => by
      simp only [rescaleAllVariables, topCoeff_affine, topCoeff_scale,
        topCoeff_rescaleAllVariables, pow_succ]
      ring

end MultiAffine

/-- The polynomial obtained after freezing the orthogonal directional
coordinates and retaining the real directional coordinates as variables. -/
noncomputable def directionalSubstitute {k : ℕ}
    (p : MultiAffine ℂ k) (phase : ℝ) (v : Fin k → ℝ) : MultiAffine ℂ k :=
  let a : ℂ := Complex.exp ((phase : ℂ) * Complex.I)
  let t : Fin k → ℂ := fun i => a * (Complex.I * (v i : ℂ))
  MultiAffine.rescaleAllVariables a (MultiAffine.translate p t)

/-- Rotating a complex number into its real and imaginary directional
coordinates and reconstructing it is the identity. -/
theorem reconstructedDirectionalAtom_parts (phase : ℝ) (z : ℂ) :
    reconstructedDirectionalAtom phase (directionalImagPart phase z)
      (directionalRealPart phase z) = z := by
  let a : ℂ := Complex.exp ((phase : ℂ) * Complex.I)
  let w : ℂ := Complex.exp (-(phase : ℂ) * Complex.I) * z
  have hw : ((w.re : ℂ) + Complex.I * (w.im : ℂ)) = w := by
    apply Complex.ext <;> simp
  have hexp : a * Complex.exp (-(phase : ℂ) * Complex.I) = 1 := by
    dsimp only [a]
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2 <;> ring
  unfold reconstructedDirectionalAtom directionalImagPart directionalRealPart
  change a * ((w.re : ℂ) + Complex.I * (w.im : ℂ)) = z
  rw [hw]
  dsimp only [w]
  rw [← mul_assoc, hexp, one_mul]

/-- Evaluation identity for the directional substitution. -/
theorem realInputEval_directionalSubstitute {k : ℕ}
    (p : MultiAffine ℂ k) (phase : ℝ) (v u : Fin k → ℝ) :
    realInputEval (directionalSubstitute p phase v) u =
      MultiAffine.eval p
        (fun i => reconstructedDirectionalAtom phase (v i) (u i)) := by
  let a : ℂ := Complex.exp ((phase : ℂ) * Complex.I)
  let t : Fin k → ℂ := fun i => a * (Complex.I * (v i : ℂ))
  simp only [directionalSubstitute, realInputEval,
    MultiAffine.eval_rescaleAllVariables, MultiAffine.eval_translate]
  apply congrArg (MultiAffine.eval p)
  funext i
  dsimp only [a, t, reconstructedDirectionalAtom]
  push_cast
  ring

/-- The phase substitution changes the full coefficient only by a unit
complex phase, so its norm is unchanged. -/
theorem norm_topCoeff_directionalSubstitute {k : ℕ}
    (p : MultiAffine ℂ k) (phase : ℝ) (v : Fin k → ℝ) :
    ‖MultiAffine.topCoeff (directionalSubstitute p phase v)‖ =
      ‖MultiAffine.topCoeff p‖ := by
  let a : ℂ := Complex.exp ((phase : ℂ) * Complex.I)
  have ha : ‖a‖ = 1 := by
    dsimp only [a]
    rw [Complex.norm_exp]
    simp
  simp [directionalSubstitute, a, ha, norm_mul, norm_pow]

/-- Under the directional split, the substituted real polynomial evaluates
to the original polynomial on the actual complex IID vector. -/
theorem directionalSubstitute_split_eval {k : ℕ}
    (p : MultiAffine ℂ k) (phase : ℝ) (x : Fin k → ℂ) :
    realInputEval
        (directionalSubstitute p phase
          ((directionalSplitVector k phase x).1))
        ((directionalSplitVector k phase x).2) =
      MultiAffine.eval p x := by
  rw [realInputEval_directionalSubstitute]
  apply congrArg (MultiAffine.eval p)
  funext i
  exact reconstructedDirectionalAtom_parts phase (x i)

/-- The actual IID complex vector, split into rotated orthogonal and
directional coordinates, is measure preserving onto the corrected joint
conditional-product law. -/
theorem iidAtom_directionalSplit_measurePreserving (k : ℕ)
    (atom : ProbabilityMeasure ℂ) (phase L : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) :
    MeasurePreserving (directionalSplitVector k phase)
      (iidMeasure (atom : Measure ℂ) k)
      (paperDirectionalProductModel k atom phase L hdir).jointMeasure := by
  refine ⟨measurable_directionalSplitVector k phase, ?_⟩
  exact iidAtom_map_directionalSplitVector_eq_compProd k atom phase L hdir

/-- The directional-density hypothesis closes the negative logarithmic half
for any actual complex IID multiaffine polynomial with nonzero full
coefficient. -/
theorem iid_complex_positiveLogLoss_of_directionalDensity
    {n : ℕ} (atom : ProbabilityMeasure ℂ) (phase L : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) (hL : 0 ≤ L)
    (p : MultiAffine ℂ (n + 1)) (htop : 0 < ‖p.topCoeff‖) :
    iidMeasure (atom : Measure ℂ) (n + 1)
        {x | ‖MultiAffine.eval p x‖ = 0} = 0 ∧
      Integrable
        (fun x => positiveLogLoss ‖p.topCoeff‖ ‖MultiAffine.eval p x‖)
        (iidMeasure (atom : Measure ℂ) (n + 1)) ∧
      ∫ x, positiveLogLoss ‖p.topCoeff‖ ‖MultiAffine.eval p x‖
          ∂iidMeasure (atom : Measure ℂ) (n + 1) ≤
        (Real.log (max 1 (((n + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
          (((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  let D := paperDirectionalProductModel (n + 1) atom phase L hdir
  let q : (Fin (n + 1) → ℝ) → MultiAffine ℂ (n + 1) :=
    fun v => directionalSubstitute p phase v
  have htopq : ∀ v, 0 < ‖(q v).topCoeff‖ := by
    intro v
    simpa only [q, norm_topCoeff_directionalSubstitute] using htop
  have heval : Measurable (fun z :
      (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        ‖realInputEval (q z.1) z.2‖) := by
    have hreconstruct : Continuous (fun z :
        (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
          fun i => reconstructedDirectionalAtom phase (z.1 i) (z.2 i)) := by
      apply continuous_pi
      intro i
      unfold reconstructedDirectionalAtom
      fun_prop
    have hcontinuous : Continuous (fun z :
        (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
          ‖MultiAffine.eval p
            (fun i => reconstructedDirectionalAtom phase (z.1 i) (z.2 i))‖) := by
      exact (p.continuous_eval_complex.comp hreconstruct).norm
    convert hcontinuous.measurable using 1
    funext z
    simp only [q, realInputEval_directionalSubstitute]
  have htopMeas : Measurable (fun v => ‖(q v).topCoeff‖) := by
    simpa only [q, norm_topCoeff_directionalSubstitute] using
      (measurable_const : Measurable
        (fun _ : Fin (n + 1) → ℝ => ‖p.topCoeff‖))
  obtain ⟨hzeroJoint, hintJoint, hboundJoint⟩ :=
    directionalProduct_joint_positiveLogLoss D hL
      (paperDirectionalProductModel_intervalBound (n + 1)
        atom phase L hdir) q htopq heval htopMeas
  let radiusJoint :
      ((Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) → ℝ :=
    fun z => ‖realInputEval (q z.1) z.2‖
  let radius : (Fin (n + 1) → ℂ) → ℝ := fun x => ‖p.eval x‖
  have hradiusJoint : Measurable radiusJoint := heval
  have hradiusEq : radius = radiusJoint ∘ directionalSplitVector (n + 1) phase := by
    funext x
    dsimp only [radius, radiusJoint, Function.comp_apply, q]
    rw [directionalSubstitute_split_eval]
  have hlossEq : (fun z => logDeficit ‖p.topCoeff‖ (radiusJoint z)) =
      (fun z => directionalProductPositiveLogLoss q z) := by
    funext z
    rw [logDeficit_eq_positiveLogLoss]
    dsimp only [radiusJoint, directionalProductPositiveLogLoss]
    rw [norm_topCoeff_directionalSubstitute]
  have hzeroJoint' : D.jointMeasure {z | radiusJoint z = 0} = 0 := by
    simpa only [radiusJoint] using hzeroJoint
  have hintJoint' :
      Integrable (fun z => logDeficit ‖p.topCoeff‖ (radiusJoint z))
        D.jointMeasure := by
    rw [hlossEq]
    exact hintJoint
  have hboundJoint' :
      ∫ z, logDeficit ‖p.topCoeff‖ (radiusJoint z) ∂D.jointMeasure ≤
        (Real.log (max 1 (((n + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
          (((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
    rw [hlossEq]
    exact hboundJoint
  have htransport := PaperIndicatorWeights.logDeficit_transport_of_measurePreserving
    (directionalSplitVector (n + 1) phase)
    (iidAtom_directionalSplit_measurePreserving (n + 1) atom phase L hdir)
    ‖p.topCoeff‖ radius radiusJoint hradiusJoint hradiusEq
    hzeroJoint' hintJoint' hboundJoint'
  simpa only [logDeficit_eq_positiveLogLoss, radius] using htransport

namespace PaperIndicatorWeights

variable {d : ℕ} {c₀ C₀ : ℝ}

/-- The isolated fresh polynomial, with selected coordinates controlled by
the manuscript's directional conditional-density assumption, closes the
negative logarithmic half on the complete actual atom product. -/
theorem exists_complex_paperFreshAtomProduct_logDeficit_withDirectionalDensity
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (z : ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < exteriorFamilyMaxL2OpNorm B)
    (atom : ProbabilityMeasure ℂ) (phase L : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) (hL : 0 ≤ L) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        let zeroAtoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ :=
          fun _ _ => 0
        let p₀ := profile.paperIndicatorFreshPolynomial
          center z zeroAtoms B r I J
        let coefficient := ‖MultiAffine.topCoeff p₀‖
        let radius := fun ω : FreshAtomIndex (d + 1) → ℂ =>
          ‖profile.paperIndicatorFreshZ center z
            (fun t ell => ω (t, ell)) B‖
        let μ := Measure.pi
          (fun _ : FreshAtomIndex (d + 1) => (atom : Measure ℂ))
        μ {ω | radius ω = 0} = 0 ∧
          Real.log (exteriorFamilyMaxL2OpNorm B) - Real.log coefficient ≤
            paperIsolatedCoefficientLoss d c₀ ∧
          Integrable (fun ω => logDeficit coefficient (radius ω)) μ ∧
          ∫ ω, logDeficit coefficient (radius ω) ∂μ ≤
            realFreshNegativeBound d L := by
  classical
  let ν : Measure ℂ := atom
  let zeroAtoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ := fun _ _ => 0
  obtain ⟨r, I, J, _heval₀, hcoefficient⟩ :=
    profile.exists_paperIndicatorFreshZ_isolatedFullMonomial_exp
      hc₀ center z zeroAtoms B
  refine ⟨r, I, J, ?_⟩
  let word : Fin (d + 1) → ResetLabel (d + 1) := arbitrarySupportWord I J
  let p₀ := profile.paperIndicatorFreshPolynomial center z zeroAtoms B r I J
  let coefficient : ℝ := ‖MultiAffine.topCoeff p₀‖
  let radius := fun ω : FreshAtomIndex (d + 1) → ℂ =>
    ‖profile.paperIndicatorFreshZ center z (fun t ell => ω (t, ell)) B‖
  let μ := Measure.pi (fun _ : FreshAtomIndex (d + 1) => ν)
  let μx := Measure.pi (fun _ : Fin (d + 1) => ν)
  let μy := Measure.pi (fun _ : UnselectedFreshIndex word => ν)
  let e := splitFreshAtomMeasurableEquiv (K := ℂ) word
  have hcoeff : exteriorFamilyMaxL2OpNorm B *
      Real.exp (-paperIsolatedCoefficientLoss d c₀) ≤ coefficient := by
    simpa only [coefficient, p₀] using hcoefficient
  have htop : 0 < coefficient :=
    (mul_pos hB (Real.exp_pos _)).trans_le hcoeff
  have hscale : Real.log (exteriorFamilyMaxL2OpNorm B) -
      Real.log coefficient ≤ paperIsolatedCoefficientLoss d c₀ :=
    log_scale_sub_log_coefficient_le_of_exp_loss hB hcoeff
  let baseAtoms := fun y : UnselectedFreshIndex word → ℂ =>
    fun t ell => e.symm ((fun _ => 0), y) (t, ell)
  let p := fun y : UnselectedFreshIndex word → ℂ =>
    profile.paperIndicatorFreshPolynomial center z (baseAtoms y) B r I J
  have hcoeff_y (y : UnselectedFreshIndex word → ℂ) :
      ‖MultiAffine.topCoeff (p y)‖ = coefficient := by
    simp only [p, p₀, coefficient,
      topCoeff_paperIndicatorFreshPolynomial]
  have htop_y (y : UnselectedFreshIndex word → ℂ) :
      0 < ‖MultiAffine.topCoeff (p y)‖ := by
    rw [hcoeff_y y]
    exact htop
  have heval (x : Fin (d + 1) → ℂ)
      (y : UnselectedFreshIndex word → ℂ) :
      MultiAffine.eval (p y) x =
        profile.paperIndicatorFreshZ center z
          (fun t ell => e.symm (x, y) (t, ell)) B := by
    calc
      MultiAffine.eval (p y) x =
          profile.paperIndicatorFreshZ center z
            (replacePaperFreshSelectedAtoms (baseAtoms y)
              (arbitrarySupportWord I J) x) B := by
        exact profile.eval_paperIndicatorFreshPolynomial_eq_freshZ_replaceSelected
          center z (baseAtoms y) B r I J x
      _ = profile.paperIndicatorFreshZ center z
            (fun t ell => e.symm (x, y) (t, ell)) B := by
        apply congrArg (fun atoms =>
          profile.paperIndicatorFreshZ center z atoms B)
        have hreconstruct :=
          splitFreshAtom_symm_eq_replacePaperFreshSelectedAtoms word x y
        simpa only [word, e, baseAtoms] using hreconstruct.symm
  let F : (Fin (d + 1) → ℂ) ×
      (UnselectedFreshIndex word → ℂ) → ℝ := fun xy =>
    logDeficit coefficient
      ‖profile.paperIndicatorFreshZ center z
        (fun t ell => e.symm xy (t, ell)) B‖
  have hradiusMeas : Measurable radius := by
    dsimp only [radius]
    exact measurable_norm_paperIndicatorFreshZ
      (d := d) (c₀ := c₀) (C₀ := C₀) profile center z
      (fun (ω : FreshAtomIndex (d + 1) → ℂ)
        (t : Fin (d + 1)) (ell : ResetLabel (d + 1)) => ω (t, ell))
      (fun (t : Fin (d + 1)) (ell : ResetLabel (d + 1)) =>
        measurable_pi_apply (t, ell)) B
  have hFmeas : Measurable F := by
    exact (measurable_logDeficit coefficient hradiusMeas).comp e.symm.measurable
  have hsectionEq (y : UnselectedFreshIndex word → ℂ) :
      (fun x => F (x, y)) =
        (fun x => positiveLogLoss ‖MultiAffine.topCoeff (p y)‖
          ‖MultiAffine.eval (p y) x‖) := by
    funext x
    rw [← logDeficit_eq_positiveLogLoss]
    dsimp only [F]
    rw [heval x y]
    rw [hcoeff_y y]
  have hnegative (y : UnselectedFreshIndex word → ℂ) :=
    iid_complex_positiveLogLoss_of_directionalDensity
      atom phase L hdir hL (p y) (htop_y y)
  have hsectionInt (y : UnselectedFreshIndex word → ℂ) :
      Integrable (fun x => F (x, y)) μx := by
    rw [hsectionEq y]
    simpa only [μx, ν, iidMeasure_eq_pi] using (hnegative y).2.1
  have hsectionBound (y : UnselectedFreshIndex word → ℂ) :
      ∫ x, F (x, y) ∂μx ≤ realFreshNegativeBound d L := by
    rw [hsectionEq y]
    simpa only [μx, ν, realFreshNegativeBound,
      iidMeasure_eq_pi, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      (hnegative y).2.2
  letI : IsProbabilityMeasure μx := by
    dsimp only [μx]
    infer_instance
  letI : IsProbabilityMeasure μy := by
    dsimp only [μy]
    infer_instance
  obtain ⟨hFint, hFbound⟩ :=
    integrable_prod_and_integral_le_of_forall_integrable_integral_le
      μx μy F hFmeas (fun xy => logDeficit_nonneg _ _)
      (realFreshNegativeBound d L)
      (realFreshNegativeBound_nonneg d L) hsectionInt hsectionBound
  have hmp : MeasurePreserving e μ (μx.prod μy) := by
    simpa only [e, μ, μx, μy, ν] using
      splitFreshAtom_measurePreserving word ν
  have hGint : Integrable (fun ω => logDeficit coefficient (radius ω)) μ := by
    have hcomp := (hmp.integrable_comp_emb e.measurableEmbedding).2 hFint
    simpa only [F, radius, Function.comp_def,
      MeasurableEquiv.symm_apply_apply] using hcomp
  have hGbound : ∫ ω, logDeficit coefficient (radius ω) ∂μ ≤
      realFreshNegativeBound d L := by
    calc
      (∫ ω, logDeficit coefficient (radius ω) ∂μ) =
          ∫ ω, F (e ω) ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        simp only [F, radius, MeasurableEquiv.symm_apply_apply]
      _ = ∫ xy, F xy ∂(μx.prod μy) := hmp.integral_comp' F
      _ ≤ realFreshNegativeBound d L := hFbound
  let ZF : Set ((Fin (d + 1) → ℂ) ×
      (UnselectedFreshIndex word → ℂ)) :=
    {xy | radius (e.symm xy) = 0}
  have hZFmeas : MeasurableSet ZF := by
    exact measurableSet_eq_fun
      (hradiusMeas.comp e.symm.measurable) measurable_const
  have hzeroSection (y : UnselectedFreshIndex word → ℂ) :
      μx {x | radius (e.symm (x, y)) = 0} = 0 := by
    have hset : {x | radius (e.symm (x, y)) = 0} =
        {x | ‖MultiAffine.eval (p y) x‖ = 0} := by
      ext x
      simp only [Set.mem_setOf_eq, radius]
      rw [heval x y]
    rw [hset]
    simpa only [μx, ν, iidMeasure_eq_pi] using (hnegative y).1
  have hzeroProd : (μx.prod μy) ZF = 0 := by
    rw [Measure.prod_apply_symm hZFmeas]
    have hsections : (fun y => μx ((fun x => (x, y)) ⁻¹' ZF)) =
        (fun _ => 0) := by
      funext y
      simpa only [ZF, Set.preimage_setOf_eq] using hzeroSection y
    rw [hsections]
    simp
  have hzero : μ {ω | radius ω = 0} = 0 := by
    have hpreimage : {ω | radius ω = 0} = e ⁻¹' ZF := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, ZF,
        MeasurableEquiv.symm_apply_apply]
    calc
      μ {ω | radius ω = 0} = μ (e ⁻¹' ZF) := congrArg μ hpreimage
      _ = Measure.map e μ ZF :=
        (Measure.map_apply e.measurable hZFmeas).symm
      _ = (μx.prod μy) ZF :=
        congrArg (fun m : Measure _ => m ZF) hmp.map_eq
      _ = 0 := hzeroProd
  exact ⟨hzero, hscale, hGint, hGbound⟩

/-- Directional negative-log closure transported to the literal flat IID
sample used by the paper's random matrix. -/
theorem exists_complex_paperIndicatorFlatFreshZ_logDeficit_withDirectionalDensity
    (N d : ℕ) [NeZero N] (hsize : d + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (center : Fin (d + 1)) (z : ℂ) (start : ZMod N)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < exteriorFamilyMaxL2OpNorm B)
    (atom : ProbabilityMeasure ℂ) (phase L : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) (hL : 0 ≤ L) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        let zeroAtoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ :=
          fun _ _ => 0
        let p₀ := profile.paperIndicatorFreshPolynomial
          center z zeroAtoms B r I J
        let coefficient := ‖MultiAffine.topCoeff p₀‖
        let radius := fun omega : Fin (N * (d + 2)) → ℂ =>
          ‖profile.paperIndicatorFreshZ center z
            (paperIndicatorFreshAtoms N d start omega) B‖
        let mu := paperIndicatorSampleMeasure N d (atom : Measure ℂ)
        mu {omega | radius omega = 0} = 0 ∧
          Real.log (exteriorFamilyMaxL2OpNorm B) - Real.log coefficient ≤
            paperIsolatedCoefficientLoss d c₀ ∧
          Integrable (fun omega => logDeficit coefficient (radius omega)) mu ∧
          ∫ omega, logDeficit coefficient (radius omega) ∂mu ≤
            realFreshNegativeBound d L := by
  classical
  let nu : Measure ℂ := atom
  obtain ⟨r, I, J, hzeroFull, hscale, hintFull, hboundFull⟩ :=
    profile.exists_complex_paperFreshAtomProduct_logDeficit_withDirectionalDensity
      hc₀ center z B hB atom phase L hdir hL
  refine ⟨r, I, J, ?_⟩
  let zeroAtoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ := fun _ _ => 0
  let p₀ := profile.paperIndicatorFreshPolynomial center z zeroAtoms B r I J
  let coefficient : ℝ := ‖MultiAffine.topCoeff p₀‖
  let radiusFull := fun omega : FreshAtomIndex (d + 1) → ℂ =>
    ‖profile.paperIndicatorFreshZ center z (fun t ell => omega (t, ell)) B‖
  let radiusFlat := fun omega : Fin (N * (d + 2)) → ℂ =>
    ‖profile.paperIndicatorFreshZ center z
      (paperIndicatorFreshAtoms N d start omega) B‖
  let muFull := Measure.pi (fun _ : FreshAtomIndex (d + 1) => nu)
  let muFlat := paperIndicatorSampleMeasure N d nu
  let T := fun omega : Fin (N * (d + 2)) → ℂ =>
    fun u => omega (paperIndicatorFreshCoordinateIndex N d start u)
  have hT : MeasurePreserving T muFlat muFull := by
    simpa only [T, muFlat, muFull, paperIndicatorSampleMeasure] using
      paperIndicatorFreshCoordinates_measurePreserving N d start hsize nu
  have hradiusFull : Measurable radiusFull := by
    dsimp only [radiusFull]
    exact measurable_norm_paperIndicatorFreshZ
      (d := d) (c₀ := c₀) (C₀ := C₀) profile center z
      (fun (omega : FreshAtomIndex (d + 1) → ℂ)
        (t : Fin (d + 1)) (ell : ResetLabel (d + 1)) => omega (t, ell))
      (fun (t : Fin (d + 1)) (ell : ResetLabel (d + 1)) =>
        measurable_pi_apply (t, ell)) B
  have hradiusEq : radiusFlat = radiusFull ∘ T := by
    funext omega
    dsimp only [radiusFlat, radiusFull, T, Function.comp_apply]
    rw [paperIndicatorFreshAtoms_eq_coordinateRestriction]
  obtain ⟨hzeroFlat, hintFlat, hboundFlat⟩ :=
    logDeficit_transport_of_measurePreserving T hT coefficient
      radiusFlat radiusFull hradiusFull hradiusEq
      (by simpa only [muFull, nu, radiusFull, coefficient, p₀, zeroAtoms]
        using hzeroFull)
      (by simpa only [muFull, nu, radiusFull, coefficient, p₀, zeroAtoms]
        using hintFull)
      (by simpa only [muFull, nu, radiusFull, coefficient, p₀, zeroAtoms]
        using hboundFull)
  exact ⟨hzeroFlat, hscale, hintFlat, hboundFlat⟩

/-- End-to-end two-sided `L¹` logarithmic closure for the genuine fresh
determinant under the manuscript's raw directional-density assumption.

The negative half uses conditional densities.  The positive half uses only
the unconditional second moment of the actual complex atom. -/
theorem complex_paperIndicatorFlatFreshZ_absLog_L1_withDirectionalDensity
    (N d : ℕ) [NeZero N] (hsize : d + 1 ≤ N)
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1)) (z : ℂ) (start : ZMod N)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < exteriorFamilyMaxL2OpNorm B)
    (atom : ProbabilityMeasure ℂ) (phase L : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) (hL : 0 ≤ L)
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (atom : Measure ℂ))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(atom : Measure ℂ) ≤ 1) :
    let radius := fun omega : Fin (N * (d + 2)) → ℂ =>
      ‖profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtoms N d start omega) B‖
    let scale := exteriorFamilyMaxL2OpNorm B
    let mu := paperIndicatorSampleMeasure N d (atom : Measure ℂ)
    mu {omega | radius omega = 0} = 0 ∧
      Integrable (fun omega =>
        |Real.log (radius omega) - Real.log scale|) mu ∧
      ∫ omega, |Real.log (radius omega) - Real.log scale| ∂mu ≤
        paperIsolatedCoefficientLoss d c₀ +
          realFreshNegativeBound d L + paperFreshPositiveBound d z := by
  classical
  obtain ⟨r, I, J, hzero, hscale, hnegativeInt, hnegative⟩ :=
    profile.exists_complex_paperIndicatorFlatFreshZ_logDeficit_withDirectionalDensity
      N d hsize hc₀ center z start B hB atom phase L hdir hL
  let zeroAtoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ := fun _ _ => 0
  let p₀ := profile.paperIndicatorFreshPolynomial center z zeroAtoms B r I J
  let coefficient : ℝ := ‖MultiAffine.topCoeff p₀‖
  let radius := fun omega : Fin (N * (d + 2)) → ℂ =>
    ‖profile.paperIndicatorFreshZ center z
      (paperIndicatorFreshAtoms N d start omega) B‖
  let scale := exteriorFamilyMaxL2OpNorm B
  let mu := paperIndicatorSampleMeasure N d (atom : Measure ℂ)
  have hradius : Measurable radius := by
    dsimp only [radius]
    exact measurable_norm_paperIndicatorFreshZ
      (d := d) (c₀ := c₀) (C₀ := C₀) profile center z
      (fun omega => paperIndicatorFreshAtoms N d start omega)
      (fun t ell => measurable_paperIndicatorFreshAtoms N d start t ell) B
  have hradiusPos : ∀ᵐ omega ∂mu, 0 < radius omega := by
    have hnotMem := measure_eq_zero_iff_ae_notMem.mp
      (by simpa only [mu, radius] using hzero)
    filter_upwards [hnotMem] with omega homega
    have hne : radius omega ≠ 0 := by
      simpa only [Set.mem_ofPred_eq] using homega
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  obtain ⟨hpositiveInt, hpositive⟩ :=
    complex_paperIndicatorFlatFreshZ_logExcess_le
      N d profile hc₀ center z start B hB (atom : Measure ℂ)
      hsecondInt hsecond
      (by simpa only [mu, radius] using hradiusPos)
  letI : IsProbabilityMeasure mu := by
    simpa only [mu, paperIndicatorSampleMeasure] using
      iidMeasure_isProbability (atom : Measure ℂ) (N * (d + 2))
  have hclosure := freshClosure_L1_of_isolatedCoefficient
    mu coefficient scale (paperIsolatedCoefficientLoss d c₀)
    hradius (paperIsolatedCoefficientLoss_nonneg hc₀ hsqrt)
    (by simpa only [scale, coefficient, p₀, zeroAtoms] using hscale)
    (by simpa only [mu, radius, coefficient, p₀, zeroAtoms] using hnegativeInt)
    (by simpa only [mu, radius, scale] using hpositiveInt)
    (by simpa only [mu, radius, coefficient, p₀, zeroAtoms] using hnegative)
    (by simpa only [mu, radius, scale, paperFreshPositiveBound] using hpositive)
  exact ⟨by simpa only [mu, radius] using hzero,
    by simpa only [mu, radius, scale] using hclosure.1,
    by simpa only [mu, radius, scale, paperFreshPositiveBound,
      Nat.cast_add, Nat.cast_one] using hclosure.2⟩

end PaperIndicatorWeights

end CircularLawSection4
