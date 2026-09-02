import BernoulliSection8.RademacherBoundarySmallBall
import BernoulliSection10.PhysicalPacketReset
import Mathlib.Topology.Algebra.MvPolynomial

/-! # The normalized physical exterior coefficient for Bernoulli packets

The artificial-boundary parameter is sent to infinity using the existing
coefficientwise and pointwise frame limits. Capped logarithms stay bounded
at zero; no finite-dimensional almost-sure invertibility is invoked.
The endpoint and outside-frame data remain fixed during the fresh-packet
integration, exactly as required for the conditional reset argument.
-/

open Filter MeasureTheory Topology
open scoped Matrix

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10 BernoulliLinearAlgebra

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Row normalization commutes with the fixed exterior-degree limit.
Every degree has the same `sigma⁻¹^(3W)` factor. -/
theorem packetFramePolynomial_eval_rowScaling
    (W r : ℕ) (sigma : ℂ) (hsigma : sigma ≠ 0) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r)
    (x : ThreeBlockVariable (Fin W) → ℂ) :
    MvPolynomial.eval (fun e => sigma⁻¹ * x e)
      (packetScalarMatrixCoefficientPolynomial r z CL BR U V s) =
      sigma⁻¹ ^ (3 * W) * MvPolynomial.eval x
        (packetScalarMatrixCoefficientPolynomial r (sigma * z)
          (sigma • CL) (sigma • BR) U V s) := by
  let a := sigma⁻¹ ^ (3 * W)
  have hboundary (q : ℕ) :
      MvPolynomial.eval (fun e => sigma⁻¹ * x e)
        (packetBoundaryPolynomial z CL BR (packetFrameTheta U V s q)) =
      a * MvPolynomial.eval x
        (packetBoundaryPolynomial (sigma * z) (sigma • CL) (sigma • BR)
          (packetFrameTheta U V s q)) := by
    rw [← eval_normalizedPacketBoundaryPolynomial,
      normalizedPacketBoundaryPolynomial_eq_scaled sigma hsigma,
      MvPolynomial.eval_mul, MvPolynomial.eval_C]
    simp only [Fintype.card_fin, a]
  have hphysical := tendsto_packetBoundaryPolynomial_frame_eval W r z CL BR U V s
    (fun e => sigma⁻¹ * x e)
  have hraw := (tendsto_packetBoundaryPolynomial_frame_eval W r (sigma * z)
    (sigma • CL) (sigma • BR) U V s x).const_mul a
  have hphysical' : Tendsto
      (fun q => a * (packetFrameComplexNormalization r q * MvPolynomial.eval x
        (packetBoundaryPolynomial (sigma * z) (sigma • CL) (sigma • BR)
          (packetFrameTheta U V s q)))) atTop
      (𝓝 ((-1 : ℂ) ^ r * MvPolynomial.eval (fun e => sigma⁻¹ * x e)
        (packetScalarMatrixCoefficientPolynomial r z CL BR U V s))) := by
    apply hphysical.congr'
    apply Filter.Eventually.of_forall
    intro q
    change packetFrameComplexNormalization r q *
        MvPolynomial.eval (fun e => sigma⁻¹ * x e)
          (packetBoundaryPolynomial z CL BR (packetFrameTheta U V s q)) =
      a * (packetFrameComplexNormalization r q * MvPolynomial.eval x
        (packetBoundaryPolynomial (sigma * z) (sigma • CL) (sigma • BR)
          (packetFrameTheta U V s q)))
    rw [hboundary q]
    ring
  have he := tendsto_nhds_unique hphysical' hraw
  have hsign : (-1 : ℂ) ^ r ≠ 0 := pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ hsign
  calc
    (-1 : ℂ) ^ r * _ = a * ((-1 : ℂ) ^ r * _) := he
    _ = (-1 : ℂ) ^ r * (sigma⁻¹ ^ (3 * W) * _) := by dsimp [a]; ring

/-- The coefficient norm in the variance-one fresh atom variables. Its
identification as the normalized boundary coefficient limit is proved below. -/
def rademacherPacketFrameCoefficient (W r : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) : ℝ :=
  ‖(packetRowScale W)⁻¹ ^ (3 * W)‖ *
    packetScalarMatrixCoefficientNorm r (packetRowScale W * z)
      ((packetRowScale W) • CL) ((packetRowScale W) • BR) U V s

theorem packetScalarCoefficientEval_eq_scaled_raw
    (W r : ℕ) (hW : 0 < W) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) (x : PacketAtomRows W) :
    packetScalarCoefficientEval W r z CL BR U V s x =
      (packetRowScale W)⁻¹ ^ (3 * W) *
        MvPolynomial.eval (fun e => ((rademacherPacketFamily W).atom e x : ℂ))
          (packetScalarMatrixCoefficientPolynomial r (packetRowScale W * z)
            ((packetRowScale W) • CL) ((packetRowScale W) • BR) U V s) := by
  have he : packetAtomAssignment W x =
      fun e => (packetRowScale W)⁻¹ * ((rademacherPacketFamily W).atom e x : ℂ) := by
    funext e
    simp [packetAtomAssignment, rademacherPacketFamily_atom, rawPacketAssignment,
      Complex.ofReal_mul, blockNormalization_eq_packetRowScale_inv]
  rw [packetScalarCoefficientEval, he]
  exact packetFramePolynomial_eval_rowScaling W r _ (packetRowScale_ne_zero W hW)
    z CL BR U V s _

private theorem eval_packetFramePolynomial_eq_evalSquarefree
    (W r : ℕ) (z : ℂ) (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) (x : PacketAtomRows W) :
    MvPolynomial.eval (fun e => ((rademacherPacketFamily W).atom e x : ℂ))
        (packetScalarMatrixCoefficientPolynomial r z CL BR U V s) =
      evalSquarefree (fun S => packetScalarMatrixCoefficientCoeffVector r z CL BR U V s S)
        (rademacherPacketFamily W).atom x := by
  classical
  have hP : HasSquarefreeSupport (packetScalarMatrixCoefficientPolynomial r z CL BR U V s) :=
    hasSquarefreeSupport_classical_to_infer
      (hasSquarefreeSupport_packetScalarMatrixCoefficientPolynomial r z CL BR U V s)
  have he : squarefreePolynomial (packetScalarMatrixCoefficientCoeffVector r z CL BR U V s) =
      packetScalarMatrixCoefficientPolynomial r z CL BR U V s :=
    squarefreePolynomial_coefficients_eq _ hP
  rw [← he]
  simpa [evalSquarefree, squarefreeMonomial] using
    eval_squarefreePolynomial_eq_evalSquarefree
      (packetScalarMatrixCoefficientCoeffVector r z CL BR U V s)
      (fun e => (rademacherPacketFamily W).atom e x)

/-- The coefficient norm is the actual fresh-packet `L²` norm. This
identity holds before imposing any endpoint good event or Cook estimate. -/
theorem rademacherPacketFrameCoefficient_parseval
    (W r : ℕ) (hW : 0 < W) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) :
    rademacherPacketFrameCoefficient W r z CL BR U V s ^ 2 =
      ∫ x, ‖packetScalarCoefficientEval W r z CL BR U V s x‖ ^ 2
        ∂packetAtomRowsLaw W rademacherLaw := by
  have hp := integral_norm_evalSquarefree_sq_eq_coeffNorm (rademacherPacketFamily W)
    (packetScalarMatrixCoefficientCoeffVector r (packetRowScale W * z)
      ((packetRowScale W) • CL) ((packetRowScale W) • BR) U V s)
  simp_rw [packetScalarCoefficientEval_eq_scaled_raw W r hW z CL BR U V s,
    norm_mul, mul_pow, eval_packetFramePolynomial_eq_evalSquarefree]
  rw [integral_const_mul, hp]
  simp only [rademacherPacketFrameCoefficient, packetScalarMatrixCoefficientNorm, mul_pow]

theorem tendsto_rademacherPacketBoundaryCoefficient_frame
    (W r : ℕ) (hW : 0 < W) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) :
    Tendsto (fun q => ‖packetFrameComplexNormalization r q‖ *
        rademacherPacketBoundaryCoefficient W z CL BR (packetFrameTheta U V s q))
      atTop (𝓝 (rademacherPacketFrameCoefficient W r z CL BR U V s)) := by
  have h := (tendsto_packetBoundaryCoefficientNorm_frame r (packetRowScale W * z)
    ((packetRowScale W) • CL) ((packetRowScale W) • BR) U V s).const_mul
      ‖(packetRowScale W)⁻¹ ^ (3 * W)‖
  simp only [rademacherPacketBoundaryCoefficient,
    normalizedPacketBoundaryCoefficient_eq_scaled _ (packetRowScale_ne_zero W hW),
    Fintype.card_fin, norm_packetFrameComplexNormalization]
  convert h using 1
  · funext q
    ring
  · rfl

theorem rademacherPacketFrameCoefficient_lower_and_pos
    (W r : ℕ) (hW : 0 < W) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ) (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) :
    rademacherBoundaryInverseGamma W z CL BR ≤
        rademacherPacketFrameCoefficient W r z CL BR U V s ∧
      0 < rademacherPacketFrameCoefficient W r z CL BR U V s := by
  have hsigma := packetRowScale_ne_zero W hW
  have h := packetScalarMatrixCoefficientNorm_bounds_and_pos r (packetRowScale W * z)
    ((packetRowScale W) • CL) ((packetRowScale W) • BR)
    (isUnit_det_smul _ hsigma CL hCL) (isUnit_det_smul _ hsigma BR hBR) U V s
  exact ⟨mul_le_mul_of_nonneg_left h.1 (norm_nonneg _),
    mul_pos (norm_pos_iff.mpr (pow_ne_zero _ (inv_ne_zero hsigma))) h.2.2⟩

theorem measurable_packetBoundaryEval (W : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) :
    Measurable (packetBoundaryEval W z CL BR Theta) := by
  unfold packetBoundaryEval
  exact (MvPolynomial.continuous_eval _).measurable.comp (by
    unfold packetAtomAssignment
    fun_prop)

theorem measurable_packetScalarCoefficientEval (W r : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) :
    Measurable (packetScalarCoefficientEval W r z CL BR U V s) := by
  unfold packetScalarCoefficientEval
  exact (MvPolynomial.continuous_eval _).measurable.comp (by
    unfold packetAtomAssignment
    fun_prop)

/-- The actual normalized frame evaluation has the same capped-loss and
zero-probability bounds as its boundary approximants. -/
theorem rademacherPacketFrame_capped_and_zero
    (cook : CookDeformedSquareInput.{0, 0}) (W r : ℕ) (z : ℂ)
    (hW : rademacherBoundaryWidthThreshold cook z ≤ W)
    (CL BR : Matrix (Fin W) (Fin W) ℂ) (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r) :
    (∀ T : ℝ, 0 < T →
      ∫ x, cappedLogLoss T (rademacherPacketFrameCoefficient W r z CL BR U V s)
        (packetScalarCoefficientEval W r z CL BR U V s x)
        ∂packetAtomRowsLaw W rademacherLaw ≤
          rademacherBoundaryBaseLoss cook W z + rademacherBoundaryBadProbability cook W * T) ∧
    (packetAtomRowsLaw W rademacherLaw).real
      {x | packetScalarCoefficientEval W r z CL BR U V s x = 0} ≤
        rademacherBoundaryBadProbability cook W := by
  have hW0 : 0 < W := by
    have h1 : 1 ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
    omega
  let c := rademacherPacketFrameCoefficient W r z CL BR U V s
  let value := packetScalarCoefficientEval W r z CL BR U V s
  have hc : 0 < c := (rademacherPacketFrameCoefficient_lower_and_pos
    W r hW0 z CL BR hCL hBR U V s).2
  have hsign : (-1 : ℂ) ^ r ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcapSign (T : ℝ) (v : ℂ) : cappedLogLoss T c ((-1 : ℂ) ^ r * v) =
      cappedLogLoss T c v := by
    simpa using cappedLogLoss_common_scale T c v ((-1 : ℂ) ^ r) hsign
  have hterminal (q : ℕ) :=
    (rademacherBoundarySmallBall cook W z hW CL BR hCL hBR
      (packetFrameTheta U V s q) (packetFrameTheta_det_isUnit U V s q)).commonScale
      (packetFrameComplexNormalization r q)
      (by simp [packetFrameComplexNormalization])
  have hcapped : ∀ T : ℝ, 0 < T →
      ∫ x, cappedLogLoss T c (value x) ∂packetAtomRowsLaw W rademacherLaw ≤
        rademacherBoundaryBaseLoss cook W z + rademacherBoundaryBadProbability cook W * T := by
    intro T hT
    have hlimit := cappedIntegral_limit_le_of_uniform_bound
      (packetAtomRowsLaw W rademacherLaw) T hT.le
      (tendsto_rademacherPacketBoundaryCoefficient_frame W r hW0 z CL BR U V s) hc
      (fun q => (hterminal q).coefficientNorm_pos)
      (fun q => ((measurable_const.mul (measurable_packetBoundaryEval W z CL BR
        (packetFrameTheta U V s q))).aestronglyMeasurable))
      (Filter.Eventually.of_forall (fun x =>
        tendsto_packetBoundaryPolynomial_frame_eval W r z CL BR U V s
          (packetAtomAssignment W x)))
      (rademacherBoundaryBaseLoss cook W z + rademacherBoundaryBadProbability cook W * T)
      (fun q => (hterminal q).capped T hT)
    change ∫ x, cappedLogLoss T c ((-1 : ℂ) ^ r * value x)
      ∂packetAtomRowsLaw W rademacherLaw ≤ _ at hlimit
    simpa only [hcapSign] using hlimit
  refine ⟨hcapped, ?_⟩
  apply zeroProbability_of_all_capped_bounds
    (TerminalAssembly.terminalUniformBaseLoss_nonneg cook 1 _ _ _)
  intro T hT
  exact (cap_mul_zeroProbability_le_integral (packetAtomRowsLaw W rademacherLaw)
    T c hT.le hc value (measurable_packetScalarCoefficientEval W r z CL BR U V s)).trans
      (hcapped T hT)

/-- Caller form on the displayed physical three-site matrix. The fixed
endpoints are part of the nine-block physical packet, and the seven fresh
blocks are integrated with their exact Bernoulli product law. -/
theorem rademacherPhysicalPacketCoefficient_parseval
    (W : ℕ) (hW : 0 < W) (z : ℂ) (ep : EndpointBlockPair W)
    (r : Fin (2 * W + 1))
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r.1) :
    rademacherPacketFrameCoefficient W r.1 z
      (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2) U V s ^ 2 =
      ∫ x, ‖physicalPacketCoefficient W z r U V s (packetPhysicalRows W (ep, x))‖ ^ 2
        ∂packetAtomRowsLaw W rademacherLaw := by
  simpa only [packetScalarCoefficientEval_eq_physical, physicalPacketCoefficient] using
    rademacherPacketFrameCoefficient_parseval W r.1 hW z
      (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2) U V s

theorem rademacherPhysicalPacketCoefficient_capped
    (cook : CookDeformedSquareInput.{0, 0}) (W : ℕ) (z : ℂ)
    (hW : rademacherBoundaryWidthThreshold cook z ≤ W)
    (ep : EndpointBlockPair W)
    (hCL : IsUnit (normalizedBlockMatrix W ep.1).det)
    (hBR : IsUnit (normalizedBlockMatrix W ep.2).det)
    (r : Fin (2 * W + 1))
    (U V : Matrix.unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : Set.powersetCard (Fin W ⊕ Fin W) r.1)
    (T : ℝ) (hT : 0 < T) :
    ∫ x, cappedLogLoss T
      (rademacherPacketFrameCoefficient W r.1 z
        (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2) U V s)
      (physicalPacketCoefficient W z r U V s (packetPhysicalRows W (ep, x)))
      ∂packetAtomRowsLaw W rademacherLaw ≤
        rademacherBoundaryBaseLoss cook W z + rademacherBoundaryBadProbability cook W * T := by
  have h := (rademacherPacketFrame_capped_and_zero cook W r.1 z hW
    (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2) hCL hBR U V s).1 T hT
  simpa only [packetScalarCoefficientEval_eq_physical, physicalPacketCoefficient] using h

end BernoulliSection8
