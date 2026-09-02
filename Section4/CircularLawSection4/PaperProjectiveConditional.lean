import CircularLawSection4.PaperProjectiveObservability
import CircularLawSection4.PaperIndicatorFreshComplex
import CircularLawSection4.PaperIndicatorFreshReal
import CircularLawSection4.MultiaffineDirectional
import CircularLawSection4.DirectionalKernelConstruction
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Tactic.FunProp

/-!
# Analytic and conditional projective observability

This module supplies the probabilistic half of projective observability.
The selected scalar variables are reinserted into the genuine fresh rows,
so the multiaffine polynomial is literally one coordinate of `B Q v`.
The scalar negative-log estimate is then lifted to the Euclidean norm of
`B Q v`.  The final generic lemmas are stated for kernels and therefore
also apply pointwise when `B` and `v` are measurable functions of the past.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory Set

noncomputable section

namespace CircularLawSection4

open Matrix Set.powersetCard

/-- Replace exactly the atom selected by `word` in every fresh row. -/
def replaceSelectedFreshAtoms {k : ℕ}
    (atoms : Fin k → ResetLabel k → ℂ)
    (word : Fin k → ResetLabel k) (x : Fin k → ℂ) :
    Fin k → ResetLabel k → ℂ :=
  fun t ell => if ell = word t then x t else atoms t ell

@[simp] theorem replaceSelectedFreshAtoms_selected {k : ℕ}
    (atoms : Fin k → ResetLabel k → ℂ)
    (word : Fin k → ResetLabel k) (x : Fin k → ℂ) (t : Fin k) :
    replaceSelectedFreshAtoms atoms word x t (word t) = x t := by
  simp [replaceSelectedFreshAtoms]

theorem replaceSelectedFreshAtoms_unselected {k : ℕ}
    (atoms : Fin k → ResetLabel k → ℂ)
    (word : Fin k → ResetLabel k) (x : Fin k → ℂ)
    (t : Fin k) {ell : ResetLabel k} (hell : ell ≠ word t) :
    replaceSelectedFreshAtoms atoms word x t ell = atoms t ell := by
  simp [replaceSelectedFreshAtoms, hell]

namespace PaperIndicatorWeights

variable {d : ℕ} {c₀ C₀ : ℝ}

/-- Replacing selected atoms does not change the frozen part of a fresh
row. -/
theorem paperIndicatorFreshBase_replaceSelectedFreshAtoms
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (word : Fin (d + 1) → ResetLabel (d + 1))
    (x : Fin (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1)) (t : Fin (d + 1)) :
    profile.paperIndicatorFreshBase center z
        (replaceSelectedFreshAtoms atoms word x) word q t =
      profile.paperIndicatorFreshBase center z atoms word q t := by
  classical
  unfold paperIndicatorFreshBase
  congr 1
  apply Finset.sum_congr rfl
  intro ell hell
  have hne : ell ≠ word t := (Finset.mem_erase.1 hell).1
  rw [replaceSelectedFreshAtoms_unselected atoms word x t hne]

/-- The genuine Euclidean vector `B Q v` after inserting the selected
fresh coordinates `x`. -/
def paperProjectiveFreshVector
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (I J : ExteriorIndex (d + 1) q) (x : Fin (d + 1) → ℂ) :
    EuclideanSpace ℂ (ExteriorIndex (d + 1) q) :=
  (EuclideanSpace.equiv (ExteriorIndex (d + 1) q) ℂ).symm
    ((B * chronologicalProduct
      (List.ofFn fun t => profile.freshExteriorRow center z
        (replaceSelectedFreshAtoms atoms (arbitrarySupportWord I J) x) q t)).mulVec
          (fun j => v j))

set_option maxHeartbeats 800000 in
/-- Evaluation at arbitrary selected coordinates is exactly a signed
coordinate of the actual vector `B Q v`. -/
theorem eval_paperProjectiveFreshPolynomial_eq_coordinate
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (o I J : ExteriorIndex (d + 1) q)
    (x : Fin (d + 1) → ℂ) :
    MultiAffine.eval
        (profile.paperProjectiveFreshPolynomial center z atoms q B v o I J) x =
      (-1 : ℂ) ^ q.val *
        profile.paperProjectiveFreshVector center z atoms q B v I J x o := by
  classical
  rw [paperProjectiveFreshVector]
  change MultiAffine.eval
      (profile.paperProjectiveFreshPolynomial center z atoms q B v o I J) x =
    (-1 : ℂ) ^ q.val *
      ((B * chronologicalProduct
        (List.ofFn fun t => profile.freshExteriorRow center z
          (replaceSelectedFreshAtoms atoms (arbitrarySupportWord I J) x) q t)).mulVec
          (fun j => v j)) o
  rw [paperProjectiveFreshPolynomial, paperIndicatorFreshPolynomial,
    orderedFreshPolynomial, eval_weightedAlternatingFreshPolynomial]
  rw [Finset.sum_eq_single q]
  · rw [singleExteriorFamily_same, trace_projectiveTestingMatrix_mul]
    congr 2
    congr 1
    apply congrArg chronologicalProduct
    apply List.ofFn_inj.2
    funext t
    have hrow := profile.paperIndicatorFreshBase_add_selected center z
      (replaceSelectedFreshAtoms atoms (arbitrarySupportWord I J) x)
      (arbitrarySupportWord I J) q t
    rw [profile.paperIndicatorFreshBase_replaceSelectedFreshAtoms
      center z atoms (arbitrarySupportWord I J) x] at hrow
    simpa only [replaceSelectedFreshAtoms_selected] using hrow
  · intro q' _ hq'
    rw [singleExteriorFamily_eq_zero q q' hq']
    simp
  · intro hq
    exact False.elim (hq (Finset.mem_univ q))

/-- The selected scalar polynomial is dominated pointwise by the actual
Euclidean projective norm. -/
theorem norm_eval_paperProjectiveFreshPolynomial_replaced_le
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (o I J : ExteriorIndex (d + 1) q)
    (x : Fin (d + 1) → ℂ) :
    ‖MultiAffine.eval
        (profile.paperProjectiveFreshPolynomial center z atoms q B v o I J) x‖ ≤
      ‖profile.paperProjectiveFreshVector center z atoms q B v I J x‖ := by
  rw [profile.eval_paperProjectiveFreshPolynomial_eq_coordinate]
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact PiLp.norm_apply_le _ o

/-- The actual projective vector is a continuous function of the selected
complex fresh coordinates. -/
theorem continuous_paperProjectiveFreshVector
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (I J : ExteriorIndex (d + 1) q) :
    Continuous (fun x : Fin (d + 1) → ℂ =>
      profile.paperProjectiveFreshVector center z atoms q B v I J x) := by
  apply (EuclideanSpace.equiv (ExteriorIndex (d + 1) q) ℂ).symm.continuous.comp
  apply continuous_pi
  intro o
  let s : ℂ := (-1 : ℂ) ^ q.val
  have hs : s ≠ 0 := pow_ne_zero _ (by norm_num)
  let p : MultiAffine ℂ (d + 1) :=
    profile.paperProjectiveFreshPolynomial center z atoms q B v o I J
  have hp : Continuous (fun x : Fin (d + 1) → ℂ => p.eval x / s) :=
    p.continuous_eval_complex.div_const s
  apply hp.congr
  intro x
  change p.eval x / s =
    profile.paperProjectiveFreshVector center z atoms q B v I J x o
  apply (div_eq_iff hs).2
  have heval := profile.eval_paperProjectiveFreshPolynomial_eq_coordinate
    center z atoms q B v o I J x
  change p.eval x = s *
    profile.paperProjectiveFreshVector center z atoms q B v I J x o at heval
  simpa only [mul_comm] using heval

/-- Explicit deterministic loss in passing from the selected full
coefficient back to the operator scale `‖B‖`. -/
noncomputable def paperProjectiveCoefficientLogLoss
    (d : ℕ) (c₀ : ℝ) (q : ExteriorDegree (d + 1)) : ℝ :=
  max 0
    (-((d + 1 : ℕ) : ℝ) * Real.log (Real.sqrt (c₀ / (d + 2 : ℝ))) +
      3 * Real.log (Fintype.card (ExteriorIndex (d + 1) q) : ℝ))

theorem paperProjectiveCoefficientLogLoss_nonneg
    (d : ℕ) (c₀ : ℝ) (q : ExteriorDegree (d + 1)) :
    0 ≤ paperProjectiveCoefficientLogLoss d c₀ q := by
  exact le_max_left _ _

/-- The quantitative coefficient selector gives the advertised logarithmic
scale comparison. -/
theorem log_norm_sub_log_topCoeff_le_paperProjectiveCoefficientLogLoss
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < ‖B‖)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (o I J : ExteriorIndex (d + 1) q)
    (hcoefficient :
      (Real.sqrt (c₀ / (d + 2 : ℝ))) ^ (d + 1) *
          (‖B‖ / (Fintype.card (ExteriorIndex (d + 1) q) : ℝ) ^ 3) ≤
        ‖MultiAffine.topCoeff
          (profile.paperProjectiveFreshPolynomial center z atoms q B v o I J)‖) :
    Real.log ‖B‖ -
        Real.log ‖MultiAffine.topCoeff
          (profile.paperProjectiveFreshPolynomial center z atoms q B v o I J)‖ ≤
      paperProjectiveCoefficientLogLoss d c₀ q := by
  letI : Nonempty (ExteriorIndex (d + 1) q) :=
    exteriorIndex_nonempty (d + 1) q
  let bmin : ℝ := Real.sqrt (c₀ / (d + 2 : ℝ))
  let card : ℝ := Fintype.card (ExteriorIndex (d + 1) q)
  have hbmin : 0 < bmin := by
    dsimp [bmin]
    exact Real.sqrt_pos.2 (div_pos hc₀ (by positivity))
  have hcard : 0 < card := by
    dsimp [card]
    exact_mod_cast Fintype.card_pos
  have hlower : 0 < bmin ^ (d + 1) * (‖B‖ / card ^ 3) :=
    mul_pos (pow_pos hbmin _) (div_pos hB (pow_pos hcard _))
  have hlog := Real.log_le_log hlower hcoefficient
  have hbmin_ne : bmin ≠ 0 := hbmin.ne'
  have hcard_ne : card ≠ 0 := hcard.ne'
  rw [Real.log_mul (pow_ne_zero _ hbmin_ne)
      (div_ne_zero hB.ne' (pow_ne_zero _ hcard_ne)),
    Real.log_pow, Real.log_div hB.ne' (pow_ne_zero _ hcard_ne),
    Real.log_pow] at hlog
  unfold paperProjectiveCoefficientLogLoss
  apply le_trans ?_ (le_max_right _ _)
  dsimp [bmin, card] at hlog ⊢
  linarith

/-- Actual projective vector for real selected coordinates. -/
def paperProjectiveFreshVectorOfReal
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (I J : ExteriorIndex (d + 1) q) (x : Fin (d + 1) → ℝ) :
    EuclideanSpace ℂ (ExteriorIndex (d + 1) q) :=
  profile.paperProjectiveFreshVector center z atoms q B v I J
    (fun t => (x t : ℂ))

theorem norm_realInputEval_paperProjectiveFreshPolynomial_le
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (o I J : ExteriorIndex (d + 1) q)
    (x : Fin (d + 1) → ℝ) :
    ‖realInputEval
        (profile.paperProjectiveFreshPolynomial center z atoms q B v o I J) x‖ ≤
      ‖profile.paperProjectiveFreshVectorOfReal center z atoms q B v I J x‖ := by
  exact profile.norm_eval_paperProjectiveFreshPolynomial_replaced_le
    center z atoms q B v o I J (fun t => (x t : ℂ))

theorem continuous_paperProjectiveFreshVectorOfReal
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (I J : ExteriorIndex (d + 1) q) :
    Continuous (fun x : Fin (d + 1) → ℝ =>
      profile.paperProjectiveFreshVectorOfReal center z atoms q B v I J x) := by
  apply (profile.continuous_paperProjectiveFreshVector
    center z atoms q B v I J).comp
  fun_prop

end PaperIndicatorWeights

/-! ## Generic analytic lifting from one coordinate to the full norm -/

/-- Away from a null zero set, a larger radius has no larger logarithmic
deficit.  This formulation accounts for Lean's totalized value `log 0 = 0`.
-/
theorem logDeficit_le_of_coordinate_ae
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {scalar radius : Omega → ℝ} {scale : ℝ}
    (hscalar0 : ∀ x, 0 ≤ scalar x) (hradius0 : ∀ x, 0 ≤ radius x)
    (hzero : mu {x | scalar x = 0} = 0)
    (hle : ∀ x, scalar x ≤ radius x) :
    (fun x => logDeficit scale (radius x)) ≤ᵐ[mu]
      (fun x => logDeficit scale (scalar x)) := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with x hx
  have hsne : scalar x ≠ 0 := by simpa only [Set.mem_setOf_eq] using hx
  have hs : 0 < scalar x := lt_of_le_of_ne (hscalar0 x) (Ne.symm hsne)
  have hr : 0 < radius x := hs.trans_le (hle x)
  unfold logDeficit
  exact max_le_max le_rfl
    (sub_le_sub_left (Real.log_le_log hs (hle x)) (Real.log scale))

/-- An integrable selected-coordinate deficit controls the deficit of the
full projective radius, including a deterministic change-of-scale loss. -/
theorem integrable_logDeficit_of_coordinate
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    {scalar radius : Omega → ℝ} (hscalar : Measurable scalar)
    (hradius : Measurable radius)
    (hscalar0 : ∀ x, 0 ≤ scalar x) (hradius0 : ∀ x, 0 ≤ radius x)
    (hzero : mu {x | scalar x = 0} = 0)
    (hle : ∀ x, scalar x ≤ radius x)
    {coefficient scale loss : ℝ} (hloss : 0 ≤ loss)
    (hscale : Real.log scale - Real.log coefficient ≤ loss)
    (hcoordinate : Integrable
      (fun x => logDeficit coefficient (scalar x)) mu) :
    Integrable (fun x => logDeficit scale (radius x)) mu ∧
      ∫ x, logDeficit scale (radius x) ∂mu ≤
        loss + ∫ x, logDeficit coefficient (scalar x) ∂mu := by
  let coordinateDeficit := fun x => logDeficit coefficient (scalar x)
  let fullDeficit := fun x => logDeficit scale (radius x)
  let majorant := fun x => loss + coordinateDeficit x
  have hcoordFull :
      (fun x => logDeficit scale (radius x)) ≤ᵐ[mu]
        (fun x => logDeficit scale (scalar x)) :=
    logDeficit_le_of_coordinate_ae mu hscalar0 hradius0 hzero hle
  have hpoint : (fun x => logDeficit scale (scalar x)) ≤ᵐ[mu]
      majorant := by
    filter_upwards with x
    exact logDeficit_le_scaleLoss_add hloss hscale
  have hfullMajorant : fullDeficit ≤ᵐ[mu] majorant := hcoordFull.trans hpoint
  have hmajorant : Integrable majorant mu :=
    (integrable_const loss).add hcoordinate
  have hfull : Integrable fullDeficit mu := by
    apply hmajorant.mono' (measurable_logDeficit scale hradius).aestronglyMeasurable
    filter_upwards [hfullMajorant] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (logDeficit_nonneg scale (radius x))]
    exact hx
  refine ⟨hfull, ?_⟩
  calc
    (∫ x, fullDeficit x ∂mu) ≤ ∫ x, majorant x ∂mu :=
      integral_mono_ae hfull hmajorant hfullMajorant
    _ = loss + ∫ x, coordinateDeficit x ∂mu := by
      rw [integral_add (integrable_const loss) hcoordinate]
      simp [coordinateDeficit]

/-- Once the positive logarithmic excess is integrable, the negative-half
bound becomes a genuine lower bound for the expectation of `log radius`. -/
theorem integrable_log_and_integral_log_ge_of_logDeficit
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    {radius : Omega → ℝ} (scale bound : ℝ)
    (hdeficit : Integrable (fun x => logDeficit scale (radius x)) mu)
    (hexcess : Integrable (fun x => logExcess scale (radius x)) mu)
    (hbound : ∫ x, logDeficit scale (radius x) ∂mu ≤ bound) :
    Integrable (fun x => Real.log (radius x)) mu ∧
      Real.log scale - bound ≤ ∫ x, Real.log (radius x) ∂mu := by
  let D := fun x => logDeficit scale (radius x)
  let E := fun x => logExcess scale (radius x)
  have hidentity : (fun x => Real.log (radius x)) =
      (fun x => Real.log scale + E x - D x) := by
    funext x
    by_cases h : Real.log scale ≤ Real.log (radius x)
    · simp only [D, E, logDeficit, logExcess,
        max_eq_left (sub_nonpos.mpr h),
        max_eq_right (sub_nonneg.mpr h)]
      ring
    · have h' : Real.log (radius x) ≤ Real.log scale := le_of_not_ge h
      simp only [D, E, logDeficit, logExcess,
        max_eq_right (sub_nonneg.mpr h'),
        max_eq_left (sub_nonpos.mpr h')]
      ring
  have hint : Integrable (fun x => Real.log scale + E x - D x) mu :=
    ((integrable_const (Real.log scale)).add hexcess).sub hdeficit
  refine ⟨hidentity.symm ▸ hint, ?_⟩
  have hformula :
      (∫ x, Real.log (radius x) ∂mu) =
        Real.log scale + ∫ x, E x ∂mu - ∫ x, D x ∂mu := by
    calc
      (∫ x, Real.log (radius x) ∂mu) =
          ∫ x, Real.log scale + E x - D x ∂mu := by
        apply integral_congr_ae
        filter_upwards with x
        exact congrFun hidentity x
      _ = (∫ x, Real.log scale + E x ∂mu) - ∫ x, D x ∂mu :=
        integral_sub ((integrable_const (Real.log scale)).add hexcess) hdeficit
      _ = Real.log scale + ∫ x, E x ∂mu - ∫ x, D x ∂mu := by
        rw [integral_add (integrable_const (Real.log scale)) hexcess]
        simp [E]
  rw [hformula]
  have hE : 0 ≤ ∫ x, E x ∂mu := integral_nonneg fun x => logExcess_nonneg _ _
  linarith

/-- If a nonnegative coordinate is dominated by a nonnegative radius, a
null coordinate zero set also rules out a zero full radius. -/
theorem measure_zeroSet_of_coordinate
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {scalar radius : Omega → ℝ}
    (hscalar0 : ∀ x, 0 ≤ scalar x)
    (hzero : mu {x | scalar x = 0} = 0)
    (hle : ∀ x, scalar x ≤ radius x) :
    mu {x | radius x = 0} = 0 := by
  have hsubset : {x | radius x = 0} ⊆ {x | scalar x = 0} := by
    intro x hx
    have hr : radius x = 0 := hx
    have hsle : scalar x ≤ 0 := by simpa only [hr] using hle x
    exact le_antisymm hsle (hscalar0 x)
  exact measure_mono_null hsubset hzero

/-- Pointwise conditional-integral wrapper for a Markov kernel.  No
measurable choice of a maximizing vector or coordinate is involved: after
the finite selector has been chosen in a fiber, this theorem is applied to
that fiber measure. -/
theorem markovKernel_integral_log_ge_of_logDeficit
    {Past Omega : Type*} [MeasurableSpace Past] [MeasurableSpace Omega]
    (kappa : ProbabilityTheory.Kernel Past Omega)
    [ProbabilityTheory.IsMarkovKernel kappa]
    (radius : Past → Omega → ℝ) (scale bound : Past → ℝ)
    (hdeficit : ∀ a, Integrable
      (fun x => logDeficit (scale a) (radius a x)) (kappa a))
    (hexcess : ∀ a, Integrable
      (fun x => logExcess (scale a) (radius a x)) (kappa a))
    (hbound : ∀ a,
      ∫ x, logDeficit (scale a) (radius a x) ∂(kappa a) ≤ bound a) :
    ∀ a,
      Integrable (fun x => Real.log (radius a x)) (kappa a) ∧
        Real.log (scale a) - bound a ≤
          ∫ x, Real.log (radius a x) ∂(kappa a) := by
  intro a
  exact integrable_log_and_integral_log_ge_of_logDeficit
    (kappa a) (scale a) (bound a) (hdeficit a) (hexcess a) (hbound a)

/-- Conditional expectation given the past coordinate is the integral
against its regular conditional fresh-coordinate law. -/
theorem condExp_past_ae_eq_freshIntegral
    {Past Fresh : Type*} [MeasurableSpace Past] [MeasurableSpace Fresh]
    [StandardBorelSpace Fresh] [Nonempty Fresh]
    (mu : Measure (Past × Fresh)) [IsFiniteMeasure mu]
    (g : Past × Fresh → ℝ) (hg : StronglyMeasurable g)
    (hgInt : Integrable g mu) :
    mu[g | (inferInstance : MeasurableSpace Past).comap Prod.fst] =ᵐ[mu]
      fun z => ∫ y, g (z.1, y) ∂ProbabilityTheory.condDistrib
        Prod.snd Prod.fst mu z.1 := by
  simpa only using
    (ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
      (μ := mu) (X := Prod.fst) (Y := Prod.snd)
      measurable_fst measurable_snd.aemeasurable hg hgInt)

/-- Turning a fiberwise conditional-integral lower bound into the exact
conditional-expectation inequality used in the manuscript. -/
theorem condExp_past_ae_ge_of_freshIntegral_ge
    {Past Fresh : Type*} [MeasurableSpace Past] [MeasurableSpace Fresh]
    [StandardBorelSpace Fresh] [Nonempty Fresh]
    (mu : Measure (Past × Fresh)) [IsFiniteMeasure mu]
    (g : Past × Fresh → ℝ) (hg : StronglyMeasurable g)
    (hgInt : Integrable g mu) (lower : Past → ℝ)
    (hlower : ∀ᵐ z ∂mu,
      lower z.1 ≤ ∫ y, g (z.1, y) ∂ProbabilityTheory.condDistrib
        Prod.snd Prod.fst mu z.1) :
    (fun z => lower z.1) ≤ᵐ[mu]
      mu[g | (inferInstance : MeasurableSpace Past).comap Prod.fst] := by
  have heq := condExp_past_ae_eq_freshIntegral mu g hg hgInt
  filter_upwards [heq, hlower] with z heqz hz
  rw [heqz]
  exact hz

namespace PaperIndicatorWeights

/-! ## Complex and real product-law specializations -/

/-- Complex planar-density projective observability for the actual fresh
product vector.  This gives a null zero set and an integrable, explicitly
bounded negative logarithmic part at the operator scale `‖B‖`. -/
theorem exists_paperProjectiveFreshVector_complex_logDeficit_withDensity
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < ‖B‖)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (hv : ‖v‖ = 1)
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L) :
    ∃ o I J : ExteriorIndex (d + 1) q,
      let p := profile.paperProjectiveFreshPolynomial
        center z atoms q B v o I J
      let radius := fun x : Fin (d + 1) → ℂ =>
        ‖profile.paperProjectiveFreshVector center z atoms q B v I J x‖
      iidMeasure (volume.withDensity f) (d + 1) {x | radius x = 0} = 0 ∧
        Integrable (fun x => logDeficit ‖B‖ (radius x))
          (iidMeasure (volume.withDensity f) (d + 1)) ∧
        ∫ x, logDeficit ‖B‖ (radius x)
              ∂iidMeasure (volume.withDensity f) (d + 1) ≤
          paperProjectiveCoefficientLogLoss d c₀ q +
            (Real.log
                (max 1 (((d + 1 : ℕ) : ℝ) * (Real.pi * L))) + 1) /
              (((2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) := by
  let _ := iidMeasure_isProbability (volume.withDensity f) (d + 1)
  letI : Nonempty (ExteriorIndex (d + 1) q) :=
    exteriorIndex_nonempty (d + 1) q
  obtain ⟨o, I, J, hcoefficient⟩ :=
    profile.exists_paperProjectiveFreshPolynomial_topCoeff_lower
      center z atoms q B v hv
  refine ⟨o, I, J, ?_⟩
  let p := profile.paperProjectiveFreshPolynomial center z atoms q B v o I J
  let radius := fun x : Fin (d + 1) → ℂ =>
    ‖profile.paperProjectiveFreshVector center z atoms q B v I J x‖
  have hbmin : 0 < Real.sqrt (c₀ / (d + 2 : ℝ)) :=
    Real.sqrt_pos.2 (div_pos hc₀ (by positivity))
  have hcard : 0 < (Fintype.card (ExteriorIndex (d + 1) q) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have htop : 0 < ‖p.topCoeff‖ := by
    apply (mul_pos (pow_pos hbmin _)
      (div_pos hB (pow_pos hcard _))).trans_le
    exact hcoefficient
  obtain ⟨hzero, _hae, hcoordinate, hcoordinateBound⟩ :=
    iid_complex_positiveLogLoss_withDensity f hL hf p htop
  have hscale :=
    profile.log_norm_sub_log_topCoeff_le_paperProjectiveCoefficientLogLoss
      hc₀ center z atoms q B hB v o I J hcoefficient
  have hlift := integrable_logDeficit_of_coordinate
    (iidMeasure (volume.withDensity f) (d + 1))
    p.continuous_eval_complex.norm.measurable
    (profile.continuous_paperProjectiveFreshVector
      center z atoms q B v I J).norm.measurable
    (fun x => norm_nonneg _) (fun x => norm_nonneg _) hzero
    (fun x => profile.norm_eval_paperProjectiveFreshPolynomial_replaced_le
      center z atoms q B v o I J x)
    (paperProjectiveCoefficientLogLoss_nonneg d c₀ q) hscale
    (by simpa only [logDeficit_eq_positiveLogLoss] using hcoordinate)
  refine ⟨measure_zeroSet_of_coordinate
      (iidMeasure (volume.withDensity f) (d + 1))
      (fun x => norm_nonneg _) hzero
      (fun x => profile.norm_eval_paperProjectiveFreshPolynomial_replaced_le
        center z atoms q B v o I J x), hlift.1, ?_⟩
  calc
    (∫ x, logDeficit ‖B‖ (radius x)
        ∂iidMeasure (volume.withDensity f) (d + 1)) ≤
      paperProjectiveCoefficientLogLoss d c₀ q +
        ∫ x, logDeficit ‖p.topCoeff‖ ‖p.eval x‖
          ∂iidMeasure (volume.withDensity f) (d + 1) := hlift.2
    _ ≤ paperProjectiveCoefficientLogLoss d c₀ q +
        (Real.log
            (max 1 (((d + 1 : ℕ) : ℝ) * (Real.pi * L))) + 1) /
          (((2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) := by
      simpa only [logDeficit_eq_positiveLogLoss, add_comm] using
        add_le_add_right hcoordinateBound
          (paperProjectiveCoefficientLogLoss d c₀ q)

/-- Real interval-density counterpart for complex fresh polynomials and
the genuine complex projective vector. -/
theorem exists_paperProjectiveFreshVector_real_logDeficit_of_intervalBound
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < ‖B‖)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (hv : ‖v‖ = 1)
    (nu : Measure ℝ) [SFinite nu] [IsProbabilityMeasure nu]
    {L : ℝ} (hL : 0 ≤ L)
    (hnu : RealIntervalBound nu (ENNReal.ofReal L)) :
    ∃ o I J : ExteriorIndex (d + 1) q,
      let p := profile.paperProjectiveFreshPolynomial
        center z atoms q B v o I J
      let radius := fun x : Fin (d + 1) → ℝ =>
        ‖profile.paperProjectiveFreshVectorOfReal center z atoms q B v I J x‖
      iidMeasure nu (d + 1) {x | radius x = 0} = 0 ∧
        Integrable (fun x => logDeficit ‖B‖ (radius x))
          (iidMeasure nu (d + 1)) ∧
        ∫ x, logDeficit ‖B‖ (radius x) ∂iidMeasure nu (d + 1) ≤
          paperProjectiveCoefficientLogLoss d c₀ q +
            (Real.log
                (max 1 (((d + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
              (((1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) := by
  let _ := iidMeasure_isProbability nu (d + 1)
  letI : Nonempty (ExteriorIndex (d + 1) q) :=
    exteriorIndex_nonempty (d + 1) q
  obtain ⟨o, I, J, hcoefficient⟩ :=
    profile.exists_paperProjectiveFreshPolynomial_topCoeff_lower
      center z atoms q B v hv
  refine ⟨o, I, J, ?_⟩
  let p := profile.paperProjectiveFreshPolynomial center z atoms q B v o I J
  let radius := fun x : Fin (d + 1) → ℝ =>
    ‖profile.paperProjectiveFreshVectorOfReal center z atoms q B v I J x‖
  have hbmin : 0 < Real.sqrt (c₀ / (d + 2 : ℝ)) :=
    Real.sqrt_pos.2 (div_pos hc₀ (by positivity))
  have hcard : 0 < (Fintype.card (ExteriorIndex (d + 1) q) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have htop : 0 < ‖p.topCoeff‖ := by
    apply (mul_pos (pow_pos hbmin _)
      (div_pos hB (pow_pos hcard _))).trans_le
    exact hcoefficient
  obtain ⟨hzero, _hae, hcoordinate, hcoordinateBound⟩ :=
    iid_realInput_complex_positiveLogLoss_of_intervalBound nu hL hnu p htop
  have hscale :=
    profile.log_norm_sub_log_topCoeff_le_paperProjectiveCoefficientLogLoss
      hc₀ center z atoms q B hB v o I J hcoefficient
  have hlift := integrable_logDeficit_of_coordinate (iidMeasure nu (d + 1))
    p.continuous_realInputEval.norm.measurable
    (profile.continuous_paperProjectiveFreshVectorOfReal
      center z atoms q B v I J).norm.measurable
    (fun x => norm_nonneg _) (fun x => norm_nonneg _) hzero
    (fun x => profile.norm_realInputEval_paperProjectiveFreshPolynomial_le
      center z atoms q B v o I J x)
    (paperProjectiveCoefficientLogLoss_nonneg d c₀ q) hscale
    (by simpa only [logDeficit_eq_positiveLogLoss] using hcoordinate)
  refine ⟨measure_zeroSet_of_coordinate (iidMeasure nu (d + 1))
      (fun x => norm_nonneg _) hzero
      (fun x => profile.norm_realInputEval_paperProjectiveFreshPolynomial_le
        center z atoms q B v o I J x), hlift.1, ?_⟩
  calc
    (∫ x, logDeficit ‖B‖ (radius x) ∂iidMeasure nu (d + 1)) ≤
      paperProjectiveCoefficientLogLoss d c₀ q +
        ∫ x, logDeficit ‖p.topCoeff‖ ‖realInputEval p x‖
          ∂iidMeasure nu (d + 1) := hlift.2
    _ ≤ paperProjectiveCoefficientLogLoss d c₀ q +
        (Real.log (max 1 (((d + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
          (((1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) := by
      simpa only [logDeficit_eq_positiveLogLoss, add_comm] using
        add_le_add_right hcoordinateBound
          (paperProjectiveCoefficientLogLoss d c₀ q)

/-- Heterogeneous directional-density version, stated fiberwise under the
correct conditional product kernel.  The finite indices `o,I,J` are chosen
inside the fixed past fiber, so no measurable singular-vector selection is
needed. -/
theorem exists_paperProjectiveFreshVector_directional_fiber_logDeficit
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < ‖B‖)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (hv : ‖v‖ = 1)
    (M : DirectionalProductModel (d + 1))
    {L : ℝ} (hL : 0 ≤ L)
    (hinterval : ∀ past i,
      RealIntervalBound (M.coordinateLaw past i : Measure ℝ)
        (ENNReal.ofReal L))
    (past : Fin (d + 1) → ℝ) :
    ∃ o I J : ExteriorIndex (d + 1) q,
      let p := profile.paperProjectiveFreshPolynomial
        center z atoms q B v o I J
      let radius := fun u : Fin (d + 1) → ℝ =>
        ‖profile.paperProjectiveFreshVectorOfReal center z atoms q B v I J u‖
      M.conditionalULaw past {u | radius u = 0} = 0 ∧
        Integrable (fun u => logDeficit ‖B‖ (radius u))
          (M.conditionalULaw past) ∧
        ∫ u, logDeficit ‖B‖ (radius u) ∂M.conditionalULaw past ≤
          paperProjectiveCoefficientLogLoss d c₀ q +
            (Real.log (max 1 (((d + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
              (((1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) := by
  let _ := M.conditionalULaw_isMarkov
  letI : Nonempty (ExteriorIndex (d + 1) q) :=
    exteriorIndex_nonempty (d + 1) q
  obtain ⟨o, I, J, hcoefficient⟩ :=
    profile.exists_paperProjectiveFreshPolynomial_topCoeff_lower
      center z atoms q B v hv
  refine ⟨o, I, J, ?_⟩
  let p := profile.paperProjectiveFreshPolynomial center z atoms q B v o I J
  let radius := fun u : Fin (d + 1) → ℝ =>
    ‖profile.paperProjectiveFreshVectorOfReal center z atoms q B v I J u‖
  have hbmin : 0 < Real.sqrt (c₀ / (d + 2 : ℝ)) :=
    Real.sqrt_pos.2 (div_pos hc₀ (by positivity))
  have hcard : 0 < (Fintype.card (ExteriorIndex (d + 1) q) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have htop : 0 < ‖p.topCoeff‖ := by
    apply (mul_pos (pow_pos hbmin _)
      (div_pos hB (pow_pos hcard _))).trans_le
    exact hcoefficient
  obtain ⟨hzero, hcoordinate, hcoordinateBound⟩ :=
    directionalProduct_fiber_positiveLogLoss M hL hinterval past p htop
  have hscale :=
    profile.log_norm_sub_log_topCoeff_le_paperProjectiveCoefficientLogLoss
      hc₀ center z atoms q B hB v o I J hcoefficient
  have hlift := integrable_logDeficit_of_coordinate (M.conditionalULaw past)
    p.continuous_realInputEval.norm.measurable
    (profile.continuous_paperProjectiveFreshVectorOfReal
      center z atoms q B v I J).norm.measurable
    (fun u => norm_nonneg _) (fun u => norm_nonneg _) hzero
    (fun u => profile.norm_realInputEval_paperProjectiveFreshPolynomial_le
      center z atoms q B v o I J u)
    (paperProjectiveCoefficientLogLoss_nonneg d c₀ q) hscale
    (by simpa only [logDeficit_eq_positiveLogLoss] using hcoordinate)
  refine ⟨measure_zeroSet_of_coordinate (M.conditionalULaw past)
      (fun u => norm_nonneg _) hzero
      (fun u => profile.norm_realInputEval_paperProjectiveFreshPolynomial_le
        center z atoms q B v o I J u), hlift.1, ?_⟩
  calc
    (∫ u, logDeficit ‖B‖ (radius u) ∂M.conditionalULaw past) ≤
      paperProjectiveCoefficientLogLoss d c₀ q +
        ∫ u, logDeficit ‖p.topCoeff‖ ‖realInputEval p u‖
          ∂M.conditionalULaw past := hlift.2
    _ ≤ paperProjectiveCoefficientLogLoss d c₀ q +
        (Real.log (max 1 (((d + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
          (((1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) := by
      simpa only [logDeficit_eq_positiveLogLoss, add_comm] using
        add_le_add_right hcoordinateBound
          (paperProjectiveCoefficientLogLoss d c₀ q)

/-- Concrete raw directional-law corollary. -/
theorem exists_paperProjectiveFreshVector_rawDirectional_fiber_logDeficit
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < ‖B‖)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (hv : ‖v‖ = 1)
    (atom : ProbabilityMeasure ℂ) (theta L : ℝ) (hL : 0 ≤ L)
    (hdir : HasDirectionalConditionalDensity atom theta L)
    (past : Fin (d + 1) → ℝ) :
    ∃ o I J : ExteriorIndex (d + 1) q,
      let radius := fun u : Fin (d + 1) → ℝ =>
        ‖profile.paperProjectiveFreshVectorOfReal center z atoms q B v I J u‖
      (paperDirectionalProductModel (d + 1) atom theta L hdir).conditionalULaw
          past {u | radius u = 0} = 0 ∧
        Integrable (fun u => logDeficit ‖B‖ (radius u))
          ((paperDirectionalProductModel (d + 1) atom theta L hdir).conditionalULaw
            past) ∧
        ∫ u, logDeficit ‖B‖ (radius u)
            ∂(paperDirectionalProductModel (d + 1) atom theta L hdir).conditionalULaw
              past ≤
          paperProjectiveCoefficientLogLoss d c₀ q +
            (Real.log (max 1 (((d + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
              (((1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) := by
  simpa only using
    profile.exists_paperProjectiveFreshVector_directional_fiber_logDeficit
      hc₀ center z atoms q B hB v hv
      (paperDirectionalProductModel (d + 1) atom theta L hdir) hL
      (fun past i => paperDirectionalProductModel_intervalBound
        (d + 1) atom theta L hdir past i) past

/-- Full conditional expectation lower bound in one heterogeneous
directional fiber. -/
theorem exists_paperProjectiveFreshVector_directional_fiber_integral_log_ge
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < ‖B‖)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (hv : ‖v‖ = 1)
    (M : DirectionalProductModel (d + 1))
    {L : ℝ} (hL : 0 ≤ L)
    (hinterval : ∀ past i,
      RealIntervalBound (M.coordinateLaw past i : Measure ℝ)
        (ENNReal.ofReal L))
    (past : Fin (d + 1) → ℝ)
    (hexcess : ∀ I J : ExteriorIndex (d + 1) q,
      Integrable (fun u : Fin (d + 1) → ℝ =>
        logExcess ‖B‖
          ‖profile.paperProjectiveFreshVectorOfReal center z atoms q B v I J u‖)
        (M.conditionalULaw past)) :
    ∃ o I J : ExteriorIndex (d + 1) q,
      let radius := fun u : Fin (d + 1) → ℝ =>
        ‖profile.paperProjectiveFreshVectorOfReal center z atoms q B v I J u‖
      M.conditionalULaw past {u | radius u = 0} = 0 ∧
        Integrable (fun u => Real.log (radius u)) (M.conditionalULaw past) ∧
        Real.log ‖B‖ -
            (paperProjectiveCoefficientLogLoss d c₀ q +
              (Real.log (max 1 (((d + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
                (((1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ))) ≤
          ∫ u, Real.log (radius u) ∂M.conditionalULaw past := by
  let _ := M.conditionalULaw_isMarkov
  obtain ⟨o, I, J, hzero, hdeficit, hbound⟩ :=
    profile.exists_paperProjectiveFreshVector_directional_fiber_logDeficit
      hc₀ center z atoms q B hB v hv M hL hinterval past
  refine ⟨o, I, J, hzero, ?_⟩
  exact integrable_log_and_integral_log_ge_of_logDeficit
    (M.conditionalULaw past) ‖B‖
    (paperProjectiveCoefficientLogLoss d c₀ q +
      (Real.log (max 1 (((d + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
        (((1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)))
    hdeficit (hexcess I J) hbound

/-- Past-dependent formulation.  Both the frozen operator and input vector
may vary with the past.  The selector remains under `∀ past, ∃ o I J`, which
is exactly what is needed for a pointwise conditional integral and avoids
introducing a measurable singular-vector choice. -/
theorem forall_past_exists_paperProjectiveFreshVector_directional_logDeficit
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : (Fin (d + 1) → ℝ) →
      Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : (Fin (d + 1) → ℝ) → Matrix
      (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : ∀ past, 0 < ‖B past‖)
    (v : (Fin (d + 1) → ℝ) →
      EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (hv : ∀ past, ‖v past‖ = 1)
    (M : DirectionalProductModel (d + 1))
    {L : ℝ} (hL : 0 ≤ L)
    (hinterval : ∀ past i,
      RealIntervalBound (M.coordinateLaw past i : Measure ℝ)
        (ENNReal.ofReal L)) :
    ∀ past, ∃ o I J : ExteriorIndex (d + 1) q,
      let radius := fun u : Fin (d + 1) → ℝ =>
        ‖profile.paperProjectiveFreshVectorOfReal center z (atoms past) q
          (B past) (v past) I J u‖
      M.conditionalULaw past {u | radius u = 0} = 0 ∧
        Integrable (fun u => logDeficit ‖B past‖ (radius u))
          (M.conditionalULaw past) ∧
        ∫ u, logDeficit ‖B past‖ (radius u) ∂M.conditionalULaw past ≤
          paperProjectiveCoefficientLogLoss d c₀ q +
            (Real.log (max 1 (((d + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
              (((1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) := by
  intro past
  simpa only using
    profile.exists_paperProjectiveFreshVector_directional_fiber_logDeficit
      hc₀ center z (atoms past) q (B past) (hB past) (v past) (hv past)
      M hL hinterval past

/-- With an integrable positive logarithmic excess, the complex
planar-density result is a genuine lower bound on the expectation of the
actual `log ‖B Q v‖`. -/
theorem exists_paperProjectiveFreshVector_complex_integral_log_ge_withDensity
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < ‖B‖)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (hv : ‖v‖ = 1)
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L)
    (hexcess : ∀ I J : ExteriorIndex (d + 1) q,
      Integrable (fun x : Fin (d + 1) → ℂ =>
        logExcess ‖B‖
          ‖profile.paperProjectiveFreshVector center z atoms q B v I J x‖)
        (iidMeasure (volume.withDensity f) (d + 1))) :
    ∃ o I J : ExteriorIndex (d + 1) q,
      let radius := fun x : Fin (d + 1) → ℂ =>
        ‖profile.paperProjectiveFreshVector center z atoms q B v I J x‖
      iidMeasure (volume.withDensity f) (d + 1) {x | radius x = 0} = 0 ∧
        Integrable (fun x => Real.log (radius x))
          (iidMeasure (volume.withDensity f) (d + 1)) ∧
        Real.log ‖B‖ -
            (paperProjectiveCoefficientLogLoss d c₀ q +
              (Real.log
                  (max 1 (((d + 1 : ℕ) : ℝ) * (Real.pi * L))) + 1) /
                (((2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ))) ≤
          ∫ x, Real.log (radius x)
            ∂iidMeasure (volume.withDensity f) (d + 1) := by
  let _ := iidMeasure_isProbability (volume.withDensity f) (d + 1)
  obtain ⟨o, I, J, hzero, hdeficit, hbound⟩ :=
    profile.exists_paperProjectiveFreshVector_complex_logDeficit_withDensity
      hc₀ center z atoms q B hB v hv f hL hf
  refine ⟨o, I, J, hzero, ?_⟩
  exact integrable_log_and_integral_log_ge_of_logDeficit
    (iidMeasure (volume.withDensity f) (d + 1)) ‖B‖
    (paperProjectiveCoefficientLogLoss d c₀ q +
      (Real.log (max 1 (((d + 1 : ℕ) : ℝ) * (Real.pi * L))) + 1) /
        (((2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)))
    hdeficit (hexcess I J) hbound

/-- Real interval-density expectation lower bound for the actual
projective vector. -/
theorem exists_paperProjectiveFreshVector_real_integral_log_ge_of_intervalBound
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1))
    (B : Matrix (ExteriorIndex (d + 1) q)
      (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < ‖B‖)
    (v : EuclideanSpace ℂ (ExteriorIndex (d + 1) q))
    (hv : ‖v‖ = 1)
    (nu : Measure ℝ) [SFinite nu] [IsProbabilityMeasure nu]
    {L : ℝ} (hL : 0 ≤ L)
    (hnu : RealIntervalBound nu (ENNReal.ofReal L))
    (hexcess : ∀ I J : ExteriorIndex (d + 1) q,
      Integrable (fun x : Fin (d + 1) → ℝ =>
        logExcess ‖B‖
          ‖profile.paperProjectiveFreshVectorOfReal center z atoms q B v I J x‖)
        (iidMeasure nu (d + 1))) :
    ∃ o I J : ExteriorIndex (d + 1) q,
      let radius := fun x : Fin (d + 1) → ℝ =>
        ‖profile.paperProjectiveFreshVectorOfReal center z atoms q B v I J x‖
      iidMeasure nu (d + 1) {x | radius x = 0} = 0 ∧
        Integrable (fun x => Real.log (radius x)) (iidMeasure nu (d + 1)) ∧
        Real.log ‖B‖ -
            (paperProjectiveCoefficientLogLoss d c₀ q +
              (Real.log (max 1 (((d + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
                (((1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ))) ≤
          ∫ x, Real.log (radius x) ∂iidMeasure nu (d + 1) := by
  let _ := iidMeasure_isProbability nu (d + 1)
  obtain ⟨o, I, J, hzero, hdeficit, hbound⟩ :=
    profile.exists_paperProjectiveFreshVector_real_logDeficit_of_intervalBound
      hc₀ center z atoms q B hB v hv nu hL hnu
  refine ⟨o, I, J, hzero, ?_⟩
  exact integrable_log_and_integral_log_ge_of_logDeficit
    (iidMeasure nu (d + 1)) ‖B‖
    (paperProjectiveCoefficientLogLoss d c₀ q +
      (Real.log (max 1 (((d + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
        (((1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)))
    hdeficit (hexcess I J) hbound

end PaperIndicatorWeights

end CircularLawSection4
