import CircularLawSection4.HeterogeneousProductSmallBall
import CircularLawSection4.MultiaffineDirectional
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Constructing the directional conditional product from an atom law

The manuscript assumes that, after one fixed phase rotation, the conditional
law of the real directional coordinate `U` given its orthogonal coordinate
`V` has a uniformly bounded density for `Law(V)`-almost every `v`.

For several independent atoms the laws of `U_j` conditional on the entire
vector `(V_j)` are independent but generally *not identical*: the `j`th law
is `Law(U | V = V_j)`.  Accordingly this file constructs the correct finite
heterogeneous product kernel.  The older `DirectionalIIDKernel` is recovered
only in the special case where the conditional coordinate law is independent
of `v`.
-/

open scoped ENNReal MeasureTheory ProbabilityTheory Topology
open MeasureTheory Set Filter ProbabilityTheory

noncomputable section

namespace CircularLawSection4

/-- Real coordinate after rotation by the manuscript's fixed direction. -/
def directionalRealPart (theta : ℝ) (z : ℂ) : ℝ :=
  (Complex.exp (-(theta : ℂ) * Complex.I) * z).re

/-- Orthogonal coordinate after the same phase rotation. -/
def directionalImagPart (theta : ℝ) (z : ℂ) : ℝ :=
  (Complex.exp (-(theta : ℂ) * Complex.I) * z).im

theorem continuous_directionalRealPart (theta : ℝ) :
    Continuous (directionalRealPart theta) := by
  unfold directionalRealPart
  fun_prop

theorem continuous_directionalImagPart (theta : ℝ) :
    Continuous (directionalImagPart theta) := by
  unfold directionalImagPart
  fun_prop

/-- The canonical regular conditional distribution `Law(U | V = v)` supplied
by disintegration on the standard Borel space `ℝ`. -/
noncomputable def directionalCondDistrib
    (atom : ProbabilityMeasure ℂ) (theta : ℝ) : Kernel ℝ ℝ :=
  condDistrib (directionalRealPart theta) (directionalImagPart theta)
    (atom : Measure ℂ)

instance directionalCondDistrib_isMarkov
    (atom : ProbabilityMeasure ℂ) (theta : ℝ) :
    IsMarkovKernel (directionalCondDistrib atom theta) := by
  unfold directionalCondDistrib
  infer_instance

/-- The manuscript's raw directional-density hypothesis, stated on the
canonical regular conditional distribution.  The `ae` quantifier is exactly
the one in Remark `directional-density`; it is not strengthened to every
orthogonal coordinate. -/
def HasDirectionalConditionalDensity
    (atom : ProbabilityMeasure ℂ) (theta L : ℝ) : Prop :=
  ∀ᵐ v ∂(atom : Measure ℂ).map (directionalImagPart theta),
    RealIntervalBound (directionalCondDistrib atom theta v)
      (ENNReal.ofReal L)

/-- A Markov kernel whose fibers obey a uniform interval bound everywhere,
and which agrees almost everywhere with a supplied conditional kernel. -/
structure EverywhereIntervalKernel {V : Type*} [MeasurableSpace V]
    (vLaw : ProbabilityMeasure V) (base : Kernel V ℝ) (L : ℝ≥0∞) where
  kernel : Kernel V ℝ
  isMarkov : IsMarkovKernel kernel
  ae_eq : kernel =ᵐ[(vLaw : Measure V)] base
  intervalBound : ∀ v, RealIntervalBound (kernel v) L

/-- Repair an almost-everywhere uniform conditional-density bound on a null
set.  The replacement fiber is one good conditional probability measure, so
the repaired object remains a measurable Markov kernel and changes no joint
law. -/
theorem exists_everywhereIntervalKernel
    {V : Type*} [MeasurableSpace V]
    (vLaw : ProbabilityMeasure V) (base : Kernel V ℝ)
    [IsMarkovKernel base] {L : ℝ≥0∞}
    (hbound : ∀ᵐ v ∂(vLaw : Measure V), RealIntervalBound (base v) L) :
    Nonempty (EverywhereIntervalKernel vLaw base L) := by
  classical
  let bad : Set V := {v | ¬ RealIntervalBound (base v) L}
  have hbad : (vLaw : Measure V) bad = 0 := by
    rw [← ae_iff]
    simpa only [bad, Set.mem_setOf_eq, not_not] using hbound
  obtain ⟨B, hbadB, hBmeas, hBzero⟩ :=
    exists_measurable_superset_of_null hbad
  have hex : ∃ v₀ : V, v₀ ∉ B := by
    by_contra h
    push_neg at h
    have hBuniv : B = Set.univ := Set.eq_univ_of_forall h
    have : (vLaw : Measure V) Set.univ = 0 := by simpa [hBuniv] using hBzero
    simpa using this
  obtain ⟨v₀, hv₀⟩ := hex
  have hv₀bound : RealIntervalBound (base v₀) L := by
    by_contra h
    exact hv₀ (hbadB h)
  let repaired : Kernel V ℝ :=
    Kernel.piecewise hBmeas (Kernel.const V (base v₀)) base
  have hmarkov : IsMarkovKernel repaired := by
    dsimp only [repaired]
    infer_instance
  refine ⟨⟨repaired, hmarkov, ?_, ?_⟩⟩
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hBzero] with v hv
    simp [repaired, Kernel.piecewise_apply, hv]
  · intro v
    by_cases hv : v ∈ B
    · simpa [repaired, Kernel.piecewise_apply, hv] using hv₀bound
    · have hvbound : RealIntervalBound (base v) L := by
        by_contra h
        exact hv (hbadB h)
      simpa [repaired, Kernel.piecewise_apply, hv] using hvbound

/-- The orthogonal marginal of one rotated atom. -/
noncomputable def directionalOrthogonalLaw
    (atom : ProbabilityMeasure ℂ) (theta : ℝ) : ProbabilityMeasure ℝ :=
  atom.map (continuous_directionalImagPart theta).measurable.aemeasurable

@[simp] theorem directionalOrthogonalLaw_toMeasure
    (atom : ProbabilityMeasure ℂ) (theta : ℝ) :
    (directionalOrthogonalLaw atom theta : Measure ℝ) =
      (atom : Measure ℂ).map (directionalImagPart theta) := rfl

/-- The everywhere-good version of the manuscript's one-atom conditional
law.  Its existence uses only regular conditional probability plus null-set
repair. -/
noncomputable def paperEverywhereDirectionalKernel
    (atom : ProbabilityMeasure ℂ) (theta L : ℝ)
    (hdir : HasDirectionalConditionalDensity atom theta L) :
    EverywhereIntervalKernel (directionalOrthogonalLaw atom theta)
      (directionalCondDistrib atom theta) (ENNReal.ofReal L) :=
  Classical.choice (exists_everywhereIntervalKernel
    (directionalOrthogonalLaw atom theta) (directionalCondDistrib atom theta)
    (by simpa [HasDirectionalConditionalDensity] using hdir))

/-- Exact one-atom disintegration after rotation.  Replacing the canonical
conditional distribution on the exceptional null set does not alter the
joint law. -/
theorem directionalAtom_map_pair_eq_compProd
    (atom : ProbabilityMeasure ℂ) (theta L : ℝ)
    (hdir : HasDirectionalConditionalDensity atom theta L) :
    (atom : Measure ℂ).map
        (fun z => (directionalImagPart theta z, directionalRealPart theta z)) =
      (directionalOrthogonalLaw atom theta : Measure ℝ) ⊗ₘ
        (paperEverywhereDirectionalKernel atom theta L hdir).kernel := by
  let G := paperEverywhereDirectionalKernel atom theta L hdir
  letI : IsMarkovKernel G.kernel := G.isMarkov
  have hdis := compProd_map_condDistrib
    (mβ := inferInstance)
    (μ := (atom : Measure ℂ))
    (X := directionalImagPart theta)
    (Y := directionalRealPart theta)
    (continuous_directionalRealPart theta).measurable.aemeasurable
  calc
    (atom : Measure ℂ).map
        (fun z => (directionalImagPart theta z, directionalRealPart theta z)) =
      (directionalOrthogonalLaw atom theta : Measure ℝ) ⊗ₘ
        directionalCondDistrib atom theta := by
          simpa [directionalCondDistrib] using hdis.symm
    _ = (directionalOrthogonalLaw atom theta : Measure ℝ) ⊗ₘ G.kernel :=
      Measure.compProd_congr G.ae_eq.symm

/-- Finite product kernel for coordinatewise conditional laws.  Its input is
the entire vector of orthogonal coordinates. -/
noncomputable def directionalProductKernel (base : Kernel ℝ ℝ)
    [IsMarkovKernel base] :
    (k : ℕ) → Kernel (Fin k → ℝ) (Fin k → ℝ)
  | 0 => Kernel.const _ (Measure.dirac fun i => Fin.elim0 i)
  | n + 1 =>
      (((directionalProductKernel base n).comap MultiAffine.dropLast
          measurable_dropLast) ×ₖ
        base.comap (fun v : Fin (n + 1) → ℝ => v (Fin.last n))
          (measurable_pi_apply (Fin.last n))).map joinLast

theorem directionalProductKernel_isMarkov (base : Kernel ℝ ℝ)
    [IsMarkovKernel base] :
    ∀ k, IsMarkovKernel (directionalProductKernel base k) := by
  intro k
  induction k with
  | zero =>
      dsimp [directionalProductKernel]
      infer_instance
  | succ n ih =>
      rw [directionalProductKernel]
      letI : IsMarkovKernel (directionalProductKernel base n) := ih
      exact Kernel.IsMarkovKernel.map _ measurable_joinLast

/-- Every fiber of `directionalProductKernel` is exactly the product of the
coordinate-specific conditional probability measures. -/
theorem directionalProductKernel_apply_eq_pi
    (base : Kernel ℝ ℝ) [IsMarkovKernel base] :
    ∀ {k : ℕ} (v : Fin k → ℝ),
      directionalProductKernel base k v =
        Measure.pi (fun i : Fin k => base (v i)) := by
  intro k
  induction k with
  | zero =>
      intro v
      rw [directionalProductKernel]
      symm
      apply Measure.pi_eq
      intro s hs
      simp
  | succ n ih =>
      intro v
      haveI : IsMarkovKernel (directionalProductKernel base n) :=
        directionalProductKernel_isMarkov base n
      rw [directionalProductKernel,
        Kernel.map_apply _ measurable_joinLast,
        Kernel.prod_apply,
        Kernel.comap_apply, Kernel.comap_apply, ih]
      symm
      apply Measure.pi_eq
      intro s hs
      have hrect : MeasurableSet (Set.pi Set.univ s) :=
        MeasurableSet.pi Set.countable_univ (fun i _ => hs i)
      have hpre :
          joinLast ⁻¹' Set.pi Set.univ s =
            Set.pi Set.univ (fun i : Fin n => s i.castSucc) ×ˢ
              s (Fin.last n) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
          Set.mem_prod]
        constructor
        · intro hy
          exact ⟨fun i => by simpa using hy i.castSucc,
            by simpa using hy (Fin.last n)⟩
        · rintro ⟨hp, hl⟩ i
          refine Fin.lastCases (by simpa using hl)
            (fun j => by simpa using hp j) i
      rw [Measure.map_apply measurable_joinLast hrect, hpre,
        Measure.prod_prod, Measure.pi_pi, Fin.prod_univ_castSucc]
      simp [MultiAffine.dropLast]

/-- Correct finite directional interface: the conditional coordinates are
independent with a coordinate-specific law. -/
structure DirectionalProductModel (k : ℕ) where
  vLaw : ProbabilityMeasure (Fin k → ℝ)
  coordinateLaw : (Fin k → ℝ) → Fin k → ProbabilityMeasure ℝ
  conditionalULaw : Kernel (Fin k → ℝ) (Fin k → ℝ)
  conditionalULaw_isMarkov : IsMarkovKernel conditionalULaw
  conditionalULaw_eq_pi : ∀ v,
    conditionalULaw v = Measure.pi (fun i => (coordinateLaw v i : Measure ℝ))

/-- Construct the corrected finite conditional product directly from the raw
one-atom directional-density assumption. -/
noncomputable def paperDirectionalProductModel (k : ℕ)
    (atom : ProbabilityMeasure ℂ) (theta L : ℝ)
    (hdir : HasDirectionalConditionalDensity atom theta L) :
    DirectionalProductModel k := by
  let G := paperEverywhereDirectionalKernel atom theta L hdir
  letI : IsMarkovKernel G.kernel := G.isMarkov
  exact
    { vLaw := ProbabilityMeasure.pi
        (fun _ : Fin k => directionalOrthogonalLaw atom theta)
      coordinateLaw := fun v i =>
        ⟨G.kernel (v i), IsMarkovKernel.isProbabilityMeasure (κ := G.kernel) (v i)⟩
      conditionalULaw := directionalProductKernel G.kernel k
      conditionalULaw_isMarkov := directionalProductKernel_isMarkov G.kernel k
      conditionalULaw_eq_pi := by
        intro v
        exact directionalProductKernel_apply_eq_pi G.kernel v }

theorem paperDirectionalProductModel_intervalBound (k : ℕ)
    (atom : ProbabilityMeasure ℂ) (theta L : ℝ)
    (hdir : HasDirectionalConditionalDensity atom theta L)
    (v : Fin k → ℝ) (i : Fin k) :
    RealIntervalBound
      ((paperDirectionalProductModel k atom theta L hdir).coordinateLaw v i :
        Measure ℝ) (ENNReal.ofReal L) := by
  exact (paperEverywhereDirectionalKernel atom theta L hdir).intervalBound (v i)

namespace DirectionalProductModel

/-- Joint law of all orthogonal and directional coordinates. -/
noncomputable def jointMeasure {k : ℕ} (M : DirectionalProductModel k) :
    Measure ((Fin k → ℝ) × (Fin k → ℝ)) :=
  (M.vLaw : Measure (Fin k → ℝ)) ⊗ₘ M.conditionalULaw

theorem jointMeasure_isProbability {k : ℕ} (M : DirectionalProductModel k) :
    IsProbabilityMeasure M.jointMeasure := by
  let _ := M.conditionalULaw_isMarkov
  unfold jointMeasure
  infer_instance

end DirectionalProductModel

/-- Fiberwise heterogeneous multiaffine small-ball estimate, with complex
coefficients and real directional inputs. -/
theorem directionalProduct_fiber_smallBall_le
    {n : ℕ} (M : DirectionalProductModel (n + 1))
    {L : ℝ} (hL : 0 ≤ L)
    (hinterval : ∀ v i,
      RealIntervalBound (M.coordinateLaw v i : Measure ℝ) (ENNReal.ofReal L))
    (v : Fin (n + 1) → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (p : MultiAffine ℂ (n + 1)) (htop : 0 < ‖p.topCoeff‖) :
    M.conditionalULaw v
        (realInputClosedSmallBall p (‖p.topCoeff‖ * ρ ^ (n + 1))) ≤
      ((n + 1 : ℕ) : ℝ≥0∞) *
        ((4 : ℝ≥0∞) * ENNReal.ofReal L) * ENNReal.ofReal ρ := by
  rw [M.conditionalULaw_eq_pi v]
  exact pi_realInput_complex_multiaffine_bound
    (fun i => (M.coordinateLaw v i : Measure ℝ))
    (fun i => hinterval v i) hρ p htop

/-- Fiberwise zero-set removal and untruncated logarithmic estimate. -/
theorem directionalProduct_fiber_positiveLogLoss
    {n : ℕ} (M : DirectionalProductModel (n + 1))
    {L : ℝ} (hL : 0 ≤ L)
    (hinterval : ∀ v i,
      RealIntervalBound (M.coordinateLaw v i : Measure ℝ) (ENNReal.ofReal L))
    (v : Fin (n + 1) → ℝ) (p : MultiAffine ℂ (n + 1))
    (htop : 0 < ‖p.topCoeff‖) :
    M.conditionalULaw v {u | ‖realInputEval p u‖ = 0} = 0 ∧
      Integrable (fun u => positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p u‖)
        (M.conditionalULaw v) ∧
      ∫ u, positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p u‖
          ∂M.conditionalULaw v ≤
        (Real.log (max 1 (((n + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
          (((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  rw [M.conditionalULaw_eq_pi v]
  have h := pi_realInput_complex_positiveLogLoss
    (fun i => (M.coordinateLaw v i : Measure ℝ)) hL
    (fun i => hinterval v i) p htop
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩

/-- Joint lower-tail event for a measurable family of complex multiaffine
polynomials. -/
def directionalProductClosedSmallBall {n : ℕ}
    (p : (Fin (n + 1) → ℝ) → MultiAffine ℂ (n + 1)) (ρ : ℝ) :
    Set ((Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :=
  {z | ‖realInputEval (p z.1) z.2‖ ≤ ‖(p z.1).topCoeff‖ * ρ ^ (n + 1)}

/-- Averaged small-ball estimate for the corrected directional product. -/
theorem directionalProduct_joint_smallBall_le
    {n : ℕ} (M : DirectionalProductModel (n + 1))
    {L : ℝ} (hL : 0 ≤ L)
    (hinterval : ∀ v i,
      RealIntervalBound (M.coordinateLaw v i : Measure ℝ) (ENNReal.ofReal L))
    {ρ : ℝ} (hρ : 0 < ρ)
    (p : (Fin (n + 1) → ℝ) → MultiAffine ℂ (n + 1))
    (htop : ∀ v, 0 < ‖(p v).topCoeff‖)
    (hmeas : MeasurableSet (directionalProductClosedSmallBall p ρ)) :
    M.jointMeasure (directionalProductClosedSmallBall p ρ) ≤
      ENNReal.ofReal ((((n + 1 : ℕ) : ℝ) * (4 * L)) * ρ) := by
  let _ := M.conditionalULaw_isMarkov
  rw [DirectionalProductModel.jointMeasure, Measure.compProd_apply hmeas]
  calc
    (∫⁻ v, M.conditionalULaw v
        (Prod.mk v ⁻¹' directionalProductClosedSmallBall p ρ)
        ∂(M.vLaw : Measure (Fin (n + 1) → ℝ))) ≤
      ∫⁻ _v, ENNReal.ofReal ((((n + 1 : ℕ) : ℝ) * (4 * L)) * ρ)
        ∂(M.vLaw : Measure (Fin (n + 1) → ℝ)) := by
      apply lintegral_mono
      intro v
      change M.conditionalULaw v
          (realInputClosedSmallBall (p v)
            (‖(p v).topCoeff‖ * ρ ^ (n + 1))) ≤ _
      calc
        _ ≤ ((n + 1 : ℕ) : ℝ≥0∞) *
              ((4 : ℝ≥0∞) * ENNReal.ofReal L) * ENNReal.ofReal ρ :=
          directionalProduct_fiber_smallBall_le M hL hinterval v hρ (p v) (htop v)
        _ = ENNReal.ofReal ((((n + 1 : ℕ) : ℝ) * (4 * L)) * ρ) := by
          rw [← ENNReal.ofReal_natCast (n + 1),
            ← ENNReal.ofReal_ofNat 4,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
            ← ENNReal.ofReal_mul (Nat.cast_nonneg (n + 1)),
            ← ENNReal.ofReal_mul
              (mul_nonneg (Nat.cast_nonneg (n + 1))
                (mul_nonneg (by norm_num) hL))]
    _ = ENNReal.ofReal ((((n + 1 : ℕ) : ℝ) * (4 * L)) * ρ) := by simp

/-- Untruncated loss on the corrected joint directional space. -/
noncomputable def directionalProductPositiveLogLoss {n : ℕ}
    (p : (Fin (n + 1) → ℝ) → MultiAffine ℂ (n + 1))
    (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) : ℝ :=
  positiveLogLoss ‖(p z.1).topCoeff‖ ‖realInputEval (p z.1) z.2‖

/-- Joint zero-set removal and untruncated expected logarithmic loss under
the manuscript's heterogeneous conditional product. -/
theorem directionalProduct_joint_positiveLogLoss
    {n : ℕ} (M : DirectionalProductModel (n + 1))
    {L : ℝ} (hL : 0 ≤ L)
    (hinterval : ∀ v i,
      RealIntervalBound (M.coordinateLaw v i : Measure ℝ) (ENNReal.ofReal L))
    (p : (Fin (n + 1) → ℝ) → MultiAffine ℂ (n + 1))
    (htop : ∀ v, 0 < ‖(p v).topCoeff‖)
    (heval : Measurable (fun z :
      (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        ‖realInputEval (p z.1) z.2‖))
    (htopMeas : Measurable (fun v => ‖(p v).topCoeff‖)) :
    M.jointMeasure {z | ‖realInputEval (p z.1) z.2‖ = 0} = 0 ∧
      Integrable (fun z => directionalProductPositiveLogLoss p z) M.jointMeasure ∧
      ∫ z, directionalProductPositiveLogLoss p z ∂M.jointMeasure ≤
        (Real.log (max 1 (((n + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
          (((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  let _ := M.conditionalULaw_isMarkov
  let _ : IsProbabilityMeasure M.jointMeasure := M.jointMeasure_isProbability
  have hloss : Measurable (fun z => directionalProductPositiveLogLoss p z) := by
    unfold directionalProductPositiveLogLoss positiveLogLoss
    exact measurable_const.max
      ((Real.measurable_log.comp (htopMeas.comp measurable_fst)).sub
        (Real.measurable_log.comp heval))
  have hzeroMeas : MeasurableSet
      {z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) |
        ‖realInputEval (p z.1) z.2‖ = 0} :=
    measurableSet_eq_fun heval measurable_const
  have hfiberZero : ∀ v, M.conditionalULaw v
      (Prod.mk v ⁻¹' {z | ‖realInputEval (p z.1) z.2‖ = 0}) = 0 := by
    intro v
    exact (directionalProduct_fiber_positiveLogLoss M hL hinterval
      v (p v) (htop v)).1
  have hzero : M.jointMeasure {z | ‖realInputEval (p z.1) z.2‖ = 0} = 0 := by
    rw [DirectionalProductModel.jointMeasure,
      Measure.compProd_apply hzeroMeas]
    simp_rw [hfiberZero]
    simp
  refine ⟨hzero, ?_⟩
  have hkR : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  apply integrable_and_expectation_le_of_exponential_tail M.jointMeasure
    (fun z => directionalProductPositiveLogLoss p z) hloss
    (fun z => positiveLogLoss_nonneg _ _)
    (((n + 1 : ℕ) : ℝ) * (4 * L))
    (((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) (div_pos (by norm_num) hkR)
  intro t ht
  let ρ : ℝ := Real.exp (-t / ((n + 1 : ℕ) : ℝ))
  have hρ : 0 < ρ := Real.exp_pos _
  have hρpow : ρ ^ (n + 1) = Real.exp (-t) := by
    dsimp [ρ]
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp [ne_of_gt hkR]
  have hρrate : ρ = Real.exp
      ((-(((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) * t) := by
    dsimp [ρ]
    congr 1
    field_simp [ne_of_gt hkR]
    norm_num
  have htailMeas : MeasurableSet
      {z | t < directionalProductPositiveLogLoss p z} :=
    measurableSet_lt measurable_const hloss
  rw [DirectionalProductModel.jointMeasure,
    Measure.compProd_apply htailMeas]
  calc
    (∫⁻ v, M.conditionalULaw v
        (Prod.mk v ⁻¹' {z | t < directionalProductPositiveLogLoss p z})
        ∂(M.vLaw : Measure (Fin (n + 1) → ℝ))) ≤
      ∫⁻ _v, ENNReal.ofReal
        ((((n + 1 : ℕ) : ℝ) * (4 * L)) *
          Real.exp ((-(((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) * t))
        ∂(M.vLaw : Measure (Fin (n + 1) → ℝ)) := by
      apply lintegral_mono
      intro v
      change M.conditionalULaw v
          {u | t < positiveLogLoss ‖(p v).topCoeff‖
            ‖realInputEval (p v) u‖} ≤ _
      calc
        _ ≤ M.conditionalULaw v
            (realInputClosedSmallBall (p v)
              (‖(p v).topCoeff‖ * ρ ^ (n + 1))) := by
          apply measure_mono
          intro u hu
          change ‖realInputEval (p v) u‖ ≤
            ‖(p v).topCoeff‖ * ρ ^ (n + 1)
          have hle := positiveLogLoss_tail_imp_radius_le
            (htop v) (norm_nonneg _) ht hu
          simpa only [hρpow] using hle
        _ ≤ ((n + 1 : ℕ) : ℝ≥0∞) *
              ((4 : ℝ≥0∞) * ENNReal.ofReal L) * ENNReal.ofReal ρ :=
          directionalProduct_fiber_smallBall_le M hL hinterval
            v hρ (p v) (htop v)
        _ = ENNReal.ofReal
            ((((n + 1 : ℕ) : ℝ) * (4 * L)) *
              Real.exp ((-(((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) * t)) := by
          rw [hρrate, ← ENNReal.ofReal_natCast (n + 1),
            ← ENNReal.ofReal_ofNat 4,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
            ← ENNReal.ofReal_mul (Nat.cast_nonneg (n + 1)),
            ← ENNReal.ofReal_mul
              (mul_nonneg (Nat.cast_nonneg (n + 1))
                (mul_nonneg (by norm_num) hL))]
    _ = ENNReal.ofReal
        ((((n + 1 : ℕ) : ℝ) * (4 * L)) *
          Real.exp ((-(((1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) * t)) := by simp

/-- The old IID interface is a genuine special case: it applies when the
one-coordinate conditional law is constant in the orthogonal coordinate. -/
noncomputable def DirectionalIIDKernel.ofConstantConditional
    {V : Type*} [MeasurableSpace V] (k : ℕ)
    (vLaw : ProbabilityMeasure V) (ν : ProbabilityMeasure ℝ) :
    DirectionalIIDKernel V k where
  vLaw := vLaw
  coordinateLaw := fun _ => ν
  conditionalULaw := Kernel.const V (iidMeasure (ν : Measure ℝ) k)
  conditionalULaw_isMarkov := by
    let _ := iidMeasure_isProbability (ν : Measure ℝ) k
    infer_instance
  conditionalULaw_eq_iid := by intro v; simp

end CircularLawSection4
