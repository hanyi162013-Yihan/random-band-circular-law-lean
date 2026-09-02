import CircularLawSection4.DirectionalKernelConstruction
import CircularLawSection4.LIntegralFiniteProduct
import CircularLawSection4.IIDOperatorAffineSmallBall

/-!
# The finite directional product is the actual rotated IID atom law

This module identifies the finite heterogeneous conditional product constructed
from the manuscript's one-atom regular conditional law with the joint law of
the rotated coordinates of an IID atom vector.
-/

open scoped ENNReal MeasureTheory ProbabilityTheory BigOperators
open MeasureTheory Set ProbabilityTheory

noncomputable section

namespace CircularLawSection4

/-- The corrected directional joint law is a probability measure.  Registering
this theorem as an instance lets mathlib form its canonical conditional
distribution in subsequent statements. -/
noncomputable instance DirectionalProductModel.jointMeasure.instIsProbabilityMeasure
    {k : ℕ} (M : DirectionalProductModel k) :
    IsProbabilityMeasure M.jointMeasure := M.jointMeasure_isProbability

/-- A finite product of identical one-coordinate joint laws, regrouped into
the two coordinate vectors, is the joint law obtained from the heterogeneous
conditional product kernel. -/
theorem product_conditional_joint_law
    (k : ℕ) (μ : ProbabilityMeasure ℝ) (κ : Kernel ℝ ℝ)
    [IsMarkovKernel κ] :
    Measure.map (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin k))
        (Measure.pi (fun _ : Fin k => ((μ : Measure ℝ) ⊗ₘ κ))) =
      Measure.pi (fun _ : Fin k => (μ : Measure ℝ)) ⊗ₘ
        directionalProductKernel κ k := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin k)
  letI : IsMarkovKernel (directionalProductKernel κ k) :=
    directionalProductKernel_isMarkov κ k
  have hcoord : IsProbabilityMeasure ((μ : Measure ℝ) ⊗ₘ κ) := by
    infer_instance
  letI : IsProbabilityMeasure ((μ : Measure ℝ) ⊗ₘ κ) := hcoord
  have hpi :
      Measure.pi (fun _ : Fin k => ((μ : Measure ℝ) ⊗ₘ κ)) =
        Measure.map e.symm
          (Measure.pi (fun _ : Fin k => (μ : Measure ℝ)) ⊗ₘ
            directionalProductKernel κ k) := by
    apply Measure.pi_eq
    intro s hs
    have hrect : MeasurableSet (Set.pi Set.univ s) :=
      MeasurableSet.pi Set.countable_univ (fun i _ => hs i)
    rw [Measure.map_apply e.symm.measurable hrect]
    have hpre :
        e.symm ⁻¹' Set.pi Set.univ s =
          {z : (Fin k → ℝ) × (Fin k → ℝ) |
            ∀ i, (z.1 i, z.2 i) ∈ s i} := by
      ext z
      simp [e, MeasurableEquiv.arrowProdEquivProdArrow, Set.mem_pi]
    rw [hpre]
    have hjoint : MeasurableSet
        {z : (Fin k → ℝ) × (Fin k → ℝ) |
          ∀ i, (z.1 i, z.2 i) ∈ s i} := by
      rw [← hpre]
      exact hrect.preimage e.symm.measurable
    rw [Measure.compProd_apply hjoint]
    have hsection (v : Fin k → ℝ) :
        Prod.mk v ⁻¹'
            {z : (Fin k → ℝ) × (Fin k → ℝ) |
              ∀ i, (z.1 i, z.2 i) ∈ s i} =
          Set.pi Set.univ (fun i => Prod.mk (v i) ⁻¹' s i) := by
      ext u
      simp [Set.mem_pi]
    simp_rw [hsection, directionalProductKernel_apply_eq_pi, Measure.pi_pi]
    calc
      (∫⁻ v : Fin k → ℝ, ∏ i, κ (v i) (Prod.mk (v i) ⁻¹' s i)
          ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ))) =
        ∏ i, ∫⁻ x, κ x (Prod.mk x ⁻¹' s i) ∂(μ : Measure ℝ) :=
          lintegral_fin_prod_eq_prod
            (fun _ : Fin k => (μ : Measure ℝ))
            (fun i x => κ x (Prod.mk x ⁻¹' s i))
            (fun i => Kernel.measurable_kernel_prodMk_left (hs i))
      _ = ∏ i, ((μ : Measure ℝ) ⊗ₘ κ) (s i) := by
        congr 1
        funext i
        rw [Measure.compProd_apply (hs i)]
  calc
    Measure.map e
        (Measure.pi (fun _ : Fin k => ((μ : Measure ℝ) ⊗ₘ κ))) =
      Measure.map e (Measure.map e.symm
        (Measure.pi (fun _ : Fin k => (μ : Measure ℝ)) ⊗ₘ
          directionalProductKernel κ k)) := by rw [← hpi]
    _ = Measure.pi (fun _ : Fin k => (μ : Measure ℝ)) ⊗ₘ
          directionalProductKernel κ k := by
      rw [Measure.map_map e.measurable e.symm.measurable]
      simp [e]

/-- The constructed product kernel is not only a convenient fiber law: it is
the canonical regular conditional distribution of the directional vector
given the orthogonal vector, up to the unavoidable marginal-null set. -/
theorem DirectionalProductModel.condDistrib_snd_fst_ae_eq
    {k : ℕ} (M : DirectionalProductModel k) :
    condDistrib Prod.snd Prod.fst M.jointMeasure =ᵐ[(M.vLaw : Measure (Fin k → ℝ))]
      M.conditionalULaw := by
  let _ := M.conditionalULaw_isMarkov
  have hfst : M.jointMeasure.map Prod.fst =
      (M.vLaw : Measure (Fin k → ℝ)) := by
    change M.jointMeasure.fst = (M.vLaw : Measure (Fin k → ℝ))
    simp [DirectionalProductModel.jointMeasure]
  have hjoint :
      M.jointMeasure.map (fun z => (z.1, z.2)) =
        M.jointMeasure.map Prod.fst ⊗ₘ M.conditionalULaw := by
    calc
      M.jointMeasure.map (fun z => (z.1, z.2)) = M.jointMeasure := by
        simpa only [Prod.eta, Measure.map_id']
      _ = (M.vLaw : Measure (Fin k → ℝ)) ⊗ₘ M.conditionalULaw := rfl
      _ = M.jointMeasure.map Prod.fst ⊗ₘ M.conditionalULaw := by rw [hfst]
  have hcond := condDistrib_ae_eq_of_measure_eq_compProd
    (μ := M.jointMeasure) Prod.fst measurable_snd.aemeasurable hjoint
  rw [hfst] at hcond
  exact hcond

/-- The vector of pairs `(V_i,U_i)` obtained by rotating an atom vector. -/
def directionalPairVector (k : ℕ) (theta : ℝ) (x : Fin k → ℂ) :
    Fin k → ℝ × ℝ :=
  fun i => (directionalImagPart theta (x i),
    directionalRealPart theta (x i))

/-- The same rotated coordinates, regrouped as the pair `(V-vector,U-vector)`.
-/
def directionalSplitVector (k : ℕ) (theta : ℝ) (x : Fin k → ℂ) :
    (Fin k → ℝ) × (Fin k → ℝ) :=
  ((fun i => directionalImagPart theta (x i)),
    fun i => directionalRealPart theta (x i))

theorem measurable_directionalPairVector (k : ℕ) (theta : ℝ) :
    Measurable (directionalPairVector k theta) := by
  apply measurable_pi_lambda
  intro i
  exact ((continuous_directionalImagPart theta).measurable.prodMk
    (continuous_directionalRealPart theta).measurable).comp
      (measurable_pi_apply i)

theorem measurable_directionalSplitVector (k : ℕ) (theta : ℝ) :
    Measurable (directionalSplitVector k theta) := by
  exact (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin k)).measurable.comp
    (measurable_directionalPairVector k theta)

/-- Exact finite-vector disintegration for the manuscript's atom law.  This
closes the gap between merely constructing a kernel of the right shape and
proving that it is the conditional product governing the actual random row.
-/
theorem iidAtom_map_directionalSplitVector_eq_compProd
    (k : ℕ) (atom : ProbabilityMeasure ℂ) (theta L : ℝ)
    (hdir : HasDirectionalConditionalDensity atom theta L) :
    (iidMeasure (atom : Measure ℂ) k).map (directionalSplitVector k theta) =
      (paperDirectionalProductModel k atom theta L hdir).jointMeasure := by
  let pairMap : ℂ → ℝ × ℝ := fun z =>
    (directionalImagPart theta z, directionalRealPart theta z)
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin k)
  let G := paperEverywhereDirectionalKernel atom theta L hdir
  letI : IsMarkovKernel G.kernel := G.isMarkov
  change (iidMeasure (atom : Measure ℂ) k).map
      (directionalSplitVector k theta) =
    Measure.pi (fun _ : Fin k =>
      (directionalOrthogonalLaw atom theta : Measure ℝ)) ⊗ₘ
      directionalProductKernel G.kernel k
  have hpairMap : Measurable pairMap :=
    (continuous_directionalImagPart theta).measurable.prodMk
      (continuous_directionalRealPart theta).measurable
  have hpairVector : Measurable (directionalPairVector k theta) :=
    measurable_directionalPairVector k theta
  rw [iidMeasure_eq_pi]
  calc
    (Measure.pi (fun _ : Fin k => (atom : Measure ℂ))).map
        (directionalSplitVector k theta) =
      Measure.map e
        ((Measure.pi (fun _ : Fin k => (atom : Measure ℂ))).map
          (directionalPairVector k theta)) := by
        rw [Measure.map_map e.measurable hpairVector]
        rfl
    _ = Measure.map e
        (Measure.pi (fun _ : Fin k => (atom : Measure ℂ).map pairMap)) := by
      rw [show directionalPairVector k theta =
          (fun x i => pairMap (x i)) by rfl,
        Measure.pi_map_pi (fun _ => hpairMap.aemeasurable)]
    _ = Measure.map e
        (Measure.pi (fun _ : Fin k =>
          (directionalOrthogonalLaw atom theta : Measure ℝ) ⊗ₘ G.kernel)) := by
      congr 2
      funext i
      exact directionalAtom_map_pair_eq_compProd atom theta L hdir
    _ = Measure.pi (fun _ : Fin k =>
          (directionalOrthogonalLaw atom theta : Measure ℝ)) ⊗ₘ
        directionalProductKernel G.kernel k :=
      product_conditional_joint_law k (directionalOrthogonalLaw atom theta)
        G.kernel

end CircularLawSection4
