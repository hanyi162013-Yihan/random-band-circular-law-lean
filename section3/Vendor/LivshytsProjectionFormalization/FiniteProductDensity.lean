/- Source snapshot: upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/FiniteProductDensity.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.LivshytsProjectionFormalization.ConcreteProjectionDensity
import Vendor.LivshytsProjectionFormalization.ProbabilityCore

/-!
# Finite products of marginal densities

This file proves that finitely many independent coordinates with prescribed
marginal densities have the corresponding product density. It also transports
that statement from ordinary function spaces to real and complex Euclidean
coordinate spaces.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set

namespace LivshytsProjectionFormalization

theorem lintegral_fin_coordinateProduct_eq_prod
    {n : Nat} {E : Fin n -> Type*}
    {mE : forall i, MeasurableSpace (E i)}
    {mu : forall i, Measure (E i)} [forall i, SigmaFinite (mu i)]
    (f : forall i, E i -> ENNReal) (hf : forall i, Measurable (f i)) :
    (∫⁻ x : forall i, E i, ∏ i, f i (x i) ∂Measure.pi mu) =
      ∏ i, ∫⁻ y, f i y ∂mu i := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (∫⁻ x : forall i, E i, ∏ i, f i (x i) ∂Measure.pi mu) =
            ∫⁻ z : E 0 × (forall j : Fin n, E (Fin.succ j)),
              f 0 z.1 * ∏ j : Fin n, f (Fin.succ j) (z.2 j)
              ∂((mu 0).prod (Measure.pi (fun j => mu (Fin.succ j)))) := by
          rw [← ((measurePreserving_piFinSuccAbove mu 0).symm).lintegral_comp_emb
            (MeasurableEquiv.piFinSuccAbove E 0).symm.measurableEmbedding]
          change (∫⁻ z : E 0 × (forall j : Fin n, E (Fin.succ j)),
            ∏ i, f i ((MeasurableEquiv.piFinSuccAbove E 0).symm z i)
            ∂((mu 0).prod (Measure.pi (fun j => mu (Fin.succ j))))) = _
          apply lintegral_congr
          intro z
          change (∏ i, f i (Fin.insertNth (0 : Fin (n + 1)) z.1 z.2 i)) = _
          rw [Fin.prod_univ_succ]
          exact congrArg₂ (fun x y : ℝ≥0∞ => x * y)
            (congrArg (f 0) (Fin.insertNth_apply_same (0 : Fin (n + 1)) z.1 z.2))
            (Finset.prod_congr rfl (fun (j : Fin n) _ => congrArg (f j.succ)
              (Fin.insertNth_apply_succAbove (0 : Fin (n + 1)) z.1 z.2 j)))
        _ = (∫⁻ y, f 0 y ∂mu 0) *
              (∫⁻ x, ∏ j : Fin n, f (Fin.succ j) (x j)
                ∂Measure.pi (fun j => mu (Fin.succ j))) := by
          exact lintegral_prod_mul (hf 0).aemeasurable
            (Finset.univ.measurable_prod fun j _ =>
              (hf (Fin.succ j)).comp (measurable_pi_apply j)).aemeasurable
        _ = (∫⁻ y, f 0 y ∂mu 0) *
              ∏ j : Fin n, ∫⁻ y, f (Fin.succ j) y ∂mu (Fin.succ j) := by
          rw [ih (fun j => f (Fin.succ j)) (fun j => hf (Fin.succ j))]
        _ = ∏ i, ∫⁻ y, f i y ∂mu i := by rw [Fin.prod_univ_succ]

theorem pi_withDensity_eq_withDensity_coordinateProduct
    {n : Nat} {E : Fin n -> Type*}
    {mE : forall i, MeasurableSpace (E i)}
    (mu : forall i, Measure (E i)) [forall i, SigmaFinite (mu i)]
    (f : forall i, E i -> ENNReal) (hf : forall i, Measurable (f i))
    (hf_top : forall i x, f i x ≠ ∞) :
    Measure.pi (fun i => (mu i).withDensity (f i)) =
      (Measure.pi mu).withDensity (fun x => ∏ i, f i (x i)) := by
  letI : forall i, SigmaFinite ((mu i).withDensity (f i)) :=
    fun i => SigmaFinite.withDensity_of_ne_top' (hf_top i)
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hfun :
      (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i)) =
        fun x => ∏ i, (s i).indicator (f i) (x i) := by
    funext x
    by_cases hx : forall i, x i ∈ s i
    · have hmem : x ∈ Set.univ.pi s := by
        simpa only [Set.mem_pi, Set.mem_univ, true_implies] using hx
      simp only [Set.indicator_of_mem hmem]
      apply Finset.prod_congr rfl
      intro i _
      rw [Set.indicator_of_mem (hx i)]
    · have hnotmem : x ∉ Set.univ.pi s := by
        simpa only [Set.mem_pi, Set.mem_univ, true_implies] using hx
      rw [Set.indicator_of_notMem hnotmem]
      obtain ⟨i, hi⟩ := not_forall.mp hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i)
        (Set.indicator_of_notMem hi (f i))).symm
  rw [hfun, lintegral_fin_coordinateProduct_eq_prod
    (fun i => (s i).indicator (f i))
    (fun i => (hf i).indicator (hs i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]

theorem map_withDensity_measurableEquiv_eq
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {mu : Measure A} {nu : Measure B}
    (e : A ≃ᵐ B) (he : MeasurePreserving e mu nu)
    (f : A -> ENNReal) (hf : Measurable f) :
    Measure.map e (mu.withDensity f) =
      nu.withDensity (f ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs]
  rw [withDensity_apply _ (e.measurable hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (e.measurable hs), ← lintegral_indicator hs]
  rw [← he.lintegral_comp ((hf.comp e.symm.measurable).indicator hs)]
  congr 1
  funext x
  simp only [Set.indicator, Function.comp_apply, e.symm_apply_apply, Set.mem_preimage]
  rfl

theorem independent_map_eq_pi_withDensity
    {Omega K : Type*} [MeasurableSpace Omega] [MeasureSpace K]
    [SigmaFinite (volume : Measure K)]
    {n : Nat} (P : Measure Omega) (X : Fin n -> Omega -> K)
    (hX : forall i, Measurable (X i))
    (hIndep : iIndepFun X P)
    (f : Fin n -> K -> ENNReal) (hf : forall i, Measurable (f i))
    (hf_top : forall i x, f i x ≠ ∞)
    (hmarginal : forall i,
      Measure.map (X i) P = volume.withDensity (f i)) :
    Measure.map (fun omega i => X i omega) P =
      volume.withDensity (fun x => ∏ i, f i (x i)) := by
  calc
    Measure.map (fun omega i => X i omega) P =
        Measure.pi (fun i => Measure.map (X i) P) :=
      hIndep.map_fun_eq_pi_map (fun i => (hX i).aemeasurable)
    _ = Measure.pi (fun i => volume.withDensity (f i)) := by
      congr 1
      funext i
      exact hmarginal i
    _ = (Measure.pi (fun _ : Fin n => (volume : Measure K))).withDensity
          (fun x => ∏ i, f i (x i)) :=
      pi_withDensity_eq_withDensity_coordinateProduct
        (fun _ : Fin n => (volume : Measure K)) f hf hf_top
    _ = volume.withDensity (fun x => ∏ i, f i (x i)) := by
      rw [← MeasureTheory.volume_pi]

private def sumFinEquivSigmaFinTwo (n : Nat) :
    Fin n ⊕ Fin n ≃ (Sigma fun _ : Fin n => Fin 2) where
  toFun
    | Sum.inl i => ⟨i, 0⟩
    | Sum.inr i => ⟨i, 1⟩
  invFun s := Fin.cases (Sum.inl s.1) (fun _ => Sum.inr s.1) s.2
  left_inv x := by
    cases x with
    | inl i => rfl
    | inr i => rfl
  right_inv s := by
    rcases s with ⟨i, j⟩
    fin_cases j <;> rfl

private noncomputable def plainComplexRealification (n : Nat) :
    (Fin n -> Complex) ≃ᵐ ((Sigma fun _ : Fin n => Fin 2) -> Real) :=
  (MeasurableEquiv.piCongrRight fun _ : Fin n => Complex.measurableEquivRealProd).trans <|
    (MeasurableEquiv.arrowProdEquivProdArrow Real Real (Fin n)).trans <|
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin n ⊕ Fin n => Real)).symm.trans <|
        MeasurableEquiv.piCongrLeft
          (fun _ : Sigma fun _ : Fin n => Fin 2 => Real)
          (sumFinEquivSigmaFinTwo n)

private noncomputable def complexEuclideanRealification (n : Nat) :
    EuclideanSpace Complex (Fin n) ≃ₗᵢ[Real]
      EuclideanSpace Real (Sigma fun _ : Fin n => Fin 2) :=
  (LinearIsometryEquiv.piLpCongrRight 2
    (fun _ : Fin n => Complex.orthonormalBasisOneI.repr)).trans
      (LinearIsometryEquiv.piLpCurry Real 2
        (fun _ : Fin n => fun _ : Fin 2 => Real)).symm

private theorem plainComplexRealification_measurePreserving (n : Nat) :
    MeasurePreserving (plainComplexRealification n) := by
  let hcoord : MeasurePreserving
      (fun z : Complex => Complex.measurableEquivRealProd z) :=
    Complex.volume_preserving_equiv_real_prod
  let hpi : MeasurePreserving
      (fun z : Fin n -> Complex =>
        fun i => Complex.measurableEquivRealProd (z i)) :=
    volume_preserving_pi (fun _ : Fin n => hcoord)
  let harrow := volume_measurePreserving_arrowProdEquivProdArrow Real Real (Fin n)
  let hsum := (volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Fin n ⊕ Fin n => Real)).symm
  let hreindex := volume_measurePreserving_piCongrLeft
    (fun _ : Sigma fun _ : Fin n => Fin 2 => Real)
    (sumFinEquivSigmaFinTwo n)
  exact hpi.trans (harrow.trans (hsum.trans hreindex))

private theorem complex_toLp_realification_commutes (n : Nat)
    (x : Fin n -> Complex) :
    complexEuclideanRealification n (WithLp.toLp 2 x) =
      WithLp.toLp 2 (plainComplexRealification n x) := by
  ext s
  rcases s with ⟨i, j⟩
  fin_cases j
  · change (x i).re = (x i).re
    rfl
  · change (x i).im = (x i).im
    rfl

theorem complex_volume_preserving_toLp (n : Nat) :
    MeasurePreserving (@WithLp.toLp 2 (Fin n -> Complex)) := by
  let p := plainComplexRealification n
  let q := complexEuclideanRealification n
  have hp : MeasurePreserving p := plainComplexRealification_measurePreserving n
  have hr : MeasurePreserving (@WithLp.toLp 2
      ((Sigma fun _ : Fin n => Fin 2) -> Real)) :=
    PiLp.volume_preserving_toLp (Sigma fun _ : Fin n => Fin 2)
  have hqSymm : MeasurePreserving q.symm :=
    LinearIsometryEquiv.measurePreserving q.symm
  have htotal := hqSymm.comp (hr.comp hp)
  have hfun :
      (q.symm ∘ ((@WithLp.toLp 2
        ((Sigma fun _ : Fin n => Fin 2) -> Real)) ∘ p)) =
        (@WithLp.toLp 2 (Fin n -> Complex)) := by
    funext x
    apply q.injective
    simp only [Function.comp_apply]
    rw [q.apply_symm_apply]
    exact (complex_toLp_realification_commutes n x).symm
  rw [← hfun]
  exact htotal

theorem independent_map_eq_coordinateProductDensity_of_volumePreserving
    {Omega k : Type*} [MeasurableSpace Omega] [RCLike k]
    {n : Nat} {K : Real} (P : Measure Omega)
    (X : Omega -> CoordinateSpace k n) (hX : Measurable X)
    (D : CoordinateDensityData k n K)
    (hIndep : iIndepFun (fun i omega => X omega i) P)
    (hmarginal : forall i,
      Measure.map (fun omega => X omega i) P =
        volume.withDensity (D.pdf i))
    (htoLp : MeasurePreserving (@WithLp.toLp 2 (Fin n -> k))) :
    Measure.map X P =
      volume.withDensity (coordinateProductDensity D.pdf) := by
  let e : (Fin n -> k) ≃ᵐ CoordinateSpace k n :=
    MeasurableEquiv.toLp 2 (Fin n -> k)
  let Y : Omega -> (Fin n -> k) := fun omega i => X omega i
  have hY : Measurable Y := by
    change Measurable (e.symm ∘ X)
    exact e.symm.measurable.comp hX
  have hplain :
      Measure.map Y P =
        volume.withDensity (fun x => ∏ i, D.pdf i (x i)) :=
    independent_map_eq_pi_withDensity P (fun i omega => X omega i)
      (fun i => (measurable_pi_apply i).comp hY) hIndep D.pdf D.measurable_pdf
      (fun i x => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (D.pdf_le i x)) hmarginal
  calc
    Measure.map X P = Measure.map e (Measure.map Y P) := by
      rw [Measure.map_map e.measurable hY]
      congr 1
    _ = Measure.map e
          (volume.withDensity (fun x => ∏ i, D.pdf i (x i))) := by rw [hplain]
    _ = volume.withDensity
          ((fun x => ∏ i, D.pdf i (x i)) ∘ e.symm) :=
      map_withDensity_measurableEquiv_eq e htoLp _
        (Finset.univ.measurable_prod fun i _ =>
          (D.measurable_pdf i).comp (measurable_pi_apply i))
    _ = volume.withDensity (coordinateProductDensity D.pdf) := by
      congr 1

theorem real_independent_map_eq_coordinateProductDensity
    {Omega : Type*} [MeasurableSpace Omega]
    {n : Nat} {K : Real} (P : Measure Omega)
    (X : Omega -> CoordinateSpace Real n) (hX : Measurable X)
    (D : CoordinateDensityData Real n K)
    (hIndep : iIndepFun (fun i omega => X omega i) P)
    (hmarginal : forall i,
      Measure.map (fun omega => X omega i) P =
        volume.withDensity (D.pdf i)) :
    Measure.map X P =
      volume.withDensity (coordinateProductDensity D.pdf) :=
  independent_map_eq_coordinateProductDensity_of_volumePreserving
    P X hX D hIndep hmarginal (PiLp.volume_preserving_toLp (Fin n))

theorem complex_independent_map_eq_coordinateProductDensity
    {Omega : Type*} [MeasurableSpace Omega]
    {n : Nat} {K : Real} (P : Measure Omega)
    (X : Omega -> CoordinateSpace Complex n) (hX : Measurable X)
    (D : CoordinateDensityData Complex n K)
    (hIndep : iIndepFun (fun i omega => X omega i) P)
    (hmarginal : forall i,
      Measure.map (fun omega => X omega i) P =
        volume.withDensity (D.pdf i)) :
    Measure.map X P =
      volume.withDensity (coordinateProductDensity D.pdf) :=
  independent_map_eq_coordinateProductDensity_of_volumePreserving
    P X hX D hIndep hmarginal (complex_volume_preserving_toLp n)

end LivshytsProjectionFormalization
