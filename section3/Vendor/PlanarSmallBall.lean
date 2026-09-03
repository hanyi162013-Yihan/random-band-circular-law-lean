/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/PlanarSmallBall.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.HighBandLSV
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Probability.Independence.Basic

/-!
# Elementary planar density bounds with a dimension loss

No projection or maximum-density theorem is assumed in this file. Independent
complex atoms may have dependent real and imaginary parts. A planar density
bound is expressed first as domination of the distribution by a multiple of
Lebesgue measure; a bounded Radon--Nikodym density is then constructed.

The final lemmas account for the extra dimension factor in the normal-event
entropy and in the column prefactor. They do not construct AppendixBInputs.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set Filter

noncomputable section

namespace HighBandLSV
namespace Planar

def mulLinear (a : Complex) : Complex →ₗ[Real] Complex where
  toFun z := a * z
  map_add' x y := mul_add a x y
  map_smul' r z := by simp [Algebra.smul_def, mul_left_comm]

theorem det_mulLinear (a : Complex) :
    LinearMap.det (mulLinear a) = ‖a‖ ^ 2 := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, mulLinear, Complex.sq_norm, Complex.normSq_apply]

/-- The Jacobian of multiplication by a nonzero complex number is its squared norm. -/
theorem map_volume_mul {a : Complex} (ha : a ≠ 0) :
    Measure.map (fun z : Complex => a * z) volume =
      ENNReal.ofReal ((‖a‖ ^ 2)⁻¹) • (volume : Measure Complex) := by
  have hdet : LinearMap.det (mulLinear a) ≠ 0 := by
    rw [det_mulLinear]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  change Measure.map (mulLinear a) volume = _
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure Complex) hdet,
    det_mulLinear, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg ‖a‖))]

/-- The usual bounded-density assumption implies domination of measures. -/
theorem withDensity_le_volume {f : Complex → ENNReal} {L : Real}
    (hf : ∀ᵐ z ∂(volume : Measure Complex), f z ≤ ENNReal.ofReal L) :
    volume.withDensity f ≤ ENNReal.ofReal L • (volume : Measure Complex) := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [withDensity_apply f hs]
  calc
    (∫⁻ z in s, f z ∂volume) ≤ ∫⁻ _z in s, ENNReal.ofReal L ∂volume :=
      lintegral_mono_ae (ae_restrict_of_ae hf)
    _ = (ENNReal.ofReal L • (volume : Measure Complex)) s := by simp

/-- A dominated finite measure has an actual measurable bounded density. -/
theorem exists_bounded_density {mu : Measure Complex} [IsFiniteMeasure mu]
    {L : Real} (hmu : mu ≤ ENNReal.ofReal L • (volume : Measure Complex)) :
    ∃ f : Complex → ENNReal, Measurable f ∧
      mu = volume.withDensity f ∧
      (∀ᵐ z ∂(volume : Measure Complex), f z ≤ ENNReal.ofReal L) := by
  have hac : mu ≪ (volume : Measure Complex) :=
    (Measure.absolutelyContinuous_of_le hmu).trans Measure.smul_absolutelyContinuous
  refine ⟨mu.rnDeriv volume, Measure.measurable_rnDeriv _ _,
    (Measure.withDensity_rnDeriv_eq mu volume hac).symm, ?_⟩
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv mu volume)
  intro s _ _
  calc
    (∫⁻ z in s, mu.rnDeriv volume z ∂volume) ≤ mu s := Measure.setLIntegral_rnDeriv_le s
    _ ≤ ENNReal.ofReal L * volume s := hmu s
    _ = ∫⁻ _z in s, ENNReal.ofReal L ∂(volume : Measure Complex) := by simp

/-- Exact density scaling, without a new analytic input. -/
theorem map_mul_le_volume {mu : Measure Complex} {L : Real}
    (hL : 0 ≤ L) (hmu : mu ≤ ENNReal.ofReal L • (volume : Measure Complex))
    {a : Complex} (ha : a ≠ 0) :
    Measure.map (fun z : Complex => a * z) mu ≤
      ENNReal.ofReal (L / ‖a‖ ^ 2) • (volume : Measure Complex) := by
  calc
    Measure.map (fun z : Complex => a * z) mu ≤
        Measure.map (fun z : Complex => a * z)
          (ENNReal.ofReal L • (volume : Measure Complex)) := Measure.map_mono hmu (by fun_prop)
    _ = ENNReal.ofReal L • Measure.map (fun z : Complex => a * z) volume :=
      Measure.map_smul _ _ _
    _ = ENNReal.ofReal (L / ‖a‖ ^ 2) • (volume : Measure Complex) := by
      rw [map_volume_mul ha, smul_smul, ← ENNReal.ofReal_mul hL]
      simp only [div_eq_mul_inv]

/-- Independent translation cannot increase a density upper bound. -/
theorem independent_add_le_volume
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] {X Y : Omega → Complex} {L : Real}
    (hX : Measurable X) (hY : Measurable Y) (hI : IndepFun X Y P)
    (hD : Measure.map X P ≤ ENNReal.ofReal L • (volume : Measure Complex)) :
    Measure.map (fun omega => X omega + Y omega) P ≤
      ENNReal.ofReal L • (volume : Measure Complex) := by
  letI : IsProbabilityMeasure (Measure.map X P) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  letI : IsProbabilityMeasure (Measure.map Y P) :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  apply Measure.le_iff.mpr
  intro s hs
  have hpre : MeasurableSet ((fun p : Complex × Complex => p.1 + p.2) ⁻¹' s) :=
    hs.preimage (by fun_prop)
  have heq : Measure.map (fun omega => X omega + Y omega) P =
      Measure.map (fun p : Complex × Complex => p.1 + p.2)
        ((Measure.map X P).prod (Measure.map Y P)) := by
    rw [← hI.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
      Measure.map_map (by fun_prop) (hX.prodMk hY)]
    rfl
  rw [heq, Measure.map_apply (by fun_prop) hs, Measure.prod_apply_symm hpre]
  calc
    (∫⁻ y, Measure.map X P
        ((fun x : Complex => (x, y)) ⁻¹'
          ((fun p : Complex × Complex => p.1 + p.2) ⁻¹' s)) ∂Measure.map Y P) ≤
        ∫⁻ _y, ENNReal.ofReal L * volume s ∂Measure.map Y P := by
      apply lintegral_mono
      intro y
      calc
        _ ≤ (ENNReal.ofReal L • (volume : Measure Complex))
            ((fun x => x + y) ⁻¹' s) := hD _
        _ = ENNReal.ofReal L * volume s := by
          simp only [Measure.smul_apply, smul_eq_mul, measure_preimage_add_right]
    _ = (ENNReal.ofReal L • (volume : Measure Complex)) s := by simp

/-- The entire sum is controlled by any one nonzero coefficient. -/
theorem sum_le_volume_of_coefficient
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] {m : Nat} (eta : Fin m → Omega → Complex)
    (heta : ∀ j, Measurable (eta j)) (hI : iIndepFun eta P)
    (a : Fin m → Complex) {L : Real} (hL : 0 ≤ L)
    (hD : ∀ j, Measure.map (eta j) P ≤ ENNReal.ofReal L • (volume : Measure Complex))
    (k : Fin m) (hak : a k ≠ 0) :
    Measure.map (fun omega => ∑ j, a j * eta j omega) P ≤
      ENNReal.ofReal (L / ‖a k‖ ^ 2) • (volume : Measure Complex) := by
  classical
  let Z : Fin m → Omega → Complex := fun j omega => a j * eta j omega
  have hZ : ∀ j, Measurable (Z j) := fun j => measurable_const.mul (heta j)
  have hZI : iIndepFun Z P := hI.comp (fun j x => a j * x)
    (fun _ => measurable_const.mul measurable_id)
  have hind' : IndepFun (∑ j ∈ Finset.univ.erase k, Z j) (Z k) P :=
    hZI.indepFun_finsetSum_of_notMem hZ (by simp)
  have hind : IndepFun (Z k) (fun omega => ∑ j ∈ Finset.univ.erase k, Z j omega) P := by
    have heq : (∑ j ∈ Finset.univ.erase k, Z j) =
        (fun omega => ∑ j ∈ Finset.univ.erase k, Z j omega) := by
      funext omega
      simp only [Finset.sum_apply]
    rw [heq] at hind'
    exact hind'.symm
  have hscale : Measure.map (Z k) P ≤
      ENNReal.ofReal (L / ‖a k‖ ^ 2) • (volume : Measure Complex) := by
    have h := map_mul_le_volume hL (hD k) hak
    rw [Measure.map_map (by fun_prop) (heta k)] at h
    exact h
  have hsum := independent_add_le_volume P (hZ k) (by fun_prop) hind hscale
  have heq : (fun omega => Z k omega + ∑ j ∈ Finset.univ.erase k, Z j omega) =
      (fun omega => ∑ j, a j * eta j omega) := by
    funext omega
    simpa only [Z] using Finset.add_sum_erase Finset.univ (fun j => Z j omega)
      (Finset.mem_univ k)
  rwa [heq] at hsum

/-- Choosing the largest coefficient costs at most the number of summands. -/
theorem exists_coefficient_density_bound {m : Nat} (a : Fin m → Complex)
    (ha : a ≠ 0) {L : Real} (hL : 0 ≤ L) :
    ∃ k : Fin m, a k ≠ 0 ∧
      L / ‖a k‖ ^ 2 ≤ (m : Real) * L / (∑ j, ‖a j‖ ^ 2) := by
  classical
  have hex : ∃ j, a j ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha (funext h)
  obtain ⟨j, hj⟩ := hex
  letI : Nonempty (Fin m) := ⟨j⟩
  obtain ⟨k, hk⟩ := Finite.exists_max (fun q : Fin m => ‖a q‖ ^ 2)
  have hE : 0 < ∑ q, ‖a q‖ ^ 2 := by
    apply Finset.sum_pos'
    · intro q _
      positivity
    · exact ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hj)⟩
  have hbound : (∑ q, ‖a q‖ ^ 2) ≤ (m : Real) * ‖a k‖ ^ 2 := by
    simpa using Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => hk q)
  have hak : a k ≠ 0 := by
    intro hzero
    simp only [hzero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hbound
    linarith
  refine ⟨k, hak, ?_⟩
  apply (div_le_div_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hak)) hE).mpr
  nlinarith [mul_le_mul_of_nonneg_left hbound hL]

/-- Elementary replacement for the dimension-free planar maximum-density lemma. -/
theorem sum_le_volume
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] {m : Nat} (eta : Fin m → Omega → Complex)
    (heta : ∀ j, Measurable (eta j)) (hI : iIndepFun eta P)
    (a : Fin m → Complex) (ha : a ≠ 0) {L : Real} (hL : 0 ≤ L)
    (hD : ∀ j, Measure.map (eta j) P ≤ ENNReal.ofReal L • (volume : Measure Complex)) :
    Measure.map (fun omega => ∑ j, a j * eta j omega) P ≤
      ENNReal.ofReal ((m : Real) * L / (∑ j, ‖a j‖ ^ 2)) •
        (volume : Measure Complex) := by
  obtain ⟨k, hak, hratio⟩ := exists_coefficient_density_bound a ha hL
  apply (sum_le_volume_of_coefficient P eta heta hI a hL hD k hak).trans
  intro s
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hratio) (le_rfl : volume s ≤ volume s)

/-- Actual density existence and its a.e. bound, not merely a small-ball hypothesis. -/
theorem sum_has_bounded_density
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] {m : Nat} (eta : Fin m → Omega → Complex)
    (heta : ∀ j, Measurable (eta j)) (hI : iIndepFun eta P)
    (a : Fin m → Complex) (ha : a ≠ 0) {L : Real} (hL : 0 ≤ L)
    (hD : ∀ j, Measure.map (eta j) P ≤ ENNReal.ofReal L • (volume : Measure Complex)) :
    ∃ f : Complex → ENNReal, Measurable f ∧
      Measure.map (fun omega => ∑ j, a j * eta j omega) P = volume.withDensity f ∧
      (∀ᵐ z ∂(volume : Measure Complex),
        f z ≤ ENNReal.ofReal ((m : Real) * L / (∑ j, ‖a j‖ ^ 2))) := by
  exact exists_bounded_density (sum_le_volume P eta heta hI a ha hL hD)

theorem small_ball_of_le_volume
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] {X : Omega → Complex} (hX : Measurable X)
    {D s : Real} (hD : 0 ≤ D) (hs : 0 ≤ s)
    (hbound : Measure.map X P ≤ ENNReal.ofReal D • (volume : Measure Complex))
    (w : Complex) :
    P {omega | ‖X omega - w‖ ≤ s} ≤ ENNReal.ofReal (min 1 (Real.pi * D * s ^ 2)) := by
  have hset : {omega | ‖X omega - w‖ ≤ s} = X ⁻¹' Metric.closedBall w s := by
    ext omega
    simp only [mem_setOf_eq, mem_preimage, Metric.mem_closedBall, dist_eq_norm]
  rw [hset, ← Measure.map_apply hX measurableSet_closedBall, ENNReal.ofReal_min]
  apply le_min
  · haveI : IsProbabilityMeasure (Measure.map X P) :=
      Measure.isProbabilityMeasure_map hX.aemeasurable
    calc
      Measure.map X P (Metric.closedBall w s) ≤ Measure.map X P Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = ENNReal.ofReal 1 := by simp
  · calc
      Measure.map X P (Metric.closedBall w s) ≤
          (ENNReal.ofReal D • (volume : Measure Complex)) (Metric.closedBall w s) := hbound _
      _ = ENNReal.ofReal (Real.pi * D * s ^ 2) := by
        have hpi : (NNReal.pi : ENNReal) = ENNReal.ofReal Real.pi :=
          ENNReal.ofReal_coe_nnreal.symm
        simp [Complex.volume_closedBall, ENNReal.ofReal_mul, ENNReal.ofReal_pow,
          hD, hs, hpi, Real.pi_pos.le, mul_comm, mul_left_comm, mul_assoc]

theorem sum_small_ball
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] {m : Nat} (eta : Fin m → Omega → Complex)
    (heta : ∀ j, Measurable (eta j)) (hI : iIndepFun eta P)
    (a : Fin m → Complex) (ha : a ≠ 0) {L s : Real} (hL : 0 ≤ L) (hs : 0 ≤ s)
    (hD : ∀ j, Measure.map (eta j) P ≤ ENNReal.ofReal L • (volume : Measure Complex))
    (w : Complex) :
    P {omega | ‖(∑ j, a j * eta j omega) - w‖ ≤ s} ≤
      ENNReal.ofReal (min 1 (Real.pi * ((m : Real) * L / (∑ j, ‖a j‖ ^ 2)) * s ^ 2)) := by
  exact small_ball_of_le_volume P (by fun_prop) (by positivity) hs
    (sum_le_volume P eta heta hI a ha hL hD) w

end Planar

/-! ## The additional dimension factor only costs one `N log N` term. -/

theorem dimension_loss_log_bound {N q : Nat} (hN : 1 ≤ N) (hq : q ≤ N) :
    Real.log ((N : Real) ^ q) ≤ (N : Real) * Real.log N := by
  rw [Real.log_pow]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hq)
    (Real.log_nonneg (by exact_mod_cast hN))

theorem dimension_loss_log_envelope {N J r : Nat} {p c W kappa : Real}
    (hN : 1 ≤ N) (hr : r * J ≤ N) (hp : 0 < p)
    (hscale : 0 ≤ (J : Real) * lambda N W kappa)
    (hraw : Real.log p ≤ -(c * W * lambda N W kappa) +
      24 * ((N : Real) * Real.log N + J * lambda N W kappa)) :
    Real.log ((N : Real) ^ (r * J) * p) ≤
      -(c * W * lambda N W kappa) +
        25 * ((N : Real) * Real.log N + J * lambda N W kappa) := by
  have hNp : (0 : Real) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  rw [Real.log_mul (pow_pos hNp _).ne' hp.ne']
  have hcost := dimension_loss_log_bound hN hr
  linarith

/-- Normal-event union and the extra factor `N^(rJ)`, with coefficient 28 rather than 27. -/
theorem dimension_loss_normal_union {N J r : Nat} {p c W kappa : Real}
    (hN : 1 ≤ N) (hJ : 0 < J) (hJN : J ≤ N) (hr : r * J ≤ N) (hp : 0 < p)
    (data : CorrectedSection5NumericalConditions N W kappa J 28 c)
    (hgrowth : 4 ≤ c * (N : Real) ^ (3 * kappa / 4))
    (hraw : Real.log p ≤ -(c * W * lambda N W kappa) +
      24 * ((N : Real) * Real.log N + J * lambda N W kappa)) :
    ((N * J * J : Nat) : Real) * (N : Real) ^ (r * J) * p ≤
      Real.exp (-(N : Real) ^ (1 + kappa / 4)) := by
  have hNp : (0 : Real) < N := data.N_pos
  have hJp : (0 : Real) < J := Nat.cast_pos.mpr hJ
  have hWp : 0 < W := data.W_pos
  have hlogN : 0 ≤ Real.log (N : Real) := Real.log_nonneg (by exact_mod_cast hN)
  have hscale : 0 ≤ (J : Real) * lambda N W kappa := by
    unfold lambda Section5Formalization.section5Scale
    positivity
  have hcost := dimension_loss_log_envelope hN hr hp hscale hraw
  have hlogJ : Real.log (J : Real) ≤ Real.log (N : Real) :=
    Real.log_le_log hJp (Nat.cast_le.mpr hJN)
  have hNlog : Real.log (N : Real) ≤ (N : Real) * Real.log N := by
    simpa using mul_le_mul_of_nonneg_right (show (1 : Real) ≤ N by exact_mod_cast hN) hlogN
  have hfactor : 0 < ((N * J * J : Nat) : Real) := by
    norm_cast
    positivity
  have hprod : 0 < ((N * J * J : Nat) : Real) * (N : Real) ^ (r * J) * p := by
    positivity
  have hlogfactor : Real.log (((N * J * J : Nat) : Real)) ≤
      3 * ((N : Real) * Real.log N) := by
    push_cast
    rw [Real.log_mul (mul_pos hNp hJp).ne' hJp.ne', Real.log_mul hNp.ne' hJp.ne']
    linarith
  have hentropy := data.entropy_versus_gain
  have hlog : Real.log (((N * J * J : Nat) : Real) * (N : Real) ^ (r * J) * p) ≤
      -(c / 4 * (N : Real) ^ (1 + kappa)) := by
    rw [mul_assoc, Real.log_mul hfactor.ne' (mul_pos (pow_pos hNp _) hp).ne']
    change -(c * W * lambda N W kappa) +
      28 * ((N : Real) * Real.log N + J * lambda N W kappa) ≤ _ at hentropy
    linarith
  have hsplit : (N : Real) ^ (1 + kappa) =
      (N : Real) ^ (3 * kappa / 4) * (N : Real) ^ (1 + kappa / 4) := by
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  have hpower : (N : Real) ^ (1 + kappa / 4) ≤ c / 4 * (N : Real) ^ (1 + kappa) := by
    rw [hsplit]
    have h := mul_le_mul_of_nonneg_right hgrowth
      (Real.rpow_nonneg hNp.le (1 + kappa / 4))
    nlinarith
  calc
    _ = Real.exp (Real.log (((N * J * J : Nat) : Real) * (N : Real) ^ (r * J) * p)) :=
      (Real.exp_log hprod).symm
    _ ≤ _ := Real.exp_le_exp.mpr (hlog.trans (neg_le_neg hpower))

def dimensionLossColumnPrefactor (N W : Real) : Real :=
  Real.sqrt N * columnPrefactor N W

/-- Doubling the bandwidth in the existing scalar bound absorbs the extra square-root factor. -/
theorem dimension_loss_final_gap {N W kappa : Real} (hN : 1 ≤ N) (hW : 1 ≤ W)
    (hbase : Real.log (columnPrefactor N (2 * W)) ≤
      Section5Formalization.finalExponentGap N (2 * W) kappa) :
    Real.log (dimensionLossColumnPrefactor N W) ≤
      Section5Formalization.finalExponentGap N W kappa := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hWp : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hPp : 0 < columnPrefactor N (2 * W) := by unfold columnPrefactor; positivity
  have hnewp : 0 < dimensionLossColumnPrefactor N W := by
    unfold dimensionLossColumnPrefactor columnPrefactor
    positivity
  have hfirst : Real.sqrt N ≤ columnPrefactor N (2 * W) := by
    unfold columnPrefactor
    calc
      Real.sqrt N = 1 * Real.sqrt N * 1 := by ring
      _ ≤ N * Real.sqrt N * Real.sqrt (2 * W) := by
        gcongr
        exact Real.one_le_sqrt.mpr (by linarith)
  have hsecond : columnPrefactor N W ≤ columnPrefactor N (2 * W) := by
    unfold columnPrefactor
    gcongr
    linarith
  have hcompare : dimensionLossColumnPrefactor N W ≤ (columnPrefactor N (2 * W)) ^ 2 := by
    unfold dimensionLossColumnPrefactor
    simpa only [pow_two] using mul_le_mul hfirst hsecond
      (by unfold columnPrefactor; positivity) hPp.le
  have hgap : 2 * Section5Formalization.finalExponentGap N (2 * W) kappa =
      Section5Formalization.finalExponentGap N W kappa := by
    unfold Section5Formalization.finalExponentGap
    field_simp
    <;> ring
  calc
    Real.log (dimensionLossColumnPrefactor N W) ≤
        Real.log ((columnPrefactor N (2 * W)) ^ 2) := Real.log_le_log hnewp hcompare
    _ = 2 * Real.log (columnPrefactor N (2 * W)) := by rw [Real.log_pow]; norm_num
    _ ≤ 2 * Section5Formalization.finalExponentGap N (2 * W) kappa := by linarith
    _ = _ := hgap

#print axioms Planar.sum_has_bounded_density
#print axioms Planar.sum_small_ball
#print axioms dimension_loss_normal_union
#print axioms dimension_loss_final_gap

end HighBandLSV
