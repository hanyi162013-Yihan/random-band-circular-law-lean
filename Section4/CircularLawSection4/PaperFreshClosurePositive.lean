import CircularLawSection4.PaperIndicatorFreshSample
import CircularLawSection4.FreshClosure
import CircularLawSection4.PositiveLogMoment
import CircularLawSection4.OrderedCoefficientL2Contraction
import CircularLawSection4.PaperIsolatedFreshMonomial
import CircularLawSection4.OperatorAffinePositiveL2
import CircularLawSection4.PaperOperatorAffineL2
import CircularLawSection4.PaperOperatorAffineRealL2
import CircularLawSection4.ProductIntegralUniformBound

open scoped BigOperators Matrix Matrix.Norms.L2Operator ENNReal MeasureTheory
open Matrix MeasureTheory

noncomputable section

namespace CircularLawSection4

set_option maxHeartbeats 1200000

theorem norm_matrix_entry_le_l2_opNorm
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (i : m) (j : n) :
    ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ n := PiLp.single 2 j 1
  have hcoord :
      ‖((EuclideanSpace.equiv m ℂ).symm (A *ᵥ e)) i‖ ≤
        ‖(EuclideanSpace.equiv m ℂ).symm (A *ᵥ e)‖ :=
    PiLp.norm_apply_le _ i
  have hop := A.l2_opNorm_mulVec e
  calc
    ‖A i j‖ = ‖((EuclideanSpace.equiv m ℂ).symm (A *ᵥ e)) i‖ := by
      simp [e, Matrix.mulVec, apply_ite]
    _ ≤ ‖(EuclideanSpace.equiv m ℂ).symm (A *ᵥ e)‖ := hcoord
    _ ≤ ‖A‖ * ‖e‖ := hop
    _ = ‖A‖ := by simp [e]

theorem norm_trace_le_card_mul_l2_opNorm
    {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) :
    ‖Matrix.trace A‖ ≤ (Fintype.card m : ℝ) * ‖A‖ := by
  calc
    ‖Matrix.trace A‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : m, ‖A‖ := Finset.sum_le_sum fun i _ =>
      norm_matrix_entry_le_l2_opNorm A i i
    _ = (Fintype.card m : ℝ) * ‖A‖ := by simp

theorem norm_chronologicalProduct_le_prod
    {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    (xs : List (Matrix m m ℂ)) :
    ‖chronologicalProduct xs‖ ≤ (xs.map norm).prod := by
  induction xs with
  | nil => simp [chronologicalProduct]
  | cons A xs ih =>
      rw [chronologicalProduct_cons, List.map_cons, List.prod_cons]
      calc
        ‖chronologicalProduct xs * A‖ ≤
            ‖chronologicalProduct xs‖ * ‖A‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ (xs.map norm).prod * ‖A‖ :=
          mul_le_mul_of_nonneg_right ih (norm_nonneg A)
        _ = ‖A‖ * (xs.map norm).prod := mul_comm _ _

theorem measurable_matrix_mul
    {Ω m : Type*} [MeasurableSpace Ω] [Fintype m]
    (A B : Ω → Matrix m m ℂ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j))
    (hB : ∀ i j, Measurable (fun ω => B ω i j)) :
    ∀ i j, Measurable (fun ω => (A ω * B ω) i j) := by
  intro i j
  simp only [Matrix.mul_apply]
  fun_prop

theorem measurable_chronologicalProduct
    {Ω m : Type*} [MeasurableSpace Ω] [Fintype m] [DecidableEq m]
    (xs : List (Ω → Matrix m m ℂ))
    (hxs : ∀ A ∈ xs, ∀ i j, Measurable (fun ω => A ω i j)) :
    ∀ i j, Measurable (fun ω =>
      chronologicalProduct (xs.map fun A => A ω) i j) := by
  induction xs with
  | nil =>
      intro i j
      exact measurable_const
  | cons A xs ih =>
      intro i j
      simp only [List.map_cons, chronologicalProduct_cons]
      exact measurable_matrix_mul _ _
        (ih fun B hB => hxs B (by simp [hB]))
        (hxs A (by simp)) i j

theorem measurable_matrix_trace
    {Ω m : Type*} [MeasurableSpace Ω] [Fintype m]
    (A : Ω → Matrix m m ℂ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j)) :
    Measurable (fun ω => Matrix.trace (A ω)) := by
  unfold Matrix.trace
  exact Finset.measurable_sum Finset.univ fun i _ => hA i i

/-- Cauchy--Schwarz on a probability space in the exact one-function form
needed below. -/
theorem integrable_and_integral_le_sqrt_integral_sq_of_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hZsq : Integrable (fun ω => Z ω ^ 2) μ) :
    Integrable Z μ ∧ (∫ ω, Z ω ∂μ) ≤ √(∫ ω, Z ω ^ 2 ∂μ) := by
  have hmem : MemLp Z 2 μ :=
    (memLp_two_iff_integrable_sq hZ.aestronglyMeasurable).2 hZsq
  have hZint : Integrable Z μ := hmem.integrable one_le_two
  refine ⟨hZint, ?_⟩
  have hnonneg : 0 ≤ᵐ[μ] Z := ae_of_all μ hZ0
  have hone : 0 ≤ᵐ[μ] (fun _ : Ω => (1 : ℝ)) :=
    ae_of_all μ fun _ => zero_le_one
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) Real.HolderConjugate.two_two hnonneg hone
    (by simpa using hmem)
    (by simpa using
      (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ))
  simpa [Real.rpow_two, Real.sqrt_eq_rpow] using hcs

namespace PaperIndicatorWeights

variable {d : ℕ} {c₀ C₀ : ℝ}

private theorem freshExteriorIndex_nonempty (D : ℕ) (q : ExteriorDegree D) :
    Nonempty (ExteriorIndex D q) := by
  have hq : q.val ≤ D := Nat.le_of_lt_succ q.isLt
  obtain ⟨s, hs⟩ :
      ((Finset.univ : Finset (Fin D)).powersetCard q.val).Nonempty :=
    Finset.powersetCard_nonempty.2 (by simpa using hq)
  exact ⟨⟨s, (Finset.mem_powersetCard.1 hs).2⟩⟩

noncomputable def paperFreshTraceFactor (d : ℕ) : ℝ :=
  ∑ q : ExteriorDegree (d + 1),
    (Fintype.card (ExteriorIndex (d + 1) q) : ℝ)

theorem paperFreshTraceFactor_pos (d : ℕ) :
    0 < paperFreshTraceFactor d := by
  unfold paperFreshTraceFactor
  exact Finset.sum_pos (fun q _ => by
    exact_mod_cast Fintype.card_pos_iff.mpr (freshExteriorIndex_nonempty (d + 1) q))
    Finset.univ_nonempty

noncomputable def freshRowNormMajorant
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (z : ℂ) (rowAtoms : ResetLabel (d + 1) → ℂ) : ℝ :=
  (∑ ell, ‖profile.orderedResetWeight ell‖ * ‖rowAtoms ell‖) + ‖z‖

noncomputable def freshRowAtomSum
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (rowAtoms : ResetLabel (d + 1) → ℂ) : ℝ :=
  ∑ ell, ‖profile.orderedResetWeight ell‖ * ‖rowAtoms ell‖

theorem freshRowNormMajorant_eq
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (z : ℂ) (rowAtoms : ResetLabel (d + 1) → ℂ) :
    profile.freshRowNormMajorant z rowAtoms =
      profile.freshRowAtomSum rowAtoms + ‖z‖ := rfl

theorem freshRowNormMajorant_nonneg
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (z : ℂ) (rowAtoms : ResetLabel (d + 1) → ℂ) :
    0 ≤ profile.freshRowNormMajorant z rowAtoms := by
  exact add_nonneg (Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (norm_nonneg _)

/-- Normalization of the paper variance profile makes every reset weight a
contraction.  This is the deterministic input needed to compare the weighted
fresh-row atom sum with an unweighted IID sum. -/
theorem norm_orderedResetWeight_le_one
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (ell : ResetLabel (d + 1)) :
    ‖profile.orderedResetWeight ell‖ ≤ 1 := by
  have hq_le_one (s : Fin (d + 2)) : profile.q s ≤ 1 := by
    calc
      profile.q s ≤ ∑ j, profile.q j :=
        Finset.single_le_sum (fun j _ => (profile.q_pos hc₀ j).le)
          (Finset.mem_univ s)
      _ = 1 := profile.normalized
  cases ell with
  | none =>
      rw [orderedResetWeight, profile.norm_b]
      exact Real.sqrt_le_one.mpr (hq_le_one _)
  | some j =>
      rw [orderedResetWeight, profile.norm_b]
      exact Real.sqrt_le_one.mpr (hq_le_one _)

/-- The weighted sum of all `d+2` atoms in a fresh row has unit scaled
second moment whenever each atom does. -/
theorem integrable_freshRowAtomSum_div_sq_and_integral_le_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (rowAtoms : Ω → ResetLabel (d + 1) → ℂ)
    (hatoms : ∀ ell, Measurable (fun ω => rowAtoms ω ell))
    (hcoord : ∀ ell,
      Integrable (fun ω => ‖rowAtoms ω ell‖ ^ 2) μ ∧
        ∫ ω, ‖rowAtoms ω ell‖ ^ 2 ∂μ ≤ 1) :
    Integrable (fun ω =>
        (profile.freshRowAtomSum (rowAtoms ω) / (d + 2 : ℝ)) ^ 2) μ ∧
      ∫ ω, (profile.freshRowAtomSum (rowAtoms ω) / (d + 2 : ℝ)) ^ 2
          ∂μ ≤ 1 := by
  let X : ResetLabel (d + 1) → Ω → ℝ := fun ell ω =>
    ‖profile.orderedResetWeight ell‖ * ‖rowAtoms ω ell‖
  have hXmeas : ∀ ell, Measurable (X ell) := by
    intro ell
    exact measurable_const.mul (hatoms ell).norm
  have hXsqInt : ∀ ell, Integrable (fun ω => (X ell ω) ^ 2) μ := by
    intro ell
    have h := (hcoord ell).1.const_mul
      (‖profile.orderedResetWeight ell‖ ^ 2)
    simpa only [X] using h.congr (ae_of_all μ fun ω => by ring)
  have hXsq : ∀ ell, ∫ ω, (X ell ω) ^ 2 ∂μ ≤ 1 := by
    intro ell
    have hw0 : 0 ≤ ‖profile.orderedResetWeight ell‖ ^ 2 := sq_nonneg _
    have hw1 : ‖profile.orderedResetWeight ell‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (profile.orderedResetWeight ell),
        profile.norm_orderedResetWeight_le_one hc₀ ell]
    calc
      (∫ ω, (X ell ω) ^ 2 ∂μ) =
          ‖profile.orderedResetWeight ell‖ ^ 2 *
            ∫ ω, ‖rowAtoms ω ell‖ ^ 2 ∂μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with ω
        dsimp [X]
        ring
      _ ≤ ‖profile.orderedResetWeight ell‖ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (hcoord ell).2 hw0
      _ ≤ 1 := by simpa using hw1
  have h := integrable_normalized_sum_sq_and_integral_le_one
    μ X hXmeas hXsqInt hXsq
  simpa only [X, freshRowAtomSum, Fintype.card_option, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two]
    using h

theorem norm_freshExteriorRow_le_freshRowNormMajorant
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (q : ExteriorDegree (d + 1)) (t : Fin (d + 1)) :
    ‖profile.freshExteriorRow center z atoms q t‖ ≤
      profile.freshRowNormMajorant z (atoms t) := by
  classical
  unfold freshExteriorRow freshRowNormMajorant
  calc
    ‖(∑ ell : ResetLabel (d + 1),
          (profile.orderedResetWeight ell * atoms t ell) •
            orderedCoefficient d q ell) +
        ∑ ell : ResetLabel (d + 1),
          freshSpectralShift center z ell • orderedCoefficient d q ell‖
        ≤ ‖∑ ell : ResetLabel (d + 1),
          (profile.orderedResetWeight ell * atoms t ell) •
            orderedCoefficient d q ell‖ +
          ‖∑ ell : ResetLabel (d + 1),
            freshSpectralShift center z ell • orderedCoefficient d q ell‖ :=
      norm_add_le _ _
    _ ≤ (∑ ell : ResetLabel (d + 1),
          ‖profile.orderedResetWeight ell‖ * ‖atoms t ell‖) + ‖z‖ := by
      apply add_le_add
      · calc
          ‖∑ ell : ResetLabel (d + 1),
              (profile.orderedResetWeight ell * atoms t ell) •
                orderedCoefficient d q ell‖
              ≤ ∑ ell : ResetLabel (d + 1),
                ‖(profile.orderedResetWeight ell * atoms t ell) •
                  orderedCoefficient d q ell‖ := norm_sum_le _ _
          _ ≤ ∑ ell : ResetLabel (d + 1),
                ‖profile.orderedResetWeight ell‖ * ‖atoms t ell‖ := by
            apply Finset.sum_le_sum
            intro ell _
            rw [norm_smul, norm_mul]
            calc
              (‖profile.orderedResetWeight ell‖ * ‖atoms t ell‖) *
                    ‖orderedCoefficient d q ell‖
                  ≤ (‖profile.orderedResetWeight ell‖ * ‖atoms t ell‖) * 1 := by
                    gcongr
                    exact orderedCoefficient_l2_opNorm_le_one d q ell
              _ = ‖profile.orderedResetWeight ell‖ * ‖atoms t ell‖ := mul_one _
      · calc
          ‖∑ ell : ResetLabel (d + 1),
              freshSpectralShift center z ell • orderedCoefficient d q ell‖
              ≤ ∑ ell : ResetLabel (d + 1),
                ‖freshSpectralShift center z ell • orderedCoefficient d q ell‖ :=
            norm_sum_le _ _
          _ ≤ ∑ ell : ResetLabel (d + 1), ‖freshSpectralShift center z ell‖ := by
            apply Finset.sum_le_sum
            intro ell _
            rw [norm_smul]
            simpa using mul_le_of_le_one_right (norm_nonneg _)
              (orderedCoefficient_l2_opNorm_le_one d q ell)
          _ = ‖z‖ := by
            rw [Fintype.sum_option]
            simp only [freshSpectralShift, norm_zero, zero_add]
            rw [Finset.sum_eq_single center]
            · simp
            · intro j _ hj
              simp [hj]
            · simp

theorem measurable_freshExteriorRow_entry
    {Ω : Type*} [MeasurableSpace Ω]
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Ω → Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (hatoms : ∀ t ell, Measurable (fun ω => atoms ω t ell))
    (q : ExteriorDegree (d + 1)) (t : Fin (d + 1))
    (i j : ExteriorIndex (d + 1) q) :
    Measurable (fun ω =>
      profile.freshExteriorRow center z (atoms ω) q t i j) := by
  simp only [freshExteriorRow, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  apply Measurable.add
  · exact Finset.measurable_sum Finset.univ fun ell _ =>
      ((measurable_const.mul (hatoms t ell)).mul measurable_const)
  · exact measurable_const

theorem norm_paperIndicatorFreshZ_le
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ) :
    ‖profile.paperIndicatorFreshZ center z atoms B‖ ≤
      paperFreshTraceFactor d * exteriorFamilyMaxL2OpNorm B *
        ∏ t : Fin (d + 1), profile.freshRowNormMajorant z (atoms t) := by
  classical
  let P : ℝ := ∏ t : Fin (d + 1), profile.freshRowNormMajorant z (atoms t)
  have hP : 0 ≤ P := Finset.prod_nonneg fun t _ =>
    profile.freshRowNormMajorant_nonneg z (atoms t)
  have hBq : ∀ q : ExteriorDegree (d + 1),
      ‖B q‖ ≤ exteriorFamilyMaxL2OpNorm B := by
    intro q
    unfold exteriorFamilyMaxL2OpNorm
    exact Finset.le_sup' (fun r : ExteriorDegree (d + 1) => ‖B r‖)
      (Finset.mem_univ q)
  have hQ : ∀ q : ExteriorDegree (d + 1),
      ‖chronologicalProduct
          (List.ofFn fun t : Fin (d + 1) =>
            profile.freshExteriorRow center z atoms q t)‖ ≤ P := by
    intro q
    letI : Nonempty (ExteriorIndex (d + 1) q) :=
      freshExteriorIndex_nonempty (d + 1) q
    calc
      ‖chronologicalProduct
          (List.ofFn fun t : Fin (d + 1) =>
            profile.freshExteriorRow center z atoms q t)‖
          ≤ (List.ofFn fun t : Fin (d + 1) =>
              ‖profile.freshExteriorRow center z atoms q t‖).prod := by
            simpa only [List.map_ofFn, Function.comp_def] using
              norm_chronologicalProduct_le_prod
                (List.ofFn fun t : Fin (d + 1) =>
                  profile.freshExteriorRow center z atoms q t)
      _ ≤ (List.ofFn fun t : Fin (d + 1) =>
              profile.freshRowNormMajorant z (atoms t)).prod := by
            simp only [List.prod_ofFn]
            exact Finset.prod_le_prod
              (fun t _ => norm_nonneg
                (profile.freshExteriorRow center z atoms q t))
              (fun t _ => profile.norm_freshExteriorRow_le_freshRowNormMajorant
                center z atoms q t)
      _ = P := by
        rw [List.prod_ofFn]
  unfold paperIndicatorFreshZ
  calc
    ‖∑ q : ExteriorDegree (d + 1), (-1 : ℂ) ^ q.val *
        Matrix.trace (B q * chronologicalProduct
          (List.ofFn fun t : Fin (d + 1) =>
            profile.freshExteriorRow center z atoms q t))‖
        ≤ ∑ q : ExteriorDegree (d + 1),
          ‖(-1 : ℂ) ^ q.val * Matrix.trace (B q * chronologicalProduct
            (List.ofFn fun t : Fin (d + 1) =>
              profile.freshExteriorRow center z atoms q t))‖ := norm_sum_le _ _
    _ ≤ ∑ q : ExteriorDegree (d + 1),
        (Fintype.card (ExteriorIndex (d + 1) q) : ℝ) *
          exteriorFamilyMaxL2OpNorm B * P := by
      apply Finset.sum_le_sum
      intro q _
      letI : Nonempty (ExteriorIndex (d + 1) q) :=
        freshExteriorIndex_nonempty (d + 1) q
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      calc
        ‖Matrix.trace (B q * chronologicalProduct
            (List.ofFn fun t : Fin (d + 1) =>
              profile.freshExteriorRow center z atoms q t))‖
            ≤ (Fintype.card (ExteriorIndex (d + 1) q) : ℝ) *
              ‖B q * chronologicalProduct
                (List.ofFn fun t : Fin (d + 1) =>
                  profile.freshExteriorRow center z atoms q t)‖ :=
          norm_trace_le_card_mul_l2_opNorm _
        _ ≤ (Fintype.card (ExteriorIndex (d + 1) q) : ℝ) *
              (‖B q‖ * ‖chronologicalProduct
                (List.ofFn fun t : Fin (d + 1) =>
                  profile.freshExteriorRow center z atoms q t)‖) := by
          gcongr
          exact Matrix.l2_opNorm_mul _ _
        _ ≤ (Fintype.card (ExteriorIndex (d + 1) q) : ℝ) *
              (exteriorFamilyMaxL2OpNorm B * P) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul (hBq q) (hQ q) (norm_nonneg _)
              ((norm_nonneg (B q)).trans (hBq q))
          · positivity
        _ = (Fintype.card (ExteriorIndex (d + 1) q) : ℝ) *
              exteriorFamilyMaxL2OpNorm B * P := by ring
    _ = paperFreshTraceFactor d * exteriorFamilyMaxL2OpNorm B *
          ∏ t : Fin (d + 1), profile.freshRowNormMajorant z (atoms t) := by
      simp only [← Finset.sum_mul, paperFreshTraceFactor, P]

/-- Measurability of the norm of the actual alternating fresh trace from
coordinatewise measurability of all row atoms. -/
theorem measurable_norm_paperIndicatorFreshZ
    {Ω : Type*} [MeasurableSpace Ω]
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Ω → Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (hatoms : ∀ t ell, Measurable (fun ω => atoms ω t ell))
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ) :
    Measurable (fun ω =>
      ‖profile.paperIndicatorFreshZ center z (atoms ω) B‖) := by
  apply Measurable.norm
  unfold paperIndicatorFreshZ
  apply Finset.measurable_sum
  intro q _
  apply measurable_const.mul
  apply measurable_matrix_trace
  apply measurable_matrix_mul
  · intro i j
    exact measurable_const
  · have hp := measurable_chronologicalProduct
        (List.ofFn fun t : Fin (d + 1) => fun ω =>
          profile.freshExteriorRow center z (atoms ω) q t)
        (by
          intro A hA i j
          simp only [List.mem_ofFn] at hA
          obtain ⟨t, rfl⟩ := hA
          exact profile.measurable_freshExteriorRow_entry
            center z atoms hatoms q t i j)
    simpa only [List.map_ofFn, Function.comp_def] using hp

/-- The positive logarithmic half of one actual paper fresh block.  The
only probabilistic input is a uniform scaled second-moment estimate for the
weighted atom sum in each row. -/
theorem integrable_and_integral_paperIndicatorFreshZ_logExcess_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Ω → Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (hatoms : ∀ t ell, Measurable (fun ω => atoms ω t ell))
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < exteriorFamilyMaxL2OpNorm B)
    (hZpos : ∀ᵐ ω ∂μ,
      0 < ‖profile.paperIndicatorFreshZ center z (atoms ω) B‖)
    (rowScale V : ℝ) (hrowScale : 1 ≤ rowScale) (hV : 0 ≤ V)
    (hscaledInt : ∀ t : Fin (d + 1),
      Integrable (fun ω =>
        (profile.freshRowAtomSum (atoms ω t) / rowScale) ^ 2) μ)
    (hscaled : ∀ t : Fin (d + 1),
      ∫ ω, (profile.freshRowAtomSum (atoms ω t) / rowScale) ^ 2 ∂μ ≤ V) :
    Integrable (fun ω =>
        logExcess (exteriorFamilyMaxL2OpNorm B)
          ‖profile.paperIndicatorFreshZ center z (atoms ω) B‖) μ ∧
      ∫ ω, logExcess (exteriorFamilyMaxL2OpNorm B)
            ‖profile.paperIndicatorFreshZ center z (atoms ω) B‖ ∂μ ≤
        Real.posLog (paperFreshTraceFactor d) +
          (d + 1 : ℝ) *
            Real.sqrt (3 * (Real.log rowScale) ^ 2 + 3 * V + 3 * ‖z‖ ^ 2) := by
  classical
  let C : ℝ := 3 * (Real.log rowScale) ^ 2 + 3 * V + 3 * ‖z‖ ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hSmeas : ∀ t : Fin (d + 1),
      Measurable (fun ω => profile.freshRowAtomSum (atoms ω t)) := by
    intro t
    unfold freshRowAtomSum
    fun_prop
  have hrowSq : ∀ t : Fin (d + 1),
      Integrable (fun ω =>
          (Real.posLog (profile.freshRowNormMajorant z (atoms ω t))) ^ 2) μ ∧
        ∫ ω, (Real.posLog
            (profile.freshRowNormMajorant z (atoms ω t))) ^ 2 ∂μ ≤ C := by
    intro t
    simpa only [Real.posLog_apply, freshRowNormMajorant_eq, C] using
      integrable_and_integral_positiveLogSquare_le_of_scaledSecondMoment
        μ (fun ω => profile.freshRowAtomSum (atoms ω t)) (hSmeas t)
        (fun ω => Finset.sum_nonneg fun _ _ =>
          mul_nonneg (norm_nonneg _) (norm_nonneg _))
        ‖z‖ rowScale V (norm_nonneg _) hrowScale
        (hscaledInt t) (hscaled t)
  have hrow : ∀ t : Fin (d + 1),
      Integrable (fun ω =>
          Real.posLog (profile.freshRowNormMajorant z (atoms ω t))) μ ∧
        ∫ ω, Real.posLog
            (profile.freshRowNormMajorant z (atoms ω t)) ∂μ ≤ Real.sqrt C := by
    intro t
    let G : Ω → ℝ := fun ω =>
      Real.posLog (profile.freshRowNormMajorant z (atoms ω t))
    have hGmeas : Measurable G := by
      dsimp [G]
      apply Real.continuous_posLog.measurable.comp
      change Measurable (fun ω =>
        profile.freshRowAtomSum (atoms ω t) + ‖z‖)
      exact (hSmeas t).add measurable_const
    obtain ⟨hGint, hGcs⟩ :=
      integrable_and_integral_le_sqrt_integral_sq_of_nonneg μ G hGmeas
        (fun _ => Real.posLog_nonneg) (hrowSq t).1
    refine ⟨hGint, hGcs.trans ?_⟩
    exact Real.sqrt_le_sqrt (hrowSq t).2
  let E : Ω → ℝ := fun ω =>
    logExcess (exteriorFamilyMaxL2OpNorm B)
      ‖profile.paperIndicatorFreshZ center z (atoms ω) B‖
  let D : Ω → ℝ := fun ω =>
    Real.posLog (paperFreshTraceFactor d) +
      ∑ t : Fin (d + 1),
        Real.posLog (profile.freshRowNormMajorant z (atoms ω t))
  have hZmeas : Measurable (fun ω =>
      ‖profile.paperIndicatorFreshZ center z (atoms ω) B‖) := by
    exact profile.measurable_norm_paperIndicatorFreshZ
      center z atoms hatoms B
  have hEmeas : Measurable E := by
    dsimp [E]
    exact measurable_logExcess _ hZmeas
  have hDint : Integrable D μ := by
    dsimp [D]
    exact (integrable_const _).add
      (integrable_finsetSum Finset.univ fun t _ => (hrow t).1)
  have hpoint : E ≤ᵐ[μ] D := by
    filter_upwards [hZpos] with ω hRpos
    let R : ℝ := ‖profile.paperIndicatorFreshZ center z (atoms ω) B‖
    let T : ℝ := paperFreshTraceFactor d *
      ∏ t : Fin (d + 1), max 1 (profile.freshRowNormMajorant z (atoms ω t))
    have hprod : 0 < ∏ t : Fin (d + 1),
        max 1 (profile.freshRowNormMajorant z (atoms ω t)) :=
      Finset.prod_pos fun _ _ => lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hT : 0 < T := mul_pos (paperFreshTraceFactor_pos d) hprod
    have hR : R ≤ exteriorFamilyMaxL2OpNorm B * T := by
      dsimp [R, T]
      calc
        ‖profile.paperIndicatorFreshZ center z (atoms ω) B‖ ≤
            paperFreshTraceFactor d * exteriorFamilyMaxL2OpNorm B *
              ∏ t : Fin (d + 1),
                profile.freshRowNormMajorant z (atoms ω t) :=
          profile.norm_paperIndicatorFreshZ_le center z (atoms ω) B
        _ ≤ paperFreshTraceFactor d * exteriorFamilyMaxL2OpNorm B *
              ∏ t : Fin (d + 1),
                max 1 (profile.freshRowNormMajorant z (atoms ω t)) := by
          apply mul_le_mul_of_nonneg_left
          · exact Finset.prod_le_prod
              (fun t _ => profile.freshRowNormMajorant_nonneg z (atoms ω t))
              (fun t _ => le_max_right _ _)
          · exact mul_nonneg (paperFreshTraceFactor_pos d).le
              hB.le
        _ = exteriorFamilyMaxL2OpNorm B *
              (paperFreshTraceFactor d *
                ∏ t : Fin (d + 1),
                  max 1 (profile.freshRowNormMajorant z (atoms ω t))) := by ring
    calc
      E ω ≤ Real.posLog T := by
        simpa only [E, R, Real.posLog_apply] using
          logExcess_le_max_zero_log_of_le_scale_mul hB hRpos hT hR
      _ ≤ Real.posLog (paperFreshTraceFactor d) +
          Real.posLog (∏ t : Fin (d + 1),
            max 1 (profile.freshRowNormMajorant z (atoms ω t))) := Real.posLog_mul
      _ ≤ Real.posLog (paperFreshTraceFactor d) +
          ∑ t : Fin (d + 1),
            Real.posLog (max 1
              (profile.freshRowNormMajorant z (atoms ω t))) := by
        exact add_le_add le_rfl (by
          simpa using (Real.posLog_prod Finset.univ
            (fun t : Fin (d + 1) =>
              max 1 (profile.freshRowNormMajorant z (atoms ω t)))))
      _ = Real.posLog (paperFreshTraceFactor d) +
          ∑ t : Fin (d + 1),
            Real.posLog (profile.freshRowNormMajorant z (atoms ω t)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro t _
        have hm0 : 0 ≤ max 1
            (profile.freshRowNormMajorant z (atoms ω t)) :=
          zero_le_one.trans (le_max_left _ _)
        have hm1 : 1 ≤ |max 1
            (profile.freshRowNormMajorant z (atoms ω t))| := by
          rw [abs_of_nonneg hm0]
          exact le_max_left _ _
        calc
          Real.posLog (max 1
              (profile.freshRowNormMajorant z (atoms ω t))) =
              Real.log (max 1
                (profile.freshRowNormMajorant z (atoms ω t))) :=
            Real.posLog_eq_log hm1
          _ = Real.posLog
              (profile.freshRowNormMajorant z (atoms ω t)) :=
            (Real.posLog_eq_log_max_one
              (profile.freshRowNormMajorant_nonneg z (atoms ω t))).symm
      _ = D ω := rfl
  have hEint : Integrable E μ := by
    apply hDint.mono' hEmeas.aestronglyMeasurable
    filter_upwards [hpoint] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hω
    · exact logExcess_nonneg _ _
  refine ⟨hEint, ?_⟩
  calc
    (∫ ω, E ω ∂μ) ≤ ∫ ω, D ω ∂μ :=
      integral_mono_ae hEint hDint hpoint
    _ = Real.posLog (paperFreshTraceFactor d) +
          ∑ t : Fin (d + 1),
            ∫ ω, Real.posLog
              (profile.freshRowNormMajorant z (atoms ω t)) ∂μ := by
      dsimp [D]
      rw [integral_add (integrable_const _) <|
        integrable_finsetSum Finset.univ fun t _ => (hrow t).1]
      rw [integral_const, integral_finsetSum Finset.univ
        (fun t _ => (hrow t).1)]
      simp
    _ ≤ Real.posLog (paperFreshTraceFactor d) +
          ∑ _t : Fin (d + 1), Real.sqrt C := by
      gcongr with t
      exact (hrow t).2
    _ = Real.posLog (paperFreshTraceFactor d) +
          (d + 1 : ℝ) * Real.sqrt C := by simp
    _ = Real.posLog (paperFreshTraceFactor d) +
          (d + 1 : ℝ) *
            Real.sqrt (3 * (Real.log rowScale) ^ 2 + 3 * V + 3 * ‖z‖ ^ 2) := rfl

/-! ### Literal flat IID sample specializations -/

/-- Every complex atom in an actual flat paper fresh block is a measurable
coordinate projection. -/
theorem measurable_paperIndicatorFreshAtoms
    (N d : ℕ) [NeZero N] (start : ZMod N)
    (t : Fin (d + 1)) (ell : ResetLabel (d + 1)) :
    Measurable (fun ω : Fin (N * (d + 2)) → ℂ =>
      paperIndicatorFreshAtoms N d start ω t ell) := by
  cases ell with
  | none =>
      change Measurable (fun ω : Fin (N * (d + 2)) → ℂ =>
        ω (paperIndicatorFlatIndex N d
          (paperIndicatorFreshRowSite N d start t) (Fin.last (d + 1))))
      exact measurable_pi_apply _
  | some j =>
      change Measurable (fun ω : Fin (N * (d + 2)) → ℂ =>
        ω (paperIndicatorFlatIndex N d
          (paperIndicatorFreshRowSite N d start t) j.castSucc))
      exact measurable_pi_apply _

/-- Positive logarithmic half for the genuine complex flat sample used by
the random-matrix model.  No row-independence is assumed here: the estimate
uses only the IID coordinate second moment. -/
theorem complex_paperIndicatorFlatFreshZ_logExcess_le
    (N d : ℕ) [NeZero N] {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ) (start : ZMod N)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < exteriorFamilyMaxL2OpNorm B)
    (ν : Measure ℂ) [SFinite ν] [IsProbabilityMeasure ν]
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1)
    (hZpos : ∀ᵐ ω ∂paperIndicatorSampleMeasure N d ν,
      0 < ‖profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtoms N d start ω) B‖) :
    Integrable (fun ω =>
        logExcess (exteriorFamilyMaxL2OpNorm B)
          ‖profile.paperIndicatorFreshZ center z
            (paperIndicatorFreshAtoms N d start ω) B‖)
      (paperIndicatorSampleMeasure N d ν) ∧
      ∫ ω, logExcess (exteriorFamilyMaxL2OpNorm B)
          ‖profile.paperIndicatorFreshZ center z
            (paperIndicatorFreshAtoms N d start ω) B‖
          ∂paperIndicatorSampleMeasure N d ν ≤
        Real.posLog (paperFreshTraceFactor d) +
          (d + 1 : ℝ) * Real.sqrt
            (3 * (Real.log (d + 2 : ℝ)) ^ 2 + 3 + 3 * ‖z‖ ^ 2) := by
  letI : IsProbabilityMeasure (paperIndicatorSampleMeasure N d ν) := by
    simpa only [paperIndicatorSampleMeasure] using
      iidMeasure_isProbability ν (N * (d + 2))
  have hcoord (t : Fin (d + 1)) (ell : ResetLabel (d + 1)) :
      Integrable (fun ω : Fin (N * (d + 2)) → ℂ =>
          ‖paperIndicatorFreshAtoms N d start ω t ell‖ ^ 2)
          (paperIndicatorSampleMeasure N d ν) ∧
        ∫ ω : Fin (N * (d + 2)) → ℂ,
            ‖paperIndicatorFreshAtoms N d start ω t ell‖ ^ 2
              ∂paperIndicatorSampleMeasure N d ν ≤ 1 := by
    cases ell with
    | none =>
        simpa only [paperIndicatorSampleMeasure,
          paperIndicatorFreshAtoms_none, paperIndicatorXi_apply] using
          iidMeasure_coordinate_norm_sq_integrable_and_integral_le_one
            (paperIndicatorFlatIndex N d
              (paperIndicatorFreshRowSite N d start t) (Fin.last (d + 1)))
            hνInt hνSecond
    | some j =>
        simpa only [paperIndicatorSampleMeasure,
          paperIndicatorFreshAtoms_some, paperIndicatorXi_apply] using
          iidMeasure_coordinate_norm_sq_integrable_and_integral_le_one
            (paperIndicatorFlatIndex N d
              (paperIndicatorFreshRowSite N d start t) j.castSucc)
            hνInt hνSecond
  have hscaled (t : Fin (d + 1)) :=
    profile.integrable_freshRowAtomSum_div_sq_and_integral_le_one
      (paperIndicatorSampleMeasure N d ν) hc₀
      (fun ω ell => paperIndicatorFreshAtoms N d start ω t ell)
      (fun ell => measurable_paperIndicatorFreshAtoms N d start t ell)
      (hcoord t)
  have hrowScale : (1 : ℝ) ≤ (d + 2 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (d + 1))
  simpa only [Nat.cast_add, Nat.cast_ofNat, mul_one] using
    profile.integrable_and_integral_paperIndicatorFreshZ_logExcess_le
      (paperIndicatorSampleMeasure N d ν) center z
      (fun ω => paperIndicatorFreshAtoms N d start ω)
      (fun t ell => measurable_paperIndicatorFreshAtoms N d start t ell)
      B hB hZpos (d + 2 : ℝ) 1 hrowScale zero_le_one
      (fun t => (hscaled t).1) (fun t => (hscaled t).2)

/-- The reset-labelled atoms of a real flat sample, embedded canonically in
`ℂ`, in exactly the same coordinate convention as the paper model. -/
def paperIndicatorFreshAtomsOfReal
    (N d : ℕ) [NeZero N] (start : ZMod N)
    (ω : Fin (N * (d + 2)) → ℝ) :
    Fin (d + 1) → ResetLabel (d + 1) → ℂ :=
  fun t ell =>
    match ell with
    | none => paperIndicatorXiOfReal N d ω
        (paperIndicatorFreshRowSite N d start t) (Fin.last (d + 1))
    | some j => paperIndicatorXiOfReal N d ω
        (paperIndicatorFreshRowSite N d start t) j.castSucc

theorem measurable_paperIndicatorFreshAtomsOfReal
    (N d : ℕ) [NeZero N] (start : ZMod N)
    (t : Fin (d + 1)) (ell : ResetLabel (d + 1)) :
    Measurable (fun ω : Fin (N * (d + 2)) → ℝ =>
      paperIndicatorFreshAtomsOfReal N d start ω t ell) := by
  cases ell with
  | none =>
      change Measurable (fun ω : Fin (N * (d + 2)) → ℝ =>
        (ω (paperIndicatorFlatIndex N d
          (paperIndicatorFreshRowSite N d start t) (Fin.last (d + 1))) : ℂ))
      exact Complex.continuous_ofReal.measurable.comp (measurable_pi_apply _)
  | some j =>
      change Measurable (fun ω : Fin (N * (d + 2)) → ℝ =>
        (ω (paperIndicatorFlatIndex N d
          (paperIndicatorFreshRowSite N d start t) j.castSucc) : ℂ))
      exact Complex.continuous_ofReal.measurable.comp (measurable_pi_apply _)

/-- Positive logarithmic half for the genuine flat real sample, after the
paper's canonical complex embedding. -/
theorem real_paperIndicatorFlatFreshZ_logExcess_le
    (N d : ℕ) [NeZero N] {c₀ C₀ : ℝ}
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ) (start : ZMod N)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < exteriorFamilyMaxL2OpNorm B)
    (ν : Measure ℝ) [SFinite ν] [IsProbabilityMeasure ν]
    (hνInt : Integrable (fun u : ℝ => u ^ 2) ν)
    (hνSecond : ∫ u : ℝ, u ^ 2 ∂ν ≤ 1)
    (hZpos : ∀ᵐ ω ∂paperIndicatorRealSampleMeasure N d ν,
      0 < ‖profile.paperIndicatorFreshZ center z
        (paperIndicatorFreshAtomsOfReal N d start ω) B‖) :
    Integrable (fun ω =>
        logExcess (exteriorFamilyMaxL2OpNorm B)
          ‖profile.paperIndicatorFreshZ center z
            (paperIndicatorFreshAtomsOfReal N d start ω) B‖)
      (paperIndicatorRealSampleMeasure N d ν) ∧
      ∫ ω, logExcess (exteriorFamilyMaxL2OpNorm B)
          ‖profile.paperIndicatorFreshZ center z
            (paperIndicatorFreshAtomsOfReal N d start ω) B‖
          ∂paperIndicatorRealSampleMeasure N d ν ≤
        Real.posLog (paperFreshTraceFactor d) +
          (d + 1 : ℝ) * Real.sqrt
            (3 * (Real.log (d + 2 : ℝ)) ^ 2 + 3 + 3 * ‖z‖ ^ 2) := by
  letI : IsProbabilityMeasure (paperIndicatorRealSampleMeasure N d ν) := by
    simpa only [paperIndicatorRealSampleMeasure] using
      iidMeasure_isProbability ν (N * (d + 2))
  have hcoord (t : Fin (d + 1)) (ell : ResetLabel (d + 1)) :
      Integrable (fun ω : Fin (N * (d + 2)) → ℝ =>
          ‖paperIndicatorFreshAtomsOfReal N d start ω t ell‖ ^ 2)
          (paperIndicatorRealSampleMeasure N d ν) ∧
        ∫ ω : Fin (N * (d + 2)) → ℝ,
            ‖paperIndicatorFreshAtomsOfReal N d start ω t ell‖ ^ 2
              ∂paperIndicatorRealSampleMeasure N d ν ≤ 1 := by
    cases ell with
    | none =>
        simpa only [paperIndicatorRealSampleMeasure,
          paperIndicatorFreshAtomsOfReal, paperIndicatorXiOfReal_apply] using
          iidMeasure_coordinate_complexifiedReal_norm_sq_integrable_and_integral_le_one
            (paperIndicatorFlatIndex N d
              (paperIndicatorFreshRowSite N d start t) (Fin.last (d + 1)))
            hνInt hνSecond
    | some j =>
        simpa only [paperIndicatorRealSampleMeasure,
          paperIndicatorFreshAtomsOfReal, paperIndicatorXiOfReal_apply] using
          iidMeasure_coordinate_complexifiedReal_norm_sq_integrable_and_integral_le_one
            (paperIndicatorFlatIndex N d
              (paperIndicatorFreshRowSite N d start t) j.castSucc)
            hνInt hνSecond
  have hscaled (t : Fin (d + 1)) :=
    profile.integrable_freshRowAtomSum_div_sq_and_integral_le_one
      (paperIndicatorRealSampleMeasure N d ν) hc₀
      (fun ω ell => paperIndicatorFreshAtomsOfReal N d start ω t ell)
      (fun ell => measurable_paperIndicatorFreshAtomsOfReal N d start t ell)
      (hcoord t)
  have hrowScale : (1 : ℝ) ≤ (d + 2 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (d + 1))
  simpa only [Nat.cast_add, Nat.cast_ofNat, mul_one] using
    profile.integrable_and_integral_paperIndicatorFreshZ_logExcess_le
      (paperIndicatorRealSampleMeasure N d ν) center z
      (fun ω => paperIndicatorFreshAtomsOfReal N d start ω)
      (fun t ell => measurable_paperIndicatorFreshAtomsOfReal N d start t ell)
      B hB hZpos (d + 2 : ℝ) 1 hrowScale zero_le_one
      (fun t => (hscaled t).1) (fun t => (hscaled t).2)

/-! ### Selected-coordinate reconstruction -/

/-- Replace exactly one selected atom in every fresh row.  The unselected
coordinates are the variables averaged in the outer Fubini integral. -/
def replacePaperFreshSelectedAtoms {k : ℕ}
    (atoms : Fin k → ResetLabel k → ℂ)
    (word : Fin k → ResetLabel k) (x : Fin k → ℂ) :
    Fin k → ResetLabel k → ℂ :=
  fun t ell => if ell = word t then x t else atoms t ell

@[simp] theorem replacePaperFreshSelectedAtoms_selected {k : ℕ}
    (atoms : Fin k → ResetLabel k → ℂ)
    (word : Fin k → ResetLabel k) (x : Fin k → ℂ) (t : Fin k) :
    replacePaperFreshSelectedAtoms atoms word x t (word t) = x t := by
  simp [replacePaperFreshSelectedAtoms]

theorem replacePaperFreshSelectedAtoms_unselected {k : ℕ}
    (atoms : Fin k → ResetLabel k → ℂ)
    (word : Fin k → ResetLabel k) (x : Fin k → ℂ)
    (t : Fin k) {ell : ResetLabel k} (hell : ell ≠ word t) :
    replacePaperFreshSelectedAtoms atoms word x t ell = atoms t ell := by
  simp [replacePaperFreshSelectedAtoms, hell]

/-- Evaluation at arbitrary selected coordinates is the actual `Z_B` after
those coordinates have been reinserted into the complete fresh atom array. -/
theorem eval_paperIndicatorFreshPolynomial_eq_freshZ_replaceSelected
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (r : ExteriorDegree (d + 1))
    (I J : ExteriorIndex (d + 1) r) (x : Fin (d + 1) → ℂ) :
    MultiAffine.eval
        (profile.paperIndicatorFreshPolynomial center z atoms B r I J) x =
      profile.paperIndicatorFreshZ center z
        (replacePaperFreshSelectedAtoms atoms
          (arbitrarySupportWord I J) x) B := by
  let atoms' := replacePaperFreshSelectedAtoms atoms
    (arbitrarySupportWord I J) x
  have hp : profile.paperIndicatorFreshPolynomial center z atoms B r I J =
      profile.paperIndicatorFreshPolynomial center z atoms' B r I J := by
    apply profile.paperIndicatorFreshPolynomial_congr_off_selected
    intro t ell hell
    exact (replacePaperFreshSelectedAtoms_unselected atoms
      (arbitrarySupportWord I J) x t hell).symm
  rw [hp]
  simpa only [atoms', replacePaperFreshSelectedAtoms_selected] using
    profile.eval_paperIndicatorFreshPolynomial_eq_freshZ
      center z atoms' B r I J

end PaperIndicatorWeights

end CircularLawSection4
