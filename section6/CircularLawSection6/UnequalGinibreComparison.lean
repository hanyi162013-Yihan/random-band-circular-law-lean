import CircularLawSection6.PublishedLocalBulkTri
import CircularLawSection6.GinibreBBVStieltjes

/-! # Different matrix dimensions and one common Stieltjes transform

The finite grid is fixed before taking the matrix-size limit. Its mesh and
height are subsequently sent to zero. Thus the two matrix dimensions need
not satisfy any relative growth condition. No limiting singular-value
measure is constructed or assumed.
-/

open MeasureTheory Set Filter Topology ShortRingAnchor Arxiv2410V3
open CircularLawSections56.Section5
open scoped ENNReal BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem unequal_matrix_grid_cdf_bound
    {Ω : Type*} {m n : ℕ} [NeZero m] [NeZero n]
    (X : Ω → Matrix (Fin m) (Fin m) ℂ)
    (Y : Ω → Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) {K v R d : ℝ} (hK : 1 ≤ K)
    (hR : 0 ≤ R) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hvlower : K ^ (-(1 / 8 : ℝ)) ≤ v)
    (hsmall : 3 * Real.sqrt v ≤ 1)
    {ω : Ω} (hgood : ω ∈ compactStieltjesGridGood
      (fun ω u => stieltjesTrace (X ω) z (spectralParameter u v))
      (fun ω u => stieltjesTrace (Y ω) z (spectralParameter u v))
      (fun u => freeDysonStieltjes z (spectralParameter u v)) K (R + 1) d) :
    matrixSquaredSingularCdfDistanceOn (X ω - z • 1) (Y ω - z • 1) R ≤
      ((8 * R + 40) * K ^ (-d) + 32 * Real.sqrt v) / Real.pi := by
  have hv : 0 < v :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hK) _).trans_le hvlower
  have hL := inverse_height_sq_le_dimension hK hvlower
  have hf := fun ω => matrix_stieltjesTrace_horizontal_lipschitz (X ω) z hv
  have hg := fun ω => matrix_stieltjesTrace_horizontal_lipschitz (Y ω) z hv
  have href : ∀ u, ‖freeDysonStieltjes z (spectralParameter u v)‖ ≤ 1 := by
    intro u
    exact (freeDysonStieltjes_norm_lt_one z _ (by simpa [spectralParameter] using hv)).le
  have hc (u : ℝ) (hu : u ∈ Icc (-(R + 1)) (R + 1)) :=
    compactStieltjesGridGood_comparison _ _ _ hK (sq_nonneg _) hL hd1 hf hg hgood hu
  have hi (u : ℝ) (hu : u ∈ Icc (-(R + 1)) (R + 1)) :=
    compactStieltjesGridGood_reference_im_le_three _ _ _ hK
      (sq_nonneg _) hL hd0 hd1 hg href hgood hu
  have h := matrix_squaredCdfDistanceOn_le_of_stieltjes (X ω) (Y ω) z
    hv hR hsmall (show 0 ≤ 4 * K ^ (-d) by positivity)
    (fun u hu => hc u (by simpa only [neg_add, sub_eq_add_neg] using hu))
    (fun u hu => hi u (by simpa only [neg_add, sub_eq_add_neg] using hu))
  have hid : matrixSquaredSingularCdfDistanceOn (X ω - z • 1) (Y ω - z • 1) R =
      empiricalCdfDistanceOn 0 (R ^ 2)
        (fun i => shiftedSingularValueFamily (X ω) z i ^ 2)
        (fun i => shiftedSingularValueFamily (Y ω) z i ^ 2) := by
    unfold matrixSquaredSingularCdfDistanceOn empiricalCdfDistanceOn
    apply congrArg (fun f : ℝ → ℝ => sSup (f '' Icc 0 (R ^ 2)))
    funext t
    exact congrArg₂ (fun x y : ℝ => |x - y|)
      (empiricalCdf_fin_dimension (by simp)
        (fun i => (X ω - z • 1).toEuclideanLin.singularValues i ^ 2) t)
      (empiricalCdf_fin_dimension (by simp)
        (fun i => (Y ω - z • 1).toEuclideanLin.singularValues i ^ 2) t)
  rw [hid]
  convert h using 1
  ring

/-- A fixed finite grid costs only a finite sum of pointwise failure
probabilities. Its size is independent of both matrix dimensions. -/
theorem compact_grid_compl_tendsto_zero
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n))
    (f g : ∀ n, Ω n → ℝ → ℂ) (reference : ℝ → ℂ)
    {K R d : ℝ} (hK : 0 < K)
    (hf : ∀ u ε, 0 < ε → Tendsto
      (fun n => μ n {ω | ε < ‖f n ω u - reference u‖}) atTop (𝓝 0))
    (hg : ∀ u ε, 0 < ε → Tendsto
      (fun n => μ n {ω | ε < ‖g n ω u - reference u‖}) atTop (𝓝 0)) :
    Tendsto (fun n => μ n (compactStieltjesGridGood (f n) (g n)
      reference K R d)ᶜ) atTop (𝓝 0) := by
  classical
  let I := Fin (horizontalGridSize R (K ^ (-(2 : ℝ))))
  let u (i : I) := horizontalGridCenter R (K ^ (-(2 : ℝ))) i
  let badA (n : ℕ) (i : I) := {ω | K ^ (-d) < ‖f n ω (u i) - reference (u i)‖}
  let badB (n : ℕ) (i : I) := {ω | K ^ (-d) < ‖g n ω (u i) - reference (u i)‖}
  have hsum : Tendsto (fun n => ∑ i : I, (μ n (badA n i) + μ n (badB n i)))
      atTop (𝓝 0) := by
    have h : Tendsto (fun n => ∑ i : I, (μ n (badA n i) + μ n (badB n i)))
        atTop (𝓝 (∑ _i : I, ((0 : ℝ≥0∞) + 0))) :=
      tendsto_finsetSum (Finset.univ : Finset I) (fun i _ =>
        (hf (u i) (K ^ (-d)) (Real.rpow_pos_of_pos hK (-d))).add
          (hg (u i) (K ^ (-d)) (Real.rpow_pos_of_pos hK (-d))))
    simpa only [add_zero, Finset.sum_const_zero] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hsum (fun _ => zero_le) (fun n => ?_)
  have hsub : (compactStieltjesGridGood (f n) (g n) reference K R d)ᶜ ⊆
      ⋃ i : I, badA n i ∪ badB n i := by
    intro ω hω
    by_contra hnot
    apply hω
    intro i
    constructor
    · exact le_of_not_gt (fun h => hnot (mem_iUnion.mpr ⟨i, Or.inl h⟩))
    · exact le_of_not_gt (fun h => hnot (mem_iUnion.mpr ⟨i, Or.inr h⟩))
  exact (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans
    (Finset.sum_le_sum (fun i _ => measure_union_le (badA n i) (badB n i))))

/-- Pointwise convergence to the same actual free Dyson transform implies
compact squared-singular CDF comparison even for unrelated dimensions. -/
theorem unequal_matrix_cdf_of_common_stieltjes
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (M N : ℕ → ℕ) [∀ n, NeZero (M n)] [∀ n, NeZero (N n)]
    (X : ∀ n, Ω n → Matrix (Fin (M n)) (Fin (M n)) ℂ)
    (Y : ∀ n, Ω n → Matrix (Fin (N n)) (Fin (N n)) ℂ)
    (z : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hX : ∀ η : ℂ, 0 < η.im → ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => μ n {ω | ε < ‖stieltjesTrace (X n ω) z η - freeDysonStieltjes z η‖})
      atTop (𝓝 0))
    (hY : ∀ η : ℂ, 0 < η.im → ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => μ n {ω | ε < ‖stieltjesTrace (Y n ω) z η - freeDysonStieltjes z η‖})
      atTop (𝓝 0)) :
    TendstoInProbabilityTri μ (fun n ω =>
      matrixSquaredSingularCdfDistanceOn (X n ω - z • 1) (Y n ω - z • 1) R) 0 := by
  intro ε hε
  let d := localBulkRateExponent 1
  have hd0 : 0 < d := localBulkRateExponent_pos (by norm_num)
  have hd1 : d ≤ 1 := by norm_num [d, localBulkRateExponent, localBulkEffectiveExponent]
  have hrate : Tendsto (fun k : ℕ => (k : ℝ) ^ (-d)) atTop (𝓝 0) :=
    localBulk_rate_tendsto_zero (by norm_num : (0 : ℝ) < 1) tendsto_id
  have hbound : Tendsto (fun k : ℕ => ((8 * R + 72) / Real.pi) * (k : ℝ) ^ (-d))
      atTop (𝓝 0) := by simpa only [mul_zero] using hrate.const_mul ((8 * R + 72) / Real.pi)
  obtain ⟨k, hk, hksmall, hkbound⟩ :=
    ((eventually_ge_atTop (2 : ℕ)).and
      ((hrate.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))).and
        (hbound.eventually (gt_mem_nhds hε)))).exists
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  let v := localBulkHeight 1 (k : ℝ)
  have hv : 0 < v := Real.rpow_pos_of_pos (zero_lt_one.trans_le hkR) _
  have hroot : Real.sqrt v ≤ (k : ℝ) ^ (-d) :=
    sqrt_localBulkHeight_le_rate (by norm_num) hkR
  let good (n : ℕ) := compactStieltjesGridGood
    (fun ω u => stieltjesTrace (X n ω) z (spectralParameter u v))
    (fun ω u => stieltjesTrace (Y n ω) z (spectralParameter u v))
    (fun u => freeDysonStieltjes z (spectralParameter u v)) k (R + 1) d
  have hbad : Tendsto (fun n => μ n (good n)ᶜ) atTop (𝓝 0) :=
    compact_grid_compl_tendsto_zero μ _ _ _ (zero_lt_one.trans_le hkR)
      (fun u => hX _ (by simpa [spectralParameter] using hv))
      (fun u => hY _ (by simpa [spectralParameter] using hv))
  have hbadReal : Tendsto (fun n => (μ n).real (good n)ᶜ) atTop (𝓝 0) := by
    simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ∞)).comp hbad
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) hbadReal
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω hg
  change ε ≤ |matrixSquaredSingularCdfDistanceOn (X n ω - z • 1) (Y n ω - z • 1) R - 0| at hω
  have hb := unequal_matrix_grid_cdf_bound (X n) (Y n) z hkR hR hd0.le hd1
    (localBulkHeight_lower hkR) (by dsimp [v] at hroot ⊢; linarith) hg
  let : Nonempty (Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin (M n))))) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using
      (inferInstance : Nonempty (Fin (M n)))
  let : Nonempty (Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin (N n))))) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using
      (inferInstance : Nonempty (Fin (N n)))
  have hnonneg : 0 ≤ matrixSquaredSingularCdfDistanceOn
      (X n ω - z • 1) (Y n ω - z • 1) R :=
    empiricalCdfDistanceOn_nonneg (sq_nonneg R) _ _
  rw [sub_zero, abs_of_nonneg hnonneg] at hω
  have hb' : matrixSquaredSingularCdfDistanceOn
      (X n ω - z • 1) (Y n ω - z • 1) R ≤
      ((8 * R + 72) / Real.pi) * (k : ℝ) ^ (-d) := by
    refine hb.trans ?_
    calc
      _ ≤ ((8 * R + 40) * (k : ℝ) ^ (-d) + 32 * (k : ℝ) ^ (-d)) / Real.pi :=
        div_le_div_of_nonneg_right
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hroot (by norm_num))) Real.pi_pos.le
      _ = _ := by ring
  exact (not_le.mpr (hb'.trans_lt hkbound)) hω

/-- The actual normalized dense Gaussian matrices, sampled from the same
infinite Gaussian array. Neither a coupling independence premise nor a
comparison between the two dimension sequences is needed. -/
theorem unequal_ginibre_cdf_of_bbv
    (hBBV : CircularLawSections56.Section5.PublishedSection3Concrete.BBVComparisonInput)
    (M N : ℕ → ℕ) (hMpos : ∀ n, 0 < M n) (hNpos : ∀ n, 0 < N n)
    (hM : Tendsto M atTop atTop) (hN : Tendsto N atTop atTop)
    (z : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    TendstoInProbabilityTri
      (fun _ => CircularLawSections56.Section5.PublishedSection3Concrete.gaussianSequenceLaw)
      (fun n ω => matrixSquaredSingularCdfDistanceOn
        (CircularLawSections56.Section5.PublishedSection3Concrete.ginibreOnSequence (M n) ω - z • 1)
        (CircularLawSections56.Section5.PublishedSection3Concrete.ginibreOnSequence (N n) ω - z • 1) R) 0 := by
  let (n : ℕ) : NeZero (M n) := ⟨(hMpos n).ne'⟩
  let (n : ℕ) : NeZero (N n) := ⟨(hNpos n).ne'⟩
  have hpoint (D : ℕ → ℕ) (hDpos : ∀ n, 0 < D n) (hD : Tendsto D atTop atTop)
      (η : ℂ) (hη : 0 < η.im) (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun n =>
        CircularLawSections56.Section5.PublishedSection3Concrete.gaussianSequenceLaw
          {ω | ε < ‖stieltjesTrace
            (CircularLawSections56.Section5.PublishedSection3Concrete.ginibreOnSequence (D n) ω)
            z η - freeDysonStieltjes z η‖}) atTop (𝓝 0) := by
    have h := (convergesInProbability_iff_norm.1
      (GinibreBBV.ginibre_stieltjes_inMeasure_of_bbv hBBV D hDpos hD z η hη)) ε hε
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds h (fun _ => zero_le) (fun n => ?_)
    apply measure_mono
    intro ω hω
    change ε < ‖stieltjesTrace
      (CircularLawSections56.Section5.PublishedSection3Concrete.ginibreOnSequence (D n) ω)
      z η - freeDysonStieltjes z η‖ at hω
    change ε ≤ ‖stieltjesTrace
      (CircularLawSections56.Section5.PublishedSection3Concrete.ginibreOnSequence (D n) ω)
      z η - freeDysonStieltjes z η‖
    exact hω.le
  exact unequal_matrix_cdf_of_common_stieltjes _ M N _ _ z hR
    (hpoint M hMpos hM) (hpoint N hNpos hN)

end CircularLawSection6
