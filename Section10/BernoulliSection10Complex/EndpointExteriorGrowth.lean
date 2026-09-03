import BernoulliSection10Complex.HodgeFamilyGrowth
import BernoulliSection10.PacketBoundary
import BernoulliSection10Complex.EndpointDeterminant

open scoped BigOperators Matrix ENNReal NNReal Matrix.Norms.Frobenius
open MeasureTheory

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

open Matrix Set Set.powersetCard
open BernoulliLinearAlgebra

local instance endpointGrowthSumLinearOrder (W : ℕ) :
    LinearOrder (Fin W ⊕ Fin W) :=
  LinearOrder.lift' (fun x : Fin W ⊕ Fin W ↦ (toLex x : Fin W ⊕ₗ Fin W))
    (fun _ _ h ↦ toLex.injective h)

def endpointPairOfRows (W : ℕ)
    (x : Fin (W + W) → Fin W → ℂ) : EndpointBlockPair W :=
  (fun i j ↦ x (finSumFinEquiv (Sum.inl i)) j,
    fun i j ↦ x (finSumFinEquiv (Sum.inr i)) j)

def endpointAmbientRow (W : ℕ) (s : Fin W ⊕ Fin W)
    (u : Fin W → ℂ) : (Fin W ⊕ Fin W) → ℂ :=
  match s with
  | Sum.inl _ => fun j => match j with
      | Sum.inl b => (blockNormalization W : ℂ) * u b
      | Sum.inr _ => 0
  | Sum.inr _ => fun j => match j with
      | Sum.inl _ => 0
      | Sum.inr b => (blockNormalization W : ℂ) * u b

theorem normalizedEndpointFactor_endpointPairOfRows_update
    (W : ℕ) (x : Fin (W + W) → Fin W → ℂ) (i : Fin (W + W))
    (u : Fin W → ℂ) :
    normalizedEndpointFactor W
        (endpointPairOfRows W (Function.update x i u)) =
      (normalizedEndpointFactor W (endpointPairOfRows W x)).updateRow
        (finSumFinEquiv.symm i)
          (endpointAmbientRow W (finSumFinEquiv.symm i) u) := by
  classical
  have hcrossLR (a b : Fin W) :
      Fin.castAdd W a ≠ Fin.natAdd W b := by
    intro h
    have hs := congrArg Fin.val h
    simp at hs
    omega
  have hcrossRL (a b : Fin W) :
      Fin.natAdd W a ≠ Fin.castAdd W b := by
    exact ne_comm.mp (hcrossLR b a)
  rcases hsi : finSumFinEquiv.symm i with a | a
  · have hi : i = finSumFinEquiv (Sum.inl a) := by
      apply finSumFinEquiv.symm.injective
      simpa only [hsi, Equiv.symm_apply_apply]
    rw [hi]
    ext b c
    rcases b with b | b <;> rcases c with c | c
    · by_cases hba : b = a <;>
      simp [normalizedEndpointFactor, endpointPairOfRows,
        normalizedBlockMatrix, endpointFactor, endpointAmbientRow,
        Matrix.updateRow_apply, Function.update_apply, Fin.castAdd_inj,
        hcrossLR, hcrossRL, hba]
    · simp [normalizedEndpointFactor, endpointPairOfRows,
        normalizedBlockMatrix, endpointFactor, endpointAmbientRow,
        Matrix.updateRow_apply]
    · simp [normalizedEndpointFactor, endpointPairOfRows,
        normalizedBlockMatrix, endpointFactor, endpointAmbientRow,
        Matrix.updateRow_apply]
    · have hne : b.addNat W ≠ Fin.castAdd W a := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
        omega
      simp [normalizedEndpointFactor, endpointPairOfRows,
        normalizedBlockMatrix, endpointFactor, endpointAmbientRow,
        Matrix.updateRow_apply, Function.update_apply, hne]
  · have hi : i = finSumFinEquiv (Sum.inr a) := by
      apply finSumFinEquiv.symm.injective
      simpa only [hsi, Equiv.symm_apply_apply]
    rw [hi]
    ext b c
    rcases b with b | b <;> rcases c with c | c
    · have hne : Fin.castAdd W b ≠ a.addNat W := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
        omega
      simp [normalizedEndpointFactor, endpointPairOfRows,
        normalizedBlockMatrix, endpointFactor, endpointAmbientRow,
        Matrix.updateRow_apply, Function.update_apply, hne]
    · simp [normalizedEndpointFactor, endpointPairOfRows,
        normalizedBlockMatrix, endpointFactor, endpointAmbientRow,
        Matrix.updateRow_apply]
    · simp [normalizedEndpointFactor, endpointPairOfRows,
        normalizedBlockMatrix, endpointFactor, endpointAmbientRow,
        Matrix.updateRow_apply]
    · by_cases hba : b = a <;>
      simp [normalizedEndpointFactor, endpointPairOfRows,
        normalizedBlockMatrix, endpointFactor, endpointAmbientRow,
        Matrix.updateRow_apply, Function.update_apply, Fin.castAdd_inj,
        hcrossLR, hcrossRL, hba]

theorem endpointAmbientRow_interpolate (W : ℕ)
    (s : Fin W ⊕ Fin W) (u v : Fin W → ℂ) (t : ℂ) :
    endpointAmbientRow W s ((1 - t) • u + t • v) =
      fun j => (1 - (t : ℂ)) * endpointAmbientRow W s u j +
        (t : ℂ) * endpointAmbientRow W s v j := by
  funext j
  rcases s with a | a <;> rcases j with b | b <;>
    simp [endpointAmbientRow]
  <;> push_cast <;> ring

def endpointForwardFamilyFlat (W : ℕ)
    (x : Fin (W + W) → Fin W → ℂ) : OneSiteClearedFamily W := fun q =>
  compound q.1 (normalizedEndpointFactor W (endpointPairOfRows W x))

theorem endpointForwardFamilyFlat_update_line
    (W : ℕ) (x : Fin (W + W) → Fin W → ℂ) (i : Fin (W + W))
    (u v : Fin W → ℂ) (t : ℂ) :
    endpointForwardFamilyFlat W
        (Function.update x i ((1 - t) • u + t • v)) =
      (1 - t) • endpointForwardFamilyFlat W (Function.update x i u) +
        t • endpointForwardFamilyFlat W (Function.update x i v) := by
  funext q s c
  let E := normalizedEndpointFactor W (endpointPairOfRows W x)
  let a := finSumFinEquiv.symm i
  let ru := endpointAmbientRow W a u
  let rv := endpointAmbientRow W a v
  have hinterp : endpointAmbientRow W a ((1 - t) • u + t • v) =
      fun j => (1 - (t : ℂ)) * ru j + (t : ℂ) * rv j := by
    simpa only [ru, rv] using endpointAmbientRow_interpolate W a u v t
  simp only [endpointForwardFamilyFlat, Pi.smul_apply, Pi.add_apply,
    Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  push_cast
  rw [normalizedEndpointFactor_endpointPairOfRows_update,
    normalizedEndpointFactor_endpointPairOfRows_update,
    normalizedEndpointFactor_endpointPairOfRows_update]
  simp only [compound_apply]
  change minor q.1 (E.updateRow a
      (endpointAmbientRow W a ((1 - t) • u + t • v))) s c = _
  rw [hinterp]
  by_cases ha : a ∈ s
  · simpa [E, a, ru, rv] using
      (minor_updateRow_interpolate_of_mem q.1 E a ru rv (t : ℂ) s c ha)
  · rw [minor_updateRow_eq_of_not_mem q.1 E a _ s c ha,
      minor_updateRow_eq_of_not_mem q.1 E a ru s c ha,
      minor_updateRow_eq_of_not_mem q.1 E a rv s c ha]
    ring

def endpointForwardFamilyRecursive (W : ℕ) :
    MultiAffineRows (List.replicate (W + W) W) → OneSiteClearedFamily W :=
  fun y => endpointForwardFamilyFlat W
    (multiAffineRowsToFinRows W (W + W) y)

theorem endpointForwardFamilyRecursive_isMultiAffine (W : ℕ) :
    IsMultiAffine (endpointForwardFamilyRecursive W) := by
  apply isMultiAffine_comp_multiAffineRowsToFinRows
  intro x i u v t
  exact endpointForwardFamilyFlat_update_line W x i u v t

def endpointForwardFamilyTensor (W : ℕ) :=
  multiAffineTensorOfFunction (endpointForwardFamilyRecursive W)

theorem endpointForwardFamilyRecursive_ne_zero (W : ℕ) :
    endpointForwardFamilyRecursive W ≠ 0 := by
  intro hzero
  let y : MultiAffineRows (List.replicate (W + W) W) :=
    finRowsToMultiAffineRows W (W + W) 0
  let q : Fin (2 * W + 1) := ⟨0, by omega⟩
  let s : powersetCard (Fin W ⊕ Fin W) 0 := ⟨∅, by simp⟩
  have h := congrFun (congrFun (congrFun hzero y) q) s
  have h' := congrFun h s
  simp [endpointForwardFamilyRecursive, endpointForwardFamilyFlat,
    compound_apply, minor, q, s] at h'

theorem endpointForwardFamily_log_deviation_recursive
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) :
    (∫⁻ y, ENNReal.ofReal
        |Real.log ‖endpointForwardFamilyRecursive W y‖ -
          Real.log ‖endpointForwardFamilyTensor W‖|
        ∂multiAffineRowLaw μ (List.replicate (W + W) W)) ≤
      multiAffineLogCost L (List.replicate (W + W) W) := by
  have hpos : ∀ p ∈ List.replicate (W + W) W, 0 < p := by
    intro p hp
    simp only [List.mem_replicate] at hp
    omega
  simpa only [endpointForwardFamilyTensor] using
    (corollary_10_3 hμ
      (endpointForwardFamilyRecursive_isMultiAffine W) hpos
      (endpointForwardFamilyRecursive_ne_zero W)).1

def EndpointAtomsBound (W : ℕ)
    (x : Fin (W + W) → Fin W → ℂ) : Prop :=
  ∀ i j, ‖x i j‖ ≤ 1

theorem endpointAtomsBound_of_corner (W : ℕ)
    (y : MultiAffineRows (List.replicate (W + W) W))
    (hy : IsReplicatedCorner W (W + W) y) :
    EndpointAtomsBound W (multiAffineRowsToFinRows W (W + W) y) := by
  intro i j
  exact abs_multiAffineRowsToFinRows_le_one_of_corner
    W (W + W) y hy i j

theorem norm_normalizedEndpointFactor_entry_le_one
    (W : ℕ) (hW : 0 < W) (x : Fin (W + W) → Fin W → ℂ)
    (hx : EndpointAtomsBound W x) (a b : Fin W ⊕ Fin W) :
    ‖normalizedEndpointFactor W (endpointPairOfRows W x) a b‖ ≤ 1 := by
  rcases a with a | a <;> rcases b with b | b
  · simp only [normalizedEndpointFactor, endpointFactor,
      Matrix.fromBlocks_apply₁₁, normalizedBlockMatrix,
      endpointPairOfRows, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul (abs_blockNormalization_le_one W hW)
      (hx (finSumFinEquiv (Sum.inl a)) b) (norm_nonneg _)
      (by norm_num)).trans_eq (mul_one 1)
  · simp [normalizedEndpointFactor, endpointFactor]
  · simp [normalizedEndpointFactor, endpointFactor]
  · simp only [normalizedEndpointFactor, endpointFactor,
      Matrix.fromBlocks_apply₂₂, normalizedBlockMatrix,
      endpointPairOfRows, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul (abs_blockNormalization_le_one W hW)
      (hx (finSumFinEquiv (Sum.inr a)) b) (norm_nonneg _)
      (by norm_num)).trans_eq (mul_one 1)

def endpointDegreeCornerBound (W q : ℕ) : ℝ :=
  (Nat.choose (2 * W) q : ℝ) ^ 2 * Nat.factorial q

theorem endpointDegreeCornerBound_nonneg (W q : ℕ) :
    0 ≤ endpointDegreeCornerBound W q := by
  unfold endpointDegreeCornerBound
  positivity

theorem norm_endpointForwardFamilyFlat_degree_le
    (W : ℕ) (hW : 0 < W) (x : Fin (W + W) → Fin W → ℂ)
    (hx : EndpointAtomsBound W x) (q : ℕ) (hq : q ≤ 2 * W) :
    ‖compound q (normalizedEndpointFactor W (endpointPairOfRows W x))‖ ≤
      endpointDegreeCornerBound W q := by
  let E := normalizedEndpointFactor W (endpointPairOfRows W x)
  have hentry (s c : powersetCard (Fin W ⊕ Fin W) q) :
      ‖compound q E s c‖ ≤ Nat.factorial q := by
    rw [compound_apply]
    have h := norm_minor_le_factorial_mul_pow q E s c 1
      (fun a b => norm_normalizedEndpointFactor_entry_le_one W hW x hx a b)
    simpa using h
  have hcard : Fintype.card (powersetCard (Fin W ⊕ Fin W) q) =
      Nat.choose (2 * W) q := by
    rw [← Nat.card_eq_fintype_card, powersetCard.card,
      Nat.card_eq_fintype_card]
    simp [Fintype.card_sum, two_mul]
  have h := frobenius_norm_le_card_mul_of_entry_norm_le
    (compound q E) (Nat.factorial q) (by positivity) hentry
  simpa only [endpointDegreeCornerBound, hcard, pow_two, mul_assoc] using h

def endpointFamilyCornerBound (W : ℕ) : ℝ :=
  ∑ q : Fin (2 * W + 1), endpointDegreeCornerBound W q.1

theorem endpointFamilyCornerBound_nonneg (W : ℕ) :
    0 ≤ endpointFamilyCornerBound W := by
  unfold endpointFamilyCornerBound
  exact Finset.sum_nonneg fun q hq => endpointDegreeCornerBound_nonneg W q.1

theorem norm_endpointForwardFamilyRecursive_le_cornerBound
    (W : ℕ) (hW : 0 < W)
    (y : MultiAffineRows (List.replicate (W + W) W))
    (hy : IsReplicatedCorner W (W + W) y) :
    ‖endpointForwardFamilyRecursive W y‖ ≤ endpointFamilyCornerBound W := by
  rw [pi_norm_le_iff_of_nonneg (endpointFamilyCornerBound_nonneg W)]
  intro q
  let x := multiAffineRowsToFinRows W (W + W) y
  have hx : EndpointAtomsBound W x := endpointAtomsBound_of_corner W y hy
  change ‖compound q.1 (normalizedEndpointFactor W (endpointPairOfRows W x))‖ ≤ _
  exact (norm_endpointForwardFamilyFlat_degree_le W hW x hx q.1
    (Nat.le_of_lt_succ q.2)).trans
      (Finset.single_le_sum
        (fun k hk => endpointDegreeCornerBound_nonneg W k.1)
        (Finset.mem_univ q))

theorem norm_endpointForwardFamilyTensor_le
    (W : ℕ) (hW : 0 < W) :
    ‖endpointForwardFamilyTensor W‖ ≤
      (1 + 2 * (W : ℝ)) ^ (W + W) * endpointFamilyCornerBound W := by
  unfold endpointForwardFamilyTensor
  exact norm_multiAffineTensorOfFunction_le_of_corner
    W (W + W) (endpointForwardFamilyRecursive W)
      (endpointFamilyCornerBound W) (endpointFamilyCornerBound_nonneg W)
      (norm_endpointForwardFamilyRecursive_le_cornerBound W hW)

def endpointDegreeCommonBound (W : ℕ) : ℝ :=
  (2 : ℝ) ^ (4 * W) * (2 * W : ℝ) ^ (2 * W)

theorem endpointDegreeCommonBound_nonneg (W : ℕ) :
    0 ≤ endpointDegreeCommonBound W := by
  unfold endpointDegreeCommonBound
  positivity

theorem endpointDegreeCornerBound_le_common
    (W q : ℕ) (hq : q ≤ 2 * W) :
    endpointDegreeCornerBound W q ≤ endpointDegreeCommonBound W := by
  have hchooseNat := Nat.choose_le_two_pow (2 * W) q
  have hchoose : (Nat.choose (2 * W) q : ℝ) ≤ (2 : ℝ) ^ (2 * W) := by
    exact_mod_cast hchooseNat
  have hchooseSq : (Nat.choose (2 * W) q : ℝ) ^ 2 ≤
      (2 : ℝ) ^ (4 * W) := by
    calc
      (Nat.choose (2 * W) q : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (2 * W)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hchoose 2
      _ = (2 : ℝ) ^ ((2 * W) * 2) := (pow_mul _ _ _).symm
      _ = (2 : ℝ) ^ (4 * W) := by congr 1 <;> omega
  have hfactNat : Nat.factorial q ≤ (2 * W) ^ (2 * W) :=
    (Nat.factorial_le hq).trans (Nat.factorial_le_pow (2 * W))
  have hfact : (Nat.factorial q : ℝ) ≤ (2 * W : ℝ) ^ (2 * W) := by
    exact_mod_cast hfactNat
  unfold endpointDegreeCornerBound endpointDegreeCommonBound
  exact mul_le_mul hchooseSq hfact (by positivity) (by positivity)

theorem endpointFamilyCornerBound_le_common (W : ℕ) :
    endpointFamilyCornerBound W ≤
      (2 * W + 1 : ℝ) * endpointDegreeCommonBound W := by
  unfold endpointFamilyCornerBound
  calc
    ∑ q : Fin (2 * W + 1), endpointDegreeCornerBound W q.1 ≤
        ∑ _q : Fin (2 * W + 1), endpointDegreeCommonBound W := by
      apply Finset.sum_le_sum
      intro q hq
      exact endpointDegreeCornerBound_le_common W q.1
        (Nat.le_of_lt_succ q.2)
    _ = (2 * W + 1 : ℝ) * endpointDegreeCommonBound W := by simp

def endpointTensorCoarseBound (W : ℕ) : ℝ :=
  (1 + 2 * (W : ℝ)) ^ (2 * W) *
    ((2 * W + 1 : ℝ) * endpointDegreeCommonBound W)

theorem endpointTensorCoarseBound_nonneg (W : ℕ) :
    0 ≤ endpointTensorCoarseBound W := by
  unfold endpointTensorCoarseBound
  exact mul_nonneg (pow_nonneg (by positivity) _)
    (mul_nonneg (by positivity) (endpointDegreeCommonBound_nonneg W))

theorem norm_endpointForwardFamilyTensor_le_coarse
    (W : ℕ) (hW : 0 < W) :
    ‖endpointForwardFamilyTensor W‖ ≤ endpointTensorCoarseBound W := by
  calc
    ‖endpointForwardFamilyTensor W‖ ≤
        (1 + 2 * (W : ℝ)) ^ (W + W) * endpointFamilyCornerBound W :=
      norm_endpointForwardFamilyTensor_le W hW
    _ ≤ (1 + 2 * (W : ℝ)) ^ (W + W) *
        ((2 * W + 1 : ℝ) * endpointDegreeCommonBound W) := by
      gcongr
      exact endpointFamilyCornerBound_le_common W
    _ = endpointTensorCoarseBound W := by
      unfold endpointTensorCoarseBound
      congr 2
      omega

def endpointTensorLogBound (W : ℕ) : ℝ :=
  (2 * W : ℝ) * Real.posLog (1 + 2 * (W : ℝ)) +
    Real.posLog (2 * W + 1 : ℝ) +
    (4 * W : ℝ) * Real.posLog 2 +
    (2 * W : ℝ) * Real.posLog (2 * W : ℝ)

theorem posLog_endpointTensorCoarseBound_le_logBound (W : ℕ) :
    Real.posLog (endpointTensorCoarseBound W) ≤
      endpointTensorLogBound W := by
  have houter := Real.posLog_mul
    (x := (1 + 2 * (W : ℝ)) ^ (2 * W))
    (y := (2 * W + 1 : ℝ) * endpointDegreeCommonBound W)
  have hinner := Real.posLog_mul
    (x := (2 * W + 1 : ℝ)) (y := endpointDegreeCommonBound W)
  have hdegree := Real.posLog_mul
    (x := (2 : ℝ) ^ (4 * W)) (y := (2 * W : ℝ) ^ (2 * W))
  unfold endpointTensorCoarseBound endpointDegreeCommonBound
    endpointTensorLogBound at *
  rw [Real.posLog_pow] at houter
  rw [Real.posLog_pow, Real.posLog_pow] at hdegree
  push_cast at houter hdegree
  linarith

theorem posLog_norm_endpointForwardFamilyTensor_le_logBound
    (W : ℕ) (hW : 0 < W) :
    Real.posLog ‖endpointForwardFamilyTensor W‖ ≤ endpointTensorLogBound W :=
  (Real.posLog_le_posLog (norm_nonneg _)
    (norm_endpointForwardFamilyTensor_le_coarse W hW)).trans
      (posLog_endpointTensorCoarseBound_le_logBound W)

def endpointTensorLogConstant : ℝ :=
  5 + 3 * Real.posLog 3 + 6 * Real.posLog 2

theorem endpointTensorLogConstant_nonneg : 0 ≤ endpointTensorLogConstant := by
  unfold endpointTensorLogConstant
  nlinarith [Real.posLog_nonneg (x := (3 : ℝ)),
    Real.posLog_nonneg (x := (2 : ℝ))]

theorem endpointTensorLogBound_le_W_log_eW
    (W : ℕ) (hW : 0 < W) :
    endpointTensorLogBound W ≤
      endpointTensorLogConstant * W * Real.log (Real.exp 1 * W) := by
  have hW1Nat : 1 ≤ W := by omega
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1Nat
  have hW0 : (0 : ℝ) ≤ W := by positivity
  let t : ℝ := Real.posLog (W : ℝ)
  let A : ℝ := 3 * Real.posLog 3 + 6 * Real.posLog 2
  have ht : 0 ≤ t := Real.posLog_nonneg
  have hA : 0 ≤ A := by
    unfold A
    nlinarith [Real.posLog_nonneg (x := (3 : ℝ)),
      Real.posLog_nonneg (x := (2 : ℝ))]
  have hbase : Real.posLog (1 + 2 * (W : ℝ)) ≤
      Real.posLog 3 + t := by
    have hle : 1 + 2 * (W : ℝ) ≤ 3 * W := by nlinarith
    calc
      Real.posLog (1 + 2 * (W : ℝ)) ≤ Real.posLog (3 * (W : ℝ)) :=
        Real.posLog_le_posLog (by positivity) hle
      _ ≤ Real.posLog 3 + t := by
        simpa only [t] using Real.posLog_mul (x := (3 : ℝ)) (y := (W : ℝ))
  have hcount : Real.posLog (2 * W + 1 : ℝ) ≤
      Real.posLog 3 + t := by
    have hle : (2 * W + 1 : ℝ) ≤ 3 * W := by
      push_cast
      nlinarith
    exact (Real.posLog_le_posLog (by positivity) hle).trans
      (by simpa only [t] using
        Real.posLog_mul (x := (3 : ℝ)) (y := (W : ℝ)))
  have hdouble : Real.posLog (2 * W : ℝ) ≤
      Real.posLog 2 + t := by
    simpa only [t] using
      Real.posLog_mul (x := (2 : ℝ)) (y := (W : ℝ))
  have hcountW : Real.posLog (2 * W + 1 : ℝ) ≤
      W * (Real.posLog 3 + t) := by
    calc
      _ ≤ Real.posLog 3 + t := hcount
      _ = 1 * (Real.posLog 3 + t) := by ring
      _ ≤ W * (Real.posLog 3 + t) :=
        mul_le_mul_of_nonneg_right hW1
          (add_nonneg Real.posLog_nonneg ht)
  have hfirst : endpointTensorLogBound W ≤ (W : ℝ) * (A + 5 * t) := by
    unfold endpointTensorLogBound
    dsimp only [A]
    push_cast
    have hb := mul_le_mul_of_nonneg_left hbase
      (show (0 : ℝ) ≤ 2 * W by positivity)
    have hd := mul_le_mul_of_nonneg_left hdouble
      (show (0 : ℝ) ≤ 2 * W by positivity)
    linarith
  calc
    endpointTensorLogBound W ≤ (W : ℝ) * (A + 5 * t) := hfirst
    _ ≤ (A + 5) * W * (1 + t) := by
      rw [show (A + 5) * (W : ℝ) * (1 + t) =
        (W : ℝ) * ((A + 5) * (1 + t)) by ring]
      apply mul_le_mul_of_nonneg_left _ hW0
      nlinarith [mul_nonneg hA ht]
    _ = endpointTensorLogConstant * W * Real.log (Real.exp 1 * W) := by
      rw [← one_add_posLog_nat_eq_log_e_mul W hW]
      simp only [A, t, endpointTensorLogConstant]
      ring

theorem posLog_norm_endpointForwardFamilyTensor_le_W_log_eW
    (W : ℕ) (hW : 0 < W) :
    Real.posLog ‖endpointForwardFamilyTensor W‖ ≤
      endpointTensorLogConstant * W * Real.log (Real.exp 1 * W) :=
  (posLog_norm_endpointForwardFamilyTensor_le_logBound W hW).trans
    (endpointTensorLogBound_le_W_log_eW W hW)

def endpointForwardWLogIntegralBound (L : ℝ) (W : ℕ) : ℝ≥0∞ :=
  multiAffineLogCost L (List.replicate (W + W) W) +
    ENNReal.ofReal
      (endpointTensorLogConstant * W * Real.log (Real.exp 1 * W))

theorem endpointForwardFamily_posLog_lintegral_recursive
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) :
    (∫⁻ y, ENNReal.ofReal
        (Real.posLog ‖endpointForwardFamilyRecursive W y‖)
        ∂multiAffineRowLaw μ (List.replicate (W + W) W)) ≤
      endpointForwardWLogIntegralBound L W := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure
      (multiAffineRowLaw μ (List.replicate (W + W) W)) := by infer_instance
  have hdev := endpointForwardFamily_log_deviation_recursive hμ W hW
  have hpoint (y : MultiAffineRows (List.replicate (W + W) W)) :
      ENNReal.ofReal (Real.posLog ‖endpointForwardFamilyRecursive W y‖) ≤
        ENNReal.ofReal
            |Real.log ‖endpointForwardFamilyRecursive W y‖ -
              Real.log ‖endpointForwardFamilyTensor W‖| +
          ENNReal.ofReal (Real.posLog ‖endpointForwardFamilyTensor W‖) := by
    calc
      ENNReal.ofReal (Real.posLog ‖endpointForwardFamilyRecursive W y‖) ≤
          ENNReal.ofReal
            (|Real.log ‖endpointForwardFamilyRecursive W y‖ -
                Real.log ‖endpointForwardFamilyTensor W‖| +
              Real.posLog ‖endpointForwardFamilyTensor W‖) :=
        ENNReal.ofReal_le_ofReal
          (posLog_le_abs_log_sub_log_add_posLog
            ‖endpointForwardFamilyRecursive W y‖
            ‖endpointForwardFamilyTensor W‖)
      _ = _ := ENNReal.ofReal_add (abs_nonneg _)
        (Real.posLog_nonneg (x := ‖endpointForwardFamilyTensor W‖))
  calc
    (∫⁻ y, ENNReal.ofReal
        (Real.posLog ‖endpointForwardFamilyRecursive W y‖)
        ∂multiAffineRowLaw μ (List.replicate (W + W) W)) ≤
      ∫⁻ y, (ENNReal.ofReal
          |Real.log ‖endpointForwardFamilyRecursive W y‖ -
            Real.log ‖endpointForwardFamilyTensor W‖| +
        ENNReal.ofReal (Real.posLog ‖endpointForwardFamilyTensor W‖))
        ∂multiAffineRowLaw μ (List.replicate (W + W) W) :=
      lintegral_mono hpoint
    _ = (∫⁻ y, ENNReal.ofReal
          |Real.log ‖endpointForwardFamilyRecursive W y‖ -
            Real.log ‖endpointForwardFamilyTensor W‖|
          ∂multiAffineRowLaw μ (List.replicate (W + W) W)) +
        ENNReal.ofReal (Real.posLog ‖endpointForwardFamilyTensor W‖) := by
      rw [lintegral_add_right _ measurable_const]
      simp
    _ ≤ endpointForwardWLogIntegralBound L W := by
      unfold endpointForwardWLogIntegralBound
      exact add_le_add hdev
        (ENNReal.ofReal_le_ofReal
          (posLog_norm_endpointForwardFamilyTensor_le_W_log_eW W hW))

def endpointPairRowsMeasurableEquiv (W : ℕ) :
    (Fin (W + W) → Fin W → ℂ) ≃ᵐ EndpointBlockPair W :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (W + W) => Fin W → ℂ) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin W ⊕ Fin W => Fin W → ℂ))

theorem endpointPairRowsMeasurableEquiv_apply
    (W : ℕ) (x : Fin (W + W) → Fin W → ℂ) :
    endpointPairRowsMeasurableEquiv W x = endpointPairOfRows W x := by
  rfl

theorem endpointPairRows_measurePreserving
    (W : ℕ) (μ : Measure ℂ) [SigmaFinite μ] :
    MeasurePreserving (endpointPairRowsMeasurableEquiv W)
      (Measure.pi fun _ : Fin (W + W) => Measure.pi fun _ : Fin W => μ)
      (endpointBlockPairLaw W μ) := by
  let rowLaw : Measure (Fin W → ℂ) := Measure.pi fun _ : Fin W => μ
  have hreindex :=
    (measurePreserving_piCongrLeft
      (α := fun _ : Fin (W + W) => Fin W → ℂ)
      (μ := fun _ : Fin (W + W) => rowLaw) finSumFinEquiv).symm
  have hsplit := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin W ⊕ Fin W => rowLaw)
  simpa only [endpointPairRowsMeasurableEquiv, endpointBlockPairLaw,
    blockAtomRowsLaw, rowLaw] using hreindex.trans hsplit

def endpointForwardFamily (W : ℕ) (x : EndpointBlockPair W) :
    OneSiteClearedFamily W := fun q =>
  compound q.1 (normalizedEndpointFactor W x)

theorem endpointForwardFamilyFlat_eq
    (W : ℕ) (x : Fin (W + W) → Fin W → ℂ) :
    endpointForwardFamilyFlat W x =
      endpointForwardFamily W (endpointPairOfRows W x) := rfl

theorem endpointForwardFamilyRecursive_finRows
    (W : ℕ) (x : Fin (W + W) → Fin W → ℂ) :
    endpointForwardFamilyRecursive W
        (finRowsMultiAffineRowsMeasurableEquiv W (W + W) x) =
      endpointForwardFamilyFlat W x := by
  unfold endpointForwardFamilyRecursive
  rw [finRowsMultiAffineRowsMeasurableEquiv_apply,
    multiAffineRowsToFinRows_leftInverse]

theorem endpointForwardFamily_posLog_lintegral_le
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W : ℕ) (hW : 0 < W) :
    (∫⁻ x, ENNReal.ofReal (Real.posLog ‖endpointForwardFamily W x‖)
        ∂endpointBlockPairLaw W μ) ≤ endpointForwardWLogIntegralBound L W := by
  letI := hμ.toIsProbabilityMeasure
  let e := finRowsMultiAffineRowsMeasurableEquiv W (W + W)
  let ep := endpointPairRowsMeasurableEquiv W
  let flatLaw : Measure (Fin (W + W) → Fin W → ℂ) :=
    Measure.pi fun _ : Fin (W + W) => Measure.pi fun _ : Fin W => μ
  have he : MeasurePreserving e flatLaw
      (multiAffineRowLaw μ (List.replicate (W + W) W)) := by
    simpa only [flatLaw] using
      finRowsMultiAffineRows_measurePreserving μ W (W + W)
  have hep : MeasurePreserving ep flatLaw (endpointBlockPairLaw W μ) := by
    simpa only [ep, flatLaw] using endpointPairRows_measurePreserving W μ
  have heqRec := he.lintegral_comp_emb e.measurableEmbedding
    (fun y => ENNReal.ofReal
      (Real.posLog ‖endpointForwardFamilyRecursive W y‖))
  have heqPair := hep.lintegral_comp_emb ep.measurableEmbedding
    (fun x => ENNReal.ofReal (Real.posLog ‖endpointForwardFamily W x‖))
  calc
    (∫⁻ x, ENNReal.ofReal (Real.posLog ‖endpointForwardFamily W x‖)
        ∂endpointBlockPairLaw W μ) =
      ∫⁻ x, ENNReal.ofReal (Real.posLog ‖endpointForwardFamilyFlat W x‖)
        ∂flatLaw := by
      symm
      simpa only [ep, endpointPairRowsMeasurableEquiv_apply,
        endpointForwardFamilyFlat_eq] using heqPair
    _ = ∫⁻ y, ENNReal.ofReal
        (Real.posLog ‖endpointForwardFamilyRecursive W y‖)
        ∂multiAffineRowLaw μ (List.replicate (W + W) W) := by
      simpa only [e, endpointForwardFamilyRecursive_finRows] using heqRec
    _ ≤ endpointForwardWLogIntegralBound L W :=
      endpointForwardFamily_posLog_lintegral_recursive hμ W hW

end BernoulliSection10Complex
