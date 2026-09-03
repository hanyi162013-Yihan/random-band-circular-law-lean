/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/HighBandLSV.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Section5Formalization
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option maxHeartbeats 800000

/-! Proof block: HighBandLSV/Parameters.lean -/


/-! Parameters of arXiv:2609.01295v1, Theorem 3.1 and Appendix B.
The source calls the main statement a theorem, not a proposition. -/

noncomputable section
open Section5Formalization

namespace HighBandLSV

structure Regime (N W : ℕ) (chi kappa : ℝ) : Prop where
  N_pos : 0 < N
  W_pos : 0 < W
  chi_pos : 0 < chi
  kappa_pos : 0 < kappa
  kappa_lt : kappa < chi / 4
  bandwidth : (N : ℝ) ^ (1 / 2 + chi) ≤ (W : ℝ)

abbrev lambda (N W kappa : ℝ) : ℝ := section5Scale N W kappa
abbrev delta (N W kappa : ℝ) : ℝ := normalDelta N W kappa
abbrev tau (N W kappa t : ℝ) : ℝ := leastSingularThreshold N W kappa t

def hsCap (N R Kz : ℝ) : ℝ := (R + Kz + 1) * Real.sqrt N

def mesh (N W kappa J C1 K : ℝ) : ℝ :=
  delta N W kappa / (C1 * (K + 1) * Real.sqrt J)

def seedSize (N W : ℕ) : ℕ := min W N / 8

/-- For positive `N,b`, this is exactly `ceil (N/b)`. -/
def ceilBlocks (N b : ℕ) : ℕ := (N - 1) / b + 1

def blockCount (N W : ℕ) : ℕ := ceilBlocks N (seedSize N W)
def blockSize (N W : ℕ) : ℕ := N / blockCount N W
def retainedRows (N W : ℕ) : ℕ := blockSize N W - 1

theorem delta_pos (N W kappa : ℝ) : 0 < delta N W kappa := Real.exp_pos _

theorem mesh_pos {N W kappa J C1 K : ℝ}
    (hJ : 0 < J) (hC1 : 0 < C1) (hK : 0 < K + 1) :
    0 < mesh N W kappa J C1 K := by
  unfold mesh
  exact div_pos (delta_pos _ _ _)
    (mul_pos (mul_pos hC1 hK) (Real.sqrt_pos.mpr hJ))

theorem hsCap_polynomial (N R Kz : ℝ) :
    hsCap N R Kz = (R + Kz + 1) * N ^ (1 / 2 : ℝ) := by
  simp [hsCap, Real.sqrt_eq_rpow]

theorem mesh_log {N W kappa J C1 K : ℝ}
    (hJ : 0 < J) (hC1 : 0 < C1) (hK : 0 < K + 1) :
    -Real.log (mesh N W kappa J C1 K) =
      lambda N W kappa + Real.log (C1 * (K + 1) * Real.sqrt J) := by
  rw [mesh, Real.log_div (ne_of_gt (delta_pos _ _ _))
    (ne_of_gt (mul_pos (mul_pos hC1 hK) (Real.sqrt_pos.mpr hJ)))]
  simp only [delta, normalDelta, Real.log_exp]
  ring

/-- The error used in the normal equation, with the paper's exact mesh. -/
theorem mesh_error {N W kappa J C1 K C : ℝ}
    (hJ : 0 < J) (hC1 : 0 < C1) (hK : 0 < K + 1)
    (hC : 0 ≤ C) (hlarge : 4 * C ≤ C1) :
    C * Real.sqrt J * mesh N W kappa J C1 K ≤
      delta N W kappa / (4 * (K + 1)) := by
  have hs : 0 < Real.sqrt J := Real.sqrt_pos.mpr hJ
  unfold mesh
  apply (le_div_iff₀ (by positivity : 0 < 4 * (K + 1))).mpr
  have heq : C * Real.sqrt J *
      (delta N W kappa / (C1 * (K + 1) * Real.sqrt J)) * (4 * (K + 1)) =
      (4 * C / C1) * delta N W kappa := by
    field_simp [hC1.ne', hK.ne', hs.ne']
    <;> ring
  rw [heq]
  exact (mul_le_mul_of_nonneg_right ((div_le_one hC1).mpr hlarge)
    (delta_pos _ _ _).le).trans_eq (one_mul _)

/-- No replacement of `3*kappa` by a different asymptotic scale. -/
theorem threshold_ratio (N W kappa t : ℝ) :
    tau N W kappa t / delta N W kappa =
      t * Real.exp (-((N ^ (3 * kappa) - N ^ kappa) * (N / W))) :=
  threshold_div_delta

/-- Elementary conversion of the planar quadratic small ball to a linear one. -/
theorem min_one_square_le {x : ℝ} (hx : 0 ≤ x) : min 1 (x ^ 2) ≤ x := by
  by_cases h : x ≤ 1
  · exact (min_le_right _ _).trans (by nlinarith)
  · exact (min_le_left _ _).trans (le_of_lt (lt_of_not_ge h))

theorem planar_to_linear {C W s d : ℝ}
    (hC : 0 ≤ C) (hW : 0 ≤ W) (hs : 0 ≤ s) (hd : 0 < d) :
    min 1 (C * W * s ^ 2 / d ^ 2) ≤ Real.sqrt C * Real.sqrt W * s / d := by
  have hsq : C * W * s ^ 2 / d ^ 2 =
      (Real.sqrt C * Real.sqrt W * s / d) ^ 2 := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hC, Real.sq_sqrt hW]
  rw [hsq]
  exact min_one_square_le (by positivity)

end HighBandLSV

end


/-! Proof block: HighBandLSV/ScalarThresholds.lean -/


/-! Pure scalar closure extracted from the original Section 5 library.
It deliberately does not import its probability/conditioning assembly. -/

noncomputable section
open Section5Formalization Filter
open scoped Topology

namespace HighBandLSV

structure CorrectedSection5NumericalConditions (N W kappa J C cmain : ℝ) : Prop where
  N_pos : 0 < N
  W_pos : 0 < W
  kappa_pos : 0 < kappa
  C_nonneg : 0 ≤ C
  cmain_nonneg : 0 ≤ cmain
  logarithmic_threshold : 4 * C / (kappa / 2) ≤ cmain * N ^ (kappa / 2)
  block_threshold : 4 * C * (J * section5Scale N W kappa) ≤ cmain * N ^ (1 + kappa)

theorem CorrectedSection5NumericalConditions.entropy_versus_gain
    {N W kappa J C cmain : ℝ}
    (d : CorrectedSection5NumericalConditions N W kappa J C cmain) :
    -(cmain * W * section5Scale N W kappa) +
        C * (N * Real.log N + J * section5Scale N W kappa) ≤
      -(cmain / 4 * N ^ (1 + kappa)) := by
  exact corrected_section5_entropy_bound d.N_pos d.W_pos d.cmain_nonneg
    (logarithmic_entropy_small_of_threshold d.N_pos d.kappa_pos d.C_nonneg
      d.logarithmic_threshold) d.block_threshold

theorem eventually_le_mul_natCast_rpow {A B p : ℝ} (hB : 0 < B) (hp : 0 < p) :
    ∀ᶠ n : ℕ in atTop, A ≤ B * (n : ℝ) ^ p := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ p) atTop atTop :=
    (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ n : ℕ in atTop, A / B < (n : ℝ) ^ p := ht.eventually_gt_atTop (A / B)
  filter_upwards [he] with n hn
  have hstrict : A < B * (n : ℝ) ^ p := by
    have := (div_lt_iff₀ hB).mp hn
    simpa [mul_comm] using this
  exact hstrict.le

theorem eventually_correctedSection5NumericalConditions
    {kappa chi C C0 cmain : ℝ}
    (hkappa : 0 < kappa) (hchi : 0 < chi) (hC : 0 ≤ C) (hC0 : 0 ≤ C0)
    (hcmain : 0 < cmain) (W J : ℕ → ℕ)
    (hWpos : ∀ᶠ n : ℕ in atTop, 0 < W n)
    (hband : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 2 + chi) ≤ (W n : ℝ))
    (hblockCount : ∀ᶠ n : ℕ in atTop, (J n : ℝ) ≤ C0 * (n : ℝ) / (W n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      CorrectedSection5NumericalConditions (n : ℝ) (W n : ℝ) kappa (J n : ℝ) C cmain := by
  have hlogThreshold : ∀ᶠ n : ℕ in atTop,
      4 * C / (kappa / 2) ≤ cmain * (n : ℝ) ^ (kappa / 2) :=
    eventually_le_mul_natCast_rpow hcmain (by positivity)
  have hpowerThreshold : ∀ᶠ n : ℕ in atTop,
      4 * C * C0 ≤ cmain * (n : ℝ) ^ (2 * chi) :=
    eventually_le_mul_natCast_rpow hcmain (by positivity)
  filter_upwards [eventually_gt_atTop (0 : ℕ), hWpos, hband, hblockCount,
    hlogThreshold, hpowerThreshold] with n hn hWn hbandn hJn hlogn hpowern
  have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hW : 0 < (W n : ℝ) := Nat.cast_pos.mpr hWn
  refine ⟨hN, hW, hkappa, hC, hcmain.le, hlogn, ?_⟩
  have hraw := block_count_scale_bound (κ := kappa) hN.le hW hC0 hJn
  have hsuppressed := bandwidth_suppresses_block_entropy (κ := kappa) hN hW hC0 hbandn
  calc
    4 * C * ((J n : ℝ) * section5Scale (n : ℝ) (W n : ℝ) kappa) ≤
        4 * C * (C0 * (n : ℝ) ^ kappa * (n : ℝ) ^ 2 / (W n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hraw (mul_nonneg (by norm_num) hC)
    _ ≤ 4 * C * (C0 * (n : ℝ) ^ (1 + kappa - 2 * chi)) :=
      mul_le_mul_of_nonneg_left hsuppressed (mul_nonneg (by norm_num) hC)
    _ ≤ cmain * (n : ℝ) ^ (1 + kappa) := block_power_small_of_threshold hN hpowern

end HighBandLSV

end


/-! Proof block: HighBandLSV/Partition.lean -/


noncomputable section
open Section5Formalization

namespace HighBandLSV

/-- Exact integer estimates for the actual ceiling choice, including the loss
of one row per block. No asymptotic notation is used here. -/
theorem ceiling_partition_arithmetic {N b : ℕ} (hb : 8 ≤ b) (hbN : b ≤ N) :
    let J := ceilBlocks N b
    let d := N / J
    let r := d - 1
    0 < J ∧ J ≤ N ∧ J * b ≤ 2 * N ∧ d ≤ b ∧ b ≤ 4 * r ∧
      r * J ≤ N ∧ J ≤ N - r * J ∧ N - r * J ≤ 2 * J := by
  dsimp only
  let J := ceilBlocks N b
  let d := N / J
  let r := d - 1
  change 0 < J ∧ J ≤ N ∧ J * b ≤ 2 * N ∧ d ≤ b ∧ b ≤ 4 * r ∧
    r * J ≤ N ∧ J ≤ N - r * J ∧ N - r * J ≤ 2 * J
  have hbpos : 0 < b := by omega
  have hNpos : 0 < N := by omega
  have hpred : N - 1 + 1 = N := by omega
  have he := Nat.mod_add_div (N - 1) b
  have hr := Nat.mod_lt (N - 1) hbpos
  have hJpos : 0 < J := Nat.succ_pos _
  have hJle : J ≤ N := by
    calc
      J = (N - 1) / b + 1 := rfl
      _ ≤ (N - 1) + 1 := Nat.add_le_add_right (Nat.div_le_self (N - 1) b) 1
      _ = N := hpred
  have hJmul : J * b = b * ((N - 1) / b) + b := by dsimp [J, ceilBlocks]; ring
  have hcover : N ≤ J * b := by rw [hJmul]; omega
  have hprod : b * ((N - 1) / b) ≤ N - 1 := by omega
  have hcount : J * b ≤ 2 * N := by
    calc
      J * b = b * ((N - 1) / b) + b := hJmul
      _ ≤ (N - 1) + b := Nat.add_le_add_right hprod b
      _ ≤ N + N := Nat.add_le_add (Nat.sub_le N 1) hbN
      _ = 2 * N := by omega
  have heN : N % J + J * d = N := Nat.mod_add_div N J
  have hrN : N % J < J := Nat.mod_lt N hJpos
  have hJd : J * d ≤ N := by omega
  have hdle : d ≤ b := by
    by_contra h
    have : b + 1 ≤ d := by omega
    have hm := Nat.mul_le_mul_left J this
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega
  have hblower : b ≤ 2 * d + 1 := by
    by_contra h
    have : 2 * d + 2 ≤ b := by omega
    have hm := Nat.mul_le_mul_left J this
    have heq : J * (2 * d + 2) = 2 * (J * d) + 2 * J := by ring
    rw [heq] at hm
    omega
  have hdpos : 0 < d := by omega
  have hrdef : r + 1 = d := by dsimp [r]; omega
  have hrlarge : b ≤ 4 * r := by omega
  have hrJ : r * J ≤ N := by
    calc
      r * J ≤ d * J := Nat.mul_le_mul_right J (Nat.sub_le d 1)
      _ = J * d := Nat.mul_comm _ _
      _ ≤ N := hJd
  have hsub : N - r * J + r * J = N := Nat.sub_add_cancel hrJ
  have hdecomp : N = N % J + r * J + J := by
    calc
      N = N % J + J * d := heN.symm
      _ = N % J + r * J + J := by rw [← hrdef]; ring
  refine ⟨hJpos, hJle, hcount, hdle, hrlarge, hrJ, ?_, ?_⟩ <;> omega

theorem seed_size_bounds {N W : ℕ} (hseed : 8 ≤ seedSize N W) :
    seedSize N W ≤ N ∧ min W N ≤ 16 * seedSize N W ∧
      2 * (seedSize N W + 1) ≤ W := by
  have he := Nat.mod_add_div (min W N) 8
  have hr := Nat.mod_lt (min W N) (by decide : 0 < 8)
  have hminN := min_le_right W N
  have hminW := min_le_left W N
  unfold seedSize at *
  constructor
  · exact (Nat.div_le_self _ _).trans hminN
  · constructor <;> omega

/-- The existing balanced consecutive intervals now use the literal Appendix B
choice of `J`; equal or cyclic-neighboring blocks are inside the band. -/
theorem actual_partition_geometry {N W : ℕ} (hseed : 8 ≤ seedSize N W) :
    let J := blockCount N W
    (∀ i : Fin N, ∃ j : Fin J, i ∈ balancedIntervalBlock N J j) ∧
    Pairwise (fun i j : Fin J =>
      Disjoint (balancedIntervalBlock N J i) (balancedIntervalBlock N J j)) ∧
    (∀ (j : Fin J), (balancedIntervalBlock N J j).card =
      if j.val < N % J then blockSize N W + 1 else blockSize N W) ∧
    (∀ {i j : Fin J} {a b : Fin N},
      a ∈ balancedIntervalBlock N J i → b ∈ balancedIntervalBlock N J j →
      CyclicNeighbor i j → cyclicDist N a b ≤ W) := by
  obtain ⟨hbN, _, hwidth⟩ := seed_size_bounds hseed
  obtain ⟨hJ, hJN, _, hd, _⟩ := ceiling_partition_arithmetic hseed hbN
  have hwidth' : 2 * (N / blockCount N W + 1) ≤ W := by
    change 2 * (N / ceilBlocks N (seedSize N W) + 1) ≤ W
    omega
  exact ⟨balancedIntervalBlock_cover _ _ hJ,
    balancedIntervalBlock_pairwise_disjoint _ _,
    balancedIntervalBlock_card_eq _ _ hJ,
    fun ha hb hn => balancedIntervalBlock_cyclic_neighbor_dist _ _ _ hJ hJN hwidth' ha hb hn⟩

/-- The precise coefficient of `log(1/delta)` and its balanced-block bound. -/
theorem entropy_coefficient {N J r : ℝ}
    (hdeficit : N - r * J ≤ 2 * J) :
    3 * J + 2 * (N - r * J) - r ≤ 7 * J - r := by linarith

/-- Real scale conversion, usable also when the nominal bandwidth exceeds `N`.
The integer estimates above supply `J*b <= 2*N` and `v <= 64*r`. -/
theorem partition_real_scales {N W J b v r Cw : ℝ}
    (hW : 0 < W) (hJ : 0 ≤ J) (hCw : 0 < Cw)
    (hWv : W ≤ Cw * v) (hvb : v ≤ 16 * b)
    (hvr : v ≤ 64 * r) (hcount : J * b ≤ 2 * N) :
    J ≤ (32 * Cw) * N / W ∧ W / (64 * Cw) ≤ r := by
  constructor
  · apply (le_div_iff₀ hW).mpr
    calc
      J * W ≤ J * (Cw * v) := mul_le_mul_of_nonneg_left hWv hJ
      _ ≤ J * (Cw * (16 * b)) := by gcongr
      _ = (16 * Cw) * (J * b) := by ring
      _ ≤ (16 * Cw) * (2 * N) := by gcongr
      _ = (32 * Cw) * N := by ring
  · apply (div_le_iff₀ (by positivity : 0 < 64 * Cw)).mpr
    calc
      W ≤ Cw * v := hWv
      _ ≤ Cw * (64 * r) := by gcongr
      _ = r * (64 * Cw) := by ring

end HighBandLSV

end


/-! Proof block: HighBandLSV/HilbertSchmidt.lean -/


noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius

namespace HighBandLSV

/-- This is the Frobenius/HS norm, not the default entrywise matrix norm. -/
def hilbertSchmidt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ := ‖A‖

def euclideanOpNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ‖A.toEuclideanLin.toContinuousLinearMap‖

def shifted {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) := X - z • 1

theorem hilbertSchmidt_formula {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    hilbertSchmidt A = Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  simp [hilbertSchmidt, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow, Real.rpow_two]

theorem norm_apply_le_hilbertSchmidt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖A.toEuclideanLin x‖ ≤ hilbertSchmidt A * ‖x‖ := by
  have heq : A * Matrix.replicateCol (Fin 1) (fun i => x i) =
      Matrix.replicateCol (Fin 1) (fun i => A.toEuclideanLin x i) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  have h := Matrix.frobenius_norm_mul A (Matrix.replicateCol (Fin 1) (fun i => x i))
  rw [heq] at h
  simpa [hilbertSchmidt, Matrix.frobenius_norm_def, Matrix.replicateCol_apply,
    EuclideanSpace.norm_eq, Real.sqrt_eq_rpow, Real.rpow_two] using h

theorem euclideanOpNorm_le_hilbertSchmidt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    euclideanOpNorm A ≤ hilbertSchmidt A := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  exact norm_apply_le_hilbertSchmidt A

theorem shifted_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    (shifted A z).toEuclideanLin x = A.toEuclideanLin x - z • x := by
  ext i
  simp [shifted, Matrix.toLpLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec]

theorem shifted_opNorm_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    euclideanOpNorm (shifted A z) ≤ hilbertSchmidt A + ‖z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg A) (norm_nonneg z))
  intro x
  change ‖(shifted A z).toEuclideanLin x‖ ≤ _
  rw [shifted_apply]
  calc
    ‖A.toEuclideanLin x - z • x‖ ≤ ‖A.toEuclideanLin x‖ + ‖z • x‖ := norm_sub_le _ _
    _ ≤ hilbertSchmidt A * ‖x‖ + ‖z‖ * ‖x‖ := by
      rw [norm_smul]
      exact add_le_add (norm_apply_le_hilbertSchmidt A x) (le_refl _)
    _ = (hilbertSchmidt A + ‖z‖) * ‖x‖ := by ring

/-- Exact specialization `A=1/2`, `K0=R+Kz+1` from the final proof. -/
theorem hs_truncation_implies_cap {n : ℕ} (hn : 0 < n)
    (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) {R Kz : ℝ}
    (hKz : 0 ≤ Kz) (hz : ‖z‖ ≤ Kz)
    (hHS : hilbertSchmidt X ≤ R * Real.sqrt (n : ℝ)) :
    euclideanOpNorm (shifted X z) ≤ hsCap (n : ℝ) R Kz := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt (n : ℝ) := by
    simpa using Real.sqrt_le_sqrt hN
  calc
    euclideanOpNorm (shifted X z) ≤ hilbertSchmidt X + ‖z‖ := shifted_opNorm_le _ _
    _ ≤ R * Real.sqrt (n : ℝ) + Kz := add_le_add hHS hz
    _ ≤ hsCap (n : ℝ) R Kz := by
      unfold hsCap
      nlinarith [mul_nonneg hKz (sub_nonneg.mpr hs)]

end HighBandLSV

end


/-! Proof block: HighBandLSV/Distance.lean -/


noncomputable section
open scoped BigOperators
open GinibreLSV

namespace HighBandLSV

theorem exists_norm_div_sqrt_le_coordinate {n : ℕ} (hn : 0 < n)
    (x : EuclideanSpace ℂ (Fin n)) :
    ∃ j : Fin n, ‖x‖ / Real.sqrt (n : ℝ) ≤ ‖x j‖ := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨j, hj⟩ := Finite.exists_max (fun i : Fin n => ‖x i‖ ^ 2)
  have hsum : ‖x‖ ^ 2 ≤ (n : ℝ) * ‖x j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      (∑ i, ‖x i‖ ^ 2) ≤ ∑ _i : Fin n, ‖x j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hj i
      _ = (n : ℝ) * ‖x j‖ ^ 2 := by simp
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  refine ⟨j, (div_le_iff₀ hs).mpr ?_⟩
  apply (sq_le_sq₀ (norm_nonneg x) (by positivity)).mp
  simpa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), mul_comm] using hsum

theorem distance_div_sqrt_le_singularQuotient {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) {d : ℝ}
    (hcols : ∀ j, d ≤ columnDistance A j)
    (x : EuclideanSpace ℂ (Fin n)) (hx : x ≠ 0) :
    d / Real.sqrt (n : ℝ) ≤ LinearMap.singularQuotient A.toEuclideanLin x := by
  obtain ⟨j, hj⟩ := exists_norm_div_sqrt_le_coordinate hn x
  have hprod : d * (‖x‖ / Real.sqrt (n : ℝ)) ≤ ‖A.toEuclideanLin x‖ := by
    calc
      d * (‖x‖ / Real.sqrt (n : ℝ)) ≤ columnDistance A j * ‖x j‖ :=
        mul_le_mul (hcols j) hj (by positivity) (norm_nonneg _)
      _ = ‖x j‖ * columnDistance A j := by ring
      _ ≤ ‖A.toEuclideanLin x‖ := norm_coordinate_mul_columnDistance_le A j x
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [LinearMap.singularQuotient]
  calc
    d / Real.sqrt (n : ℝ) = (d * (‖x‖ / Real.sqrt (n : ℝ))) / ‖x‖ := by field_simp
    _ ≤ ‖A.toEuclideanLin x‖ / ‖x‖ := (div_le_div_iff_of_pos_right hxnorm).mpr hprod

theorem distance_div_sqrt_le_lsv {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) {d : ℝ}
    (hcols : ∀ j, d ≤ columnDistance A j) :
    d / Real.sqrt (n : ℝ) ≤ leastSingularValue A := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let j : Fin n := ⟨0, hn⟩
  letI : Nonempty {x : EuclideanSpace ℂ (Fin n) // x ≠ 0} :=
    ⟨⟨EuclideanSpace.single j 1, by simp⟩⟩
  rw [leastSingularValue_eq_iInf_singularQuotient hn]
  exact le_ciInf fun x => distance_div_sqrt_le_singularQuotient hn A hcols x x.property

/-- Closed thresholds and the exact `sqrt N` factor; no strict-threshold slack. -/
theorem small_lsv_implies_close_column {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) {t : ℝ}
    (hsmall : leastSingularValue A ≤ t) :
    ∃ j, columnDistance A j ≤ t * Real.sqrt (n : ℝ) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨j, hj⟩ := Finite.exists_min (columnDistance A)
  have h := (distance_div_sqrt_le_lsv hn A hj).trans hsmall
  exact ⟨j, (div_le_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))).mp h⟩

end HighBandLSV

end


/-! Proof block: HighBandLSV/Ledger.lean -/


noncomputable section
open Section5Formalization Filter
open scoped Topology

namespace HighBandLSV

/-- Literal fixed-(i,k,l) upper envelope displayed in Appendix B. -/
def rawFixedBound (N J r : ℕ) (W kappa C C1 K : ℝ) : ℝ :=
  let h := mesh N W kappa J C1 K
  let d := delta N W kappa
  (C / h) ^ (3 * J) * C ^ N / h ^ (2 * N) *
    (C * W * d ^ 2) ^ (r * J) * (C * (K + 1) * J * d) ^ r

def logEnvelope (N J r W kappa C C1 K : ℝ) : ℝ :=
  (3 * J + N) * Real.log C +
    (3 * J + 2 * N) *
      (lambda N W kappa + Real.log (C1 * (K + 1) * Real.sqrt J)) +
    r * J * (Real.log (C * W) - 2 * lambda N W kappa) +
    r * (Real.log (C * (K + 1) * J) - lambda N W kappa)

def remainder (N J r W C C1 K : ℝ) : ℝ :=
  (3 * J + N) * Real.log C +
    (3 * J + 2 * N) * Real.log (C1 * (K + 1) * Real.sqrt J) +
    r * J * Real.log (C * W) + r * Real.log (C * (K + 1) * J)

theorem exact_log_coefficient (N J r W kappa C C1 K : ℝ) :
    logEnvelope N J r W kappa C C1 K =
      (3 * J + 2 * (N - r * J) - r) * lambda N W kappa +
        remainder N J r W C C1 K := by
  unfold logEnvelope remainder
  ring

theorem log_rawFixedBound {N J r : ℕ} {W kappa C C1 K : ℝ}
    (hJ : 0 < J) (hW : 0 < W) (hC : 0 < C) (hC1 : 0 < C1)
    (hK : 0 < K + 1) :
    Real.log (rawFixedBound N J r W kappa C C1 K) =
      logEnvelope N J r W kappa C C1 K := by
  have hJR : (0 : ℝ) < J := Nat.cast_pos.mpr hJ
  have hd := delta_pos (N : ℝ) W kappa
  have hm := mesh_pos (N := (N : ℝ)) (W := W) (kappa := kappa) hJR hC1 hK
  have hs : 0 < Real.sqrt (J : ℝ) := Real.sqrt_pos.mpr hJR
  simp (disch := positivity) only [rawFixedBound, logEnvelope,
    Real.log_mul, Real.log_div, Real.log_pow, mesh, delta, normalDelta, Real.log_exp]
  push_cast
  ring

theorem rawFixedBound_eq_exp {N J r : ℕ} {W kappa C C1 K : ℝ}
    (hJ : 0 < J) (hW : 0 < W) (hC : 0 < C) (hC1 : 0 < C1)
    (hK : 0 < K + 1) :
    rawFixedBound N J r W kappa C C1 K =
      Real.exp (logEnvelope N J r W kappa C C1 K) := by
  have hm := mesh_pos (N := (N : ℝ)) (W := W) (kappa := kappa)
    (Nat.cast_pos.mpr hJ) hC1 hK
  have hd := delta_pos (N : ℝ) W kappa
  have hp : 0 < rawFixedBound N J r W kappa C C1 K := by
    unfold rawFixedBound
    positivity
  rw [← log_rawFixedBound hJ hW hC hC1 hK, Real.exp_log hp]

/-- Polynomial norm caps affect only the logarithmic remainder. These are
explicit scalar log bounds, not probabilistic assumptions. -/
theorem remainder_le_24 {N J r W C C1 K : ℝ}
    (hN : 1 ≤ N) (hJ : 0 ≤ J) (hJN : J ≤ N)
    (hr : 0 ≤ r) (hrN : r ≤ N) (hrJN : r * J ≤ N)
    (ha : Real.log C ≤ Real.log N)
    (hb : Real.log (C1 * (K + 1) * Real.sqrt J) ≤ 3 * Real.log N)
    (hc : Real.log (C * W) ≤ 2 * Real.log N)
    (hd : Real.log (C * (K + 1) * J) ≤ 3 * Real.log N) :
    remainder N J r W C C1 K ≤ 24 * (N * Real.log N) := by
  have hl : 0 ≤ Real.log N := Real.log_nonneg hN
  have h1 := mul_le_mul_of_nonneg_left ha (by linarith : 0 ≤ 3 * J + N)
  have h2 := mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ 3 * J + 2 * N)
  have h3 := mul_le_mul_of_nonneg_left hc (mul_nonneg hr hJ)
  have h4 := mul_le_mul_of_nonneg_left hd hr
  have h5 := mul_le_mul_of_nonneg_right hJN hl
  have h6 := mul_le_mul_of_nonneg_right hrN hl
  have h7 := mul_le_mul_of_nonneg_right hrJN hl
  unfold remainder
  nlinarith

/-- With `K=K0*sqrt N`, the four concrete log bounds hold once the
displayed constants are at most `N`. -/
theorem hs_cap_log_bounds {N J W C C1 K0 Cw : ℝ}
    (hN : 1 ≤ N) (hJ : 0 < J) (hJN : J ≤ N) (hW : 0 < W)
    (hC : 0 < C) (hC1 : 0 < C1) (hK0 : 0 ≤ K0)
    (hCw : 0 ≤ Cw) (hWN : W ≤ Cw * N)
    (hNC : C ≤ N) (hNB : C1 * (K0 + 1) ≤ N)
    (hND : C * (K0 + 1) ≤ N) (hNW : C * Cw ≤ N) :
    let K := K0 * Real.sqrt N
    Real.log C ≤ Real.log N ∧
    Real.log (C1 * (K + 1) * Real.sqrt J) ≤ 3 * Real.log N ∧
    Real.log (C * W) ≤ 2 * Real.log N ∧
    Real.log (C * (K + 1) * J) ≤ 3 * Real.log N := by
  have hNpos : 0 < N := by linarith
  have hsN : Real.sqrt N ≤ N := (Real.sqrt_le_left hNpos.le).mpr (by nlinarith)
  have hsJ : Real.sqrt J ≤ N := (Real.sqrt_le_left hNpos.le).mpr (by nlinarith)
  have hK : K0 * Real.sqrt N + 1 ≤ (K0 + 1) * N := by nlinarith
  have hB : C1 * (K0 * Real.sqrt N + 1) * Real.sqrt J ≤ N ^ 3 := by
    calc
      _ ≤ C1 * ((K0 + 1) * N) * N := by gcongr
      _ = (C1 * (K0 + 1)) * N ^ 2 := by ring
      _ ≤ N * N ^ 2 := by gcongr
      _ = N ^ 3 := by ring
  have hD : C * (K0 * Real.sqrt N + 1) * J ≤ N ^ 3 := by
    calc
      _ ≤ C * ((K0 + 1) * N) * N := by gcongr
      _ = (C * (K0 + 1)) * N ^ 2 := by ring
      _ ≤ N * N ^ 2 := by gcongr
      _ = N ^ 3 := by ring
  have hCW : C * W ≤ N ^ 2 := by
    calc
      C * W ≤ C * (Cw * N) := by gcongr
      _ = (C * Cw) * N := by ring
      _ ≤ N * N := by gcongr
      _ = N ^ 2 := by ring
  refine ⟨Real.log_le_log hC hNC, ?_, ?_, ?_⟩
  · simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by positivity : 0 < C1 * (K0 * Real.sqrt N + 1) * Real.sqrt J) hB
  · simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (mul_pos hC hW) hCW
  · simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by positivity : 0 < C * (K0 * Real.sqrt N + 1) * J) hD

theorem envelope_le_entropy_gain {N J r W kappa C C1 K c : ℝ}
    (hN : 0 < N) (hW : 0 < W) (hJ : 0 ≤ J)
    (hdeficit : N - r * J ≤ 2 * J) (hr : c * W ≤ r)
    (hrem : remainder N J r W C C1 K ≤ 24 * (N * Real.log N)) :
    logEnvelope N J r W kappa C C1 K ≤
      -(c * W * lambda N W kappa) +
        24 * (N * Real.log N + J * lambda N W kappa) := by
  have hl : 0 ≤ lambda N W kappa := by unfold lambda section5Scale; positivity
  have he := mul_le_mul_of_nonneg_right (entropy_coefficient hdeficit) hl
  have hr' := mul_le_mul_of_nonneg_right hr hl
  rw [exact_log_coefficient]
  nlinarith [mul_nonneg hJ hl]

/-- The extra `N*J^2` union is included, not hidden in the target exponent. -/
theorem normal_union_absorption {N J W kappa c E : ℝ}
    (hN : 1 ≤ N) (hJ : 1 ≤ J) (hJN : J ≤ N)
    (data : CorrectedSection5NumericalConditions N W kappa J 27 c)
    (hE : E ≤ -(c * W * lambda N W kappa) +
      24 * (N * Real.log N + J * lambda N W kappa))
    (htarget : 4 ≤ c * N ^ (3 * kappa / 4)) :
    (N * J * J) * Real.exp E ≤ Real.exp (-(N ^ (1 + kappa / 4))) := by
  have hNp : 0 < N := by linarith
  have hJp : 0 < J := by linarith
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlJ := Real.log_le_log hJp hJN
  have hlog : Real.log (N * J * J) ≤ 3 * (N * Real.log N) := by
    rw [Real.log_mul (by positivity) hJp.ne', Real.log_mul hNp.ne' hJp.ne']
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) hlN]
  have hl : 0 ≤ lambda N W kappa := by
    unfold lambda section5Scale
    exact mul_nonneg (Real.rpow_nonneg hNp.le _) (div_nonneg hNp.le data.W_pos.le)
  have hcombined : Real.log (N * J * J) + E ≤
      -(c / 4 * N ^ (1 + kappa)) := by
    have hledger := data.entropy_versus_gain
    nlinarith [mul_nonneg hJp.le hl]
  have hpower : N ^ (3 * kappa / 4) * N ^ (1 + kappa / 4) = N ^ (1 + kappa) := by
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  have ht := mul_le_mul_of_nonneg_right htarget (Real.rpow_nonneg hNp.le (1 + kappa / 4))
  have htarget' : N ^ (1 + kappa / 4) ≤ c / 4 * N ^ (1 + kappa) := by
    rw [mul_assoc, hpower] at ht
    linarith
  calc
    (N * J * J) * Real.exp E = Real.exp (Real.log (N * J * J) + E) := by
      rw [Real.exp_add, Real.exp_log (by positivity)]
    _ ≤ Real.exp (-(N ^ (1 + kappa / 4))) := by
      apply Real.exp_le_exp.mpr
      linarith

/-- The exact final-column prefactor used in Appendix B. -/
def columnPrefactor (N W : ℝ) : ℝ := N * Real.sqrt N * Real.sqrt W

theorem column_prefactor_bound {N W kappa t : ℝ}
    (hN : 0 < N) (hW : 0 < W) (ht : 0 ≤ t)
    (hlog : Real.log (columnPrefactor N W) ≤ finalExponentGap N W kappa) :
    columnPrefactor N W * (tau N W kappa t / delta N W kappa) ≤ t := by
  exact final_lsv_prefactor_bound (by unfold columnPrefactor; positivity) ht hlog

/-- All exponent-absorption thresholds for the normal union are eventually
automatic under the high-bandwidth and block-count hypotheses. -/
theorem eventually_normal_numerics {kappa chi c C0 : ℝ}
    (hk : 0 < kappa) (hchi : 0 < chi) (hc : 0 < c) (hC0 : 0 ≤ C0)
    (W J : ℕ → ℕ)
    (hWp : ∀ᶠ n : ℕ in atTop, 0 < W n)
    (hband : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 2 + chi) ≤ (W n : ℝ))
    (hcount : ∀ᶠ n : ℕ in atTop, (J n : ℝ) ≤ C0 * (n : ℝ) / (W n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      CorrectedSection5NumericalConditions (n : ℝ) (W n : ℝ) kappa (J n : ℝ) 27 c ∧
      4 ≤ c * (n : ℝ) ^ (3 * kappa / 4) := by
  exact (eventually_correctedSection5NumericalConditions hk hchi (by norm_num) hC0 hc
    W J hWp hband hcount).and (eventually_le_mul_natCast_rpow hc (by positivity))

end HighBandLSV

end


/-! Proof block: HighBandLSV/Asymptotics.lean -/


noncomputable section
open Section5Formalization Filter
open scoped Topology

namespace HighBandLSV

/-- A fully explicit sufficient threshold for the last exponential absorption.
Only `W <= Cw*N` is needed here; high bandwidth enters the normal ledger. -/
theorem final_log_dominance_of_threshold {N W kappa Cw : ℝ}
    (hN : 1 ≤ N) (hW : 0 < W) (hk : 0 < kappa) (hCw : 1 ≤ Cw)
    (hWN : W ≤ Cw * N)
    (hgrowth : 1 + Cw * (Cw + 1 + 2 / kappa) ≤ N ^ (2 * kappa)) :
    Real.log (columnPrefactor N W) ≤ finalExponentGap N W kappa := by
  have hNp : 0 < N := by linarith
  have hCwp : 0 < Cw := by linarith
  have hD : 0 < Cw + 1 := by linarith
  have hp : 1 ≤ N ^ kappa := Real.one_le_rpow hN hk.le
  have hs : Real.sqrt W ≤ (Cw + 1) * Real.sqrt N := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [mul_pow, Real.sq_sqrt hNp.le]
    nlinarith [mul_nonneg hNp.le (sq_nonneg Cw)]
  have hP : columnPrefactor N W ≤ (Cw + 1) * N ^ 2 := by
    unfold columnPrefactor
    calc
      N * Real.sqrt N * Real.sqrt W ≤ N * Real.sqrt N * ((Cw + 1) * Real.sqrt N) := by
        gcongr
      _ = (Cw + 1) * N * (Real.sqrt N) ^ 2 := by ring
      _ = (Cw + 1) * N ^ 2 := by rw [Real.sq_sqrt hNp.le]; ring
  have hPpos : 0 < columnPrefactor N W := by unfold columnPrefactor; positivity
  have hlogP := Real.log_le_log hPpos hP
  rw [Real.log_mul hD.ne' (by positivity), Real.log_pow] at hlogP
  have hlogD := Real.log_le_sub_one_of_pos hD
  have hlogN := Real.log_le_rpow_div hNp.le hk
  have hB : 0 ≤ Cw + 1 + 2 / kappa := by positivity
  have hlog : Real.log (columnPrefactor N W) ≤
      (Cw + 1 + 2 / kappa) * N ^ kappa := by
    have hconst := mul_le_mul_of_nonneg_left hp hD.le
    norm_num at hlogP
    simp only [mul_one] at hconst
    calc
      Real.log (columnPrefactor N W) ≤ Real.log (Cw + 1) + 2 * Real.log N := hlogP
      _ ≤ (Cw + 1) + 2 * (N ^ kappa / kappa) :=
        add_le_add (by linarith) (mul_le_mul_of_nonneg_left hlogN (by norm_num))
      _ ≤ (Cw + 1) * N ^ kappa + 2 * (N ^ kappa / kappa) :=
        add_le_add hconst (le_refl _)
      _ = (Cw + 1 + 2 / kappa) * N ^ kappa := by ring
  have hpow : N ^ (3 * kappa) = N ^ (2 * kappa) * N ^ kappa := by
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  have hgap : (Cw + 1 + 2 / kappa) * N ^ kappa ≤ finalExponentGap N W kappa := by
    unfold finalExponentGap
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hW).mpr
    calc
      ((Cw + 1 + 2 / kappa) * N ^ kappa) * W ≤
          ((Cw + 1 + 2 / kappa) * N ^ kappa) * (Cw * N) := by gcongr
      _ = (Cw * (Cw + 1 + 2 / kappa)) * N ^ kappa * N := by ring
      _ ≤ (N ^ (2 * kappa) - 1) * N ^ kappa * N := by
        gcongr
        linarith
      _ = (N ^ (3 * kappa) - N ^ kappa) * N := by rw [hpow]; ring
  exact hlog.trans hgap

/-- The paper's final polynomial prefactor is eventually absorbed, uniformly
over every bandwidth sequence with `0<W<=Cw*N`. -/
theorem eventually_final_log_dominance {kappa Cw : ℝ}
    (hk : 0 < kappa) (hCw : 1 ≤ Cw) (W : ℕ → ℕ)
    (hWp : ∀ᶠ n : ℕ in atTop, 0 < W n)
    (hWN : ∀ᶠ n : ℕ in atTop, (W n : ℝ) ≤ Cw * (n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, Real.log (columnPrefactor (n : ℝ) (W n : ℝ)) ≤
      finalExponentGap (n : ℝ) (W n : ℝ) kappa := by
  have hg : ∀ᶠ n : ℕ in atTop,
      1 + Cw * (Cw + 1 + 2 / kappa) ≤ (n : ℝ) ^ (2 * kappa) := by
    simpa using (eventually_le_mul_natCast_rpow
      (A := 1 + Cw * (Cw + 1 + 2 / kappa)) (B := 1)
      (p := 2 * kappa) (by norm_num) (by positivity))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hWp, hWN, hg] with n hn hw hupper hgrowth
  exact final_log_dominance_of_threshold (by exact_mod_cast hn)
    (Nat.cast_pos.mpr hw) hk hCw hupper hgrowth

end HighBandLSV

end


/-! Proof block: HighBandLSV/Assembly.lean -/


noncomputable section
open MeasureTheory Set GinibreLSV Section5Formalization
open scoped ENNReal

namespace HighBandLSV

def leastSingularBadEvent {Omega : Type*} {n : ℕ}
    (A : Omega → Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : Set Omega :=
  {w | leastSingularValue (A w) ≤ t}

theorem normalStructureIndex_card (N J : ℕ) :
    Fintype.card (NormalStructureIndex N J) = N * J * J := by
  simp [NormalStructureIndex] <;> ac_rfl

def hsEvent {Omega : Type*} {n : ℕ}
    (X : Omega → Matrix (Fin n) (Fin n) ℂ) (R : ℝ) : Set Omega :=
  {w | hilbertSchmidt (X w) ≤ R * Real.sqrt (n : ℝ)}

def capEvent {Omega : Type*} {n : ℕ}
    (X : Omega → Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (R Kz : ℝ) : Set Omega :=
  {w | euclideanOpNorm (shifted (X w) z) ≤ hsCap (n : ℝ) R Kz}

def closedColumnEvent {Omega : Type*} {n : ℕ}
    (A : Omega → Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (j : Fin n) : Set Omega :=
  {w | columnDistance (A w) j ≤ s}

/-- Explicit probability boundary. The fields are NOT asserted to follow from
the atom hypotheses by this file. In particular, the per-column estimate has
no HS cutoff, so no unjustified conditioning on that cutoff occurs. -/
structure AppendixBInputs (Omega : Type*) [MeasurableSpace Omega]
    (mu : Measure Omega) (N J r : ℕ)
    (X : Omega → Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (W kappa R Kz C C1 Ccol : ℝ) where
  good : Set Omega
  fixedBad : NormalStructureIndex N J → Set Omega
  normal_cover : capEvent X z R Kz \ good ⊆ ⋃ q, fixedBad q
  fixed_small_ball : ∀ q, mu (fixedBad q) ≤
    ENNReal.ofReal (rawFixedBound N J r W kappa C C1 (hsCap N R Kz))
  column_small_ball : ∀ (j : Fin N) (s : ℝ), 0 ≤ s →
    mu (closedColumnEvent (fun w => shifted (X w) z) s j ∩ good) ≤
      ENNReal.ofReal (Ccol * Real.sqrt W * s / delta N W kappa)

/-- The exact HS-truncated conclusion of Theorem 3.1, conditional on the
documented net/conditioning inputs and the separately proved scalar ledger.
This is not advertised as an unconditional derivation from the atom model. -/
theorem high_band_lsv_from_inputs
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {N J r : ℕ} {X : Omega → Matrix (Fin N) (Fin N) ℂ} {z : ℂ}
    {W kappa R Kz C C1 Ccol t : ℝ}
    (hn : 0 < N) (hW : 0 < W) (ht : 0 ≤ t) (hKz : 0 ≤ Kz)
    (hz : ‖z‖ ≤ Kz) (hCcol : 0 ≤ Ccol)
    (data : AppendixBInputs Omega mu N J r X z W kappa R Kz C C1 Ccol)
    (hnormal : ((N * J * J : ℕ) : ℝ) *
      rawFixedBound N J r W kappa C C1 (hsCap N R Kz) ≤
      Real.exp (-((N : ℝ) ^ (1 + kappa / 4))))
    (hgap : Real.log (columnPrefactor N W) ≤ finalExponentGap N W kappa) :
    mu (leastSingularBadEvent (fun w => shifted (X w) z) (tau N W kappa t) ∩ hsEvent X R) ≤
      ENNReal.ofReal (Ccol * t) + ENNReal.ofReal (Real.exp (-((N : ℝ) ^ (1 + kappa / 4)))) := by
  let A := fun w => shifted (X w) z
  let s := tau N W kappa t * Real.sqrt (N : ℝ)
  have hs : 0 ≤ s := by
    dsimp [s, tau, leastSingularThreshold]
    positivity
  have hcap : hsEvent X R ⊆ capEvent X z R Kz := by
    intro w hw
    exact hs_truncation_implies_cap hn (X w) z hKz hz hw
  have hbad : mu (hsEvent X R \ data.good) ≤
      ENNReal.ofReal (Real.exp (-((N : ℝ) ^ (1 + kappa / 4)))) := by
    apply finite_union_probability_bound mu (hsEvent X R \ data.good)
      data.fixedBad (ENNReal.ofReal (rawFixedBound N J r W kappa C C1 (hsCap N R Kz))) _
    · intro w hw
      exact data.normal_cover ⟨hcap hw.1, hw.2⟩
    · exact data.fixed_small_ball
    · calc
        (∑' _q : NormalStructureIndex N J,
          ENNReal.ofReal (rawFixedBound N J r W kappa C C1 (hsCap N R Kz))) =
            ENNReal.ofReal (((N * J * J : ℕ) : ℝ) *
              rawFixedBound N J r W kappa C C1 (hsCap N R Kz)) := by
                rw [tsum_fintype, Finset.sum_const, Finset.card_univ, normalStructureIndex_card]
                rw [nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg (N * J * J))]
                simp only [ENNReal.ofReal_natCast]
        _ ≤ _ := ENNReal.ofReal_le_ofReal hnormal
  have hgood : mu (leastSingularBadEvent A (tau N W kappa t) ∩ hsEvent X R ∩ data.good) ≤
      ENNReal.ofReal (Ccol * t) := by
    apply finite_union_probability_bound mu _
      (fun j => closedColumnEvent A s j ∩ data.good)
      (ENNReal.ofReal (Ccol * Real.sqrt W * s / delta N W kappa)) _
    · intro w hw
      obtain ⟨j, hj⟩ := small_lsv_implies_close_column hn (A w) hw.1.1
      exact mem_iUnion.mpr ⟨j, hj, hw.2⟩
    · intro j
      exact data.column_small_ball j s hs
    · have hp := column_prefactor_bound (Nat.cast_pos.mpr hn) hW ht hgap
      have halg : (N : ℝ) * (Ccol * Real.sqrt W * s / delta N W kappa) =
          Ccol * (columnPrefactor N W * (tau N W kappa t / delta N W kappa)) := by
        dsimp [s, columnPrefactor]
        ring
      calc
        (∑' _j : Fin N, ENNReal.ofReal (Ccol * Real.sqrt W * s / delta N W kappa)) =
            ENNReal.ofReal ((N : ℝ) * (Ccol * Real.sqrt W * s / delta N W kappa)) := by
              simp [ENNReal.ofReal_mul, nsmul_eq_mul]
        _ ≤ ENNReal.ofReal (Ccol * t) := by
          apply ENNReal.ofReal_le_ofReal
          rw [halg]
          exact mul_le_mul_of_nonneg_left hp hCcol
  exact final_lsv_probability_assembly mu (leastSingularBadEvent A (tau N W kappa t))
    (hsEvent X R) data.good _ _ hgood hbad

end HighBandLSV

end


/-! Proof block: HighBandLSV/NumericalAssembly.lean -/


noncomputable section
open Section5Formalization MeasureTheory

namespace HighBandLSV

/-- All fields are explicit scalar conditions. No probability bound, and no
bound on `rawFixedBound`, is assumed by this numerical certificate. -/
structure NumericalCertificate (N J r : ℕ) (W kappa R Kz C C1 c Cw : ℝ) : Prop where
  N_pos : 0 < N
  J_pos : 0 < J
  J_le_N : J ≤ N
  rows_le : r * J ≤ N
  deficit_le : (N : ℝ) - (r : ℝ) * J ≤ 2 * J
  rows_lower : c * W ≤ (r : ℝ)
  R_nonneg : 0 ≤ R
  Kz_nonneg : 0 ≤ Kz
  C_pos : 0 < C
  C1_pos : 0 < C1
  Cw_ge_one : 1 ≤ Cw
  bandwidth_upper : W ≤ Cw * N
  constant_C : C ≤ (N : ℝ)
  constant_mesh : C1 * ((R + Kz + 1) + 1) ≤ (N : ℝ)
  constant_ratio : C * ((R + Kz + 1) + 1) ≤ (N : ℝ)
  constant_variance : C * Cw ≤ (N : ℝ)
  entropy : CorrectedSection5NumericalConditions N W kappa J 27 c
  normal_growth : 4 ≤ c * (N : ℝ) ^ (3 * kappa / 4)
  column_growth : 1 + Cw * (Cw + 1 + 2 / kappa) ≤ (N : ℝ) ^ (2 * kappa)

theorem NumericalCertificate.normal_bound
    {N J r : ℕ} {W kappa R Kz C C1 c Cw : ℝ}
    (d : NumericalCertificate N J r W kappa R Kz C C1 c Cw) :
    ((N * J * J : ℕ) : ℝ) * rawFixedBound N J r W kappa C C1 (hsCap N R Kz) ≤
      Real.exp (-((N : ℝ) ^ (1 + kappa / 4))) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast d.N_pos
  have hJ : (1 : ℝ) ≤ J := by exact_mod_cast d.J_pos
  have hJN : (J : ℝ) ≤ N := by exact_mod_cast d.J_le_N
  have hrJ : (r : ℝ) * J ≤ N := by exact_mod_cast d.rows_le
  have hrN : (r : ℝ) ≤ N := by nlinarith [show (0 : ℝ) ≤ r from Nat.cast_nonneg r]
  have hK0 : 0 ≤ R + Kz + 1 := by linarith [d.R_nonneg, d.Kz_nonneg]
  have hK : 0 < hsCap N R Kz + 1 := by unfold hsCap; positivity
  obtain ⟨ha, hb, hc, hd⟩ := hs_cap_log_bounds hN
    (Nat.cast_pos.mpr d.J_pos) hJN d.entropy.W_pos d.C_pos d.C1_pos hK0
    (by linarith [d.Cw_ge_one]) d.bandwidth_upper d.constant_C
    d.constant_mesh d.constant_ratio d.constant_variance
  have hrem : remainder N J r W C C1 (hsCap N R Kz) ≤ 24 * ((N : ℝ) * Real.log N) := by
    exact remainder_le_24 hN (Nat.cast_nonneg J) hJN (Nat.cast_nonneg r) hrN hrJ ha hb hc hd
  have hE := envelope_le_entropy_gain (kappa := kappa) d.entropy.N_pos d.entropy.W_pos
    (Nat.cast_nonneg J) d.deficit_le d.rows_lower hrem
  have hbound := normal_union_absorption hN hJ hJN d.entropy hE d.normal_growth
  rw [rawFixedBound_eq_exp d.J_pos d.entropy.W_pos d.C_pos d.C1_pos hK]
  simpa only [Nat.cast_mul] using hbound

theorem NumericalCertificate.final_gap
    {N J r : ℕ} {W kappa R Kz C C1 c Cw : ℝ}
    (d : NumericalCertificate N J r W kappa R Kz C C1 c Cw) :
    Real.log (columnPrefactor N W) ≤ finalExponentGap N W kappa := by
  exact final_log_dominance_of_threshold (by exact_mod_cast d.N_pos)
    d.entropy.W_pos d.entropy.kappa_pos d.Cw_ge_one d.bandwidth_upper d.column_growth

/-- Preferred final entry point. Both exponential estimates are derived from
the explicit numerical certificate; the probability boundary remains visible. -/
theorem high_band_lsv_from_numerics
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {N J r : ℕ} {X : Omega → Matrix (Fin N) (Fin N) ℂ} {z : ℂ}
    {W kappa R Kz C C1 c Cw Ccol t : ℝ}
    (numerics : NumericalCertificate N J r W kappa R Kz C C1 c Cw)
    (inputs : AppendixBInputs Omega mu N J r X z W kappa R Kz C C1 Ccol)
    (ht : 0 ≤ t) (hz : ‖z‖ ≤ Kz) (hCcol : 0 ≤ Ccol) :
    mu (leastSingularBadEvent (fun w => shifted (X w) z) (tau N W kappa t) ∩ hsEvent X R) ≤
      ENNReal.ofReal (Ccol * t) + ENNReal.ofReal (Real.exp (-((N : ℝ) ^ (1 + kappa / 4)))) := by
  exact high_band_lsv_from_inputs numerics.N_pos numerics.entropy.W_pos ht
    numerics.Kz_nonneg hz hCcol inputs numerics.normal_bound numerics.final_gap

end HighBandLSV

end

-- Build-time foundational dependency audit; these commands introduce no assumptions.
#print axioms HighBandLSV.high_band_lsv_from_numerics
#print axioms HighBandLSV.ceiling_partition_arithmetic
#print axioms HighBandLSV.log_rawFixedBound
#print axioms HighBandLSV.eventually_final_log_dominance

/-! Actual-parameter closure and uniform large-N statement. -/
noncomputable section
open Section5Formalization Filter MeasureTheory
open scoped Topology
namespace HighBandLSV

structure ActualPartitionBounds (N W : ℕ) (Cw : ℝ) : Prop where
  count_pos : 0 < blockCount N W
  count_le : blockCount N W ≤ N
  rows_le : retainedRows N W * blockCount N W ≤ N
  deficit_le : (N : ℝ) - (retainedRows N W : ℝ) * blockCount N W ≤ 2 * blockCount N W
  rows_lower : (1 / (64 * Cw)) * (W : ℝ) ≤ (retainedRows N W : ℝ)
  count_scale : (blockCount N W : ℝ) ≤ (32 * Cw) * (N : ℝ) / (W : ℝ)

theorem actual_partition_bounds {N W : ℕ} {Cw : ℝ}
    (hseed : 8 ≤ seedSize N W) (hCw : 1 ≤ Cw) (hupper : (W : ℝ) ≤ Cw * (N : ℝ)) :
    ActualPartitionBounds N W Cw := by
  obtain ⟨hbN, hvb, hwidth⟩ := seed_size_bounds hseed
  obtain ⟨hJ, hJN, hcount, _, hbr, hrJ, _, hdef⟩ := ceiling_partition_arithmetic hseed hbN
  have hWp : 0 < W := by omega
  have hCwp : 0 < Cw := by linarith
  have hWv : (W : ℝ) ≤ Cw * (min W N : ℕ) := by
    by_cases h : W ≤ N
    · rw [min_eq_left h]
      nlinarith [mul_le_mul_of_nonneg_right hCw (Nat.cast_nonneg W)]
    · rw [min_eq_right (by omega : N ≤ W)]
      exact hupper
  have hvr : min W N ≤ 64 * retainedRows N W := by
    change seedSize N W ≤ 4 * retainedRows N W at hbr
    omega
  have hscales := partition_real_scales (N := (N : ℝ))
    (b := (seedSize N W : ℝ)) (r := (retainedRows N W : ℝ)) (Nat.cast_pos.mpr hWp)
    (Nat.cast_nonneg (blockCount N W)) hCwp hWv
    (by exact_mod_cast hvb) (by exact_mod_cast hvr) (by exact_mod_cast hcount)
  have hdefNat : N ≤ 2 * blockCount N W + retainedRows N W * blockCount N W :=
    Nat.sub_le_iff_le_add.mp hdef
  have hdefR : (N : ℝ) ≤ 2 * (blockCount N W : ℝ) +
      (retainedRows N W : ℝ) * (blockCount N W : ℝ) := by exact_mod_cast hdefNat
  refine ⟨hJ, hJN, hrJ, by linarith, ?_, hscales.1⟩
  convert hscales.2 using 1 <;> ring

/-- All numerical fields, with the literal floor/ceiling choices, are now
constructed eventually. No numerical certificate remains an external input. -/
theorem eventually_actual_numerics
    {chi kappa R Kz C C1 Cw : ℝ}
    (hchi : 0 < chi) (hk : 0 < kappa) (hR : 0 ≤ R) (hKz : 0 ≤ Kz)
    (hC : 0 < C) (hC1 : 0 < C1) (hCw : 1 ≤ Cw)
    (W : ℕ → ℕ) (hWp : ∀ᶠ n : ℕ in atTop, 0 < W n)
    (hband : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 2 + chi) ≤ (W n : ℝ))
    (hupper : ∀ᶠ n : ℕ in atTop, (W n : ℝ) ≤ Cw * (n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, NumericalCertificate n (blockCount n (W n)) (retainedRows n (W n))
      (W n : ℝ) kappa R Kz C C1 (1 / (64 * Cw)) Cw := by
  have hCwp : 0 < Cw := by linarith
  have hpower : ∀ᶠ n : ℕ in atTop, (64 : ℝ) ≤ (n : ℝ) ^ (1 / 2 + chi) := by
    simpa using (eventually_le_mul_natCast_rpow (A := 64) (B := 1)
      (p := 1 / 2 + chi) (by norm_num) (by linarith))
  have hseed : ∀ᶠ n : ℕ in atTop, 8 ≤ seedSize n (W n) := by
    filter_upwards [eventually_ge_atTop (64 : ℕ), hpower, hband] with n hn hp hb
    have hw : 64 ≤ W n := by exact_mod_cast hp.trans hb
    unfold seedSize
    omega
  have hparts : ∀ᶠ n : ℕ in atTop, ActualPartitionBounds n (W n) Cw := by
    filter_upwards [hseed, hupper] with n hs hu
    exact actual_partition_bounds hs hCw hu
  have hcount : ∀ᶠ n : ℕ in atTop,
      (blockCount n (W n) : ℝ) ≤ (32 * Cw) * (n : ℝ) / (W n : ℝ) := by
    filter_upwards [hparts] with n hn
    exact hn.count_scale
  have hnum := eventually_normal_numerics hk hchi
    (c := 1 / (64 * Cw)) (by positivity) (C0 := 32 * Cw) (by positivity)
    W (fun n => blockCount n (W n)) hWp hband hcount
  have hconst : ∀ A : ℝ, ∀ᶠ n : ℕ in atTop, A ≤ (n : ℝ) := by
    intro A
    simpa using (eventually_le_mul_natCast_rpow (A := A) (B := 1) (p := 1)
      (by norm_num) (by norm_num))
  have hcol : ∀ᶠ n : ℕ in atTop,
      1 + Cw * (Cw + 1 + 2 / kappa) ≤ (n : ℝ) ^ (2 * kappa) := by
    simpa using (eventually_le_mul_natCast_rpow
      (A := 1 + Cw * (Cw + 1 + 2 / kappa)) (B := 1) (p := 2 * kappa)
      (by norm_num) (by positivity))
  filter_upwards [hparts, hnum, hupper, hconst C,
    hconst (C1 * ((R + Kz + 1) + 1)), hconst (C * ((R + Kz + 1) + 1)),
    hconst (C * Cw), hcol] with n hp hn hu hc hm hr hv hg
  exact
    { N_pos := Nat.cast_pos.mp hn.1.N_pos
      J_pos := hp.count_pos
      J_le_N := hp.count_le
      rows_le := hp.rows_le
      deficit_le := hp.deficit_le
      rows_lower := hp.rows_lower
      R_nonneg := hR
      Kz_nonneg := hKz
      C_pos := hC
      C1_pos := hC1
      Cw_ge_one := hCw
      bandwidth_upper := hu
      constant_C := hc
      constant_mesh := hm
      constant_ratio := hr
      constant_variance := hv
      entropy := hn.1
      normal_growth := hn.2
      column_growth := hg }

/-- Uniform-in-z and uniform-in-t version of the paper's large-N statement,
with the actual partition and all scalar thresholds discharged. The only
remaining inputs are the explicitly documented probability certificates. -/
theorem eventually_high_band_lsv
    {Omega : ℕ → Type*} [∀ n, MeasurableSpace (Omega n)]
    (mu : ∀ n, Measure (Omega n))
    (X : ∀ n, Omega n → Matrix (Fin n) (Fin n) ℂ)
    {chi kappa R Kz C C1 Cw Ccol : ℝ}
    (hchi : 0 < chi) (hk : 0 < kappa) (_hkupper : kappa < chi / 4)
    (hR : 0 ≤ R) (hKz : 0 ≤ Kz) (hC : 0 < C) (hC1 : 0 < C1)
    (hCw : 1 ≤ Cw) (hCcol : 0 ≤ Ccol)
    (W : ℕ → ℕ) (hWp : ∀ᶠ n : ℕ in atTop, 0 < W n)
    (hband : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 2 + chi) ≤ (W n : ℝ))
    (hupper : ∀ᶠ n : ℕ in atTop, (W n : ℝ) ≤ Cw * (n : ℝ))
    (hinputs : ∀ᶠ n : ℕ in atTop, ∀ z : ℂ, ‖z‖ ≤ Kz →
      Nonempty (AppendixBInputs (Omega n) (mu n) n (blockCount n (W n)) (retainedRows n (W n))
        (X n) z (W n : ℝ) kappa R Kz C C1 Ccol)) :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℂ, ‖z‖ ≤ Kz → ∀ t : ℝ, 0 ≤ t →
      mu n (leastSingularBadEvent (fun w => shifted (X n w) z)
        (tau n (W n) kappa t) ∩ hsEvent (X n) R) ≤
      ENNReal.ofReal (Ccol * t) + ENNReal.ofReal (Real.exp (-((n : ℝ) ^ (1 + kappa / 4)))) := by
  have hnum := eventually_actual_numerics hchi hk hR hKz hC hC1 hCw W hWp hband hupper
  filter_upwards [hnum, hinputs] with n hn hi
  intro z hz t ht
  obtain ⟨inputs⟩ := hi z hz
  exact high_band_lsv_from_numerics hn inputs ht hz hCcol

end HighBandLSV
end

#print axioms HighBandLSV.eventually_actual_numerics
#print axioms HighBandLSV.eventually_high_band_lsv

