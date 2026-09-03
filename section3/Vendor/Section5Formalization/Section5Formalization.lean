/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/Section5Formalization/Section5Formalization.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise
import Mathlib.Data.Nat.Dist
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Vendor.GinibreLSV.Deterministic

noncomputable section

open scoped BigOperators
open Set MeasureTheory

namespace Section5Formalization

open GinibreLSV

/--
Distance on the cyclic index set `Fin N` used in the block-band adjacency condition.
-/
def cyclicDist (N : ℕ) (a b : Fin N) : ℕ :=
  let d : ℕ := Nat.dist a.1 b.1
  min d (N - d)

/--
Abstract data structure for the cyclic block partition in Fact 5.11.

This structure packages only the combinatorial outputs used later (block cardinality
bounds, partition coverage, and neighbor-distance compatibility). Exact proof of
existence is kept as an explicit interface assumption.
-/
structure BalancedCyclicPartition (N W : ℕ) where
  L : ℕ
  hL_pos : 0 < L
  blocks : Fin L → Finset (Fin N)
  d : ℕ
  c0 : ℕ
  C0 : ℕ
  h_cover : ∀ i : Fin N, ∃ j : Fin L, i ∈ blocks j
  h_disjoint : Pairwise fun i j => Disjoint (blocks i) (blocks j)
  h_card_lower : ∀ j : Fin L, d ≤ (blocks j).card
  h_card_upper : ∀ j : Fin L, (blocks j).card ≤ d + 1
  h_scale_lower : c0 * W ≤ d
  h_scale_upper : d + 1 ≤ C0 * W
  h_block_count : L * W ≤ C0 * N
  neighbors : Fin L → Finset (Fin L)
  h_neighbor_dist :
    ∀ {i j : Fin L} (hij : j ∈ neighbors i) (a : Fin N) (ha : a ∈ blocks i)
      (b : Fin N) (hb : b ∈ blocks j), cyclicDist N a b ≤ W

/-- A cyclic-distance estimate inherited from the ordinary distance estimate. -/
lemma cyclicDist_le_of_dist_le {N W : ℕ} {a b : Fin N}
    (h : Nat.dist a.1 b.1 ≤ W) : cyclicDist N a b ≤ W := by
  exact (min_le_left _ _).trans h

/--
Mathlib's finite equipartition theorem supplies the balanced-cardinality part
of Fact 5.11: for every positive `L ≤ N`, `Fin N` has exactly `L` parts, each
of cardinality `N / L` or `N / L + 1`.
-/
theorem exists_balanced_finpartition (N L : ℕ) (hL : 0 < L) (hLN : L ≤ N) :
    ∃ P : Finpartition (Finset.univ : Finset (Fin N)),
      P.IsEquipartition ∧ P.parts.card = L ∧
        ∀ B ∈ P.parts, N / L ≤ B.card ∧ B.card ≤ N / L + 1 := by
  obtain ⟨P, hP, hcard⟩ :=
    Finpartition.exists_equipartition_card_eq
      (s := (Finset.univ : Finset (Fin N))) (n := L) hL.ne' (by simpa using hLN)
  refine ⟨P, hP, hcard, ?_⟩
  intro B hB
  constructor
  · simpa [hcard] using hP.average_le_card_part hB
  · simpa [hcard] using hP.card_part_le_average_add_one hB

/--
The normal space of the deleted-row operator `P_i(X-zI)^*` is represented as the
orthogonal complement of the span of all other columns; this is the
paper-level normal-space object used for distance-to-span and least-singular-value
reductions.
-/
def normalSpaceDeletedColumn {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    Submodule ℂ (EuclideanSpace ℂ (Fin N)) :=
  (columnSpanExcept A i)ᗮ

@[simp]
lemma normalSpaceDeletedColumn_eq (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    normalSpaceDeletedColumn (N := N) A i = (columnSpanExcept A i)ᗮ := by
  rfl

/--
The abstract kernel/range identity behind
`ker (P_i (X-zI)^*) = (span(other columns))ᗮ`.
Once a deleted-column synthesis map has the stated range, its adjoint kernel
is exactly the paper's normal space.
-/
theorem normalSpaceDeletedColumn_eq_ker_adjoint_of_range_eq
    {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (A : Matrix (Fin N) (Fin N) ℂ) (i : Fin N)
    (T : E →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (hrange : T.range = columnSpanExcept A i) :
    normalSpaceDeletedColumn A i = T.adjoint.ker := by
  rw [normalSpaceDeletedColumn, ← hrange]
  exact LinearMap.orthogonal_range T

/-- Canonical synthesis operator whose range is the span of the other columns. -/
def deletedColumnSynthesis {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    columnSpanExcept A i →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
  (columnSpanExcept A i).subtype

/-- Canonical realization of the paper's deleted-row adjoint operator. -/
def deletedRowAdjoint {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    EuclideanSpace ℂ (Fin N) →ₗ[ℂ] columnSpanExcept A i :=
  LinearMap.adjoint (𝕜 := ℂ) (E := columnSpanExcept A i)
    (F := EuclideanSpace ℂ (Fin N)) (deletedColumnSynthesis A i)

/-- The kernel of the canonical deleted-row adjoint is exactly the normal space. -/
theorem ker_deletedRowAdjoint {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    (deletedRowAdjoint A i).ker = normalSpaceDeletedColumn A i := by
  have horth :
      (deletedColumnSynthesis A i).rangeᗮ = (deletedRowAdjoint A i).ker := by
    simpa [deletedRowAdjoint] using
      (LinearMap.orthogonal_range (𝕜 := ℂ) (E := columnSpanExcept A i)
        (F := EuclideanSpace ℂ (Fin N)) (deletedColumnSynthesis A i))
  rw [normalSpaceDeletedColumn, ← horth]
  congr 1
  simp [deletedColumnSynthesis]

/--
Distance-to-span inequality exactly in the paper's form:
`‖v_i‖ · dist([A]^i,[H]^i) ≤ ‖Av‖`.
-/
lemma distance_to_span_implication {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (v : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    ‖v i‖ * columnDistance A i ≤ ‖A.toEuclideanLin v‖ := by
  simpa using GinibreLSV.norm_coordinate_mul_columnDistance_le A i v

/--
The cyclic path/`π` product identity from the proof of
`eq:path-telescope`.

This is written for the canonical one-step update
`π(j) = l` when `j = k`, `π(j)=j` otherwise.
-/
theorem cyclic_path_telescope {L : ℕ} (ζ : Fin L → ℝ) (k l : Fin L)
    (_hkl : k ≠ l) (hz : ζ k ≠ 0) :
    let π : Fin L → Fin L := fun j => if j = k then l else j
    (∏ j : Fin L, ζ (π j)) = (∏ j : Fin L, ζ j) * (ζ l / ζ k) := by
  classical
  intro π
  have hk : k ∈ (Finset.univ : Finset (Fin L)) := Finset.mem_univ k
  have hreplace :
      (∏ j : Fin L, ζ (π j)) =
        ζ l * (∏ j ∈ (Finset.univ : Finset (Fin L)).erase k, ζ j) := by
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin L))
      (fun j => ζ (π j)) hk]
    simp only [π, if_pos]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro j hj
    simp [π, (Finset.mem_erase.mp hj).1]
  have horiginal :
      ζ k * (∏ j ∈ (Finset.univ : Finset (Fin L)).erase k, ζ j) =
        ∏ j : Fin L, ζ j := by
    simpa using Finset.mul_prod_erase (Finset.univ : Finset (Fin L)) ζ hk
  calc
    (∏ j : Fin L, ζ (π j)) =
        ζ l * (∏ j ∈ (Finset.univ : Finset (Fin L)).erase k, ζ j) := hreplace
    _ = (ζ k * (∏ j ∈ (Finset.univ : Finset (Fin L)).erase k, ζ j)) *
        (ζ l / ζ k) := by
      field_simp [hz]
    _ = (∏ j : Fin L, ζ j) * (ζ l / ζ k) := by
      rw [horiginal]

/-- Telescoping of all successive ratios along an arbitrary finite path. -/
theorem cyclic_path_ratio_telescope_real (ζ : ℕ → ℝ)
    (hζ : ∀ q, ζ q ≠ 0) (s : ℕ) :
    (∏ q ∈ Finset.range s, ζ (q + 1) / ζ q) = ζ s / ζ 0 := by
  induction s with
  | zero => simp [hζ 0]
  | succ s ih =>
      rw [Finset.prod_range_succ, ih]
      field_simp [hζ]

/-- Cross-multiplied path telescope, valid even when some path weights vanish. -/
theorem cyclic_path_product_telescope (ζ : ℕ → ℝ) (s : ℕ) :
    (∏ q ∈ Finset.range s, ζ (q + 1)) * ζ 0 =
      (∏ q ∈ Finset.range s, ζ q) * ζ s := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      calc
        ((∏ q ∈ Finset.range s, ζ (q + 1)) * ζ (s + 1)) * ζ 0 =
            ((∏ q ∈ Finset.range s, ζ (q + 1)) * ζ 0) * ζ (s + 1) := by ring
        _ = ((∏ q ∈ Finset.range s, ζ q) * ζ s) * ζ (s + 1) := by rw [ih]

/--
Algebraic cancellation between a complex block-net entropy factor and the
two-dimensional small-ball factor when they occur with the same exponent.
-/
lemma block_net_smallBall_cancellation (C ζ h ρ t : ℝ) (m : ℕ)
    (hζ : ζ ≠ 0) (hh : h ≠ 0) :
    (C * ζ / h ^ 2) ^ m * (C * ρ ^ 2 * t ^ 2 / ζ) ^ m =
      (C ^ 2 * ρ ^ 2 * t ^ 2 / h ^ 2) ^ m := by
  rw [← mul_pow]
  congr 1
  field_simp [hζ, hh] <;> ring

/--
The deterministic exponent ledger behind `eq:entropy-versus-gain`.
If entropy and the desired final exponent are each at most half of the
small-ball gain, the logarithmic union bound has the required sign.
-/
lemma entropy_vs_gain_ledger (gain entropy target : ℝ)
    (hentropy : 2 * entropy ≤ gain) (htarget : 2 * target ≤ gain) :
    -gain + entropy ≤ -target := by
  linarith

/-- The Section 5 specialization of the abstract exponent ledger. -/
lemma section5_exponent_ledger (c C W D NlogN L c' Npow : ℝ)
    (hentropy : 2 * (C * (NlogN + L * D)) ≤ c * W * D)
    (htarget : 2 * (c' * Npow) ≤ c * W * D) :
    -(c * W * D) + C * (NlogN + L * D) ≤ -(c' * Npow) := by
  exact entropy_vs_gain_ledger (c * W * D) (C * (NlogN + L * D))
    (c' * Npow) hentropy htarget

/--
Deterministic bridge from column distances to a least-singular-value lower bound.
-/
theorem least_singular_via_column_distances
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (δ : ℝ) (hn : 0 < n) (hcol : ∀ j, δ ≤ GinibreLSV.columnDistance A j) :
    δ / (n : ℝ) ≤ GinibreLSV.leastSingularValue A := by
  exact GinibreLSV.delta_div_nat_le_leastSingularValue hn A hcol

/--
The complex small-ball event used by the block-net lemma.
-/
def complexSmallBall {Ω : Type*} {m : ℕ}
    (ξ : Ω → EuclideanSpace ℂ (Fin m))
    (u : EuclideanSpace ℂ (Fin m)) (w : ℂ) (t : ℝ) : Set Ω :=
  {ω | ‖inner ℂ (ξ ω) u - w‖ ≤ t}

/--
Explicit interface for Lemma `block-net`.  It records the finite parameter
families, covering property, cardinality estimate, and the actual
measure-valued small-ball estimate.  Density and projection arguments are
inputs through this structure.
-/
structure ComplexBlockNetInterface
    (Ω : Type*) [MeasurableSpace Ω] (m : ℕ) (μ : Measure Ω)
    (ξ : Ω → EuclideanSpace ℂ (Fin m)) (h t ρ C : ℝ) where
  Params : Type*
  [paramsFintype : Fintype Params]
  net : Params → Set (EuclideanSpace ℂ (Fin m))
  zeta : Params → ℝ
  zeta_pos : ∀ p, 0 < zeta p
  family_count : (Fintype.card Params : ℝ) ≤ (C / h) ^ 3
  covers : ∀ v : EuclideanSpace ℂ (Fin m), ‖v‖ ≤ 1 →
    ∃ p, ∃ u ∈ net p, ‖v - u‖ ≤ C * h
  net_card : ∀ p, ((net p).ncard : ℝ) ≤ (C * zeta p / h ^ 2) ^ m
  small_ball : ∀ p, ∀ u ∈ net p, ∀ w : ℂ,
    μ (complexSmallBall ξ u w t) ≤
      ENNReal.ofReal (min 1 (C * ρ ^ 2 * t ^ 2 / zeta p))

/-- Data needed for tensorization.  The tensorized estimate itself is proved
from independence in `ProbabilityCore`; it is no longer assumed as a field. -/
structure TensorizedSmallBallInterface
    (Ω : Type*) [MeasurableSpace Ω] (L r : ℕ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] where
  rowEvent : Fin L × Fin r → Set Ω
  targetEvent : Set Ω
  rowBound : Fin L → ENNReal
  target_subset : targetEvent ⊆ ⋂ p, rowEvent p
  independent_rows : ProbabilityTheory.iIndepSet rowEvent μ
  row_small_ball : ∀ p, μ (rowEvent p) ≤ rowBound p.1

/-- Index set for the union over the column, small block, and large block. -/
abbrev NormalStructureIndex (N L : ℕ) := Fin N × Fin L × Fin L

/--
Probabilistic interface remaining after the deterministic net and exponent
calculation.  The final normal-structure estimate is not a field: it is
derived below from fixed-index estimates and a finite-union ledger.
-/
structure Section5ProbabilityInterface
    (Ω : Type*) [MeasurableSpace Ω] (N L : ℕ) (μ : Measure Ω)
    (K κ : ℝ) where
  badNormal : Set Ω
  fixedBad : NormalStructureIndex N L → Set Ω
  fixedBound : ENNReal
  bad_subset : badNormal ⊆ ⋃ q, fixedBad q
  fixed_small_ball : ∀ q, μ (fixedBad q) ≤ fixedBound
  exponent_ledger :
    (∑' _q : NormalStructureIndex N L, fixedBound) ≤
      ENNReal.ofReal (Real.exp (-((N : ℝ) ^ (1 + κ / 4))))

/--
The corrected normal-structure probability bound.  Countable subadditivity,
the fixed-index small-ball estimate, and the exponent ledger are assembled
inside Lean.
-/
theorem theorem5_51093
    {Ω : Type*} [MeasurableSpace Ω] {N W : ℕ} (μ : Measure Ω)
    (K κ : ℝ) (_partition : BalancedCyclicPartition N W)
    (_prob : Section5ProbabilityInterface Ω N _partition.L μ K κ) :
    μ _prob.badNormal ≤
      ENNReal.ofReal (Real.exp (-((N : ℝ) ^ (1 + κ / 4)))) := by
  calc
    μ _prob.badNormal ≤ μ (⋃ q, _prob.fixedBad q) :=
      measure_mono _prob.bad_subset
    _ ≤ ∑' q, μ (_prob.fixedBad q) := measure_iUnion_le _
    _ ≤ ∑' _q : NormalStructureIndex N _partition.L, _prob.fixedBound :=
      ENNReal.tsum_le_tsum fun q => _prob.fixed_small_ball q
    _ ≤ ENNReal.ofReal (Real.exp (-((N : ℝ) ^ (1 + κ / 4)))) :=
      _prob.exponent_ledger

/-- A reusable finite-union small-ball assembly, used for the final column union. -/
theorem finite_union_probability_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (bad : Set Ω) (piece : ι → Set Ω)
    (pieceBound totalBound : ENNReal)
    (hcover : bad ⊆ ⋃ i, piece i)
    (hpiece : ∀ i, μ (piece i) ≤ pieceBound)
    (hledger : (∑' _i : ι, pieceBound) ≤ totalBound) :
    μ bad ≤ totalBound := by
  calc
    μ bad ≤ μ (⋃ i, piece i) := measure_mono hcover
    _ ≤ ∑' i, μ (piece i) := measure_iUnion_le _
    _ ≤ ∑' _i : ι, pieceBound := ENNReal.tsum_le_tsum hpiece
    _ ≤ totalBound := hledger

/--
Final measure-theoretic assembly for the least-singular-value event: split
according to the normal-structure good event and use subadditivity.
-/
theorem final_lsv_probability_assembly
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (smallSV opBound goodNormal : Set Ω) (mainBound tailBound : ENNReal)
    (hgood : μ (smallSV ∩ opBound ∩ goodNormal) ≤ mainBound)
    (hbad : μ (opBound \ goodNormal) ≤ tailBound) :
    μ (smallSV ∩ opBound) ≤ mainBound + tailBound := by
  have hsubset :
      smallSV ∩ opBound ⊆
        (smallSV ∩ opBound ∩ goodNormal) ∪ (opBound \ goodNormal) := by
    intro ω hω
    rcases hω with ⟨hsmall, hop⟩
    by_cases hnormal : ω ∈ goodNormal
    · exact Or.inl ⟨⟨hsmall, hop⟩, hnormal⟩
    · exact Or.inr ⟨hop, hnormal⟩
  calc
    μ (smallSV ∩ opBound) ≤
        μ ((smallSV ∩ opBound ∩ goodNormal) ∪ (opBound \ goodNormal)) :=
      measure_mono hsubset
    _ ≤ μ (smallSV ∩ opBound ∩ goodNormal) + μ (opBound \ goodNormal) :=
      measure_union_le _ _
    _ ≤ mainBound + tailBound := add_le_add hgood hbad

end Section5Formalization
