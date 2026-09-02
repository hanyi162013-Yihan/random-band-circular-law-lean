import BernoulliSection8.CellConcentration
import BernoulliSection10.IntervalConcatenation

/-!
# Physical cells, flattening, and fresh core laws

The complete-cell array and its chronological interval are connected by
literal coordinate equivalences preserving the IID law. Restricting each
cell to the sites after its three-site reset gives exactly the independent
core law used by Lemma 8.1, with no density assumption.
-/

open MeasureTheory
open scoped BigOperators NNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace BernoulliSection8

open BernoulliSection10

/-- A density-free version of the existing physical restriction transport. -/
theorem physicalRestriction_measurePreserving
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {W s t : ℕ} (e : Fin t ↪ Fin s) :
    MeasurePreserving (intervalRestriction (W := W) e)
      (intervalRowsLaw W s μ) (intervalRowsLaw W t μ) := by
  letI : IsProbabilityMeasure (physicalRowLaw W μ) := by
    unfold physicalRowLaw
    infer_instance
  exact measurePreserving_pi_restrict_embedding
    (physicalRowLaw W μ) (intervalRowEmbedding e)

/-- An entire scalar row index is decoded as cell and within-cell row. -/
def completeCellRowEquiv (W c K : ℕ) :
    Fin ((K * c) * W) ≃ Fin K × Fin (c * W) :=
  (finCongr (Nat.mul_assoc K c W)).trans finProdFinEquiv.symm

/-- Concatenate all physical cell rows in increasing cell order. -/
def flattenCompleteCells (W c K : ℕ) (x : Fin K → IntervalRows W c) :
    IntervalRows W (K * c) :=
  fun i => x (completeCellRowEquiv W c K i).1 (completeCellRowEquiv W c K i).2

/-- Read the actual complete cells from a chronological physical interval. -/
def unflattenCompleteCells (W c K : ℕ) (x : IntervalRows W (K * c)) :
    Fin K → IntervalRows W c :=
  fun k i => x ((completeCellRowEquiv W c K).symm (k, i))

@[simp] theorem unflatten_flatten_completeCells (W c K : ℕ)
    (x : Fin K → IntervalRows W c) :
    unflattenCompleteCells W c K (flattenCompleteCells W c K x) = x := by
  funext k i
  simp [unflattenCompleteCells, flattenCompleteCells]

@[simp] theorem flatten_unflatten_completeCells (W c K : ℕ)
    (x : IntervalRows W (K * c)) :
    flattenCompleteCells W c K (unflattenCompleteCells W c K x) = x := by
  funext i
  simp [unflattenCompleteCells, flattenCompleteCells]

theorem flattenCompleteCells_measurePreserving
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (W c K : ℕ) :
    MeasurePreserving (flattenCompleteCells W c K)
      (independentCoreLaw μ W c K) (intervalRowsLaw W (K * c) μ) := by
  letI : IsProbabilityMeasure (physicalRowLaw W μ) := by
    unfold physicalRowLaw
    infer_instance
  exact (measurePreserving_iid_reindex (physicalRowLaw W μ)
    (completeCellRowEquiv W c K)).comp
    (measurePreserving_iid_uncurry (physicalRowLaw W μ))

theorem unflattenCompleteCells_measurePreserving
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (W c K : ℕ) :
    MeasurePreserving (unflattenCompleteCells W c K)
      (intervalRowsLaw W (K * c) μ) (independentCoreLaw μ W c K) := by
  letI : IsProbabilityMeasure (physicalRowLaw W μ) := by
    unfold physicalRowLaw
    infer_instance
  exact (measurePreserving_iid_curry (physicalRowLaw W μ)).comp
    (measurePreserving_iid_reindex (physicalRowLaw W μ)
      (completeCellRowEquiv W c K).symm)

/-- Site `j` of cell `k`, in the chronological interval. -/
def completeCellSite {c K : ℕ} (k : Fin K) (j : Fin c) : Fin (K * c) :=
  finProdFinEquiv (k, j)

theorem completeCellRowEquiv_rowIndex (W c K : ℕ)
    (k : Fin K) (j : Fin c) (a : Fin W) :
    completeCellRowEquiv W c K (intervalRowIndex (completeCellSite k j) a) =
      (k, intervalRowIndex j a) := by
  apply finProdFinEquiv.injective
  simp only [completeCellRowEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  apply Fin.ext
  simp [intervalRowIndex, completeCellSite, finProdFinEquiv]
  ring

theorem unflattenCompleteCells_row (W c K : ℕ)
    (x : IntervalRows W (K * c)) (k : Fin K) (j : Fin c) (a : Fin W) :
    unflattenCompleteCells W c K x k (intervalRowIndex j a) =
      x (intervalRowIndex (completeCellSite k j) a) := by
  unfold unflattenCompleteCells
  congr 1
  apply (completeCellRowEquiv W c K).injective
  simp only [Equiv.apply_symm_apply, completeCellRowEquiv_rowIndex]

/-- The core is the suffix after the three reset sites. The use of
`3+s` instead of `s+3` only fixes a convenient literal finite index type. -/
def completeCellCore (W s : ℕ) (x : IntervalRows W (3 + s)) : IntervalRows W s :=
  intervalRestriction (Fin.natAddEmb 3) x

/-- The first three physical sites are the reset packet. -/
def completeCellReset (W s : ℕ) (x : IntervalRows W (3 + s)) : IntervalRows W 3 :=
  intervalRestriction (Fin.castAddEmb s) x

/-- The core stands to the left of the reset in chronological transfer
order. This polynomial identity holds even at singular interfaces. -/
theorem completeCellProduct_split (W s : ℕ) (z : ℂ)
    (x : IntervalRows W (3 + s)) (r : Fin (2 * W + 1)) :
    intervalClearedProduct W (3 + s) z x r =
      intervalClearedProduct W s z (completeCellCore W s x) r *
        intervalClearedProduct W 3 z (completeCellReset W s x) r :=
  intervalClearedProduct_split W 3 s z x r

theorem intervalSiteBlocks_flattenCompleteCells (W c K : ℕ) (z : ℂ)
    (x : Fin K → IntervalRows W c) (k : Fin K) (j : Fin c) :
    intervalSiteBlocks z (flattenCompleteCells W c K x) (completeCellSite k j) =
      intervalSiteBlocks z (x k) j := by
  apply PhysicalBlocks.ext <;> ext a b <;>
    simp only [intervalSiteBlocks, intervalPhysicalRow, flattenCompleteCells,
      completeCellRowEquiv_rowIndex]

theorem reverseMatrixProduct_cells {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K c : ℕ} (F : Fin (K * c) → Matrix ι ι ℂ) :
    reverseMatrixProduct F = reverseMatrixProduct
      (fun k : Fin K => reverseMatrixProduct (fun j : Fin c => F (completeCellSite k j))) := by
  have hblocks : List.ofFn F =
      (List.ofFn fun k : Fin K => List.ofFn fun j : Fin c => F (completeCellSite k j)).flatten := by
    rw [List.ofFn_mul]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext k
    apply congrArg List.ofFn
    funext j
    congr 1
    apply Fin.ext
    simp [completeCellSite, finProdFinEquiv]
    ring
  have hrev {n : ℕ} (G : Fin n → Matrix ι ι ℂ) :
      reverseMatrixProduct G = (List.ofFn G).reverse.prod :=
    congrArg List.prod (list_ofFn_fin_rev G)
  simp_rw [hrev]
  rw [hblocks, List.reverse_flatten, List.prod_flatten]
  simp only [List.map_reverse, List.map_map, List.map_ofFn, Function.comp_def]

/-- Flattening is compatible with the actual cleared exterior product;
the later cells remain on the left. -/
theorem intervalClearedProduct_flattenCompleteCells (W c K : ℕ) (z : ℂ)
    (x : Fin K → IntervalRows W c) (r : Fin (2 * W + 1)) :
    intervalClearedProduct W (K * c) z (flattenCompleteCells W c K x) r =
      reverseMatrixProduct (fun k : Fin K => intervalClearedProduct W c z (x k) r) := by
  unfold intervalClearedProduct
  rw [reverseMatrixProduct_cells]
  congr 1
  funext k
  congr 1
  funext j
  simp only [intervalClearedStep, intervalSiteBlocks_flattenCompleteCells]

/-- Actual physical interval product in the form used by reset
telescoping: one `core * reset` factor for each chronological cell. -/
theorem intervalClearedProduct_flatten_core_reset (W s K : ℕ) (z : ℂ)
    (x : Fin K → IntervalRows W (3 + s)) (r : Fin (2 * W + 1)) :
    intervalClearedProduct W (K * (3 + s)) z
      (flattenCompleteCells W (3 + s) K x) r =
      reverseMatrixProduct (fun k : Fin K =>
        intervalClearedProduct W s z (completeCellCore W s (x k)) r *
          intervalClearedProduct W 3 z (completeCellReset W s (x k)) r) := by
  rw [intervalClearedProduct_flattenCompleteCells]
  congr 1
  funext k
  exact completeCellProduct_split W s z (x k) r

def completeCellsCores (W s K : ℕ) (x : Fin K → IntervalRows W (3 + s)) :
    Fin K → IntervalRows W s :=
  fun k => completeCellCore W s (x k)

theorem completeCellCore_measurePreserving
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (W s : ℕ) :
    MeasurePreserving (completeCellCore W s)
      (intervalRowsLaw W (3 + s) μ) (intervalRowsLaw W s μ) :=
  physicalRestriction_measurePreserving μ (Fin.natAddEmb 3)

theorem completeCellsCores_measurePreserving
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (W s K : ℕ) :
    MeasurePreserving (completeCellsCores W s K)
      (independentCoreLaw μ W (3 + s) K) (independentCoreLaw μ W s K) := by
  letI : IsProbabilityMeasure (intervalRowsLaw W s μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  exact measurePreserving_pi _ _ (fun _ : Fin K => completeCellCore_measurePreserving μ W s)

/-- The `K` actual cell cores in a single physical interval have the
specified independent core law. This discharges cell independence for
the interval caller of Lemma 8.1. -/
theorem intervalCores_measurePreserving
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (W s K : ℕ) :
    MeasurePreserving
      (completeCellsCores W s K ∘ unflattenCompleteCells W (3 + s) K)
      (intervalRowsLaw W (K * (3 + s)) μ) (independentCoreLaw μ W s K) :=
  (completeCellsCores_measurePreserving μ W s K).comp
    (unflattenCompleteCells_measurePreserving μ W (3 + s) K)

theorem measurePreserving_real_preimage_le
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsFiniteMeasure ν]
    {f : Ω → Ξ} (hf : MeasurePreserving f μ ν) (E : Set Ξ) :
    μ.real (f ⁻¹' E) ≤ ν.real E :=
  ENNReal.toReal_mono (measure_ne_top ν E) (hf.measure_preimage_le E)

/-- Lemma 8.1 for the cores of the actual chronological `K`-cell interval.
The input sample is a single literal array of physical rows; its fresh
cores are extracted internally and have the common pressure in (8.33). -/
theorem lemma_8_1_interval_cells
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : ℝ≥0) (hA : 0 < A)
    (W s K : ℕ) (hW : 2 ≤ W) (hK : 0 < K) (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    (intervalRowsLaw W (K * (3 + s)) μ).real {x |
      3 * (A : ℝ) * Real.sqrt ((K : ℝ) * (Real.log W + u)) <
        finitePressureMax (fun r => |∑ k,
          (clippedCoreLog A W s z r
            (completeCellCore W s (unflattenCompleteCells W (3 + s) K x k)) -
            clippedCorePressure μ A W s z r)|)} ≤ 2 * Real.exp (-u) := by
  have h := measurePreserving_real_preimage_le
    (intervalCores_measurePreserving μ W s K)
    {x | 3 * (A : ℝ) * Real.sqrt ((K : ℝ) * (Real.log W + u)) <
      finitePressureMax (fun r => |∑ k,
        (clippedCoreLog A W s z r (x k) - clippedCorePressure μ A W s z r)|)}
  exact h.trans (lemma_8_1_independent_cores μ A hA W s K hW hK z hu)

end BernoulliSection8
