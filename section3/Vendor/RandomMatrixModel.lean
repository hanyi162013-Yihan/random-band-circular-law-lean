/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RandomMatrixModel.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.PlanarSmallBall
import Vendor.GinibreLSV.Conditioning
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# A concrete independent-entry complex band model

Samples are stored column first. Zero profile coefficients do not require a
density for the resulting degenerate matrix entry: the density hypothesis is
on the unscaled atom. No real/imaginary independence is assumed.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set

noncomputable section

namespace HighBandLSV

instance complexMatrixMeasurableSpace (N : Nat) :
    MeasurableSpace (Matrix (Fin N) (Fin N) Complex) := borel _

instance complexMatrixBorelSpace (N : Nat) : BorelSpace (Matrix (Fin N) (Fin N) Complex) :=
  ⟨rfl⟩

abbrev AtomColumn (N : Nat) := Fin N → Complex
abbrev MatrixSample (N : Nat) := Fin N → AtomColumn N

/-- The normalized variance-profile assumptions and independent atom laws.
The first argument of `atomLaw` is the column, the second the row. -/
structure PlanarBandModel (N W : Nat) (c C L : Real) where
  sigma : Matrix (Fin N) (Fin N) Real
  sigma_nonneg : ∀ i j, 0 ≤ sigma i j
  local_floor : ∀ i j, Section5Formalization.cyclicDist N i j ≤ W →
    c / (W : Real) ≤ sigma i j ^ 2
  upper : ∀ i j, sigma i j ^ 2 ≤ C / (W : Real)
  row_normalization : ∀ i, ∑ j, sigma i j ^ 2 = 1
  atomLaw : Fin N → Fin N → Measure Complex
  atom_probability : ∀ j i, IsProbabilityMeasure (atomLaw j i)
  atom_density : ∀ j i, atomLaw j i ≤ ENNReal.ofReal L • (volume : Measure Complex)

namespace PlanarBandModel

variable {N W : Nat} {c C L : Real} (m : PlanarBandModel N W c C L)

def columnLaw (j : Fin N) : Measure (AtomColumn N) := Measure.pi (m.atomLaw j)

instance columnLaw_probability (j : Fin N) : IsProbabilityMeasure (m.columnLaw j) := by
  letI : ∀ i, IsProbabilityMeasure (m.atomLaw j i) := m.atom_probability j
  unfold columnLaw
  infer_instance

def law : Measure (MatrixSample N) := Measure.pi m.columnLaw

instance law_probability : IsProbabilityMeasure m.law := by
  unfold law
  infer_instance

def matrix (omega : MatrixSample N) : Matrix (Fin N) (Fin N) Complex :=
  fun i j => (m.sigma i j : Complex) * omega j i

theorem continuous_matrix : Continuous m.matrix := by
  unfold matrix
  fun_prop

theorem measurable_matrix : Measurable m.matrix := m.continuous_matrix.measurable

theorem atom_marginal (j i : Fin N) :
    Measure.map (fun x : AtomColumn N => x i) (m.columnLaw j) = m.atomLaw j i := by
  letI : ∀ i, IsProbabilityMeasure (m.atomLaw j i) := m.atom_probability j
  exact (measurePreserving_eval (m.atomLaw j) i).map_eq

theorem column_marginal (j : Fin N) :
    Measure.map (fun omega : MatrixSample N => omega j) m.law = m.columnLaw j :=
  (measurePreserving_eval m.columnLaw j).map_eq

theorem independent_columns :
    iIndepFun (fun j (omega : MatrixSample N) => omega j) m.law := by
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

theorem independent_column_atoms (j : Fin N) :
    iIndepFun (fun i (x : AtomColumn N) => x i) (m.columnLaw j) := by
  letI : ∀ i, IsProbabilityMeasure (m.atomLaw j i) := m.atom_probability j
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

include m in
/-- Row normalization supplies the paper's upper bandwidth bound. -/
theorem bandwidth_le (hN : 0 < N) (hW : 0 < W) :
    (W : Real) ≤ C * N := by
  let i : Fin N := ⟨0, hN⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => m.upper i j)
  rw [m.row_normalization i] at hsum
  have h : (1 : Real) ≤ (N : Real) * (C / (W : Real)) := by
    simpa using hsum
  have hw : 0 < (W : Real) := Nat.cast_pos.mpr hW
  have ht := mul_le_mul_of_nonneg_right h hw.le
  field_simp at ht
  nlinarith

def coefficients (j : Fin N) (u : Fin N → Complex) (i : Fin N) : Complex :=
  star (u i) * (m.sigma i j : Complex)

def energy (j : Fin N) (u : Fin N → Complex) : Real :=
  ∑ i, ‖m.coefficients j u i‖ ^ 2

def linearForm (j : Fin N) (u : Fin N → Complex) (x : AtomColumn N) : Complex :=
  ∑ i, m.coefficients j u i * x i

theorem coefficient_norm_sq (j i : Fin N) (u : Fin N → Complex) :
    ‖m.coefficients j u i‖ ^ 2 = ‖u i‖ ^ 2 * m.sigma i j ^ 2 := by
  simp [coefficients, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]

theorem linearForm_matrix (j : Fin N) (u : Fin N → Complex) (omega : MatrixSample N) :
    m.linearForm j u (omega j) = ∑ i, star (u i) * m.matrix omega i j := by
  simp only [linearForm, coefficients, matrix, mul_assoc]

theorem energy_nonneg (j : Fin N) (u : Fin N → Complex) : 0 ≤ m.energy j u :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The band floor transfers block mass to the actual linear-form energy. -/
theorem energy_ge_block (j : Fin N) (u : Fin N → Complex) (B : Finset (Fin N))
    (hB : ∀ i ∈ B, Section5Formalization.cyclicDist N i j ≤ W) :
    (c / (W : Real)) * (∑ i ∈ B, ‖u i‖ ^ 2) ≤ m.energy j u := by
  rw [Finset.mul_sum]
  calc
    (∑ i ∈ B, c / (W : Real) * ‖u i‖ ^ 2) ≤
        ∑ i ∈ B, ‖m.coefficients j u i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [m.coefficient_norm_sq]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_right (m.local_floor i j (hB i hi)) (sq_nonneg ‖u i‖)
    _ ≤ m.energy j u :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
        (fun _ _ _ => sq_nonneg _)

theorem coefficients_ne_zero (j : Fin N) (u : Fin N → Complex)
    (henergy : 0 < m.energy j u) : m.coefficients j u ≠ 0 := by
  intro h
  have hz : m.energy j u = 0 := by simp [energy, h]
  linarith

/-- A genuine frozen-column estimate derived from atom laws, not assumed. -/
theorem linearForm_small_ball (hL : 0 ≤ L) (j : Fin N) (u : Fin N → Complex)
    (henergy : 0 < m.energy j u) (w : Complex) {s : Real} (hs : 0 ≤ s) :
    m.columnLaw j {x | ‖m.linearForm j u x - w‖ ≤ s} ≤
      ENNReal.ofReal (min 1 (Real.pi * ((N : Real) * L / m.energy j u) * s ^ 2)) := by
  have hD : ∀ i, Measure.map (fun x : AtomColumn N => x i) (m.columnLaw j) ≤
      ENNReal.ofReal L • (volume : Measure Complex) := by
    intro i
    rw [m.atom_marginal]
    exact m.atom_density j i
  have hI := m.independent_column_atoms j
  have ha := m.coefficients_ne_zero j u henergy
  change m.columnLaw j {x | ‖(∑ i, m.coefficients j u i * x i) - w‖ ≤ s} ≤ _
  unfold energy
  apply Planar.sum_small_ball
  all_goals first | exact hL | exact hs | exact hI | exact ha | exact hD |
    exact (fun i => measurable_pi_apply i)

theorem linearForm_small_ball_of_energy_lower (hL : 0 ≤ L)
    (j : Fin N) (u : Fin N → Complex) {E : Real} (hE : 0 < E)
    (hlower : E ≤ m.energy j u) (w : Complex) {s : Real} (hs : 0 ≤ s) :
    m.columnLaw j {x | ‖m.linearForm j u x - w‖ ≤ s} ≤
      ENNReal.ofReal (min 1 (Real.pi * ((N : Real) * L / E) * s ^ 2)) := by
  apply (m.linearForm_small_ball hL j u (hE.trans_le hlower) w hs).trans
  apply ENNReal.ofReal_le_ofReal
  apply min_le_min_left
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg s)
  apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
  exact div_le_div_of_nonneg_left (by positivity) hE hlower

/-- The band-local form of the frozen-column estimate. -/
theorem block_small_ball (hL : 0 ≤ L) (hc : 0 < c) (hW : 0 < W)
    (j : Fin N) (u : Fin N → Complex) (B : Finset (Fin N))
    (hB : ∀ i ∈ B, Section5Formalization.cyclicDist N i j ≤ W)
    {d : Real} (hd : 0 < d) (hmass : d ^ 2 ≤ ∑ i ∈ B, ‖u i‖ ^ 2)
    (w : Complex) {s : Real} (hs : 0 ≤ s) :
    m.columnLaw j {x | ‖m.linearForm j u x - w‖ ≤ s} ≤
      ENNReal.ofReal (min 1
        (Real.pi * ((N : Real) * L / ((c / W) * d ^ 2)) * s ^ 2)) := by
  have hcw : 0 < c / (W : Real) := div_pos hc (Nat.cast_pos.mpr hW)
  apply m.linearForm_small_ball_of_energy_lower hL j u (mul_pos hcw (sq_pos_of_pos hd))
    _ w hs
  exact (mul_le_mul_of_nonneg_left hmass hcw.le).trans (m.energy_ge_block j u B hB)

/-- Functions of distinct original columns are independent. This is the
row-independence needed for the deleted-row adjoint, not independence of rows of X. -/
theorem independent_linearForms (u : Fin N → Fin N → Complex) (w : Fin N → Complex) :
    iIndepFun (fun j (omega : MatrixSample N) =>
      m.linearForm j (u j) (omega j) - w j) m.law := by
  apply iIndepFun_pi (μ := m.columnLaw)
    (X := fun j x => m.linearForm j (u j) x - w j)
  intro j
  apply Measurable.aemeasurable
  unfold linearForm
  fun_prop

/-- Exact tensorization for any selected set of adjoint rows. -/
theorem selected_rows_probability (u : Fin N → Fin N → Complex) (w : Fin N → Complex)
    (S : Finset (Fin N)) (s : Real) :
    m.law {omega | ∀ j ∈ S, ‖m.linearForm j (u j) (omega j) - w j‖ ≤ s} =
      ∏ j ∈ S, m.columnLaw j {x | ‖m.linearForm j (u j) x - w j‖ ≤ s} := by
  have hI := m.independent_linearForms u w
  have hset : MeasurableSet {z : Complex | ‖z‖ ≤ s} :=
    measurableSet_le measurable_norm measurable_const
  have heq := hI.measure_inter_preimage_eq_mul S (sets := fun _ => {z : Complex | ‖z‖ ≤ s})
    (fun _ _ => hset)
  have htarget :
      {omega : MatrixSample N | ∀ j ∈ S, ‖m.linearForm j (u j) (omega j) - w j‖ ≤ s} =
      ⋂ j ∈ S, (fun omega : MatrixSample N => m.linearForm j (u j) (omega j) - w j) ⁻¹'
        {z : Complex | ‖z‖ ≤ s} := by ext omega; simp
  rw [htarget, heq]
  apply Finset.prod_congr rfl
  intro j _
  let T : Set (AtomColumn N) := {x | ‖m.linearForm j (u j) x - w j‖ ≤ s}
  have hf : Measurable (fun x : AtomColumn N => ‖m.linearForm j (u j) x - w j‖) := by
    unfold linearForm
    fun_prop
  have hT : MeasurableSet T := measurableSet_le hf measurable_const
  change m.law ((fun omega : MatrixSample N => omega j) ⁻¹' T) = m.columnLaw j T
  exact (measurePreserving_eval m.columnLaw j).measure_preimage hT.nullMeasurableSet

/-- The fixed-vector product estimate follows from the concrete atom laws. -/
theorem selected_rows_small_ball (hL : 0 ≤ L)
    (u : Fin N → Fin N → Complex) (w : Fin N → Complex) (S : Finset (Fin N))
    (E : Fin N → Real) (hE : ∀ j ∈ S, 0 < E j)
    (hlower : ∀ j ∈ S, E j ≤ m.energy j (u j)) {s : Real} (hs : 0 ≤ s) :
    m.law {omega | ∀ j ∈ S, ‖m.linearForm j (u j) (omega j) - w j‖ ≤ s} ≤
      ∏ j ∈ S, ENNReal.ofReal (min 1 (Real.pi * ((N : Real) * L / E j) * s ^ 2)) := by
  rw [m.selected_rows_probability]
  apply Finset.prod_le_prod'
  intro j hj
  exact m.linearForm_small_ball_of_energy_lower hL j (u j) (hE j hj) (hlower j hj) (w j) hs

/-- A finite union of fixed-vector net events; probability estimates are now
proved, while any geometric covering implication must be proved separately. -/
theorem finite_net_small_ball {Q : Type*} [Fintype Q]
    (hL : 0 ≤ L) (u : Q → Fin N → Fin N → Complex) (w : Q → Fin N → Complex)
    (S : Finset (Fin N)) (E : Q → Fin N → Real)
    (hE : ∀ q j, j ∈ S → 0 < E q j)
    (hlower : ∀ q j, j ∈ S → E q j ≤ m.energy j (u q j))
    {s : Real} (hs : 0 ≤ s) :
    m.law (⋃ q, {omega | ∀ j ∈ S, ‖m.linearForm j (u q j) (omega j) - w q j‖ ≤ s}) ≤
      ∑ q, ∏ j ∈ S, ENNReal.ofReal (min 1 (Real.pi * ((N : Real) * L / E q j) * s ^ 2)) := by
  exact (measure_iUnion_fintype_le m.law _).trans
    (Finset.sum_le_sum fun q _ => m.selected_rows_small_ball hL (u q) (w q) S
      (E q) (hE q) (hlower q) hs)

end PlanarBandModel

namespace ColumnExposure

variable {n W : Nat} {c C L : Real}
  (m : PlanarBandModel (n + 1) W c C L) (j : Fin (n + 1))

abbrev Rest := Fin n → AtomColumn (n + 1)

def restLaw : Measure (Rest (n := n)) :=
  Measure.pi (fun k => m.columnLaw (j.succAbove k))

instance restLaw_probability : IsProbabilityMeasure (restLaw m j) := by
  unfold restLaw
  infer_instance

def expose : MatrixSample (n + 1) ≃ᵐ AtomColumn (n + 1) × Rest (n := n) :=
  MeasurableEquiv.piFinSuccAbove (fun _ => AtomColumn (n + 1)) j

/-- A proved measure-preserving exposure of an actual column. -/
theorem expose_preserving :
    MeasurePreserving (expose (n := n) j) m.law ((m.columnLaw j).prod (restLaw m j)) :=
  measurePreserving_piFinSuccAbove m.columnLaw j

def conditionalKernel : Kernel (Rest (n := n)) (AtomColumn (n + 1)) :=
  Kernel.const _ (m.columnLaw j)

theorem conditionalKernel_apply (rest : Rest (n := n)) :
    conditionalKernel m j rest = m.columnLaw j := rfl

/-- The reconstructed law is an actual product law, not a disintegration assumption. -/
theorem conditional_jointLaw :
    restLaw m j ⊗ₘ conditionalKernel m j = (restLaw m j).prod (m.columnLaw j) := by
  simp [conditionalKernel]

/-- Uniform frozen-normal estimates integrate without conditioning on an HS event.
The coefficients and the center may measurably depend on all other columns. -/
theorem moving_linearForm_small_ball (hL : 0 ≤ L)
    (u : Rest (n := n) → Fin (n + 1) → Complex) (hu : Measurable u)
    (w : Rest (n := n) → Complex) (hw : Measurable w)
    (G : Set (Rest (n := n))) (hG : MeasurableSet G)
    {E : Real} (hE : 0 < E)
    (henergy : ∀ rest ∈ G, E ≤ m.energy j (u rest))
    {s : Real} (hs : 0 ≤ s) :
    m.law {omega | (expose j omega).2 ∈ G ∧
      ‖m.linearForm j (u (expose j omega).2) (expose j omega).1 -
        w (expose j omega).2‖ ≤ s} ≤
      ENNReal.ofReal (min 1 (Real.pi * (((n + 1 : Nat) : Real) * L / E) * s ^ 2)) := by
  let event : Set (AtomColumn (n + 1) × Rest (n := n)) :=
    {p | p.2 ∈ G ∧ ‖m.linearForm j (u p.2) p.1 - w p.2‖ ≤ s}
  have hevent : MeasurableSet event := by
    have hf : Measurable (fun p : AtomColumn (n + 1) × Rest (n := n) =>
        ‖m.linearForm j (u p.2) p.1 - w p.2‖) := by
      unfold PlanarBandModel.linearForm PlanarBandModel.coefficients
      fun_prop
    exact (hG.preimage measurable_snd).inter (measurableSet_le hf measurable_const)
  change m.law ((expose j) ⁻¹' event) ≤ _
  rw [(expose_preserving m j).measure_preimage hevent.nullMeasurableSet]
  apply GinibreLSV.prod_measure_le_of_forall_left_fiber _ _ event hevent
  intro rest
  by_cases hrest : rest ∈ G
  · have hfiber : (fun x : AtomColumn (n + 1) => (x, rest)) ⁻¹' event =
        {x | ‖m.linearForm j (u rest) x - w rest‖ ≤ s} := by
      ext x
      simp [event, hrest]
    rw [hfiber]
    exact m.linearForm_small_ball_of_energy_lower hL j (u rest) hE (henergy rest hrest) (w rest) hs
  · have hempty : (fun x : AtomColumn (n + 1) => (x, rest)) ⁻¹' event = ∅ := by
      ext x
      simp [event, hrest]
    simp [hempty]

/-- The local band floor supplies the energy hypothesis of the moving-column estimate. -/
theorem moving_block_small_ball (hL : 0 ≤ L) (hc : 0 < c) (hW : 0 < W)
    (u : Rest (n := n) → Fin (n + 1) → Complex) (hu : Measurable u)
    (w : Rest (n := n) → Complex) (hw : Measurable w)
    (G : Set (Rest (n := n))) (hG : MeasurableSet G)
    (B : Finset (Fin (n + 1)))
    (hB : ∀ i ∈ B, Section5Formalization.cyclicDist (n + 1) i j ≤ W)
    {d : Real} (hd : 0 < d)
    (hmass : ∀ rest ∈ G, d ^ 2 ≤ ∑ i ∈ B, ‖u rest i‖ ^ 2)
    {s : Real} (hs : 0 ≤ s) :
    m.law {omega | (expose j omega).2 ∈ G ∧
      ‖m.linearForm j (u (expose j omega).2) (expose j omega).1 -
        w (expose j omega).2‖ ≤ s} ≤
      ENNReal.ofReal (min 1
        (Real.pi * (((n + 1 : Nat) : Real) * L / ((c / W) * d ^ 2)) * s ^ 2)) := by
  have hcw : 0 < c / (W : Real) := div_pos hc (Nat.cast_pos.mpr hW)
  apply moving_linearForm_small_ball m j hL u hu w hw G hG
    (mul_pos hcw (sq_pos_of_pos hd)) _ hs
  intro rest hrest
  exact (mul_le_mul_of_nonneg_left (hmass rest hrest) hcw.le).trans
    (m.energy_ge_block j (u rest) B hB)

end ColumnExposure

#print axioms PlanarBandModel.selected_rows_small_ball
#print axioms PlanarBandModel.finite_net_small_ball
#print axioms ColumnExposure.expose_preserving
#print axioms ColumnExposure.moving_block_small_ball

end HighBandLSV

