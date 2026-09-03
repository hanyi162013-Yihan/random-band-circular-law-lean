/- Source snapshot: upstream-sources/high-band-lsv-2609-01295/RealRandomMatrixModel.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.RealProjectionAdapter
import Vendor.HighBandLSV
import Mathlib.Probability.Independence.Basic

/-! A genuine independent-entry real band model and its projected density law.
No conditional density, coordinate independence, or projection law is postulated.
The sole analytic input below is the explicitly named real geometric BL theorem. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace HighBandLSV
open LivshytsProjectionFormalization

local instance (n : Nat) : MeasurableSpace (Matrix (Fin n) (Fin n) Complex) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin n → Complex))

structure RealBandModel (N W : Nat) (c C rho : Real) where
  sigma : Matrix (Fin N) (Fin N) Real
  sigma_nonneg : ∀ i j, 0 ≤ sigma i j
  local_floor : ∀ i j, Section5Formalization.cyclicDist N i j ≤ W →
    c / (W : Real) ≤ sigma i j ^ 2
  variance_upper : ∀ i j, sigma i j ^ 2 ≤ C / (W : Real)
  row_normalization : ∀ i, ∑ j, sigma i j ^ 2 = 1
  density : Fin N → CoordinateDensityData Real N rho

namespace RealBandModel
variable {N W : Nat} {c C rho : Real} (m : RealBandModel N W c C rho)

abbrev AtomColumn (N : Nat) := Fin N → Real
abbrev Sample (N : Nat) := Fin N → AtomColumn N

def atomLaw (j i : Fin N) : Measure Real :=
  volume.withDensity ((m.density j).pdf i)

instance atomLaw_probability (j i : Fin N) : IsProbabilityMeasure (m.atomLaw j i) := by
  refine ⟨?_⟩
  rw [atomLaw, withDensity_apply _ MeasurableSet.univ]
  simpa using (m.density j).integral_pdf i

def columnLaw (j : Fin N) : Measure (AtomColumn N) := Measure.pi (m.atomLaw j)

instance columnLaw_probability (j : Fin N) : IsProbabilityMeasure (m.columnLaw j) := by
  unfold columnLaw
  infer_instance

def law : Measure (Sample N) := Measure.pi m.columnLaw

instance law_probability : IsProbabilityMeasure m.law := by
  unfold law
  infer_instance

def matrix (omega : Sample N) : Matrix (Fin N) (Fin N) Complex :=
  fun i j => ((m.sigma i j * omega j i : Real) : Complex)

theorem measurable_matrix : Measurable m.matrix := by
  unfold matrix
  fun_prop

def coordinateRV : AtomColumn N → CoordinateSpace Real N := fun x => WithLp.toLp 2 x

theorem measurable_coordinateRV : Measurable (coordinateRV (N := N)) := by
  unfold coordinateRV
  fun_prop

theorem independent_coordinates (j : Fin N) :
    iIndepFun (fun i (x : AtomColumn N) => coordinateRV x i) (m.columnLaw j) := by
  simpa only [coordinateRV, WithLp.ofLp_toLp, columnLaw, id] using
    (iIndepFun_pi (μ := m.atomLaw j) (X := fun _ => id)
      (fun _ => measurable_id.aemeasurable))

theorem marginal_law (j i : Fin N) :
    Measure.map (fun x : AtomColumn N => coordinateRV x i) (m.columnLaw j) =
      volume.withDensity ((m.density j).pdf i) := by
  exact (measurePreserving_eval (m.atomLaw j) i).map_eq

/-- The concrete column law satisfies the real projection theorem's entire probabilistic input. -/
def projectedBoundedDensity
    (hGBL : RealFiniteGeometricBrascampLieb) (hrho : 0 < rho)
    (j : Fin N) {d : Nat} (E : Submodule Real (CoordinateSpace Real N))
    (hE : Module.finrank Real E = d) :
    HasBoundedDensity
      (Measure.map (fun x => E.orthogonalProjectionOnto (coordinateRV x)) (m.columnLaw j))
      (subspaceVolume E) (rho ^ d * Real.exp ((d : Real) / 2)) :=
  real_independent_randomProjection_hasBoundedDensity_provedCoarea hGBL hrho
    coordinateRV (m.columnLaw j) measurable_coordinateRV (m.independent_coordinates j)
    E hE (m.density j) (m.marginal_law j)

def projectionInterface
    (hGBL : RealFiniteGeometricBrascampLieb) (hrho : 0 < rho) (j : Fin N) :
    HighBandLSV.Real.OneTwoProjectionDensityInterface (AtomColumn N) N
      (m.columnLaw j) coordinateRV rho (Real.exp 1) :=
  HighBandLSV.Real.realOneTwoProjectionDensityInterfaceFromGBL hGBL hrho
    measurable_coordinateRV (m.independent_coordinates j) (m.density j) (m.marginal_law j)

end RealBandModel
end HighBandLSV

#print axioms HighBandLSV.RealBandModel.projectedBoundedDensity

