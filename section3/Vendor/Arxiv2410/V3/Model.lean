/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Model.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.Hermitian

/-!
# The v3 Hermitization and normalized resolvent trace

These are the definitions preceding arXiv:2410.16457v3, formula (3.1) and Proposition 3.4.
-/

namespace Arxiv2410V3

open Matrix Complex

/-- The `2n`-dimensional index of the Hermitian dilation. -/
abbrev HermitizationIndex (n : ℕ) := Fin n ⊕ Fin n

/-- The dilation index really has the paper's dimension `2n`. -/
@[simp] theorem card_hermitizationIndex (n : ℕ) :
    Fintype.card (HermitizationIndex n) = 2 * n := by
  simp [HermitizationIndex, two_mul]

/-- The shifted matrix `X_z = X - z I_n`. -/
def shiftedMatrix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  X - z • 1

/-- v3 formula (3.1): `𝒴_z = [[0, X-zI], [(X-zI)ᴴ, 0]]`. -/
def hermitization {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ :=
  let Y := shiftedMatrix X z
  Matrix.fromBlocks 0 Y Yᴴ 0

/-- The dilation in v3 formula (3.1) is Hermitian. -/
theorem hermitization_isHermitian {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    (hermitization X z).IsHermitian := by
  exact Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero rfl Matrix.isHermitian_zero

/-- v3 definition: `𝒢_z(η) = (𝒴_z - η I_(2n))⁻¹`. -/
noncomputable def greenFunction {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℂ) (z eta : ℂ) :
    Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ :=
  (hermitization X z - eta • 1)⁻¹

/-- Normalized trace `tr_N A = Tr(A)/N` used throughout v3 Section 3. -/
noncomputable def normalizedTrace {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) : ℂ :=
  Matrix.trace A / (Fintype.card ι : ℂ)

/-- On the Hermitian dilation, `normalizedTrace` is exactly `Tr / (2n)`. -/
theorem normalizedTrace_hermitizationIndex {n : ℕ}
    (A : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ) :
    normalizedTrace A = Matrix.trace A / ((2 * n : ℕ) : ℂ) := by
  unfold normalizedTrace
  rw [card_hermitizationIndex]

/-- The paper's `m_z(η) = tr_(2n) 𝒢_z(η)`. -/
noncomputable def stieltjesTrace {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℂ) (z eta : ℂ) : ℂ :=
  normalizedTrace (greenFunction X z eta)

/-- The upper half-plane condition used in Proposition 3.4. -/
def InUpperHalfPlane (eta : ℂ) : Prop := 0 < eta.im

end Arxiv2410V3

