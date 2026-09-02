import BernoulliSection10.PacketLawTransport
import BernoulliSection10.PacketFrameProbability
import BernoulliSection10.IntegratedHodge

/-! # Identifying packet evaluations with the physical three-site product -/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliSection10

open BernoulliLinearAlgebra Matrix Set Set.powersetCard

set_option maxHeartbeats 1600000

local instance packetPhysicalSumOrder (W : ℕ) : LinearOrder (Fin W ⊕ Fin W) :=
  BernoulliLinearAlgebra.clearedStepCompoundSumLinearOrder

theorem intervalSiteBlocks_packetPhysicalRows
    (W : ℕ) (z : ℂ) (p : EndpointBlockPair W × PacketAtomRows W) (j : Fin 3) :
    intervalSiteBlocks z (packetPhysicalRows W p) j =
      ![(⟨threeBlockBL (packetAtomAssignment W p.2),
          threeBlockAL (packetAtomAssignment W p.2) - z • 1,
          normalizedBlockMatrix W p.1.1⟩ : PhysicalBlocks (Fin W)),
        ⟨threeBlockBC (packetAtomAssignment W p.2),
          threeBlockAC (packetAtomAssignment W p.2) - z • 1,
          threeBlockCC (packetAtomAssignment W p.2)⟩,
        ⟨normalizedBlockMatrix W p.1.2,
          threeBlockAR (packetAtomAssignment W p.2) - z • 1,
          threeBlockCR (packetAtomAssignment W p.2)⟩] j := by
  fin_cases j <;> apply PhysicalBlocks.ext <;> ext a c
  all_goals
    simp only [intervalSiteBlocks, intervalPhysicalRow, physicalRowGroupOfAtoms,
      normalizedPhysicalAtom, packetPhysicalRows_apply]
    simp [packetSourceFlatten, endpointAtomsFlatten, packetSelectedAtom,
      packetColumnSite, packetSiteEquiv, packetLeftRow, packetCenterRow, packetRightRow,
      threeBlockAL, threeBlockBL, threeBlockCC, threeBlockAC, threeBlockBC, threeBlockCR,
      threeBlockAR, normalizedBlockMatrix, packetAtomAssignment, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul, mul_ite]

theorem intervalClearedProduct_packetPhysicalRows
    (W : ℕ) (z : ℂ) (p : EndpointBlockPair W × PacketAtomRows W)
    (r : Fin (2 * W + 1)) :
    intervalClearedProduct W 3 z (packetPhysicalRows W p) r =
      polynomialClearedCompoundProduct r.1
        (boundaryCompanionSteps
          (threeBlockBL (packetAtomAssignment W p.2))
          (threeBlockBC (packetAtomAssignment W p.2))
          (normalizedBlockMatrix W p.1.2)
          (threeBlockAL (packetAtomAssignment W p.2) - z • 1)
          (threeBlockAC (packetAtomAssignment W p.2) - z • 1)
          (threeBlockAR (packetAtomAssignment W p.2) - z • 1)
          (normalizedBlockMatrix W p.1.1)
          (threeBlockCC (packetAtomAssignment W p.2))
          (threeBlockCR (packetAtomAssignment W p.2))) := by
  simp [intervalClearedProduct, reverseMatrixProduct, List.ofFn_succ, Fin.rev,
    intervalClearedStep, intervalSiteBlocks_packetPhysicalRows,
    boundaryCompanionSteps, polynomialClearedCompoundProduct, compound_one,
    Matrix.mul_assoc]

theorem packetScalarCoefficientEval_eq_physical
    (W : ℕ) (z : ℂ) (ep : EndpointBlockPair W) (x : PacketAtomRows W)
    (r : Fin (2 * W + 1))
    (U V : unitaryGroup (Fin W ⊕ Fin W) ℂ)
    (s : powersetCard (Fin W ⊕ Fin W) r.1) :
    packetScalarCoefficientEval W r.1 z
      (normalizedBlockMatrix W ep.1) (normalizedBlockMatrix W ep.2) U V s x =
      ((compound r.1 (U : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ))ᴴ *
        intervalClearedProduct W 3 z (packetPhysicalRows W (ep, x)) r *
        compound r.1 (V : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)) s s := by
  unfold packetScalarCoefficientEval
  rw [eval_packetScalarMatrixCoefficientPolynomial, intervalClearedProduct_packetPhysicalRows]

end BernoulliSection10
