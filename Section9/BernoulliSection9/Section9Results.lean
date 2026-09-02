import BernoulliSection9.InterfaceEndpointBridge
import BernoulliSection9.InterfaceCanonicalLargeW
import BernoulliSection9.RandomFrameConditional
import BernoulliSection9.RandomQConditional
import BernoulliSection9.Section9CombinedBridge
import BernoulliSection9.Section9DeductionFromTerminal
import BernoulliSection9.StrongRRQR
import BernoulliSection9.TerminalCanonicalLargeW
import BernoulliSection9.TerminalConcretePublic
import BernoulliSection9.TerminalPhysicalResult

/-!
# Caller-facing Section 9 results

This module collects the public theorem interfaces.  Internal finite choices,
coordinate masks, reindexings, CUR eliminations, and conditioning sigma-field
constructions do not occur as assumptions.  The only literature inputs in
the completed probabilistic interfaces are the explicit structures from
`ExternalInputs`.
-/

noncomputable section

namespace BernoulliSection9

open scoped Matrix.Norms.L2Operator

open MeasureTheory ProbabilityTheory BernoulliLinearAlgebra

/- Both conditional source modules use the finite-dimensional Borel
structure on complex matrices.  Fix the same structure here so that the
public measurability hypotheses elaborate definitionally to those source
theorem signatures. -/
local instance section9MatrixMeasurableSpace {m n : Type*} :
    MeasurableSpace (Matrix m n Complex) := borel _

local instance section9MatrixBorelSpace {m n : Type*} :
    BorelSpace (Matrix m n Complex) := ⟨rfl⟩

/-! ## The paper's coordinate-set form of strong RRQR -/

/-- Strong RRQR together with the literal finite row and column sets `I,J`.
The ordered embeddings enumerate those sets and make
`K_piv = Q.submatrix rowIndex colIndex` literal.  All quantitative content is
carried by `rrqr`; this wrapper only makes the paper's set notation explicit.
-/
structure PaperStrongRRQRConclusion {n : Nat}
    (A : Matrix (Fin n) (Fin n) Complex) (tau : Real) (r : Nat) where
  rrqr : StrongRRQRConclusion A tau r
  I : Finset (Fin n)
  J : Finset (Fin n)
  rowIndex : Fin r ↪ Fin n
  colIndex : Fin r ↪ Fin n
  card_I : I.card = r
  card_J : J.card = r
  I_eq_range : I = Finset.univ.map rowIndex
  J_eq_range : J = Finset.univ.map colIndex
  K_piv_eq : rrqr.data.Kpiv = A.submatrix rowIndex colIndex

/-- Complex coordinate RRQR in the paper's `I,J` notation, with the proved
polynomial exponent `16` (Lemma 9.1 uses exponent `4`).  This is
a construction from `A` and `tau`, not a certificate accepted from a caller.
-/
noncomputable def paperStrongRRQRConclusion {n : Nat}
    (A : Matrix (Fin n) (Fin n) Complex) (tau : Real)
    (hn : 2 ≤ n) (htau : 1 ≤ tau) :
    PaperStrongRRQRConclusion A tau (largeSingularValueCount A tau) := by
  let c := strongRRQRConclusion A tau hn htau
  let rowIndex : Fin (largeSingularValueCount A tau) ↪ Fin n :=
    { toFun := fun i => c.rowEquiv (Sum.inl i)
      inj' := c.rowEquiv.injective.comp Sum.inl_injective }
  let colIndex : Fin (largeSingularValueCount A tau) ↪ Fin n :=
    { toFun := fun i => c.colEquiv (Sum.inl i)
      inj' := c.colEquiv.injective.comp Sum.inl_injective }
  refine
    { rrqr := c
      I := Finset.univ.map rowIndex
      J := Finset.univ.map colIndex
      rowIndex := rowIndex
      colIndex := colIndex
      card_I := ?_
      card_J := ?_
      I_eq_range := rfl
      J_eq_range := rfl
      K_piv_eq := ?_ }
  · simp
  · simp
  · simpa [rowIndex, colIndex] using c.pivot_eq

/-- Existential paper form, with the exact threshold count retained in the
output structure and no caller-supplied row/column choice. -/
theorem exists_paperStrongRRQRConclusion {n : Nat}
    (A : Matrix (Fin n) (Fin n) Complex) (tau : Real)
    (hn : 2 ≤ n) (htau : 1 ≤ tau) :
    ∃ r : Nat, Nonempty (PaperStrongRRQRConclusion A tau r) :=
  ⟨largeSingularValueCount A tau,
    ⟨paperStrongRRQRConclusion A tau hn htau⟩⟩

/-! ## Terminal and arbitrary-frame conclusions -/

universe u v

/-- The common paper-level width threshold for the interface and terminal
parts of Section 9.  It depends only on the two explicit literature inputs,
the fixed shift exponent, and a fixed upper bound for the subgaussian
parameter. -/
def section9CanonicalLargeWThreshold
    (nguyen : NguyenBottomSingularInput)
    (cook : CookDeformedSquareInput) (Kz : Nat) : Nat :=
  max (interfaceCanonicalLargeWThreshold nguyen)
    (TerminalAssembly.terminalCanonicalLargeWThreshold cook Kz (cook.subgaussianBound : Real))

/-- Proposition `prop:local-terminal` in the row-scaled normalization.  The
RRQR selection, literal CUR reduction, two iid squares, both conditioning
sigma-fields, both norm truncations, and all scalar large-width inequalities
are internal constructions.  The canonical choice is `t = W`. -/
noncomputable def section9TerminalSmallBall
    {Omega : Type u} [MeasurableSpace Omega]
    (cook : CookDeformedSquareInput.{u, u})
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {W : Nat} (Kz : Nat)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (hsubg : (X.subgaussianParameter : Real) <= (cook.subgaussianBound : Real))
    (hW : TerminalAssembly.terminalCanonicalLargeWThreshold
      cook Kz (cook.subgaussianBound : Real) <= W)
    (hz : ‖z‖ <= (W : Real) ^ Kz) :=
  TerminalAssembly.packetTerminalConcreteConclusion
    cook mu Kz z X (W : Real)
      (TerminalAssembly.packetTerminalCanonicalLargeWConditions_of_ge_threshold
        cook Kz (cook.subgaussianBound : Real) (by exact_mod_cast cook.subgaussianBound_one_le) z X hsubg hsubg hW hz)

/-- The conditional form explicitly claimed in `prop:local-terminal`: the
outer matrix may be measurable with respect to an arbitrary outside
sigma-field independent of the full fresh packet.  Conditional capped loss,
zero probability, the reverse-event estimate, and fiberwise Parseval are
all included. -/
noncomputable def section9TerminalSmallBallConditional
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    (cook : CookDeformedSquareInput.{u, u})
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {W : Nat} (Kz : Nat)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (hsubg : (X.subgaussianParameter : Real) <= (cook.subgaussianBound : Real))
    (hW : TerminalAssembly.terminalCanonicalLargeWThreshold
      cook Kz (cook.subgaussianBound : Real) <= W)
    (hz : ‖z‖ <= (W : Real) ^ Kz)
    (mOutside : MeasurableSpace Omega) (hmOutside : mOutside <= mOmega)
    (Q : Omega -> Matrix (TerminalAssembly.PacketOuter (Fin W))
      (TerminalAssembly.PacketOuter (Fin W)) Complex)
    (hQ : @Measurable Omega
      (Matrix (TerminalAssembly.PacketOuter (Fin W))
        (TerminalAssembly.PacketOuter (Fin W)) Complex)
      mOutside (borel _) Q)
    (h_indep : @Indep Omega mOutside
      (MeasurableSpace.comap
        (@TerminalAssembly.packetFreshSample Omega (Fin W) mOmega
          inferInstance inferInstance mu X) inferInstance) mOmega mu) := by
  letI : MeasurableSpace Omega := mOmega
  exact TerminalAssembly.packetTerminalRandomQConditionalResult
    cook mu Kz z X (W : Real)
      (TerminalAssembly.packetTerminalCanonicalLargeWConditions_of_ge_threshold
        cook Kz (cook.subgaussianBound : Real) (by exact_mod_cast cook.subgaussianBound_one_le) z X hsubg hsubg hW hz)
      mOutside hmOutside Q hQ h_indep

/-- The terminal small-ball conclusion in the paper's original physical
normalization.  Scaling invariance is proved internally and `sigma` is only
required to be nonzero. -/
noncomputable def section9PhysicalTerminalSmallBall
    {Omega : Type u} [MeasurableSpace Omega]
    (cook : CookDeformedSquareInput.{u, u})
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {W : Nat} (Kz : Nat)
    (z sigma : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (hsubg : (X.subgaussianParameter : Real) <= (cook.subgaussianBound : Real))
    (hW : TerminalAssembly.terminalCanonicalLargeWThreshold
      cook Kz (cook.subgaussianBound : Real) <= W)
    (hz : ‖sigma * z‖ <= (W : Real) ^ Kz)
    (hsigma : sigma ≠ 0)
    (Q : Matrix (TerminalAssembly.PacketOuter (Fin W))
      (TerminalAssembly.PacketOuter (Fin W)) Complex) :=
  TerminalAssembly.physicalPacketTerminalSmallBallConclusion
    cook X (W : Real)
      (TerminalAssembly.packetTerminalConcreteConclusion
        cook mu Kz (sigma * z) X (W : Real)
          (TerminalAssembly.packetTerminalCanonicalLargeWConditions_of_ge_threshold
            cook Kz (cook.subgaussianBound : Real) (by exact_mod_cast cook.subgaussianBound_one_le) (sigma * z) X hsubg hsubg hW hz))
    hsigma Q

/-- Section 9.2 for arbitrary orthonormal frames, conditional on the paper's
endpoint good datum.  Endpoint inverses, exterior powers, Hodge comparison,
boundary charts, and the terminal packet theorem are all produced inside the
definition. -/
noncomputable def section9ArbitraryFrameSmallBall
    {Omega : Type u} [MeasurableSpace Omega]
    (cook : CookDeformedSquareInput.{u, u})
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {W Kz r : Nat} (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (hsubg : (X.subgaussianParameter : Real) <= (cook.subgaussianBound : Real))
    (hW : TerminalAssembly.terminalCanonicalLargeWThreshold
      cook Kz (cook.subgaussianBound : Real) <= W)
    (hz : ‖z‖ <= (W : Real) ^ Kz)
    (CL BR : Matrix (Fin W) (Fin W) Complex)
    (B delta : Real) (endpoint : PaperEndpointGood CL BR B delta)
    (U V : ComplexFrame r (2 * W)) (h : r <= 2 * W) :=
  literalArbitraryFrameSmallBall_of_packetConcrete
    cook z X (W : Real)
      (TerminalAssembly.packetTerminalConcreteConclusion
        cook mu Kz z X (W : Real)
          (TerminalAssembly.packetTerminalCanonicalLargeWConditions_of_ge_threshold
            cook Kz (cook.subgaussianBound : Real) (by exact_mod_cast cook.subgaussianBound_one_le) z X hsubg hsubg hW hz))
    CL BR B delta endpoint U V h

/-- Conditional arbitrary-frame form for endpoint and frame data measurable
with respect to an outside parameter.  The internal unitary completions are
eliminated from the measurability proof by the direct exterior-minor formula;
the caller supplies only the ordinary coordinatewise measurability of the
given frames. -/
noncomputable def section9ArbitraryFrameSmallBallConditional
    {Omega : Type u} {Param : Type v}
    [mOmega : MeasurableSpace Omega] [MeasurableSpace Param]
    (cook : CookDeformedSquareInput.{u, u})
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {W Kz r : Nat} (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (hsubg : (X.subgaussianParameter : Real) <= (cook.subgaussianBound : Real))
    (hW : TerminalAssembly.terminalCanonicalLargeWThreshold
      cook Kz (cook.subgaussianBound : Real) <= W)
    (hz : ‖z‖ <= (W : Real) ^ Kz)
    (mOutside : MeasurableSpace Omega) (hmOutside : mOutside <= mOmega)
    (parameter : Omega -> Param)
    (hparameter : @Measurable Omega Param mOutside inferInstance parameter)
    (h_indep : @Indep Omega mOutside
      (MeasurableSpace.comap
        (@RandomFrame.freshSample Omega (ThreeBlockVariable (Fin W))
          mOmega inferInstance mu X) inferInstance)
      mOmega mu)
    (CL BR : Param -> Matrix (Fin W) (Fin W) Complex)
    (B delta : Param -> Real)
    (endpoint : forall p, PaperEndpointGood (CL p) (BR p) (B p) (delta p))
    (U V : Param -> ComplexFrame r (2 * W)) (h : r <= 2 * W)
    (hCL : Measurable CL) (hBR : Measurable BR)
    (hU : RandomFrame.FrameCoordinateMeasurable U)
    (hV : RandomFrame.FrameCoordinateMeasurable V) := by
  letI : MeasurableSpace Omega := mOmega
  exact RandomFrame.literalRandomFrameConditionalResult_of_packetConcrete
    mu cook z X (W : Real)
      (TerminalAssembly.packetTerminalConcreteConclusion
        cook mu Kz z X (W : Real)
          (TerminalAssembly.packetTerminalCanonicalLargeWConditions_of_ge_threshold
            cook Kz (cook.subgaussianBound : Real) (by exact_mod_cast cook.subgaussianBound_one_le) z X hsubg hsubg hW hz))
      mOutside hmOutside parameter hparameter h_indep
      CL BR B delta endpoint U V h hCL hBR hU hV

/-- The full interface-to-arbitrary-frame Section 9 conclusion.  Its only
literature inputs are the explicit Nguyen and Cook structures: outside the
internally defined pair-interface bad event it constructs the endpoint datum
and then applies the arbitrary-frame theorem. -/
noncomputable def section9InterfaceAndArbitraryFrameSmallBall
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {W Kz r : Nat}
    (nguyen : NguyenBottomSingularInput.{u, u})
    (SL SR : IidSubgaussianSquare Omega mu W)
    (hSL : SL.subgaussianParameter <= nguyen.subgaussianBound)
    (hSR : SR.subgaussianParameter <= nguyen.subgaussianBound)
    (cook : CookDeformedSquareInput.{u, u})
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (hsubg : (X.subgaussianParameter : Real) <= (cook.subgaussianBound : Real))
    (hW : section9CanonicalLargeWThreshold nguyen cook Kz <= W)
    (hz : ‖z‖ <= (W : Real) ^ Kz)
    (U V : ComplexFrame r (2 * W)) (h : r <= 2 * W) :=
  let hinterfaceW : interfaceCanonicalLargeWThreshold nguyen <= W :=
    (le_max_left _ _).trans hW
  let hterminalW : TerminalAssembly.terminalCanonicalLargeWThreshold
      cook Kz (cook.subgaussianBound : Real) <= W :=
    (le_max_right _ _).trans hW
  let hinterface := interfaceCanonicalLargeWConditions nguyen hinterfaceW
  interfacePairProbabilityAndLiteralArbitraryFrameSmallBall_of_packetConcrete
    mu nguyen SL SR hSL hSR hinterface.1 hinterface.2.1 hinterface.2.2 cook z X
      (W : Real)
      (TerminalAssembly.packetTerminalConcreteConclusion
        cook mu Kz z X (W : Real)
          (TerminalAssembly.packetTerminalCanonicalLargeWConditions_of_ge_threshold
            cook Kz (cook.subgaussianBound : Real) (by exact_mod_cast cook.subgaussianBound_one_le) z X hsubg hsubg hterminalW hz))
      U V h

end BernoulliSection9
