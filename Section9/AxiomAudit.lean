import BernoulliLinearAlgebra

/-!
# Axiom audit for the deterministic Section 9 library

References use arXiv:2609.01295v1. Run from the repository root:
`lake env lean Section9/AxiomAudit.lean`.

Theorems below cover the raw, unit-entry-weight finite-constant core of
Lemma 7.5 (proof in Section 9.1.3), Lemma 7.6 (Section 9.3),
Proposition 9.3 and Corollary 9.4, the deterministic comparison underlying
Lemma 7.7 (Section 9.5), and Lemma 7.8.

This checks kernel dependencies, not completeness of the paper translation.
See FORMALIZATION_MAP.md for retained hypotheses and coverage limitations.
-/

#print axioms BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket_concreteComparison
#print axioms BernoulliLinearAlgebra.concrete_block_floquet_identity
#print axioms BernoulliLinearAlgebra.polynomialClearedSignedCompoundTrace_listOfFn_eq_physical
#print axioms BernoulliLinearAlgebra.concreteKTheta_det_eq
#print axioms BernoulliLinearAlgebra.polynomialClearedBoundaryTrace_eq_concreteBoundaryK_det
#print axioms BernoulliLinearAlgebra.eval_globalBoundaryDetPolynomial_eq_polynomialClearedBoundaryTrace
#print axioms BernoulliLinearAlgebra.scaledGlobalConcreteKPolynomial_det
#print axioms BernoulliLinearAlgebra.compound_inverse_norm_eq_of_isUnit
#print axioms BernoulliLinearAlgebra.globalBoundaryCoefficientNorm_bounds_fullyInstantiated
#print axioms BernoulliLinearAlgebra.globalBoundaryCoefficientNorm_bounds_of_hodgeBounds_fullyInstantiated
#print axioms BernoulliLinearAlgebra.globalBoundaryCoefficientNorm_pos_fullyInstantiated
#print axioms BernoulliLinearAlgebra.globalBoundaryDetPolynomial_eq_squarefreePolynomial
#print axioms BernoulliLinearAlgebra.gramVolume_operatorCompound_two_sided_twoBlock_two_pow
