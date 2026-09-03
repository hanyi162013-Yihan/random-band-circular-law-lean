import ShortRingAnchor.Proposition36Models
import ShortRingAnchor.AlmostSureNonsingularity
import ShortRingAnchor.BC12.LogdetConvergence
import ShortRingAnchor.BC12.NegativeMomentCounting
import ShortRingAnchor.LocalStieltjesNet
import ShortRingAnchor.ExplicitStieltjesRate
import ShortRingAnchor.HorizontalPolynomialNet
import ShortRingAnchor.HorizontalComparisonProbability
import ShortRingAnchor.HilbertSchmidtCutoffRemoval
import ShortRingAnchor.PoissonSmoothingProbability
import ShortRingAnchor.Lemma35FromV3
import ShortRingAnchor.Proposition36Concrete
import ShortRingAnchor.Proposition36Counting
import ShortRingAnchor.Proposition36Planar
import ShortRingAnchor.Proposition36PublishedTheorem31
import ShortRingAnchor.Proposition38.AtomMoments
import ShortRingAnchor.Proposition38.Scales
import ShortRingAnchor.Proposition38.BlockNorm
import ShortRingAnchor.Proposition38.Assembly
import ShortRingAnchor.Proposition36VerifiedGinibre
import ShortRingAnchor.Proposition38.VerifiedGinibre

/-!
# The finite-moment short-ring anchor

Root module for a Lean reconstruction of Proposition 3.6 in
`Circular_Law_Combined_Manuscript.pdf`.

The BC12-free endpoints are now
`ShortRingAnchor.proposition36_cyclicShortRing_withoutBC12` and
`ShortRingAnchor.Proposition38.proposition38_withoutBC12`.
They specify the genuine Gaussian reference law and derive all BC12 inputs
internally from the pinned Ginibre proof dependency and the existing
Gaussian small-ball / v3 counting route. See `BC12_INTEGRATION.md` for the
precise remaining non-BC12 hypotheses and the compatibility policy.
The descriptions below refer to the retained generic conditional APIs.

The planar-density source-model conditional theorem is
`ShortRingAnchor.proposition36_cyclicShortRing_planar_from_published_theorem31`.
The real/complex-alternative endpoint is
`ShortRingAnchor.proposition36_cyclicShortRing_from_published_theorem31`;
it retains the copied real theorem's explicit geometric Brascamp--Lieb premise.
It constructs both the Hermitization counting event and the least-value event:
the former uses the actual v3 probability bound and the latter reuses the
user's copied, proved Theorem 3.1. Its Lemma 3.5 input is derived from the
actual independent atom arrays and the explicit BBV comparison. Every deterministic and
elementary step in (3.9)--(3.14) is proved internally.  The genuinely cited
random-matrix conclusions remain explicit hypotheses in
`ShortRingAnchor.ExternalInputs`.  The BC12 full-logdet premise can now be
discharged from the named finite Ginibre formulas by
`ShortRingAnchor.BC12.ginibre_matrix_logdet_convergesInProbability_of_formulas`.

The `Proposition38` subdirectory contains the subgaussian full-block
high-band anchor, `ShortRingAnchor.Proposition38.proposition38`. Its two
new explicit literature hypotheses are Proposition 3.2 and Cook 1.12;
the existing BBV and BC12 boundary is documented in `PROPOSITION38.md`.
The actual cyclic profile, Cook norm guard, spread and broad-connectivity
conditions, the two-branch LSV floor, and the final assembly are internal.
-/
