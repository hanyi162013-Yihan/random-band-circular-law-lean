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

/-!
# The finite-moment short-ring anchor

Root module for a Lean reconstruction of Proposition 3.6 in
`Circular_Law_Combined_Manuscript.pdf`.

The planar-density source-model conditional theorem is
`ShortRingAnchor.proposition36_cyclicShortRing_planar_from_published_theorem31`.
It constructs both the Hermitization counting event and the least-value event:
the former uses the actual v3 probability bound and the latter reuses the
user's copied, proved Theorem 3.1. Its Lemma 3.5 input is derived from the
actual independent atom arrays and the explicit BBV comparison. Every deterministic and
elementary step in (3.9)--(3.14) is proved internally.  The genuinely cited
random-matrix conclusions remain explicit hypotheses in
`ShortRingAnchor.ExternalInputs`.  The BC12 full-logdet premise can now be
discharged from the named finite Ginibre formulas by
`ShortRingAnchor.BC12.ginibre_matrix_logdet_convergesInProbability_of_formulas`.
-/
