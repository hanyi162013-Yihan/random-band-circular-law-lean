import Mathlib

/-!
# Source statement

This project formalizes Theorem 2.1 (Replacement principle) of:

Terence Tao, Van Vu, with an appendix by Manjunath Krishnapur,
*Random matrices: Universality of ESDs and the circular law*,
Annals of Probability 38 (2010), 2023--2065; arXiv:0807.4898v5.

The source theorem compares the empirical spectral distributions of
`n⁻¹ᐟ² Aₙ` and `n⁻¹ᐟ² Bₙ`.  Its two assumptions are boundedness in probability
(or almost sure boundedness) of the normalized Hilbert--Schmidt norms and,
for planar Lebesgue-almost every deterministic `z`, convergence of the
normalized log-determinant difference.  No independence assumption is made.

The theorem itself will be introduced only after each notion occurring in it
has a machine-checked definition.  This file deliberately declares no axiom or
unproved theorem.
-/

namespace TaoVuReplacement

/-- Bibliographic locator for the exact arXiv version used by this project. -/
def sourceArxivVersion : String := "arXiv:0807.4898v5"

/-- Numbering of the result in the source. -/
def sourceTheoremNumber : String := "Theorem 2.1"

end TaoVuReplacement

