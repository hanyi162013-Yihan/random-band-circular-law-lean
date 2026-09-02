import SubgaussianSection8.Atom
import BernoulliSection8.Section3HighBand

open MeasureTheory ProbabilityTheory
noncomputable section
namespace SubgaussianSection8

theorem Atom.section3Atom (A : Atom) :
    BernoulliSection8.IsRealSubgaussianAtom A.law A.parameter :=
  ⟨A.probability, A.centered, A.second_moment, A.subgaussian⟩

/-- The permitted Section 3 input is reused at the general law. -/
abbrev Section3Input (A : Atom) :=
  BernoulliSection8.Section3SubgaussianHighBandInput A.law A.parameter

/-- The old model is one instance of the new atom interface. -/
def rademacherAtom : Atom where
  law := BernoulliSection8.rademacherLaw
  parameter := 1
  probability := measure_univ
  centered := BernoulliSection8.rademacherLaw_mean_zero
  second_moment := BernoulliSection8.rademacherLaw_second_moment
  subgaussian := BernoulliSection8.rademacherLaw_subgaussian


end SubgaussianSection8
