import SubgaussianSection8.SourceInputs
import BernoulliSection8.Section3Integration

/-! Connect the general Section 8 atom to the concrete, proved Section 3.8. -/

noncomputable section
namespace SubgaussianSection8

def Atom.toSection3Atom (A : Atom) : ShortRingAnchor.Proposition38.Atom :=
  A.section3Atom.toSection3Atom

abbrev Section3UpstreamInputs (A : Atom) :=
  BernoulliSection8.Section3Bridge.UpstreamInputs A.toSection3Atom

theorem section3_input (A : Atom) (known : Section3UpstreamInputs A) : Section3Input A :=
  BernoulliSection8.Section3Bridge.highBandInput A.toSection3Atom known

end SubgaussianSection8
