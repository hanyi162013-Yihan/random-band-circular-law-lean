/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/TraceComparison.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- Local import-only adaptation: avoid building the unrelated tactic umbrella.
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The deterministic comparison chain in v3 Proposition 3.4

The main theorem in this file is the machine-checked triangle-inequality reconstruction of
formula (3.11).  It deliberately treats the four genuinely probabilistic/free-probability
estimates as inputs; their provenance is recorded in `External/VanHandel.lean` and
`External/Concentration.lean`.
-/

namespace Arxiv2410V3

/-- The four-term right-hand side of v3 formula (3.11), in its displayed order. -/
noncomputable def formula311Error (n B v C CD : ℝ) : ℝ :=
  C / (Real.sqrt B * v ^ 4) +
  C / (B * v ^ 5) +
  CD * Real.sqrt (Real.log n) / (Real.sqrt n * v) +
  C * Real.sqrt (Real.log n) / (Real.sqrt B * v ^ 2)

/-- v3 formula (3.11): combine scalar concentration, trace universality,
Gaussian-to-free comparison, and diagonal pseudovariance correction.

The five complex numbers stand for
`m`, `𝔼m`, `𝔼mᴳ`, `𝔼mᴳᐟᵒ`, and `mᵒ_free`, respectively.
-/
theorem four_term_trace_bound
    (m em emG emGo mfree : ℂ) {e1 e2 e3 e4 : ℝ}
    (hconc : ‖m - em‖ ≤ e3)
    (huniv : ‖em - emG‖ ≤ e1)
    (hpseudo : ‖emG - emGo‖ ≤ e4)
    (hfree : ‖emGo - mfree‖ ≤ e2) :
    ‖m - mfree‖ ≤ e1 + e2 + e3 + e4 := by
  have h₁ : ‖m - mfree‖ ≤ ‖m - em‖ + ‖em - mfree‖ := by
    calc
      ‖m - mfree‖ = ‖(m - em) + (em - mfree)‖ := by ring_nf
      _ ≤ ‖m - em‖ + ‖em - mfree‖ := norm_add_le _ _
  have h₂ : ‖em - mfree‖ ≤ ‖em - emG‖ + ‖emG - mfree‖ :=
    by
      calc
        ‖em - mfree‖ = ‖(em - emG) + (emG - mfree)‖ := by ring_nf
        _ ≤ ‖em - emG‖ + ‖emG - mfree‖ := norm_add_le _ _
  have h₃ : ‖emG - mfree‖ ≤ ‖emG - emGo‖ + ‖emGo - mfree‖ :=
    by
      calc
        ‖emG - mfree‖ = ‖(emG - emGo) + (emGo - mfree)‖ := by ring_nf
        _ ≤ ‖emG - emGo‖ + ‖emGo - mfree‖ := norm_add_le _ _
  nlinarith

/-- The same formula with the four explicit terms from v3 (3.11). -/
theorem formula311_of_four_inputs
    (m em emG emGo mfree : ℂ) {n B v C CD : ℝ}
    (hconc : ‖m - em‖ ≤ CD * Real.sqrt (Real.log n) / (Real.sqrt n * v))
    (huniv : ‖em - emG‖ ≤ C / (Real.sqrt B * v ^ 4))
    (hpseudo : ‖emG - emGo‖ ≤
      C * Real.sqrt (Real.log n) / (Real.sqrt B * v ^ 2))
    (hfree : ‖emGo - mfree‖ ≤ C / (B * v ^ 5)) :
    ‖m - mfree‖ ≤ formula311Error n B v C CD := by
  unfold formula311Error
  exact four_term_trace_bound m em emG emGo mfree hconc huniv hpseudo hfree

/-- The last deterministic step from v3 (3.9) to (3.10): a comparison error at most one
and a free-transform bound `Cfree` give the universal bound `Cfree + 1`. -/
theorem trace_bound_of_comparison
    (m mfree : ℂ) {delta Cfree : ℝ}
    (herr : ‖m - mfree‖ ≤ delta)
    (hfree : ‖mfree‖ ≤ Cfree)
    (hdelta : delta ≤ 1) :
    ‖m‖ ≤ Cfree + 1 := by
  have htri : ‖m‖ ≤ ‖m - mfree‖ + ‖mfree‖ := by
    calc
      ‖m‖ = ‖(m - mfree) + mfree‖ := by ring_nf
      _ ≤ ‖m - mfree‖ + ‖mfree‖ := norm_add_le _ _
  nlinarith

/-- An explicit finite-`n` rate certificate.  This is data, not an axiom: a caller must prove
the displayed inequality from the scale assumptions before invoking v3 formula (3.9). -/
structure PolynomialRateCertificate (n error : ℝ) where
  exponent : ℝ
  exponent_pos : 0 < exponent
  error_le : error ≤ Real.rpow n (-exponent)

/-- Once the rate ledger has bounded the right side of (3.11), formula (3.9) is immediate. -/
theorem formula39_of_formula311
    (m mfree : ℂ) {n error : ℝ}
    (h311 : ‖m - mfree‖ ≤ error)
    (rate : PolynomialRateCertificate n error) :
    ‖m - mfree‖ ≤ Real.rpow n (-rate.exponent) :=
  h311.trans rate.error_le

end Arxiv2410V3
