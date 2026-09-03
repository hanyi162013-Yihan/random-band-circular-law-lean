# Direct Section 3 connection: exact proof route

This file records the implemented proof route. Both source-connected endpoints
compiled in cloud run `33717194294` at `e7ca00c`; the canonical shared version
and all final fresh audits passed scoped run `33719162307` at `362c47f`. No whole-root recheck
is required under the user's updated instructions. See `SOURCE_CONNECTION_AUDIT.md` for the
current release gates.
The selected Section 3 baseline is `section3/` at commit `42c26b6`, with
the density-field correction documented in `DENSITY_SCHEMA_CORRECTION.md`.
The user explicitly excluded the later, unrelated Proposition 3.8 additions
from this verification task; they are not imported by these Section 10 proofs.
Publication preserves those unrelated additions already present on main.
Root Lake now selects `section3/` instead of the older
`vendor/short-ring-analysis/`. The concrete `IIDModels`, `PlanarHighBand`,
`DensityRepresentative`, and `RealHighBand` adapters have compiled in cloud
CI. No local integration compilation has been performed.

All steps below have compiled implementations, including `LiteratureInputs`,
`FullBlockLogLimit`, `ConnectedHighBand`, and the public `DensityCircularLaw`
module. The separate final signature/axiom audit also passed.

## Why the old record is not the final interface

The historical `SourceInputs.Section3Inputs` asks for statements over every
profile and every admissible dimension sequence. Its counting field even
specifies all intervals and a particular exceptional-probability exponent.
The Section 10 full-block proof needs only the count near zero with a
vanishing exceptional probability. The new Section 3 source already proves
exactly that required consequence. No stronger unproved counting statement
should be renamed “BBV” or retained as an extra hypothesis.

The added real and complex `HighBandClosure` modules isolate the actual
Proposition 10.1 conclusion. The final theorem must **prove** this internal
premise and pass it to `density_circular_law_of_highBand`. No
`HighBandLogLimit`, `Section3Inputs`, LSV, counting, comparison, reset or
model-validity certificate may remain in the final caller signature.

## Source calls and concrete constructions

1. Build the source v3 random-matrix model with coefficient exactly
   `physicalProfile W s`. Reuse its proved nonnegativity, both stochastic
   sums, exact bandwidth `3W`, entry independence and the actual IID law.
2. Construct the planar / real high-band model with local variance floor
   `(1/3)/W`, upper bound `1/W`, and `W ≤ (s+3)W`.
   Transfer its whole matrix law using
   `identDistrib_matrix_of_independent_entries`, not an assumed LSV law.
3. Invoke `eventually_planar_lsv_along_dimensions` or
   `eventually_real_lsv_along_dimensions` and
   `theorem31MinimumInput_of_truncated_estimate`. These accommodate eventual
   bandwidth conditions, so no pointwise strengthening or arbitrary-sequence
   numerical-certificate assumption is needed.
4. Invoke `hermitizationAllCutoffsCountingInput_of_v3_model`, specialize
   its proved count at the source cutoff, and use the deterministic scale
   bookkeeping. Its `4N^{-8}` exceptional probability already tends to zero.
5. Invoke `lemma35LocalBulkComparisonInput_of_v3_models` for the actual
   profile matrix and literal circular Gaussian comparison. The exact
   cutoff and polynomial rate feed
   `proposition36_matrix_form_highProbability`, which is a general matrix
   theorem and does not require a scalar-indicator profile.
6. Construct the Gaussian atom's moments and planar density from
   `circularGaussianPairLaw`; `GaussianReferenceFacts` supplies this
   cloud-verified elementary part. Transfer its IID laws,
   prove nonsingularity by the existing source theorem, and transport the
   explicitly retained BC12 conclusions to the product sample space.
7. Connect the resulting high-band limit to both Section 10 closures and
   remove the complex numerical density normalization via
   `IsPlanarDensityAtom.normalized`.

## Allowed external mathematical boundary

- BBV, stated at the source's canonical Gaussian/free comparison.
- BC12, stated for the actual normalized circular Gaussian ensemble.
- Real branch only: `RealFiniteGeometricBrascampLieb`.

All constants may be enlarged internally. Any universal BBV formulation
must preserve its genuine constant quantifiers, not assume that an
arbitrarily small constant works. Kernel-axiom allowlisting and printed
parameter inspection are separate checks.
