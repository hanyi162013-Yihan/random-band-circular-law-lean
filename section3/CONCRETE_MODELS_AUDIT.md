# Concrete cyclic/dense models and Proposition 3.6 integration

Date: 2026-09-02. This checkpoint continues the completed actual-matrix
Stieltjes and v3 probability reconstruction. It removes the explicit
Lemma 3.5 `hBulk` premise from a new source-facing Proposition 3.6 endpoint.

## Verification

Both final commands passed on 2026-09-02, after the comparison-constant
generalization:

- `lake build`: exit 0, **3432 jobs**.
- `lake build ShortRingAnchor.Audit`: exit 0, **3432 jobs**.

The audit reports **196 distinct declarations**, including all previous
163 declarations, all 27 new theorems and the six new definitions. Every
reported axiom belongs to the standard set `propext`, `Classical.choice`,
`Quot.sound`; no unexpected axiom occurs. A separate coverage check found
no new theorem or definition missing from `Audit.lean`.

- [Captured full build](audit/concrete-models-build-2026-09-02.log)
- [Captured full axiom audit](audit/concrete-models-2026-09-02.log)
- [All audit commands](ShortRingAnchor/Audit.lean)

Source scans found no proof placeholder, `admit`, `unsafe`, custom axiom,
`native_decide`, or kernel-check bypass. The new modules contain no
`set_option` commands. Existing upstream informational/style warnings are
replayed by Lake; the final commands have no errors.

## New files and declarations

Nine new Lean modules, containing 27 theorems and six auxiliary definitions:

| File under `ShortRingAnchor/` | Theorems | Role |
| --- | ---: | --- |
| [CyclicVarianceProfile.lean](ShortRingAnchor/CyclicVarianceProfile.lean) | 9 | Actual cyclic placement, row/column normalization, exact bandwidth |
| [IndependentConstantExtension.lean](ShortRingAnchor/IndependentConstantExtension.lean) | 1 | Independence after inserting deterministic coordinates |
| [IndependentAtomCopies.lean](ShortRingAnchor/IndependentAtomCopies.lean) | 4 | Explicit i.i.d. data, moment transport, deterministic zero law |
| [CyclicV3Model.lean](ShortRingAnchor/CyclicV3Model.lean) | 2 | Entry independence/laws and construction of the actual cyclic v3 model |
| [DenseV3Model.lean](ShortRingAnchor/DenseV3Model.lean) | 2 | Dense variance normalization, exact bandwidth, actual dense v3 model |
| [ConcreteBulkScales.lean](ShortRingAnchor/ConcreteBulkScales.lean) | 3 | Absorb the fixed profile constant and identify the common exponent |
| [Lemma35Concrete.lean](ShortRingAnchor/Lemma35Concrete.lean) | 4 | Common moment budget and the concrete Lemma 3.5 constructor |
| [AtomDensityTransport.lean](ShortRingAnchor/AtomDensityTransport.lean) | 1 | Transport the real/complex density alternative along equality of laws |
| [Proposition36Concrete.lean](ShortRingAnchor/Proposition36Concrete.lean) | 1 | Proposition 3.6 with `hBulk` supplied internally |

The modules total 754 lines. Each theorem has a source or proof-step comment.
`IndependentAtomCopies21` is ordinary model data: measurability,
independence, and equality of laws. It asserts no random-matrix conclusion.

Other new project files are this report and the two captured command logs
listed in the verification section. Existing files updated are
`ShortRingAnchor.lean`, `ShortRingAnchor/Audit.lean`, `README.md`,
`RADIUS_SHORTCUT.md`, and `BUILD_AUDIT.md`. No vendored source was changed
in this checkpoint.

## Fully checked internal theorems with no external literature conclusion

All names below are in namespace `ShortRingAnchor`. Their ordinary
deterministic or distributional assumptions remain explicit.

From `CyclicVarianceProfile`:

- `cyclicColumn_row_bijective`;
- `cyclicPlacement_sum_at`;
- `cyclicShortRingMatrix_at`;
- `cyclicShortRingMatrix_off_band`;
- `cyclicVarianceCoefficient_at`;
- `cyclicVarianceCoefficient_off_band`;
- `cyclicVarianceCoefficient_sq`;
- `cyclicVarianceCoefficient_col_sq_sum`;
- `cyclicVarianceProfile_isBandwidth`.

Independence and atom-law deductions:

- `iIndepFun_of_constant_outside`;
- `AtomMomentAssumption21.of_identDistrib`;
- `ringEntryMomentCopies21_of_independentAtomCopies`;
- `denseAtomMomentCopies21_of_independentAtomCopies`;
- `identDistrib_zero_probability`;
- `cyclicShortRingRandomMatrix_entries_independent`;
- `cyclicShortRingRandomMatrix_entry_law`;
- `AtomDensityAlternative21.of_identDistrib`.

Dense normalization and scale deductions:

- `denseVarianceCoefficient_sq`;
- `denseVarianceProfile_isBandwidth`;
- `eventually_cyclic_bandwidth_ge_half_power`;
- `dense_bandwidth_ge_half_power`;
- `localBulkRateExponent_half_eq`;
- `sourceV3MomentBudget_ge_eight`;
- `sourceV3MomentBudget_ge_left`;
- `sourceV3MomentBudget_ge_right`.

These are 25 theorems. The audit also includes the six definitions
`cyclicVarianceCoefficient`, `cyclicVarianceProfile`, `cyclicV3Model`,
`denseVarianceProfile`, `denseV3Model`, and `sourceV3MomentBudget`, including
the proofs filling their model/profile fields.

## Two conditional endpoint theorems

### Concrete Lemma 3.5

`lemma35LocalBulkComparisonInput_cyclic_dense` takes the actual cyclic and
dense atom arrays, their fixed source laws, Assumption-2.1 moment data,
dimensions tending to infinity, and `W >= M^beta` with `0 < beta <= 2`.
The only external theorem premises are `bbvA` and `bbvG`, two instances of
the same centralized BBV comparison, for the canonical circularized models.

For every fixed `R >= 0` and every arbitrary fixed complex shift `z`, it
proves the exact named `Lemma35LocalBulkComparisonInput` with rate

```text
M^(-beta/128).
```

The models themselves are constructed inside Lean. For the cyclic model,
fixing an offset permutes the row indices. Fixing a row injects the offsets
into distinct columns. Thus each active matrix entry is exactly one scaled
atom, while off-band entries are deterministic zero. Independence of the
full entry family follows from the proved constant-extension lemma.
Column and row variance sums are both one, and the attained maximum yields
the exact bandwidth `(max q_s)^(-1)`. The dense bandwidth is exactly `M`.

The deterministic bound `B >= W/C0` and dimension growth imply eventually
`B >= M^(beta/2)`. Applying the preceding matrix-level proof with
`epsilon = beta/2` gives height `M^(-beta/32)` and exponent `beta/128`.
This is a valid non-optimal reconstruction; it does not change the source.

The comparison budget is

```text
max comparisonConstant
  (max 8 (max(E|atomA|³, E|atomG|³) + E|standard complex Gaussian|³)).
```

Here `comparisonConstant` is arbitrary and fixed, so no numerical value is
guessed for BBV's absolute constant. Both third-moment inequalities are
proved from the two fixed source laws. No independence between dimensions
or between the two ensembles is assumed. There is no radius-five or
`|z| <= 2.5` restriction.

`CanonicalBBVAt` is the existing transparent specialization of
`External.BBVTheorem28GaussianFreeHypothesis`, not a new asserted theorem.
As documented upstream, this specialized interface includes identification
of the abstract free endpoint with the canonical scalar Dyson transform.
BBV is not proved. McDiarmid, the specialized BVH Remark 6.13 comparison,
Gaussian realization, trace identities, net arguments and smoothing are
supplied by the previously checked development.

### Source-facing Proposition 3.6

`proposition36_cyclicShortRing_of_atom_copies_and_bbv` supplies the previous
assembly's `hBulk` using the concrete constructor at each cutoff, with the
single exponent

```text
zeta = (8/9 + omega) / 128 > 0.
```

It also derives the previous moment-copy packages from equality of laws,
and transports one density assumption on the dense source atom to all its
entries. The endpoint does not assume a CDF comparison, v3 model validity,
bandwidth identification, row-second-moment conclusions or nonsingularity.

This is still a conditional Proposition 3.6. Besides the named BBV
instances, it explicitly retains:

1. `hLSV`: the Theorem 3.1 minimum-singular-value input;
2. `hCount`: the all-cutoff Hermitization counting input;
3. `hBC12Negative`: bounded negative singular-value moments;
4. `hBC12Full`: full normalized dense/Ginibre logdet convergence.

These are proof parameters, not axioms. Passing an axiom audit verifies
the deductions and does not prove their input propositions.

## Unfinished integration and shortest continuation

The concrete-model/Lemma-3.5 adapter is complete and its final checks passed.
The remaining integration is separate:

- use the newly constructed cyclic v3 model to connect the existing
  Corollary 3.5 estimates to `hCount` at the manuscript mesoscopic cutoff;
- connect the published Theorem 3.1 model and its Hilbert--Schmidt cutoff
  removal to `hLSV`; the real-density branch must keep its explicit
  Brascamp--Lieb premise unless that is separately discharged;
- connect the shifted Gaussian least-value/count estimates to the already
  proved BC12 negative-moment route;
- supply `hBC12Full` using the already proved formula-to-logdet theorem.
  The allowed finite Ginibre correlation/projection formulas remain
  explicit external inputs; they are not derived from Gaussian entries.

No new spectral trace or Stieltjes-to-CDF smoothing theorem is needed.

## Resource and source hygiene

No large files or replacement dependency caches were downloaded. No cache
was deleted and no other project's process was stopped. The pre-existing
resource-only `-j 1` setting remains unchanged. The temporary incremental
Lean checker was shut down after use. The manuscript and original proof
projects were not edited, and nothing was pushed to GitHub in this turn.
