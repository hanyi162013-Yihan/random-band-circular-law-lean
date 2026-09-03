# Section 10 continuation: proof provenance

The continuation is based on arXiv:2609.01295v1, with the theorem-by-theorem
alignment in `FORMALIZATION_MAP.md`. The earlier Section 10 local estimates
and the Section 9 deterministic library are retained as module dependencies.
The original external workspaces have not been edited.

The current source-connected extension is verified by scoped run
`33719162307` at `362c47f`. Root Lake now uses `section3/`, at common baseline
`42c26b6` with shared density correction `5c7be7b`; the old generic vendor
snapshot below remains only as historical provenance. Actual BBV/BC12
applications and the real-only geometric Brascamp–Lieb boundary are recorded
in [SOURCE_CONNECTION_AUDIT.md](SOURCE_CONNECTION_AUDIT.md) and
[COMPLEX_REUSE_AUDIT.md](COMPLEX_REUSE_AUDIT.md). No newer Proposition 3.8
result is used by the Section 10 endpoint.

## Proved dependencies included in this repository

- `vendor/tao-vu-replacement`: the user's Tao–Vu project, pinned at
  `2f96f5460eea0965956f69d787ebc722f1392078`. Its 13 library modules are
  reused with unchanged proof text. See its provenance, Apache-2.0 license,
  and exact SHA-256 manifest.
- `vendor/short-ring-analysis`: 30 modules from the user's
  `finite-moment-short-ring-anchor` workspace, inspected on 2026-09-02.
  They contain generic singular-value truncation, moment bounds,
  probability-limit arguments, scalar-ring geometry, and elementary disk
  potential calculations. The copied files are byte-identical to that
  non-Git source snapshot; a SHA-256 manifest is included.

Neither dependency is a new mathematical assumption. Their proved lemmas
are kernel-checked, and the final theorem's transitive axioms are audited.

## Adapted proofs

The following Section 10 modules adapt proofs from the user's
`circularlawsections5-6` workspace, rather than importing that workspace or
its abstract model certificates:

The Section 5/6 labels in this provenance table identify the original
workspace's modules, not the chapter number of the present paper. All
current results and source-item mappings use arXiv v1's Section 10 numbering.

| Section 10 module | Source proof / adaptation |
|---|---|
| `ProbabilityLimits` | Section 5 triangular probability convergence and deterministic calibration; local concrete measure types |
| `PhysicalReplacement` | Section 6 physical normalization bridge; arbitrary dimension sequence |
| `DiskReferenceLaw` | Section 5 normalized disk measure and its potential; local namespace and explicit analytical dependencies |
| `DiagonalDiskReference` | Section 5 internally constructed diagonal disk reference; subsequences of arbitrary diverging dimensions |
| `SpectralLimitAssembly` | Section 6 addition of the reference spectral limit to the replacement conclusion |
| `CircularLawFromPotential` | Section 5 internal product-space construction and removal of the auxiliary disk sample |
| `WeakCircularLaw` | Section 5 compact-support cutoff argument, generalized to arbitrary positive matrix dimensions |

`DimensionReplacement` adapts the proved Tao–Vu argument from the index
`Fin (k+1)` to `Fin (d k+1)`. `PositiveMatrixIndex` then proves the reindexing
identities needed for the paper's actual dimension `(s+3)W`. These are
checked proof adaptations, not casts of an unavailable theorem.

## Historical conditional endpoint's permitted theorem inputs

`SourceInputs.Section3Inputs` records exactly the real-IID specializations
of Theorem 3.1, Proposition 3.3, Lemma 3.4, and Proposition 3.5. It is an
ordinary proposition supplied to the final theorem, as authorized by the
user. No other paper theorem or literature result is postulated by a
custom axiom. In particular, Proposition 10.1, the pressure limit, the
remainder estimate, the comparison model, and Tao–Vu are not input fields.

The least-singular-value input retains its Hilbert–Schmidt cutoff. The
cutoff is removed by `CutoffRemoval` using the actual expected normalized
energy. The two bulk comparisons use the same Ginibre array, which cancels;
no extra Ginibre full-logarithm limit or negative-moment premise is used.

The audit and formalization map, not the presence of a source file alone,
determine which modules have completed verification at a given checkpoint.
