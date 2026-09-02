# Reused analytical proofs

Source: the user's local `finite-moment-short-ring-anchor` project,
snapshot 2026-09-02. That source directory is not a Git checkout.
The selected 30-module dependency closure is included as source so that
building this repository does not require the user's original directory.

These modules provide finite singular-value truncation, hard/soft edge
bookkeeping, probability limits, Hilbert–Schmidt identities, and the
elementary disk-potential integral. They do not assert Proposition 10.1.
Their generic input structures are ordinary theorem hypotheses, never
axioms; the Section 10 integration must construct them from the actual
model and the explicitly permitted Section 3 inputs.

In particular, the `BC12` namespace on the elementary disk-potential
calculation is a source organization choice, not an assumed Ginibre
circular-law theorem. Neither a BC12 limit assumption nor a Ginibre
negative-moment assumption may remain in the final Section 10 theorem.

The originals are preserved unchanged. No separate upstream license file
was present in the user's source project.

All 30 copied Lean files are byte-identical to the inspected local snapshot.
`SHA256SUMS` records that snapshot. Verify it from this directory with
`shasum -a 256 -c SHA256SUMS`.
