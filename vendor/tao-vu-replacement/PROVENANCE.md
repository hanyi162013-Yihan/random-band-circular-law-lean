# Proved Tao–Vu dependency

Source: https://github.com/hanyi162013-Yihan/tao-vu-replacement-principle-lean

Pinned source commit: `2f96f5460eea0965956f69d787ebc722f1392078`.
Retrieved from the user's clean local checkout on 2026-09-02.
License: Apache-2.0; the original license is included.
Toolchain and mathlib: v4.33.0, matching this project.

The 13 library modules required by `TaoVuReplacement.ReplacementPrinciple`
are included locally for reproducible, network-independent source delivery.
They are proof dependencies, not additional mathematical assumptions.
The upstream audit driver is not copied; the integrated Section 10 audit
checks the final theorems and their complete transitive axiom dependencies.

Any adaptation from the upstream size convention `k + 1` to arbitrary
positive dimension sequences is proved separately in Section 10. The
upstream library files are not modified for that purpose.

The proof text was compared against the pinned Git objects. The only byte
difference is one additional final blank line in each copied Lean file.
`SHA256SUMS` records the exact vendored bytes; verify it from this directory
with `shasum -a 256 -c SHA256SUMS`.
