# Dependency provenance and repository layout

This is a source-only subproject of
[random-band-circular-law-lean](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean).
Its `lakefile.toml` uses only repository-relative paths.

## Current Section 3 integration (2026-09-03)

The active `ShortRingAnchor` and `Vendor` libraries come from the checked
`../section3/` package, including the shared corrected bounded-density field.
For this publication, all 316 imported non-Section-5 repository modules were
checked byte-for-byte against main `3c2005e1ce2987e9fc211d10c156d70240b5b93e`.
No Section 3, Section 4, replacement, or parent library-registration change is
needed. The old vendor snapshot and five historical support copies remain for
provenance, but no longer own the active modules. See
[SECTION3_INTEGRATION.md](SECTION3_INTEGRATION.md) and
[CONCRETE_SECTION3_INTERFACE.md](CONCRETE_SECTION3_INTERFACE.md).
The original release's dependency alignment below is retained as history.

## Checked versions

- Lean: `leanprover/lean4:v4.33.0`.
- mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d` (v4.33.0).
- Parent snapshot inspected:
  `d6c29a1e3f125da59c3da47f68848797259e2cf7`.
- Replacement upstream:
  [tao-vu-replacement-principle-lean](https://github.com/hanyi162013-Yihan/tao-vu-replacement-principle-lean),
  commit `2f96f5460eea0965956f69d787ebc722f1392078`.

The original parent package supplied `CircularLawSection4` from `../Section4`,
`TaoVuReplacement` from `../vendor/tao-vu-replacement`, and the existing
`ShortRingAnchor` support modules from `../vendor/short-ring-analysis`.
The child shares `../.lake/packages`; no second mathlib checkout is required.

The 271-module local project/upstream import closure was checked against that
parent snapshot. All required Section 4 files matched byte-for-byte. All twelve
used replacement modules differ only in the parent snapshot's extra final
newline; all thirteen available replacement modules were checked this way.
Existing short-ring support modules matched byte-for-byte.

## Five additional short-ring support modules

The original parent snapshot lacked these files used by Section 5:

- `ShortRingAnchor.AtomAssumption21`
- `ShortRingAnchor.NormalizedGinibre`
- `ShortRingAnchor.Proposition36Source`
- `ShortRingAnchor.CutoffDominance`
- `ShortRingAnchor.Proposition36`

Exact copies of the locally checked source files are included under `upstream/`
(49,222 bytes total). Their build locations are now in the parent's
`vendor/short-ring-analysis/ShortRingAnchor/` directory, so the existing
`ShortRingAnchor` library owns every module in this namespace. CI checks that
the five build copies are byte-identical to the checksummed `upstream/` copies.
An initial attempt to register them in a second, child library caused Lake to
look for the same modules under the parent library as well; that duplicate
registration has been removed. No pre-existing parent source was replaced.
Their generic estimates remain explicit hypotheses. This is not a claim that
Section 3, or its full short-ring input, has been proved.

The source is the user's local finite-moment-short-ring-anchor project,
snapshot 2026-09-02. It is not a Git checkout and had no separate license file.
No additional mathematical assumptions are hidden by this packaging.

## Verification

The original mathematical source remains unchanged from the checked local
Section 5 project. The new concrete Section 3 adapter is separately covered by
successful cloud run 33725000131 and its 93-declaration transitive audit.
The historical local verification included integrated compilation,
strict extension-module checks, both axiom audits, 15 boundary regressions, and
118-module kernel replay. The additional repository-relative local build was
interrupted at the user's request on 2026-09-02, with no error reported before
interruption. Its successful completion is not claimed. The remaining integrated
build and audit are delegated to the repository's **Section 5 verification**
GitHub Actions workflow; consult its run for the actual result.

`SOURCE_SHA256SUMS` records the published source/configuration/validation files.
From this directory, verify file integrity with
`shasum -a 256 -c SOURCE_SHA256SUMS`.

The local publication check reuses the already installed shared packages and
compiled caches. A fresh machine still needs a compatible Lean/mathlib
installation; no dependency download is initiated as part of preparing this
publication. The new `.github/workflows/section5.yml` runs on GitHub-hosted
Ubuntu with shared mathlib dependencies, project build caching, and retained
build/audit logs. Its downloads occur on the remote runner, not this local
machine. Existing workflows and parent build targets are unchanged.
