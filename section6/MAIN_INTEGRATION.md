# Verified Section 6 publication on main — 2026-09-03

This publication starts from main `6887a8c7591ec15c37513f6c0944605c3680d5ef`
and imports the Section 6 source snapshot
`c4d3273060e5537d5344863bfe1b90620808aef7`. The proof files are identical
to the successful checkpoint `9d98ca87d112a240fc5b596d1a27801450b15cbe`.

[Cloud run 33740349647](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33740349647)
passed the final target and its transitive imports, the 203-declaration
axiom audit, all seven new regressions and the 196-file selected source scan.
The only permitted audit foundations were `propext`, `Classical.choice`
and `Quot.sound`. See [the precise result and remaining inputs](BBV_ONLY_ENDPOINT.md).

## Preserved sources and minimal additions

A source-import closure check covers 587 project Lean files for the final
endpoint, audit and regression entry points. Of its 422 files outside
`section6/`, 419 already have identical Git blob identities on main and the
verified development snapshot. Exactly three are added without alteration:

- `section3/ShortRingAnchor/BC12/GinibreSmallBall.lean`
- `section3/ShortRingAnchor/BC12/GinibreNegativeMoments.lean`
- `section3/Vendor/Arxiv2410/V3/FreeDysonUniqueness.lean`

No existing Section 3 Lean file is changed. Its Proposition 3.8 additions,
umbrella imports, source-export scripts and previous verification records
are preserved. The density-definition correction is already present on main
and is not applied a second time. Its historical integration note and source
manifest entries for the additions are included.

Sections 4, 5, 8, 9, 10, the replacement dependency, root library registrations,
all pinned manifests/toolchains, and existing workflows are preserved.
Section 6 remains an independent subproject requiring Section 5; it does not
alter the root's default build targets. Section 6 proof files and its package
configuration are copied unchanged. Root/Section 6 documentation and a
dedicated Section 6 workflow provide the publication entry points.

## Verification and future builds

This is a source-identity publication of already cloud-verified proofs, not
a new whole-main compilation claim. The publication commit uses `[skip ci]`
so it does not rerun unrelated or previously verified suites. No local Lean
build, toolchain/mathlib/cache download or repository clone is needed.

For a later targeted check on a suitably provisioned machine or cloud runner:

```sh
cd section6
lake --no-cache build CircularLawSection6.BBVOnlyProfileEndpoint
lake --no-cache env lean -DwarningAsError=true BBVGinibreAudit.lean
lake --no-cache env lean -DwarningAsError=true BBVOnlyRegression.lean
```

The dedicated Section 6 workflow defaults to this final endpoint and audit/
regression chain and reuses shared caches. Its source scan uses the existing
main scanner's `--path` interface. The historical full-library mode remains
available with the explicit `[section6-full]` commit marker; the older
narrow interface markers retain their previous meaning. This workflow
configuration is checked for YAML and shell syntax during publication;
the successful run above verifies the unchanged Lean proof chain, not a
fresh execution of the publication's workflow configuration.

The current theorem retains the published BBV comparison and the two
pre-given finite Section 4 pressure estimates for each compact core.
It does not add independent Ginibre raw-log/spectral, squared-singular-law,
BC12 or Han hypotheses. These remaining mathematical premises are not
discharged by an axiom audit.
