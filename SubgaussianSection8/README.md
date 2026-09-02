# General subgaussian Section 8

Independent working checkout and Lean library extending the verified Rademacher specialization to a fixed real centered variance-one subgaussian atom. Cook, Nguyen, and Section 3 Proposition 3.8 remain explicit external inputs. The final goal keeps the original logarithmic bandwidth hypothesis and every bounded continuous real test function.

This branch extends the verified RandomBandCircularLaw commit `24a1e37550a7e471bec4bb668ce4bde92fae3cbb`. GitHub branch: `codex/section8-subgaussian` in the existing repository. All new source belongs to the `SubgaussianSection8` namespace in this project. The prior project is not modified. Only imported modules are required; Section 4 must not enter the import closure.

Build the explicit target `lake build SubgaussianSection8`. The general theorem is under development and is not yet verified. Local development uses existing dependency artifacts read-only; final acceptance requires a normal scoped Lake build, placeholder scan, axiom audit, and review of the compiled public signature.
