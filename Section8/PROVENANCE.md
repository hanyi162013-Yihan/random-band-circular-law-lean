# Source and checkout provenance

The mathematical source is the fixed arXiv `2609.01295v1` snapshot already provided for this task. Section 8 occupies PDF pages 43–53, with Lemma 8.1, Proposition 8.2, Lemma 8.3, Corollary 8.4 and equations (8.1)–(8.69). The high-band input is Proposition 3.8.

- PDF SHA-256: `c09843c706aebf8a33358d870a7c9d11d7c52926b0132605fa2ffd7eed4f512d`
- `part2_block.tex` SHA-256: `9ad6009606b66d6a02afbe7df56872276f98e9196ecf66522032f91de86c1fbc`
- Repository base: `d6c29a1e3f125da59c3da47f68848797259e2cf7`
- Working branch: `section8-bernoulli`
- Lean: `4.33.0`
- Mathlib checkout: `db584cd6d46c92f209a44c0f1c829460d327499d`

The task uses its own checkout and build outputs. The concurrent publication checkout is read-only for this task. Previously compiled dependencies were reused for development only when their source code and toolchain matched; the few algebra modules with documentation-only differences were compared after masking comments. No Lake trace or hash files were fabricated. The required build gate is now the normal Section 8 target and its necessary dependencies, as requested by the user; unrelated library targets are not part of this task's verification.
