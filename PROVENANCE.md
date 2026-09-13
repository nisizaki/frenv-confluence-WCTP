# Provenance and packaging changes

## Pinned upstream revisions

| Component | Repository | Commit |
|---|---|---|
| Isabelle and mathematical notes | [nisizaki/frenv-yamauchi](https://github.com/nisizaki/frenv-yamauchi) | `b5e666f51d0ad2e45e71c46ee8ace41c656dbd6c` |
| Lean and specifications | [nisizaki/frenv-lean4](https://github.com/nisizaki/frenv-lean4) | `b9bf34a8ea306eda158a54487d9fc7a92285d2d2` |

The source snapshots were obtained on 2026-09-13. [UPSTREAM.json](UPSTREAM.json) records each imported file's original path and SHA-256 hash. Those hashes identify upstream contents before the documented packaging edits; they are not hashes of the modified artifact files.

## Included and excluded material

- All active `FREnv/*.thy` and `EnvEps/*.thy` files, their session definitions, and the related mathematical Markdown files are included.
- The `Regular-Sets` and `Abstract-Rewriting` AFP snapshots required by these sessions are included with their auxiliary document files.
- Lean's library sources, entry point, exact toolchain, Lake configuration, dependency manifest, and mathematical notes are included.
- Historical unsuccessful proof experiments, unrelated repositories, assistant configuration, private handoff notes, PDFs, runtime installations, caches, and Git histories are not included.

## Packaging edits

1. Separate `isabelle/` and `lean/` projects and English top-level documentation were added.
2. `isabelle/ROOTS` registers the vendored libraries and both application sessions.
3. The application sessions explicitly disable `quick_and_dirty`.
4. Two stale theory introduction paragraphs that described already repaired gaps were updated; the formal definitions and proof bodies were not changed. The old vendor path in the introduction to `Newmans_Lemma.thy` was updated.
5. A few Japanese labels in the mathematical Markdown files were translated into English. Historical thesis and roadmap numbering was preserved.
6. `lean/Audit.lean`, platform-specific verification instructions, and independent CI jobs were added. Lean's definitions and proofs were copied without semantic changes.

This packaging does not complete Lean's remaining proof obligations or change either calculus to make the encodings coincide.

## Attribution

Authors and attribution notices in the imported source files are preserved. The upstream application repositories do not supply a repository-wide license in these snapshots; this extraction does not invent one. Vendored AFP sources retain their own licensing; see [the vendor notice](isabelle/vendor/README.md).
