# Verification record

## Source inspection

The artifact was assembled from the two revisions recorded in [PROVENANCE.md](../PROVENANCE.md). Isabelle's final theorem is present with its transitive imports; Lean's confluence target is only a proposition definition. See [proof-map.md](proof-map.md).

## Reproducible checks

The [verification workflow](../.github/workflows/verify.yml) runs independent jobs on clean Ubuntu runners:

- Isabelle2025-2: `isabelle build -v -j 1 -o threads=2 -o quick_and_dirty=false -D isabelle`.
- Lean v4.33.0: `lake build`, followed by `lake env lean Audit.lean`; the job rejects a printed `sorryAx` dependency.

## Lean result

The Lean job of [run 34745901197](https://github.com/nisizaki/frenv-confluence-WCTP/actions/runs/34745901197), on artifact commit `6c9262f37a0e1e9e3313ab8f224001443438efe4`, succeeded on 2026-09-13. It used Lean 4.33.0 on x86_64 Linux and reported `Build completed successfully (5 jobs)`.

All ten supporting theorems listed in `Audit.lean` reported no axiom dependencies. The printed `ParStronglyConfluent` declaration was a definition of a proposition, not a proof. This result therefore does not establish Lean confluence.

## Isabelle result

The first run was cancelled while obtaining Isabelle from the main distribution endpoint; it had not reached proof checking. CI was changed to the official Cambridge mirror with explicit connection and transfer timeouts. The replacement Isabelle run is pending. Source inspection alone is not reported as a successful proof-assistant build.

## Packaging checks

- All 48 application theory files retain the upstream formal declarations and proof bodies; only the documented introductory text and session settings changed.
- Lean's `Basic.lean` and `Par.lean` match the upstream files byte-for-byte.
- The final Isabelle theorem's local transitive import closure contains 51 theories, including vendored theories. All those files are included. Additional theories are retained to build the complete upstream active sessions.
- All Markdown links to local files resolve, and Japanese labels in the included mathematical notes were translated into English.
