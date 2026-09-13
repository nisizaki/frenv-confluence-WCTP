# Verification record

## Source inspection

The artifact was assembled from the two revisions recorded in [PROVENANCE.md](../PROVENANCE.md). Isabelle's final theorem is present with its transitive imports; Lean's confluence target is only a proposition definition. See [proof-map.md](proof-map.md).

## Reproducible checks

The [verification workflow](../.github/workflows/verify.yml) runs independent jobs on clean Ubuntu runners:

- Isabelle2025-2: `isabelle build -v -j 1 -o threads=2 -o quick_and_dirty=false -D isabelle`.
- Lean v4.33.0: `lake build`, followed by `lake env lean Audit.lean`; the job rejects a printed `sorryAx` dependency.

The initial CI execution is pending. This sentence will be replaced with the observed run result after verification. Source inspection alone is not reported as a successful proof-assistant build.
