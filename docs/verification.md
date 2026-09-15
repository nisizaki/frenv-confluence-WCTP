# Verification record

## Source inspection

The artifact was assembled from the two revisions recorded in [PROVENANCE.md](../PROVENANCE.md). Isabelle's final theorem is present with its transitive imports. The Lean development has since been extended with its own confluence proof, and a third, Mizar development was written for this artifact; see [proof-map.md](proof-map.md).

## Reproducible checks

The [verification workflow](../.github/workflows/verify.yml) runs independent jobs on clean Ubuntu runners:

- Isabelle2025-2: `isabelle build -v -j 1 -o threads=2 -o quick_and_dirty=false -D isabelle`.
- Lean v4.33.0: `lake build`, followed by `lake env lean Audit.lean`; the job rejects a printed `sorryAx` dependency.

## Verified revision

Both jobs in [run 34746238118](https://github.com/nisizaki/frenv-confluence-WCTP/actions/runs/34746238118) succeeded on 2026-09-13 at artifact commit `31222ddbc0cb8d1d70a9174cffae42609795413a`, on clean Ubuntu 24.04 x86_64 runners. Subsequent changes recording this result modify documentation only; the checked theories, Lean sources, session configurations, and workflow commands are unchanged.

## Lean result

The Lean job of [run 34745901197](https://github.com/nisizaki/frenv-confluence-WCTP/actions/runs/34745901197), on artifact commit `6c9262f37a0e1e9e3313ab8f224001443438efe4`, succeeded on 2026-09-13. It used Lean 4.33.0 on x86_64 Linux and reported `Build completed successfully (5 jobs)`.

The Lean build and audit also succeeded in the final verification run linked above.

All ten supporting theorems listed in the `Audit.lean` of that revision reported no axiom dependencies. The printed `ParStronglyConfluent` declaration was a definition of a proposition, not a proof. That run therefore did not establish Lean confluence.

### Lean confluence proof (added after the run above)

The Lean sources were subsequently extended with a full confluence proof. The extended development was checked locally with the pinned toolchain `leanprover/lean4:v4.33.0` on Ubuntu 26.04 aarch64 under WSL2, using exactly the documented commands `lake build` and `lake env lean Audit.lean`; both returned exit status 0. `Audit.lean` reports, for every listed theorem, only the standard Lean axioms `propext`, `Classical.choice` and `Quot.sound`; no output mentions `sorryAx`, and the sources contain no `sorry`. `Classical.choice` enters through the sigma-normal-form operator `snf`, which selects a normal form.

The main declaration is `LambdaFrenv.frenv_beta_sigma_confluent`. `LambdaFrenv.not_parStronglyConfluent` additionally refutes the strong-confluence target that the earlier revision had left open.

This extended development was then verified on clean runners as well. Both jobs of [run 34750771522](https://github.com/nisizaki/frenv-confluence-WCTP/actions/runs/34750771522) succeeded on 2026-09-13 at artifact commit `725b0b698632235c1f4881966e0c1653331f1b99` on `main`, on `ubuntu-24.04` x86_64 runners: the Isabelle job in 2 m 10 s and the Lean job in 21 s. The Lean job log reports `Build completed successfully (16 jobs)` and prints, for `LambdaFrenv.frenv_beta_sigma_confluent`, the axioms `[propext, Classical.choice, Quot.sound]`; the job fails if any audited theorem depends on `sorryAx`, and it did not. The local build was on aarch64 and the CI build on x86_64, so the result is not architecture-specific.

## Mizar result

The Mizar development was added after the runs above and is checked locally, not in CI: there is no packaged Mizar distribution that a clean runner can install without a manual download step.

It was verified on 2026-09-15 with Mizar Ver. 8.1.15 (Linux/FPC) and MML 5.99 on Ubuntu under WSL 2, by running `./verify.sh` from `mizar/` on a clean checkout. All fifteen articles produced empty `.err` files, and so did `text/audit.miz`, which restates the six main results and justifies each by its citation alone. The development was reorganised for readability later the same day and re-verified in full afterwards. The main result is

```text
FRENV_5:8   for V being non empty set holds FrRed(V) is confluent
```

Mizar has no `sorry` and no mechanism for an article to introduce an axiom, so an empty error file means the verifier accepted every inference in the article. The only items an article may assume are the environment items it declares, which the accommodator resolves against the MML and the local `prel/` database built from the earlier articles. See [the Mizar verification guide](../mizar/docs/verification.md) for the details and for how to inspect individual results.

## Isabelle result

The first run was cancelled while obtaining Isabelle from the main distribution endpoint; it had not reached proof checking. CI was changed to the official Cambridge mirror with explicit connection and transfer timeouts.

The replacement [Isabelle job](https://github.com/nisizaki/frenv-confluence-WCTP/actions/runs/34746238118/job/103694579460) succeeded with Isabelle2025-2 and `quick_and_dirty=false`. Its log reports completion of `Regular-Sets`, `Abstract-Rewriting`, `EnvEps`, and `FREnv`, and explicitly reports 100% processing of `EnvEps.FREnv_Full_Confluence_Via_Translation`. The build command took approximately 1 minute 39 seconds on that runner, excluding download and extraction. This timing is an observation, not a performance guarantee.

This is a fresh proof-assistant build of the packaged sources, not only a source-and-history assessment.

## Packaging checks

- All 48 application theory files retain the upstream formal declarations and proof bodies; only the documented introductory text and session settings changed.
- Lean's `Basic.lean` and `Par.lean` match the upstream files byte-for-byte.
- The final Isabelle theorem's local transitive import closure contains 51 theories, including vendored theories. All those files are included. Additional theories are retained to build the complete upstream active sessions.
- All Markdown links to local files resolve, and Japanese labels in the included mathematical notes were translated into English.
