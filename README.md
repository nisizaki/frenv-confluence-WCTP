# FREnv Confluence — WCTP 2026 Artifact

This repository collects the Isabelle/HOL development of full beta/sigma confluence of FREnv and the associated Lean 4 development. It is intended to accompany a paper submitted to WCTP 2026.

**Verification:** both the Isabelle2025-2 build and the Lean 4.33.0 build/audit passed on clean GitHub Actions runners on 2026-09-13. See [the verification record](docs/verification.md) for the exact checked commit and logs.

**The two developments have different completion statuses.** Isabelle contains the full-confluence theorem and its dependencies. The imported Lean development contains syntax, reduction relations, and proved parallel-reduction infrastructure; it does **not** yet prove confluence. A successful Lean build verifies the declarations that are present, not the remaining confluence obligations.

## Layout

```text
isabelle/
  ROOTS                 Registers the four self-contained sessions
  FREnv/                FREnv syntax, reduction, and local confluence
  EnvEps/               Auxiliary calculus and transfer of full confluence
  vendor/               Required AFP Regular-Sets and Abstract-Rewriting sources
  docs/                 English mathematical explanations
  README.md             Isabelle build and interactive inspection instructions
lean/
  lean-toolchain        Pinned Lean version
  lakefile.toml         Lake project configuration
  lake-manifest.json     Dependency manifest (no external packages)
  LambdaFrenv.lean       Library entry point
  LambdaFrenv/           Definitions and proved supporting lemmas
  Audit.lean            Checks declarations and prints theorem axioms
  docs/                 English specifications and remaining obligations
  README.md             Lean build instructions and exact scope
docs/
  proof-map.md          Main results, dependency route, and differences
  verification.md       Verification record
UPSTREAM.json           Exact source commits and original file hashes
PROVENANCE.md           Extraction scope and packaging changes
.github/workflows/      Independent Isabelle and Lean verification jobs
```

## Obtain the artifact

```sh
git clone https://github.com/nisizaki/frenv-confluence-WCTP.git
cd frenv-confluence-WCTP
git rev-parse HEAD
```

Record the full commit hash when citing or evaluating the artifact. Use `git checkout <commit-hash>` to reproduce a particular revision. Neither submodules nor the original repositories are required for building this checkout.

## Verify Isabelle/HOL

Install **Isabelle2025-2** for your platform from the [official installation page](https://isabelle.in.tum.de/installation.html). Put its `bin` directory on your `PATH`, then run from this repository's root:

```sh
isabelle version
isabelle build -v -j 1 -o threads=2 -o quick_and_dirty=false -D isabelle
```

This builds the vendored AFP dependencies, the `FREnv` session, and the `EnvEps` session containing the final result:

```text
FREnv_Full_Confluence_Via_Translation.frenv_beta_sigma_confluent
```

The result states that any two finite beta/sigma reduction sequences from the same FREnv term have a common reduct. See [the Isabelle instructions](isabelle/README.md) for platform details and interactive inspection. Proof checking is enabled: the artifact explicitly disables `quick_and_dirty`.

## Verify Lean 4

Install [Elan](https://lean-lang.org/install/manual/), the Lean toolchain manager, and make `lake` available on your `PATH`. Then run:

```sh
cd lean
lake env lean --version
lake build
lake env lean Audit.lean
```

The checked-in `lean-toolchain` selects **leanprover/lean4:v4.33.0**. Elan downloads that version if necessary. There is no Mathlib dependency or cache-download step. See [the Lean instructions](lean/README.md) for the proved declarations and the distinction between a proposition definition and a proof.

## Results and scope

| Development | Main checked content | Full FREnv confluence |
|---|---|---|
| Isabelle/HOL | Auxiliary-calculus confluence, translation, surjectivity, simulation, lifting, and the final confluence theorem | Verified by the recorded strict session build |
| Lean 4 | Syntax with constants, beta/sigma reduction, parallel reduction, closure congruence, embedding, and simulation | Not supplied in the imported revision |

The languages also differ: Isabelle uses string names and has no primitive constants; Lean parameterizes variables and constants by types. This artifact does not claim a proved equivalence of the two encodings. The [proof map](docs/proof-map.md) explains these differences.

The mathematical Markdown files explain the proof route but are not themselves machine-checked. Historical thesis and roadmap references are retained for traceability; the thesis PDF is not needed to run either proof assistant.

## Reproducibility and attribution

See [PROVENANCE.md](PROVENANCE.md) for the pinned upstream revisions and changes made for packaging, [UPSTREAM.json](UPSTREAM.json) for a file-level source inventory, and [docs/verification.md](docs/verification.md) for actual verification results. The two GitHub Actions jobs repeat the build commands on clean runners.

The bundled AFP sources retain their authorship and license notices. See [the vendor notice](isabelle/vendor/README.md). No new blanket license is assigned to the upstream developments by this extraction.
