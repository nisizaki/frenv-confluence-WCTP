# FREnv Confluence — WCTP 2026 Artifact

English | [日本語](README-ja.md) | [Tagalog](README-tl.md) | [简体中文](README-zh.md)

This repository collects the Isabelle/HOL development of full beta/sigma confluence of FREnv and the associated Lean 4 and Mizar developments. It is intended to accompany a paper submitted to WCTP 2026.

**Verification:** both the Isabelle2025-2 build and the Lean 4.33.0 build/audit passed on clean GitHub Actions runners on 2026-09-13, at commit `725b0b6`, which is the revision that contains the Lean confluence proof. See [the verification record](docs/verification.md) for the exact checked commits and logs.

**All three developments now prove full confluence, by independent routes.** Isabelle contains the full-confluence theorem and its dependencies. The Lean development proves the same statement for its own encoding, as `LambdaFrenv.frenv_beta_sigma_confluent`, and the Mizar development proves it as `FRENV_5:8`. All three follow the same mathematical route (auxiliary calculus, sigma normalization, beta over sigma, translation) but with their own definitions and proofs. The encodings still differ — Lean has a primitive constants type, and the three treat variables differently — and this artifact does not claim a proved equivalence between them.

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
  LambdaFrenv/           Definitions and proofs, including the confluence theorem
  LambdaFrenv/EnvEps/    The auxiliary calculus and its confluence proof
  Audit.lean            Checks declarations and prints theorem axioms
  docs/                 English specifications of the syntax and reductions
  README.md             Lean build instructions, layout, and proof route
mizar/
  text/                 The fifteen articles, plus the audit article
  dict/                 Private vocabularies for the symbols introduced here
  verify.sh             Verifies every article in dependency order
  check.sh              Verifies one article
  docs/                 Verification instructions and records of the work
  README.md             Mizar requirements, layout, and proof route
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

The checked-in `lean-toolchain` selects **leanprover/lean4:v4.33.0**. Elan downloads that version if necessary. There is no Mathlib dependency or cache-download step. The build establishes

```text
LambdaFrenv.frenv_beta_sigma_confluent
```

the Lean counterpart of the Isabelle theorem. See [the Lean instructions](lean/README.md) for the module layout and the proof route.

## Verify Mizar

Install **Mizar Ver. 8.1.15** with its MML from the
[Mizar download page](https://mizar.uwb.edu.pl/system/), put its executables on
your `PATH`, and set `MIZFILES` to the Mizar library directory. Then run:

```sh
cd mizar
export MIZFILES=/usr/local/share/mizar   # if not already set by the installer
./verify.sh
```

This verifies the fifteen articles in dependency order, exporting each to a
local `prel/` database so the next one can import it, and finally checks an
audit article that restates each main result and justifies it by its citation
alone. Nothing outside the standard MML is used and nothing is downloaded. The
build establishes

```text
FRENV_5:8   for V being non empty set holds FrRed(V) is confluent
```

the Mizar counterpart of the Isabelle and Lean theorems. Mizar has no `sorry`
and no way for an article to introduce an axiom, so an empty `.err` file means
every inference was checked. See [the Mizar instructions](mizar/README.md) for
the layout and the proof route, and
[the verification guide](mizar/docs/verification.md) for what the output means
and how to inspect individual results.

## Results and scope

| Development | Main checked content | Full FREnv confluence |
|---|---|---|
| Isabelle/HOL | Auxiliary-calculus confluence, translation, surjectivity, simulation, lifting, and the final confluence theorem | Verified by the recorded strict session build |
| Lean 4 | Abstract rewriting and Newman's lemma, the auxiliary calculus, sigma termination and confluence, sigma-normal forms, the parallel-beta diamond property, composition compatibility, translation and lifting | Verified by the recorded Lean build |
| Mizar | Parse-tree syntax of both calculi, sigma termination and confluence via the MML's Newman's lemma, sigma-normal forms, the parallel-beta triangle property, composition compatibility, Hardin's interpretation method, translation and lifting | Verified by `mizar/verify.sh` |

The languages also differ: Isabelle uses string names and has no primitive constants; Lean parameterizes variables and constants by types; Mizar parameterizes the development by an arbitrary non-empty set of variables and, like Isabelle, has no constants. This artifact does not claim a proved equivalence of the three encodings. The [proof map](docs/proof-map.md) explains these differences.

The mathematical Markdown files explain the proof route but are not themselves machine-checked. Historical thesis and roadmap references are retained for traceability; the thesis PDF is not needed to run either proof assistant.

## Reproducibility and attribution

See [PROVENANCE.md](PROVENANCE.md) for the pinned upstream revisions and changes made for packaging, [UPSTREAM.json](UPSTREAM.json) for a file-level source inventory, and [docs/verification.md](docs/verification.md) for actual verification results. The two GitHub Actions jobs repeat the build commands on clean runners.

The bundled AFP sources retain their authorship and license notices. See [the vendor notice](isabelle/vendor/README.md). No new blanket license is assigned to the upstream developments by this extraction.
