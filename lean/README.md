# Lean 4 verification

## Install and build

Install [Elan](https://lean-lang.org/install/manual/) and open a new terminal in which `lake` is available. On Windows, use the native Elan installation or a Linux Elan installation inside WSL. On Linux and macOS, use the standard shell installation.

From the repository root:

```sh
cd lean
lake env lean --version
lake build
lake env lean Audit.lean
```

These commands must run in `lean/`, so that Elan finds `lean-toolchain` and Lake finds `lakefile.toml`. The pinned toolchain is `leanprover/lean4:v4.33.0`. The project uses Lean's core library only. Keep the committed manifest; no `lake update` or Mathlib download is required.

For a clean rebuild:

```sh
lake clean
lake build
lake env lean Audit.lean
```

Successful commands return exit status 0. Build products are written under `.lake/` and are not committed. `Audit.lean` prints the axioms of the proved supporting theorems and displays the confluence proposition's definition. In particular, theorem output should not depend on `sorryAx`.

## What is proved

The entry point `LambdaFrenv.lean` imports `LambdaFrenv/Basic.lean` and `LambdaFrenv/Par.lean`.

| Declaration | Meaning |
|---|---|
| `LambdaFrenv.ReflTransGen.trans` | Transitivity of the custom reflexive-transitive closure |
| `LambdaFrenv.ReflTransGen.single` | Embedding a single step in the closure |
| `LambdaFrenv.BetaSigmaSteps.lam`, `.appL`, `.appR`, `.extL`, `.extR`, `.eps` | Closure under term constructors |
| `LambdaFrenv.ParStep.embed` | Embedding one beta/sigma step into parallel reduction |
| `LambdaFrenv.ParStep.sim` | Simulating a parallel step by beta/sigma multi-step reduction |

`ParStep.refl` is a constructor of the parallel-reduction relation.

## What remains open

`ParStronglyConfluent` and the `overlap...` declarations at the end of `Par.lean` are **definitions of propositions**, not proofs of those propositions. For example, `def ParStronglyConfluent : Prop := ...` constructs a proposition; it does not construct an inhabitant of that proposition.

This imported revision provides no theorem establishing `ParStronglyConfluent` or full FREnv confluence. There are no admitted proofs needed to state these open goals, so absence of `sorry` does not mean the intended theorem is complete. The [parallel-reduction notes](docs/frenv-parallel-reduction.md) describe the remaining work.

This is an accompanying development, not a completed Lean replay of the Isabelle result. It includes a primitive constants type and constant-related rules, unlike the Isabelle encoding. See [the comparison](../docs/proof-map.md).

## Interactive use

With the Lean 4 extension installed in VS Code, open **this `lean/` directory** as the project folder and inspect `LambdaFrenv/Basic.lean`, `LambdaFrenv/Par.lean`, or `Audit.lean`. The editor should select the same pinned toolchain as the command-line build.
