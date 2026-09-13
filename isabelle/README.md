# Isabelle/HOL verification

## Requirements

Use Isabelle2025-2. Platform bundles and installation details are available from the [official installation page](https://isabelle.in.tum.de/installation.html). A separate AFP installation is unnecessary: the required sources are in `vendor/`.

On Linux or macOS, use the distribution's `bin/isabelle` executable. On Windows, open the distribution's **Cygwin-Terminal** and run the same shell commands; for example, a checkout under `C:\work` is reachable as `/cygdrive/c/work`. In WSL, install the Linux bundle matching the WSL architecture and run entirely inside WSL. Do not invoke the Windows executable as a Linux binary.

Check the selected executable:

```sh
isabelle version
```

The expected version is `Isabelle2025-2`.

## Batch verification

From the top-level repository directory:

```sh
isabelle build -v -j 1 -o threads=2 -o quick_and_dirty=false -D isabelle
```

Alternatively, from this `isabelle/` directory:

```sh
isabelle build -v -j 1 -o threads=2 -o quick_and_dirty=false -D .
```

`ROOTS` registers `Regular-Sets`, `Abstract-Rewriting`, `FREnv`, and `EnvEps`. The first two are vendored dependencies. `FREnv` depends on HOL; `EnvEps` has `Abstract-Rewriting` as its parent and imports theories from the `FREnv` session. The theory lists preserve all active upstream FREnv and EnvEps theories, including local confluence as a separately useful supporting result.

A successful command exits with status 0 and reports the sessions finished or already up to date. The first build also checks the library dependencies and may take substantially longer than later builds. To force a fresh build of the main sessions:

```sh
isabelle build -c -v -j 1 -o threads=2 -o quick_and_dirty=false -d isabelle FREnv EnvEps
```

The session configurations explicitly set `quick_and_dirty = false`. Do not enable it when evaluating the proof artifact. A build that permits skipped proofs is not the verification described here.

## Inspect the final theorem

After batch verification, start the IDE from the repository root:

```sh
isabelle jedit -d isabelle -l HOL isabelle/EnvEps/FREnv_Full_Confluence_Via_Translation.thy
```

Navigate to `frenv_beta_sigma_confluent`. Its fully qualified name is:

```text
FREnv_Full_Confluence_Via_Translation.frenv_beta_sigma_confluent
```

The assumptions are two reflexive-transitive beta/sigma reductions from one FREnv term. The conclusion supplies one term reachable from both endpoints. It is a theorem of full confluence on all terms, not only local confluence or confluence restricted to normal forms.

The main dependencies are explained in [the proof map](../docs/proof-map.md). The English mathematical notes are in [docs/](docs/). Paths written as `docs/...` inside upstream theory comments refer to this directory's `docs/` folder; they are explanatory text, not imports.

## Troubleshooting

- **Unknown session or theory:** run from the repository root with `-D isabelle`, or from this directory with `-D .`; retain the complete `vendor/` directories.
- **Different Isabelle version:** select the Isabelle2025-2 executable explicitly. Compatibility with another release is not implied.
- **Memory pressure:** keep `-j 1` and reduce `threads` to 1. The distribution's standard HOL heap is also needed.
- **Stale heap:** use the clean-build command above. Isabelle normally stores heaps and logs in its user directory, not beside the theories.
- **IDE still processing:** batch verification is the primary reproducible check; wait for document processing before interpreting the IDE status.
