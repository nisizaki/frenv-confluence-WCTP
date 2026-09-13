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

Successful commands return exit status 0. Build products are written under `.lake/` and are not committed. `Audit.lean` prints the axioms of the main theorems and their ingredients. No output mentions `sorryAx`, and the sources contain no `sorry`; the only axioms that appear are Lean's three standard ones, `propext`, `Classical.choice` and `Quot.sound`.

## Main result

```text
LambdaFrenv.frenv_beta_sigma_confluent :
  BetaSigmaSteps P Q₁ → BetaSigmaSteps P Q₂ → ∃ L, BetaSigmaSteps Q₁ L ∧ BetaSigmaSteps Q₂ L
```

Any two finite beta/sigma reduction sequences out of the same `λ_FREnv` term have a common reduct. This is the Lean counterpart of the Isabelle declaration `FREnv_Full_Confluence_Via_Translation.frenv_beta_sigma_confluent`.

## Layout

| File | Contents |
|---|---|
| `LambdaFrenv/Basic.lean` | `λ_FREnv` syntax, `BetaSigmaStep`, `ReflTransGen`, confluence predicates |
| `LambdaFrenv/Par.lean` | Parallel reduction of `λ_FREnv`, its embedding and simulation |
| `LambdaFrenv/Rewriting.lean` | Abstract rewriting: diamond property, `SN`, Newman's lemma |
| `LambdaFrenv/ParNotStrong.lean` | Refutation of `ParStronglyConfluent` |
| `LambdaFrenv/EnvEps/Syntax.lean` | The auxiliary calculus `λ_EnvEps` with a primitive `comp`, its `σ`, `β` and `βσ` relations |
| `LambdaFrenv/EnvEps/Length.lean` | The multiplicative length measure; `σ` is strongly normalizing |
| `LambdaFrenv/EnvEps/SigmaConfluence.lean` | Critical-pair analysis; `σ` is locally confluent, hence confluent |
| `LambdaFrenv/EnvEps/NormalForm.lean` | The `σ`-normal-form operator `snf`, its laws, and the normal-form grammar |
| `LambdaFrenv/EnvEps/PStep.lean` | Parallel `β` reduction, complete development, diamond property |
| `LambdaFrenv/EnvEps/Compat.lean` | Composition compatibility of parallel `β` with `snf` |
| `LambdaFrenv/EnvEps/BetaOverSigma.lean` | Beta over sigma; confluence of `λ_EnvEps` |
| `LambdaFrenv/Translation.lean` | `tr`, `incl`, simulation, single- and multi-step lifting, confluence of `λ_FREnv` |
| `LambdaFrenv/Confluence.lean` | The main theorems, restated |

## Proof route

`λ_FREnv` writes environment composition and function application with the same form `App (Eps M) N`, and the two readings overlap: `Assoc` and `DApp` both apply to `App (Eps (App (Eps L) M)) N`. Because of that overlap, parallel reduction of `λ_FREnv` is **not** strongly confluent (see below), and the sigma fragment of `λ_FREnv` has no obvious termination measure.

The proof therefore follows the Isabelle development and goes through the auxiliary calculus `λ_EnvEps`, whose syntax has a primitive composition constructor `comp` that separates the two readings:

1. `σ` on `λ_EnvEps` strictly decreases the measure `elen` (multiplicative on `comp`), so it is strongly normalizing.
2. `σ` is locally confluent — all nine root rules are `comp`-headed and pairwise non-overlapping, so only `idR` and congruence peaks need work. Newman's lemma gives confluence of `σ`, hence a well-defined normal form `snf`.
3. The `β` fragment is orthogonal, so parallel `β` reduction `PStep` has the diamond property, proved by the complete development `bcd`.
4. `key`: parallel `β` commutes with `σ`-normalization — `P ⇒β R` implies `snf P ⇒β S` with `snf S = snf R`. Its `comp` case is composition compatibility (`cc`), which is proved by induction on the length measure over the grammar of `σ`-normal forms.
5. Hence `BOS M N := ∃ W, PStep M W ∧ N = snf W` has the diamond property, and confluence of `λ_EnvEps`'s `→βσ` follows.
6. The translation `tr` collapses `comp A B` and `app (eps A) B`. It is surjective and simulates every `λ_EnvEps` step. A `λ_FREnv` step out of `tr M` need not be the image of a step out of `M`, but `lift1` produces a preimage sharing a `λ_EnvEps` reduct with `M`; confluence of `λ_EnvEps` then upgrades this to arbitrary chains, and confluence transfers to `λ_FREnv`.

Note that `→β*` and `→σ*` of `λ_EnvEps` do **not** commute, so the cheaper Hindley–Rosen route is unavailable; step 4 above is what replaces it.

## `ParStronglyConfluent` is false

`Par.lean` states `ParStronglyConfluent` — the diamond property of `λ_FREnv`'s `ParStep` — as an open target. `LambdaFrenv.not_parStronglyConfluent` proves its negation for every variable type with an inhabitant. On the associativity pentagon `((v∘v)∘v)∘v` (writing `A∘B` for `App (Eps A) B`) the root `Assoc` step and the `Assoc` step one level down give

```text
N₁ = (v∘v)∘(v∘v)          N₂ = (v∘(v∘v))∘v
```

and each of `N₁`, `N₂` has exactly three parallel reducts — itself, its root `Assoc` reduct and its root `DApp` reduct — with the two sets disjoint. The `overlap...` declarations at the end of `Par.lean` remain definitions of propositions; they are not used by the confluence proof.

## Interactive use

With the Lean 4 extension installed in VS Code, open **this `lean/` directory** as the project folder. The editor should select the same pinned toolchain as the command-line build.
