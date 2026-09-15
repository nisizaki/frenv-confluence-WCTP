# Mizar verification

A Mizar formalization of full beta/sigma confluence of $\lambda_{\mathrm{FREnv}}$,
following the same mathematical route as the Isabelle/HOL and Lean 4
developments in this artifact: an auxiliary calculus
$\lambda_{\mathrm{Env}\varepsilon}$ with a primitive environment composition,
sigma termination and confluence, sigma normal forms, parallel beta reduction,
Hardin's interpretation method, and finally a translation back to
$\lambda_{\mathrm{FREnv}}$.

## Requirements

Mizar **Ver. 8.1.15** with MML **5.99** (1507 articles), from the
[Mizar download page](https://mizar.uwb.edu.pl/system/). Any recent Mizar
release with a matching MML should work; nothing outside the standard MML is
used.

After installation, `mizf`, `verifier`, `accom`, `makeenv` and `miz2prel` must
be on `PATH`, and `MIZFILES` must point at the Mizar library directory — the
one containing `mml/`, `prel/` and `mizar.msg`. The Linux distribution
installs it at `/usr/local/share/mizar`, which is what the scripts here assume
when `MIZFILES` is unset.

```sh
export MIZFILES=/usr/local/share/mizar
verifier            # prints: Mizar Ver. 8.1.15 (Linux/FPC)
```

## Batch verification

From this `mizar/` directory:

```sh
./verify.sh
```

The script verifies the fourteen articles in dependency order and exports each
to a local `prel/` database so that the next one can import it, then checks
`text/audit.miz`, which restates each main result and justifies it by its
citation alone. On success it prints one `ok` per article and ends with

```text
All 14 articles verified with no errors, and the audit article
re-derives each main result from its citation alone.
Main theorem: FRENV_5:8  (FrRed(V) is confluent)
```

It exits non-zero and prints the error file if any article fails. A full run
takes about one and a half minutes on a laptop.

`./verify.sh clean` removes everything Mizar generated, leaving only the
sources.

To re-check a single article after the ones it depends on have been exported:

```sh
./check.sh enveps_8
```

Mizar has no `sorry` and no admitted-goal mechanism, so an empty `.err` file
means every inference in the article was machine checked. See
[docs/verification.md](docs/verification.md) for how to read the error files
and how to inspect individual results.

## Main theorem

```text
FRENV_5:8   for V being non empty set holds FrRed(V) is confluent
```

`FrRed(V)` is the beta/sigma reduction of $\lambda_{\mathrm{FREnv}}$ over a
variable set `V`, defined as the least relation closed under the ten root rules
and six congruence rules. `confluent` is the attribute of `REWRITE1`, the MML
theory of abstract rewriting: any two finite reduction sequences from a common
source have a common reduct.

The theorem in term form, which is what the attribute unfolds to for terms, is

```text
FRENV_5:6   for P,Q1,Q2 being FrEnvTerm of V
            st FrRed(V) reduces P,Q1 & FrRed(V) reduces P,Q2
            ex Q being FrEnvTerm of V st
              FrRed(V) reduces Q1,Q & FrRed(V) reduces Q2,Q
```

Intermediate results:

| Result | Declaration |
|---|---|
| $\to_\sigma$ terminates | `ENVEPS_1:43` |
| $\to_\sigma$ is locally confluent | `ENVEPS_4:11` |
| $\to_\sigma$ is confluent | `ENVEPS_4:12` |
| $\to_\beta$ is confluent | `ENVEPS_7:34` |
| parallel reduction commutes with sigma normalization | `ENVEPS_8:30` |
| $\to_{\beta\sigma}$ of $\lambda_{\mathrm{Env}\varepsilon}$ is confluent | `ENVEPS_9:13` |
| **$\to_{\beta\sigma}$ of $\lambda_{\mathrm{FREnv}}$ is confluent** | `FRENV_5:8` |

## Layout

```text
text/          the fourteen Mizar articles (.miz), plus audit.miz
dict/          private vocabularies for the symbols introduced here (.voc)
verify.sh      verify everything in dependency order; `clean` removes output
check.sh       verify one article and show its error file
docs/          verification instructions and the records of the work
prel/          local library, created by verify.sh (not tracked)
```

| Article | Lines | Theorems | Content |
|---|---:|---:|---|
| `enveps_1` | 2104 | 44 | syntax, constructors, structural induction, length measure, $\sigma$ reduction, termination |
| `enveps_2` | 866 | 28 | multi-step congruence, inversion, the sixteen $\sigma$ rules as named steps |
| `enveps_3` | 1091 | 9 | inversion by head constructor, convergence witness, chaining |
| `enveps_4` | 2228 | 12 | the eight root peaks, the composition peak, local confluence, confluence |
| `enveps_5` | 635 | 19 | $\sigma$ normal forms, their grammar, `snf` and its computation laws |
| `enveps_6` | 2194 | 57 | $\beta$ reduction, $\beta\sigma$ reduction, the nineteen rules |
| `enveps_7` | 2651 | 34 | parallel reduction, the triangle property, the diamond property, confluence of $\beta$ |
| `enveps_8` | 1461 | 30 | composition compatibility and the key lemma |
| `enveps_9` | 421 | 13 | Hardin's interpretation method; confluence of $\beta\sigma$ |
| `frenv_1` | 818 | 17 | syntax of $\lambda_{\mathrm{FREnv}}$ |
| `frenv_2` | 1097 | 25 | $\beta\sigma$ reduction of $\lambda_{\mathrm{FREnv}}$ |
| `frenv_3` | 799 | 20 | the translation, its recursion equations, surjectivity and inversion |
| `frenv_4` | 473 | 3 | simulation |
| `frenv_5` | 879 | 8 | single-step and multi-step lifting, confluence |
| `audit` | 54 | 6 | restates the main results, each justified by its citation alone |

## The proof route

1. $\sigma$ terminates by a multiplicative length measure, and is locally
   confluent by a case analysis over the twelve critical pairs. Newman's lemma
   is available in the MML as the registration
   `strongly-normalizing locally-confluent -> confluent` of `REWRITE1`, and
   with it the normal form operator, which gives `snf`.
2. $\beta$ is confluent by the Tait–Martin-Löf method, with a parallel
   reduction whose triangle property is stated in existential form — for every
   term there is a term absorbing all of its parallel reducts. The complete
   development cannot be written as a `DTCONSTR` structural recursion, because
   the beta-closure rule inspects a grandchild of the node.
3. The two layers are combined by Hardin's interpretation method. The key
   lemma is that parallel reduction commutes with $\sigma$-normalization. Its
   heart is the composition compatibility lemma, proved by strong induction on
   the length measure over the grammar of $\sigma$ normal forms.
4. Confluence transfers to $\lambda_{\mathrm{FREnv}}$ along the translation
   $[\![M \circ N]\!] = \varepsilon([\![M]\!])\,[\![N]\!]$, which is surjective
   and simulates every step by zero or one steps. The converse is the lifting
   lemma: a step out of a translated term need not be the image of a step,
   because the translation collapses $M \circ N$ and $\varepsilon(M)\,N$, but it
   always has a preimage sharing a reduct with the original term.

## Design notes

Mizar has no inductive datatypes and no inductive predicates. Terms are built
as parse trees over a symbol alphabet using `DTCONSTR` — the term set `TS(G)`,
its induction scheme `sch 7`, its recursion scheme `sch 8` and its uniqueness
scheme `sch 9`. Symbols are pairs, tagged by their first component:

| Symbol | Meaning | Arity |
|---|---|---|
| `[0,v]` | variable $v$ | terminal |
| `[1,0]` | `id` | terminal |
| `[2,v]` | $\lambda v.\,{-}$ | 1 |
| `[3,0]` | application | 2 |
| `[4,v]` | $({-}/v)\cdot{-}$ | 2 |
| `[5,0]` | $\varepsilon({-})$ | 1 |
| `[6,0]` | composition $\circ$ | 2 |

$\lambda_{\mathrm{FREnv}}$ uses the same alphabet without `[6,0]`. Indexing the
binder symbols by the variable keeps the name inside the node rather than as a
child subterm, so the encoding contains no junk terms. As in the Isabelle and
Lean developments, $\lambda$ is not a binder at the syntax level: names are
first-order data and no $\alpha$-equivalence quotient is used.

Every reduction relation is defined as the least relation closed under its
rules, which gives rule induction for free from the minimality clause. Rule
induction alone does not give inversion; that is obtained by showing that the
set of pairs matching one of the rule shapes, intersected with the reduction
itself, is closed under the rules, and then appealing to minimality.

## Differences from the other two developments

Like the Isabelle development and unlike the Lean one, neither calculus here
has constants; the constant rule $\varepsilon(c)\,M \to c$ behaves exactly like
$\varepsilon(\varepsilon(M))\,N \to \varepsilon(M)$ and plays no role in the
argument. Variables are an arbitrary non-empty set `V` passed as a parameter,
as in Lean, rather than the fixed `string` of the Isabelle development. There
is no counterpart here of the Isabelle `FREnv/` session, which develops local
confluence of $\lambda_{\mathrm{FREnv}}$ directly in addition to the transfer
along the translation.

As with the other two developments, this artifact does not claim a proved
equivalence between the three encodings.

## Documents

| File | Language | Content |
|---|---|---|
| [docs/verification.md](docs/verification.md) | English | how to verify, what the output means, how to inspect individual results |
| [docs/inventory.md](docs/inventory.md) | Japanese | file inventory with line and character counts, and a size comparison of the three developments |
| [docs/timeline.md](docs/timeline.md) | Japanese | how long each stage of the formalization took |
| [docs/worklog.md](docs/worklog.md) | Japanese | the work record kept during the formalization |
