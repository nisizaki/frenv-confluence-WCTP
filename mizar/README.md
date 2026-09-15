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

The script verifies the fifteen articles (19,409 lines, 369 theorems) in
dependency order and exports each
to a local `prel/` database so that the next one can import it, then checks
`text/audit.miz`, which restates each main result and justifies it by its
citation alone. On success it prints one `ok` per article and ends with

```text
All 15 articles verified with no errors, and the audit article
re-derives each main result from its citation alone.
Main theorem: FRENV_5:8  (FrRed(V) is confluent)
```

It exits non-zero and prints the error file if any article fails. A full run
takes about one and a half minutes on a laptop.

`./verify.sh clean` removes everything Mizar generated, leaving only the
sources.

To re-check a single article after the ones it depends on have been exported:

```sh
./check.sh envkey
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
| $\to_\sigma$ terminates | `ENVSIG:51` |
| $\to_\sigma$ is locally confluent | `ENVPEAK:11` |
| $\to_\sigma$ is confluent | `ENVPEAK:12` |
| $\to_\beta$ is confluent | `ENVPAR:34` |
| parallel reduction commutes with sigma normalization | `ENVKEY:30` |
| $\to_{\beta\sigma}$ of $\lambda_{\mathrm{Env}\varepsilon}$ is confluent | `ENVCONF:13` |
| **$\to_{\beta\sigma}$ of $\lambda_{\mathrm{FREnv}}$ is confluent** | `FRENV_5:8` |

## Layout

```text
text/          the fifteen Mizar articles (.miz), plus audit.miz
dict/          private vocabularies for the symbols introduced here (.voc)
verify.sh      verify everything in dependency order; `clean` removes output
check.sh       verify one article and show its error file
docs/          verification instructions and the records of the work
prel/          local library, created by verify.sh (not tracked)
```

| Article | Lines | Theorems | Content |
|---|---:|---:|---|
| `envsyn` | 1258 | 26 | syntax as parse trees, the seven constructors, structural induction and structural recursion schemes, relations on terms, the infix notation |
| `envlen` | 388 | 15 | the length measure, defined by the recursion scheme |
| `envcc` | 1709 | 30 | the compatible closure `CC Q` of a relation on terms, with its congruence rules, inversion, inversion by head constructor, monotonicity, `CC (Q1 \/ Q2) = CC Q1 \/ CC Q2` and multi-step congruence |
| `envsig` | 2631 | 56 | the eight $\sigma$ root rules; $\to_\sigma$ as their compatible closure; the sixteen named rules, inversion, length decrease, termination |
| `envbeta` | 1942 | 61 | the three $\beta$ root rules; $\to_\beta$ and $\to_{\beta\sigma}$ as compatible closures; the nineteen named rules, inversion, multi-step congruence |
| `envpeak` | 2225 | 12 | the eight root peaks, the composition peak, local confluence, confluence of $\sigma$ |
| `envnf` | 636 | 19 | $\sigma$ normal forms, their grammar, `snf` and its computation laws |
| `envpar` | 2678 | 34 | parallel reduction, the triangle property, the diamond property, confluence of $\beta$ |
| `envkey` | 1461 | 30 | composition compatibility and the key lemma |
| `envconf` | 421 | 13 | Hardin's interpretation method; confluence of $\beta\sigma$ |
| `frenv_1` | 818 | 17 | syntax of $\lambda_{\mathrm{FREnv}}$ |
| `frenv_2` | 1099 | 25 | $\beta\sigma$ reduction of $\lambda_{\mathrm{FREnv}}$ |
| `frenv_3` | 800 | 20 | the translation, its recursion equations, surjectivity and inversion |
| `frenv_4` | 463 | 3 | simulation |
| `frenv_5` | 880 | 8 | single-step and multi-step lifting, confluence |
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

Mizar has no inductive datatypes and no inductive predicates. Two pieces of
infrastructure carry that weight, and both are proved once and reused.

**Structural recursion.** Terms are parse trees over a symbol alphabet, built
with `DTCONSTR`. Its recursion scheme hands a definition the *values* at the
children together with the node's symbol, so a recursive definition written
directly against it has to project values out of a sequence and dispatch on a
tag with a cascade of `IFEQ`s. `ENVSYN:sch 2` does that once, and a recursive
definition is then seven equations, one per constructor.

**The compatible closure.** A reduction relation is the least relation
containing its root rules and closed under the eight congruence rules. `envcc`
defines that closure `CC Q` for an arbitrary `Q` and proves there — once — the
congruence rules, inversion, inversion by each head constructor, the multi-step
congruence lemmas, monotonicity, and that closing a union is the union of the
closures. Each calculus then only names its own root rules:

```text
  func SigmaRed(V)     -> EnvEpsRel of V equals CC SigmaRoot(V);
  func BetaRed(V)      -> EnvEpsRel of V equals CC BetaRoot(V);
  func BetaSigmaRed(V) -> EnvEpsRel of V equals CC BetaSigmaRoot(V);
```

and `BetaSigmaRed(V) = BetaRed(V) \/ SigmaRed(V)` is a theorem (`ENVBETA:32`),
not a definition: it follows from `CC (Q1 \/ Q2) = CC Q1 \/ CC Q2`.

Composition and application are written infix, `M (o) N` and `M (@) N`, so the
deeply nested terms of the sigma rules read the way the paper writes them:

```text
  ( ex A,B,C being EnvEpsTerm of V st
      P = (A (o) B) (o) C & S = A (o) (B (o) C) ) or
```

Reductions themselves are written as membership in a relation,
`[M,N] in SigmaRed(V)`. An infix arrow for them was tried and dropped: a
defined predicate does not unfold inside the large disjunctions of the
inversion lemmas, nor against the normal-form and convergence definitions of
`REWRITE1`, so it would have forced an explicit bridging step at every
interface with the MML.

Symbols are pairs, tagged by their first component:


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
itself, is closed under the rules, and then appealing to minimality. For the
three reductions of $\lambda_{\mathrm{Env}\varepsilon}$ that argument is made
once in `envcc`, for an arbitrary root relation; `frenv_2` repeats it for
`FrRed(V)`, whose terms live in a different parse-tree algebra.

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
