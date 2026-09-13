# Syntax of $\lambda_{\mathrm{Env}\varepsilon}$

This document describes the syntax of the untyped lambda calculus with
environments and environment abstraction, denoted $\lambda_{\mathrm{Env}\varepsilon}$.

> **Note for AI-assisted formalization.**
> This document is written to support formalization in Isabelle/HOL (or a
> similar proof assistant).  Each section makes the intended Isabelle encoding
> explicit so that a language model can generate correct definitions without
> guessing.

---

## 1  Preliminary Sets

| Set | Notation | Ranged over by |
| --- | --- | --- |
| Variables | $\mathbf{Var}$ | $x, y, z$ |
| Terms | $\mathbf{Term}$ | $M, N, L$ |

In Isabelle/HOL, $\mathbf{Var}$ is typically modelled as `string` or as an
abstract type `name`.

> **Note.**  Neither $\lambda_{\mathrm{Env}\varepsilon}$ nor
> $\lambda_{\mathrm{FREnv}}$ has a set of constants; there is no
> constant-valued term former in either calculus.

---

## 2  Abstract Syntax (Definition 4 — Terms of $\lambda_{\mathrm{Env}\varepsilon}$)

The set of terms $\mathbf{Term}$ is the least set satisfying the following
grammar (equation (2.9) of the thesis).

$$
M, N, L \;::=\;
    x
  \;\mid\; \mathsf{id}
  \;\mid\; M_1\,M_2
  \;\mid\; (M_1/x) \cdot M_2
  \;\mid\; \lambda x.\, M_1
  \;\mid\; M_1 \circ M_2
  \;\mid\; \varepsilon(M_1)
$$

### 2.1  Constructor Table

Each grammar alternative corresponds to exactly one constructor.

| Constructor | Written | Arity | Description |
| --- | --- | --- | --- |
| `Var x` | $x$ | 1 (name) | Variable |
| `Id` | $\mathsf{id}$ | 0 | Identity environment |
| `App M N` | $M_1\,M_2$ | 2 | Application |
| `Ext M x N` | $(M_1/x)\cdot M_2$ | 3 (term, name, term) | Environment extension |
| `Lam x M` | $\lambda x.\,M_1$ | 2 (name, term) | Lambda abstraction |
| `Comp M N` | $M_1 \circ M_2$ | 2 | Environment composition |
| `Eps M` | $\varepsilon(M_1)$ | 1 | Environment abstraction |

### 2.2  Suggested Isabelle/HOL Datatype

```isabelle
datatype term
  = Var  name          (* variable x        *)
  | Id                 (* id                *)
  | App  term term     (* M₁ M₂             *)
  | Ext  term name term (* (M₁/x)·M₂       *)
  | Lam  name term     (* λx. M₁            *)
  | Comp term term     (* M₁ ∘ M₂           *)
  | Eps  term          (* ε(M₁)             *)
```

> **Naming convention.**  The constructor `Ext M x N` stores the slot name
> `x` in the *middle* position so that the arguments read left-to-right as
> "the value `M`, the slot name `x`, the base environment `N`."

---

## 3  $\lambda$ Is Not a Binder in This Calculus

> **Important -- do not apply ordinary lambda-calculus binding theory here.**
> In $\lambda_{\mathrm{Env}\varepsilon}$, $\lambda x.\,M_1$ does **not**
> bind occurrences of $x$ in $M_1$ the way it does in the ordinary lambda
> calculus. The variable $x$ in `Lam x M` is, like the $x$ in `Ext M x N`,
> merely a *name tag* attached to the constructor -- a piece of first-order
> data, not a meta-level binder.
>
> Consequently, this document does **not** define free variables, bound
> variables, or $\alpha$-equivalence for $\mathbf{Term}$. Name resolution
> (i.e., which occurrence of a variable a given name refers to) is handled
> entirely at the level of the *reduction rules* -- through explicit
> environments (`Ext`/`Id`), environment composition (`Comp`), and the
> `VarRef`/`VarSkip`-style substitution rules -- not through a
> capture-avoiding substitution operation defined on the raw syntax.
>
> **Isabelle note.**  Because `Lam x M` carries no binding semantics at the
> syntax level, `x` can be formalized as a plain `name` field, exactly like
> the `x` in `Ext M x N`. Do **not** use a nominal/locally-nameless binder
> representation (e.g., Nominal2's binding types, or a de Bruijn index) for
> the `x` in `Lam`; a first-order `datatype` with plain `name` arguments,
> as given in §2.2, is the correct and sufficient representation. Any
> substitution semantics belongs in the definition of the reduction
> relation, not in the term datatype itself.

---

## 4  Parsing and Precedence Conventions

- Application (`App`) is **left-associative**: $M_1\,M_2\,M_3 = (M_1\,M_2)\,M_3$.
- Lambda abstraction is **right-associative** and has the **lowest**
  precedence among term-forming operations.
- Environment composition (`Comp`, written $\circ$) has **higher** precedence
  than application when appearing as a subterm, but the thesis treats it as a
  distinct syntactic category from plain application.
- The parentheses in $(M_1/x)$ are mandatory notation, not a precedence rule.

---

## 5  Informal Meaning of Each Constructor

**`Var x`.**  A variable drawn from $\mathbf{Var}$.

**`Id`.**  The identity environment — the environment that adds no new
binding.

**`App M N`.**  Application of $M$ to argument $N$.  When $M = \mathsf{Eps}\,M'$,
this application is a *composition redex*: `App (Eps M') N` reduces to
`Comp M' N` by the $\mathrm{Comp}_\varepsilon$ rule (see below).

**`Ext M x N`.**  The environment obtained by extending $N$ with a binding
that maps variable $x$ to term $M$.  Multiple extensions nest to the right:
$((M_1/x_1)\cdot((M_2/x_2)\cdot \mathsf{id}))$ maps $x_1$ to $M_1$ and
$x_2$ to $M_2$.

**`Lam x M`.**  A function with formal parameter $x$ and body $M$.

**`Comp M N`.**  Environment composition $M \circ N$.  Intuitively, applying
$M \circ N$ to a further environment $L$ first applies $N$ and then $M$, so
bindings in $M$ take precedence.  This constructor is the key difference from
$\lambda_{\mathrm{FREnv}}$, where composition is not a syntactic primitive.

**`Eps M`.**  An environment-abstraction term.  When `Eps M` is applied to an
environment $N$ via `App (Eps M) N`, the $\mathrm{Comp}_\varepsilon$ rule
reduces it to `Comp M N`:

$$
\varepsilon(M_1)\,M_2 \;\to\; M_1 \circ M_2 \qquad (\mathrm{Comp}_\varepsilon)
$$

Subsequent $\sigma$-rules then decompose `Comp M N` according to the
structure of $M$.

---

## 6  Reduction Rules Overview (for Formalization Context)

The reduction relation of $\lambda_{\mathrm{Env}\varepsilon}$ consists of
three groups of rules.  Each group acts on specific constructors, so knowing
the constructor at the head of a term determines which rules apply.

| Rule group | Head constructor of redex |
| --- | --- |
| Beta rule | `App (Lam x M) N` |
| $\mathrm{Comp}_\varepsilon$ rule | `App (Eps M) N` |
| Substitution ($\sigma$) rules | `Comp M N` (decompose by structure of $M$) |
| Congruence rules | any constructor (reduce a subterm) |

> **Isabelle note.**  When defining the one-step reduction relation, it is
> useful to pattern-match on the outermost constructor first to select the
> applicable rule group.

---

## 7  Relationship to $\lambda_{\mathrm{FREnv}}$

$\lambda_{\mathrm{Env}\varepsilon}$ and $\lambda_{\mathrm{FREnv}}$ share
all six constructors of $\lambda_{\mathrm{FREnv}}$: `Var`, `Id`, `App`,
`Ext`, `Lam`, `Eps`.  The difference is:

| $\lambda_{\mathrm{Env}\varepsilon}$ | $\lambda_{\mathrm{FREnv}}$ |
| --- | --- |
| Has `Comp M N` ($M \circ N$) as a primitive | No `Comp` constructor |

In $\lambda_{\mathrm{Env}\varepsilon}$, the composition `Comp M N` is a
first-class term.  The substitution ($\sigma$) rules decompose it by
case-splitting on the structure of $M$.

In $\lambda_{\mathrm{FREnv}}$, composition is not represented in the syntax.
Every application `App (Eps M) N` is treated directly as a substitution step
without introducing an intermediate `Comp` node.

> **Isabelle note.**  When formalizing both calculi, the `term` datatype for
> $\lambda_{\mathrm{Env}\varepsilon}$ has **seven** constructors (as above);
> the datatype for $\lambda_{\mathrm{FREnv}}$ simply omits `Comp`, leaving
> **six** constructors (see `frenv-syntax.md`).
