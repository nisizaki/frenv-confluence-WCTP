# Syntax of $\lambda_{\mathrm{FREnv}}$

This document describes the syntax of the untyped lambda calculus with
functionally referable environments, denoted $\lambda_{\mathrm{FREnv}}$.

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

> **Note.**  $\lambda_{\mathrm{FREnv}}$ has **no** set of constants
> $\mathbf{Const}$; there is no constant-valued term former.

---

## 2  Abstract Syntax (Definition — Terms of $\lambda_{\mathrm{FREnv}}$)

The set of terms $\mathbf{Term}$ is the least set satisfying the following
grammar.

$$
M, N, L \;::=\;
    x
  \;\mid\; \lambda x.\, M
  \;\mid\; M\,N
  \;\mid\; \mathsf{id}
  \;\mid\; (M/x) \cdot N
  \;\mid\; \varepsilon(M)
$$

### 2.1  Constructor Table

Each grammar alternative corresponds to exactly one constructor.

| Constructor | Written | Arity | Description |
| --- | --- | --- | --- |
| `Var x` | $x$ | 1 | Variable |
| `Lam x M` | $\lambda x.\,M$ | 2 (name, term) | Lambda abstraction |
| `App M N` | $M\,N$ | 2 | Application |
| `Id` | $\mathsf{id}$ | 0 | Identity environment |
| `Ext M x N` | $(M/x)\cdot N$ | 3 (term, name, term) | Environment extension |
| `Eps M` | $\varepsilon(M)$ | 1 | Environment abstraction |

### 2.2  Suggested Isabelle/HOL Datatype

```isabelle
datatype term
  = Var   name          (* variable x *)
  | Lam   name term     (* λx. M      *)
  | App   term term     (* M N        *)
  | Id                  (* id         *)
  | Ext   term name term (* (M/x)·N  *)
  | Eps   term          (* ε(M)       *)
```

> **Naming convention.**  The constructor `Ext M x N` stores the bound-name
> `x` in the *middle* position so that the three arguments read left-to-right
> as "the value `M`, the slot name `x`, the base environment `N`."

---

## 3  $\lambda$ Is Not a Binder in This Calculus

> **Important -- do not apply ordinary lambda-calculus binding theory here.**
> In $\lambda_{\mathrm{FREnv}}$, $\lambda x.\,M$ does **not** bind
> occurrences of $x$ in $M$ the way it does in the ordinary lambda calculus.
> The variable $x$ in `Lam x M` is, like the $x$ in `Ext M x N`, merely a
> *name tag* attached to the constructor -- a piece of first-order data, not
> a meta-level binder.
>
> Consequently, this document does **not** define free variables, bound
> variables, or $\alpha$-equivalence for $\mathbf{Term}$. Name resolution
> (i.e., which occurrence of a variable a given name refers to) is handled
> entirely at the level of the *reduction rules* -- through explicit
> environments (`Ext`/`Id`) and the `VarRef`/`VarSkip`-style substitution
> rules -- not through a capture-avoiding substitution operation defined on
> the raw syntax.
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

- Application (`App`) is **left-associative**: $M\,N\,L = (M\,N)\,L$.
- Lambda abstraction is **right-associative** and has the **lowest**
  precedence: $\lambda x.\,M\,N = \lambda x.\,(M\,N)$.
- The parentheses in $(M/x)$ are mandatory notation, not a precedence rule.

---

## 5  Informal Meaning of Each Constructor

**`Var x`.**  A variable drawn from $\mathbf{Var}$.

**`Lam x M`.**  A function with formal parameter $x$ and body $M$.

**`App M N`.**  Application of $M$ to argument $N$.

**`Id`.**  The identity environment — the environment that adds no new
binding.

**`Ext M x N`.**  The environment obtained by extending $N$ with a binding
that maps variable $x$ to term $M$.  Multiple extensions nest to the right:
$((M_1/x_1)\cdot((M_2/x_2)\cdot \mathsf{id}))$ is an environment that maps
$x_1$ to $M_1$ and $x_2$ to $M_2$.

**`Eps M`.**  An environment-abstraction term.  When `Eps M` is applied to
an environment $N$ via `App (Eps M) N`, the result is intuitively "evaluate
$M$ under $N$."  More precisely, `App (Eps M) N` reduces to `Comp M N` in
$\lambda_{\mathrm{Env}\varepsilon}$; in $\lambda_{\mathrm{FREnv}}$ the
$\sigma$-rules directly decompose such applications.

---

## 6  Relationship to $\lambda_{\mathrm{Env}\varepsilon}$

$\lambda_{\mathrm{FREnv}}$ and $\lambda_{\mathrm{Env}\varepsilon}$ share
all six of their constructors except one.  The difference is:

| $\lambda_{\mathrm{FREnv}}$ | $\lambda_{\mathrm{Env}\varepsilon}$ |
| --- | --- |
| No `Comp` constructor | Has `Comp M N` ($M \circ N$) as a primitive |

In $\lambda_{\mathrm{FREnv}}$, the composition $M \circ N$ is *not* a
syntactic primitive.  Instead, the $\sigma$-rules reduce `App (Eps M) N`
directly, treating every `App`-`Eps` redex as a substitution step.

In $\lambda_{\mathrm{Env}\varepsilon}$, `App (Eps M) N` first reduces to
`Comp M N` via the $\mathrm{Comp}_\varepsilon$ rule, and subsequent
substitution rules decompose `Comp`.

> **Isabelle note.**  When formalizing both calculi, the `term` datatype for
> $\lambda_{\mathrm{FREnv}}$ has **six** constructors (as above); the
> datatype for $\lambda_{\mathrm{Env}\varepsilon}$ adds one more
> constructor, `Comp` (see `enve-syntax.md`).
