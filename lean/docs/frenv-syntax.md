# Syntax of $\lambda_{\mathrm{FREnv}}$

This document describes the syntax of the untyped lambda calculus with functionally referable environments, denoted by $\lambda_{\mathrm{FREnv}}$.

The calculus extends the ordinary untyped lambda calculus with syntactic forms for environments and for referring to environments as first-class objects.

## Preliminary Sets

We assume the following two sets.

* $\mathbf{Var}$: a set of variables
* $\mathbf{Const}$: a set of constants

Variables are ranged over by $x$, $y$, and $z$.
Constants are ranged over by $c$.
Terms are ranged over by $L$, $M$, and $N$.

#### Definition (Terms of $\lambda_{\mathrm{FREnv}}$)

The set of terms of $\lambda_{\mathrm{FREnv}}$, written $\mathbf{Term}$, is defined by the following grammar.

$$
M, N, L ::= c
       \mid x
       \mid \lambda x. M
       \mid M\,N
       \mid \mathsf{id}
       \mid (M/x) \cdot N
       \mid \varepsilon(M)
$$

The intended meanings of these syntactic forms are as follows.

| Form | Name | Informal meaning |
| --- | --- | --- |
| $c$ | constant | A constant value |
| $x$ | variable | A variable |
| $\lambda x. M$ | lambda abstraction | A function whose formal parameter is $x$ and whose body is $M$ |
| $M\,N$ | application | Application of $M$ to $N$ |
| $\mathsf{id}$ | identity environment | The identity environment |
| $(M/x) \cdot N$ | environment extension | The environment obtained by extending $N$ with a binding of $x$ to $M$ |
| $\varepsilon(M)$ | environment abstraction | A term that refers functionally to an environment when applied to one |

In the environment extension $(M/x)\cdot N$, the occurrence of $x$ is not a binding occurrence; in particular, it does not bind any occurrences of $x$ in either $M$ or $N$.

## Informal Explanation

The ordinary lambda-calculus constructs are constants, variables, lambda abstraction, and application.

The additional constructs are $\mathsf{id}$, $(M/x) \cdot N$, and $\varepsilon(M)$.

The term $\mathsf{id}$ denotes the identity environment. It represents the environment that does not add any new binding.

The term $(M/x) \cdot N$ represents an environment extension. It is read as the environment $N$ extended by a binding that maps the variable $x$ to the term $M$.

The term $\varepsilon(M)$ represents a functional reference to the term $M$ under an environment. Intuitively, when $\varepsilon(M)$ is applied to an environment, the term $M$ is evaluated or interpreted relative to that environment.

Thus, an expression of the form

$$
\varepsilon(M)\,N
$$

may be read informally as "evaluate $M$ under the environment $N$."

## Binding and Parsing Conventions

The lambda abstraction $\lambda x. M$ binds the variable $x$ in $M$.

The environment extension $(M/x) \cdot N$ should be read as extending the environment $N$ by a binding for $x$. In this notation, $M$ is the term associated with $x$, and $N$ is the underlying environment.

Application is written by juxtaposition. As usual, application associates to the left. Thus,

$$
M\,N\,L
$$

is read as

$$
(M\,N)\,L.
$$

The expression $(M/x) \cdot N$ is written with parentheses around $M/x$ to avoid ambiguity.

## Design Intuition

The calculus is intended to express environments as first-class syntactic objects.

In a more traditional explicit-environment calculus, one may use a separate operator for composing or applying environments. In $\lambda_{\mathrm{FREnv}}$, the construct $\varepsilon(M)$ allows an environment to be supplied by ordinary application. Therefore, application remains the single binary connective used for applying both functions and environment-referential terms.

For example, the expression

$$
\varepsilon(M)\,((N/x) \cdot \mathsf{id})
$$

can be read as evaluating $M$ under the environment obtained by extending the identity environment with a binding of $x$ to $N$.

This notation makes environments explicit while keeping the basic term formation rules close to those of the ordinary lambda calculus.

### Relationship between $\lambda_{\textrm{env}}$ and $\lambda_{\textrm{FREnv}}$

In $\lambda_{\textrm{env}}$, $M \circ N$ means an evaluation of $M$ under an environment $N$. This is represented as $\varepsilon(M) N$ in $\lambda_{\textrm{FREnv}}$.