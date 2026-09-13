# $\sigma$-Normal Form on $\lambda_{\mathrm{Env}\varepsilon}$

This document records thesis Definition 12 (§2.4.3): the $\sigma$-normal form of a $\lambda_{\mathrm{Env}\varepsilon}$ term, and what it means for a term to *be* a $\sigma$-normal form.

> **Prerequisite.** This definition is only meaningful because $\to_{\sigma}$
> on $\lambda_{\mathrm{Env}\varepsilon}$ is **terminating**
> (`docs/enve-sigma-reduction-termination.md`, thesis Theorem 4) and
> **locally confluent** (`docs/enve-sigma-reduction-local-confluence.md`,
> thesis Lemma 5) -- equivalently, by Newman's Lemma, **confluent**
> (`docs/enve-sigma-reduction-confluence.md`, thesis Theorem 5). Termination
> guarantees that every term reaches *at least one* $\sigma$-irreducible
> term; confluence (built from local confluence plus termination)
> guarantees that this irreducible term is the *same one* no matter which
> sequence of $\sigma$-steps is taken to reach it. Without both facts, "the"
> $\sigma$-normal form of a term would not be well defined -- see the
> Well-Definedness section below.

> **Note for AI-assisted formalization.**
> $\sigma(M)$ is not defined here by a recursive formula on the structure
> of $M$; it is defined *indirectly*, as "the" term reached by reducing $M$
> with $\to_{\sigma}$ until no further $\sigma$-step applies. Formalizing
> it directly as a total function requires first formalizing termination
> and confluence of $\to_{\sigma}$ (both cited above) and then either (a)
> extracting the normal form from a terminating reduction strategy, or (b)
> defining it via Hilbert's choice operator / `SOME` over "the unique $N$
> with $M \to_{\sigma}^{*} N$ and $N$ $\sigma$-irreducible", relying on the
> uniqueness this document establishes.

---

#### Definition (σ-Normal Form)

Say a $\lambda_{\mathrm{Env}\varepsilon}$ term $N$ is **$\sigma$-irreducible** if there is no $\lambda_{\mathrm{Env}\varepsilon}$ term $N_1$ with $N \to_{\sigma} N_1$.

For a $\lambda_{\mathrm{Env}\varepsilon}$ term $M$, its **$\sigma$-normal form**, written $\sigma(M)$, is the unique $\sigma$-irreducible term $N$ such that $M \to_{\sigma}^{*} N$.

For $\lambda_{\mathrm{Env}\varepsilon}$ terms $N, L$: $N$ **is a $\sigma$-normal form** if $N = \sigma(L)$ for some $L$ -- equivalently (see below), if $N$ is itself $\sigma$-irreducible.

### Well-Definedness

For $\sigma(M)$ to denote a single, unambiguous term, both existence and uniqueness of the $\sigma$-irreducible $N$ with $M \to_{\sigma}^{*} N$ must hold.

- **Existence.** By termination of $\to_{\sigma}$ (thesis Theorem 4), there is no infinite reduction sequence $M \to_{\sigma} M_1 \to_{\sigma} M_2 \to_{\sigma} \cdots$ starting from $M$. So any sequence of $\sigma$-steps out of $M$ must stop after finitely many steps, at some term $N$ with $M \to_{\sigma}^{*} N$ where no further step applies -- i.e. $N$ is $\sigma$-irreducible. At least one such $N$ therefore always exists.
- **Uniqueness.** Suppose $M \to_{\sigma}^{*} N$ and $M \to_{\sigma}^{*} N'$ with both $N$ and $N'$ $\sigma$-irreducible. By confluence of $\to_{\sigma}$ (`docs/enve-sigma-reduction-confluence.md`, thesis Theorem 5 -- itself obtained from termination and local confluence via Newman's Lemma), there is $L$ with $N \to_{\sigma}^{*} L$ and $N' \to_{\sigma}^{*} L$. But $N$ is $\sigma$-irreducible, so the only way $N \to_{\sigma}^{*} L$ can hold is with zero steps, i.e. $N = L$; likewise $N' = L$. Hence $N = L = N'$: any two $\sigma$-irreducible terms reachable from $M$ coincide.

Together, existence and uniqueness mean $\sigma(M)$ names exactly one term, for every $M$.

### Equivalent characterization of "being a $\sigma$-normal form"

$N$ is a $\sigma$-normal form (i.e. $N = \sigma(L)$ for some $L$) if and only if $N$ is $\sigma$-irreducible. One direction is immediate: $\sigma(L)$ is, by definition, $\sigma$-irreducible, for any $L$. Conversely, if $N$ itself is $\sigma$-irreducible, then $N \to_{\sigma}^{*} N$ trivially (zero steps), so $N$ is *the* $\sigma$-irreducible term reachable from $N$, i.e. $N = \sigma(N)$ -- taking $L := N$ shows $N$ is a $\sigma$-normal form.

---

## Remarks and Adjustments Made to the Source Material

- **Prerequisites made explicit.** The thesis states this definition immediately after citing "Theorem 4, 5" (termination and confluence) in the section header, without re-deriving why they are needed. This document adds the "Well-Definedness" section spelling out exactly how termination gives existence and confluence gives uniqueness of $\sigma(M)$, since without both, $\sigma(M)$ would not denote a single well-defined term. As requested, the more fundamental prerequisites -- termination and *local* confluence of $\to_{\sigma}$ -- are named up front, with full confluence noted as the consequence of those two (via Newman's Lemma, `docs/enve-sigma-reduction-confluence.md`) that is used directly in the uniqueness argument.
- **Added the irreducibility characterization.** The thesis's second sentence ("$N$ is a $\sigma$-normal form if $N = \sigma(L)$ for some $L$") is restated with an explicit equivalent characterization ("if and only if $N$ is $\sigma$-irreducible"), since that is the more directly checkable condition and is the one used, e.g., when reasoning about the shape of the $\sigma$-irreducible terms of $\lambda_{\mathrm{Env}\varepsilon}$'s grammar.
- **No constants involved.** As with every other reduction document in this repository, this definition does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{Env}\varepsilon}$ has none (`docs/enve-syntax.md`).
