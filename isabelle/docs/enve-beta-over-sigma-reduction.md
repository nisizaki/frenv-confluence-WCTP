# $\beta/\sigma$-Reduction on $\sigma$-Normal Forms of $\lambda_{\mathrm{Env}\varepsilon}$

This document records thesis Definition 13 (§2.4.4): a reduction relation $\to_{\beta/\sigma}$, defined only on $\sigma$-normal forms of $\lambda_{\mathrm{Env}\varepsilon}$ (`docs/enve-sigma-normal-form.md`), that combines one $\beta$-step with re-normalizing by $\sigma$.

> **Note.** $\to_{\beta/\sigma}$ (with a slash) is a *different* relation from
> $\to_{\beta\sigma}$ (`docs/enve-reduction-beta-sigma.md`, no slash, defined
> on *all* of $\mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$). Do not
> confuse the two notations.

> **Note for AI-assisted formalization.**
> $\to_{\beta/\sigma}$ is defined only between $\sigma$-normal forms
> (`docs/enve-sigma-normal-form-grammar.md`): its domain and codomain are
> both the restricted grammar (2.32), not all of
> $\mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$. It is *not* itself
> defined by structural recursion on the term; it is defined indirectly, by
> quantifying over an intermediate term $M$ and reduction sequences of two
> other, already-defined relations ($\to_{\beta}$ and $\to_{\sigma}^{*}$).

---

## Preliminary: the relation $\to_{\beta}$

Definition 13 refers to a one-step relation $\to_{\beta}$, which is the fragment of $\to_{\beta\sigma}$ (`docs/enve-reduction-beta-sigma.md`) obtained by dropping the eight substitution ($\sigma$-)rules and keeping only:

- the three beta rules `Beta`, `BetaClos`, `Comp` ($\mathrm{Comp}_{\varepsilon}$), and
- all eight congruence rules (`Lam`, `Eop`, `AppL`, `AppR`, `ExtnL`, `ExtnR`, `CompL`, `CompR`), so that a $\beta$-step may occur at any position inside a term, not only at the root.

So $\to_{\beta}$ and $\to_{\sigma}$ (`docs/enve-reduction-sigma.md`) are the two complementary "halves" of $\to_{\beta\sigma}$ that together make up all of its rules: $\to_{\beta\sigma} \;=\; \to_{\beta} \,\cup\, \to_{\sigma}$.

---

#### Definition ($\beta/\sigma$-Reduction)

Let $U$ be a $\sigma$-normal form of $\lambda_{\mathrm{Env}\varepsilon}$. Say $U$ is **$\beta/\sigma$-reduced to** $V$, written $U \to_{\beta/\sigma} V$, if there exist $\lambda_{\mathrm{Env}\varepsilon}$ terms $M, V$ such that:

$$
U \to_{\beta} M,
\qquad
M \to_{\sigma}^{*} V,
\qquad
V \text{ is a } \sigma\text{-normal form.}
$$

That is: $U \to_{\beta/\sigma} V$ exactly when $V$ can be reached from $U$ by taking a single $\to_{\beta}$-step to some $M$, and then reducing $M$ down to a $\sigma$-normal form $V$ by zero or more $\to_{\sigma}$-steps.

### Why $V$ is uniquely determined once $M$ is fixed

Although Definition 13 phrases $V$ as merely "some" $\sigma$-normal form with $M \to_{\sigma}^{*} V$, this $V$ is in fact uniquely determined by $M$: by termination of $\to_{\sigma}$ (`docs/enve-sigma-reduction-termination.md`, thesis Theorem 4) and confluence of $\to_{\sigma}$ (`docs/enve-sigma-reduction-confluence.md`, thesis Theorem 5), every term has exactly one $\sigma$-normal form, namely $\sigma(M)$ (`docs/enve-sigma-normal-form.md`, thesis Definition 12). So the definition above is equivalent to the more direct statement
$$
U \to_{\beta/\sigma} V
\quad\Longleftrightarrow\quad
\exists M.\; U \to_{\beta} M \text{ and } V = \sigma(M).
$$

What is genuinely **not** unique is $M$ itself: $U$ may contain more than one $\to_{\beta}$-redex (at different positions, or of different rules), and different choices of $M$ can lead to different $\sigma$-normal forms $V$. So $\to_{\beta/\sigma}$ is, in general, a one-to-many relation on $\sigma$-normal forms (like $\to_{\beta}$ itself), not a function -- exactly as its notation as a reduction relation, rather than a defined operation, suggests.

---

## Remarks and Adjustments Made to the Source Material

- **$\to_{\beta}$ made explicit.** The thesis uses $\to_{\beta}$ in this definition without restating what it is; this document adds the "Preliminary" section identifying it precisely as the beta-rules-plus-congruence-rules fragment of $\to_{\beta\sigma}$ (`docs/enve-reduction-beta-sigma.md`), i.e. the complement of $\to_{\sigma}$ within $\to_{\beta\sigma}$.
- **Uniqueness of $V$ noted.** The source states the existence of *some* $\sigma$-normal form $V$ with $M \to_{\sigma}^{*} V$; this document adds the observation (using Theorems 4 and 5, and Definition 12, all already in this repository) that this $V$ is in fact the unique $\sigma$-normal form of $M$, i.e. $V = \sigma(M)$, while flagging that the overall relation $\to_{\beta/\sigma}$ is still not a function of $U$ alone, since $M$ ranges over all possible single $\to_{\beta}$-reducts of $U$.
- **Notation kept distinct from $\to_{\beta\sigma}$.** Per the request, this relation is written $\to_{\beta/\sigma}$ (with a slash) throughout, to avoid confusion with the pre-existing $\to_{\beta\sigma}$ (no slash) of `docs/enve-reduction-beta-sigma.md`, which is a different relation (defined on *all* terms, not just $\sigma$-normal forms).
- **No constants involved.** As with every other reduction document in this repository, this definition does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{Env}\varepsilon}$ has none (`docs/enve-syntax.md`).
