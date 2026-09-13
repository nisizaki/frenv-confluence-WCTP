# Multi-Step Lifting Lemma for the $\lambda_{\mathrm{Env}\varepsilon}$-to-$\lambda_{\mathrm{FREnv}}$ Translation

This document states and proves thesis Lemma 4 (§2.3.1): the Single-Step Lifting Lemma (`docs/enve-frenv-translation-lifting.md`, thesis Lemma 3) generalizes from a single $\lambda_{\mathrm{FREnv}}$-side step to an arbitrary finite sequence of them, **provided** $\lambda_{\mathrm{Env}\varepsilon}$'s own $\to_{\beta\sigma}$ is confluent. Confluence of $\lambda_{\mathrm{Env}\varepsilon}$ is not established anywhere in this repository yet, so it appears here exactly as the thesis uses it: as an explicit hypothesis of the lemma, not as a fact this document proves or assumes silently.

> **Note for AI-assisted formalization.**
> This lemma needs confluence of $\lambda_{\mathrm{Env}\varepsilon}$'s
> $\to_{\beta\sigma}$, **not** of $\lambda_{\mathrm{FREnv}}$'s. It is
> therefore unrelated to `docs/frenv-beta-sigma-local-confluence.md` (which
> is about $\lambda_{\mathrm{FREnv}}$, and which the Single-Step Lifting
> Lemma turned out not to need either). Do not substitute one calculus's
> confluence for the other's when using this lemma.

---

## Lemma (Multi-Step Lifting Lemma)

Let $M$ be a term of $\lambda_{\mathrm{Env}\varepsilon}$ and $N'$ a term of $\lambda_{\mathrm{FREnv}}$. **Assume $\lambda_{\mathrm{Env}\varepsilon}$'s $\to_{\beta\sigma}$ is confluent**, i.e.: for all $\lambda_{\mathrm{Env}\varepsilon}$ terms $P, Q_1, Q_2$, if $P \to_{\beta\sigma}^{*} Q_1$ and $P \to_{\beta\sigma}^{*} Q_2$, then there exists $\lambda_{\mathrm{Env}\varepsilon}$ term $R$ with $Q_1 \to_{\beta\sigma}^{*} R$ and $Q_2 \to_{\beta\sigma}^{*} R$.

Then: if $⟦M⟧ \to_{\beta\sigma}^{*} N'$, there exist $\lambda_{\mathrm{Env}\varepsilon}$ terms $N, L$ such that
$$
⟦N⟧ = N',
\qquad
N \to_{\beta\sigma}^{*} L,
\qquad
M \to_{\beta\sigma}^{*} L.
$$

Informally: this extends the Single-Step Lifting Lemma from one $\lambda_{\mathrm{FREnv}}$-side step to a whole chain of them, at the cost of needing confluence on the $\lambda_{\mathrm{Env}\varepsilon}$ side to keep reconciling each new step against everything found so far.

#### Proof.

Write $⟦M⟧ \to_{\beta\sigma}^{*} N'$ as $⟦M⟧ \to_{\beta\sigma}^{n} N'$ for some $n \geq 0$ (a chain of exactly $n$ single steps), and induct on $n$.

**Base case ($n = 0$).** Then $N' = ⟦M⟧$. Set $N := M$ and $L := M$. Then $⟦N⟧ = ⟦M⟧ = N'$, $N \to_{\beta\sigma}^{*} L$ holds in zero steps ($N = L$), and $M \to_{\beta\sigma}^{*} L$ holds in zero steps ($M = L$).

**Inductive case ($n > 0$).** Write the chain as $⟦M⟧ \to_{\beta\sigma} N_1' \to_{\beta\sigma}^{n-1} N'$ for some $\lambda_{\mathrm{FREnv}}$ term $N_1'$.

From $⟦M⟧ \to_{\beta\sigma} N_1'$, the Single-Step Lifting Lemma (thesis Lemma 3) gives $\lambda_{\mathrm{Env}\varepsilon}$ terms $N_1, L_1$ such that
$$
⟦N_1⟧ = N_1', \qquad N_1 \to_{\beta\sigma}^{*} L_1, \qquad M \to_{\beta\sigma}^{*} L_1.
$$

From $⟦N_1⟧ = N_1' \to_{\beta\sigma}^{n-1} N'$, the induction hypothesis (applied to $N_1$ in place of $M$, with the shorter chain of length $n - 1$) gives $\lambda_{\mathrm{Env}\varepsilon}$ terms $N_2, L_2$ such that
$$
⟦N_2⟧ = N', \qquad N_2 \to_{\beta\sigma}^{*} L_2, \qquad N_1 \to_{\beta\sigma}^{*} L_2.
$$

We now have two reductions out of the same $\lambda_{\mathrm{Env}\varepsilon}$ term $N_1$: $N_1 \to_{\beta\sigma}^{*} L_1$ (from the Lifting Lemma step above) and $N_1 \to_{\beta\sigma}^{*} L_2$ (from the induction hypothesis). By the assumed confluence of $\lambda_{\mathrm{Env}\varepsilon}$'s $\to_{\beta\sigma}$, there exists a $\lambda_{\mathrm{Env}\varepsilon}$ term $L_3$ such that
$$
L_1 \to_{\beta\sigma}^{*} L_3, \qquad L_2 \to_{\beta\sigma}^{*} L_3.
$$

Chaining these together:
$$
M \to_{\beta\sigma}^{*} L_1 \to_{\beta\sigma}^{*} L_3,
\qquad
N_2 \to_{\beta\sigma}^{*} L_2 \to_{\beta\sigma}^{*} L_3.
$$

Setting $N := N_2$ and $L := L_3$ gives $⟦N⟧ = N'$, $N \to_{\beta\sigma}^{*} L$, and $M \to_{\beta\sigma}^{*} L$, as required.

#### End of Proof.

---

## Remarks and Adjustments Made to the Source Material

- **Confluence hypothesis kept exactly as stated, not discharged.** The thesis states this lemma conditionally ("in the case that $\lambda_{\mathrm{Env}\varepsilon}$ satisfies confluence"), and this document preserves that framing rather than trying to prove or assume confluence of $\lambda_{\mathrm{Env}\varepsilon}$ outright. Establishing that confluence (if it holds -- $\lambda_{\mathrm{Env}\varepsilon}$'s reduction relation includes the same kind of non-terminating computation as $\lambda_{\mathrm{FREnv}}$'s, so it is not automatic) is separate, not-yet-written-up work.
- **Distinguished from the $\lambda_{\mathrm{FREnv}}$ local confluence document.** `docs/frenv-beta-sigma-local-confluence.md` proves *local* confluence of a *different* calculus's ($\lambda_{\mathrm{FREnv}}$'s) reduction, and the Single-Step Lifting Lemma (thesis Lemma 3) that this lemma builds on turned out not to need it at all. This lemma's hypothesis is full confluence of $\lambda_{\mathrm{Env}\varepsilon}$, an unrelated fact; the two should not be conflated.
- **No constants involved.** As with every other reduction document in this repository, this lemma does not involve `Const` or any constant symbols, since neither $\lambda_{\mathrm{FREnv}}$ nor $\lambda_{\mathrm{Env}\varepsilon}$ has any (`docs/frenv-syntax.md`, `docs/enve-syntax.md`).
