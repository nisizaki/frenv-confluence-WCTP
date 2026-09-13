# Confluence of $\lambda_{\mathrm{Env}\varepsilon}$

This document states and proves thesis Theorem 13 (§2.4.5): $\lambda_{\mathrm{Env}\varepsilon}$'s full reduction relation $\to_{\beta\sigma}$ (`docs/enve-reduction-beta-sigma.md`) is confluent -- on *all* terms, not just $\sigma$-normal forms. This is the calculus's headline confluence result, assembled from the $\sigma$-normal-form machinery built up over `docs/enve-sigma-normal-form.md` through `docs/enve-beta-over-sigma-confluence.md`.

> **Note on the cited proof.** The thesis states this theorem's proof as
> "follows from Theorem 7, Theorem 12, and Theorem 1." Theorem 7
> (`docs/enve-beta-normal-form-simulation.md`) and Theorem 12
> (`docs/enve-beta-over-sigma-confluence.md`) are already established in
> this repository. "Theorem 1" is an early, general abstract lemma from
> the thesis's preliminary chapter (§1.3.2, itself citing external
> rewriting-theory literature) that combines two component relations into
> a confluence statement about their union; its exact original wording
> could not be reliably recovered from the scanned source (the relevant
> page is badly garbled by an OCR/font-encoding issue affecting the
> Japanese text throughout this document set). Rather than guess at its
> precise statement, this document supplies a complete, self-contained
> proof of Theorem 13 directly from Theorem 7, Theorem 12, and the basic
> properties of $\sigma$-normal forms (Definition 12,
> `docs/enve-sigma-normal-form.md`) already on record -- reaching the same
> conclusion the thesis's citation of "Theorem 1" was presumably used to
> package.

---

## Theorem (Confluence of $\lambda_{\mathrm{Env}\varepsilon}$)

For all $M, N_1, N_2 \in \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$, if $M \to_{\beta\sigma}^{*} N_1$ and $M \to_{\beta\sigma}^{*} N_2$, then there exists $L \in \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$ such that $N_1 \to_{\beta\sigma}^{*} L$ and $N_2 \to_{\beta\sigma}^{*} L$.

#### Proof.

Recall that $\to_{\beta\sigma}$ is exactly $\to_{\beta} \cup \to_{\sigma}$ (`docs/enve-beta-over-sigma-reduction.md`), and that every $\sigma$-normal form map $\sigma(-)$ (Definition 12) satisfies $P \to_{\sigma}^{*} \sigma(P)$ for every term $P$.

**Fact (lifting $\to_{\beta\sigma}^{*}$ to $\to_{\beta/\sigma}^{*}$ on normal forms).** If $P \to_{\beta\sigma}^{*} Q$, then $\sigma(P) \to_{\beta/\sigma}^{*} \sigma(Q)$.

*Proof of the Fact.* By induction on the number of steps in $P \to_{\beta\sigma}^{*} Q$. Zero steps give $P = Q$, so $\sigma(P) = \sigma(Q)$, hence $\sigma(P) \to_{\beta/\sigma}^{*} \sigma(Q)$ trivially. For the inductive step, write the chain as $P \to_{\beta\sigma} P_1 \to_{\beta\sigma}^{*} Q$, and consider the first step:
- If $P \to_{\sigma} P_1$ (a $\sigma$-step), then $\sigma(P) = \sigma(P_1)$, since $\sigma$-reduction never changes a term's (unique) $\sigma$-normal form. So the induction hypothesis, applied to $P_1 \to_{\beta\sigma}^{*} Q$, already gives $\sigma(P_1) \to_{\beta/\sigma}^{*} \sigma(Q)$, i.e. $\sigma(P) \to_{\beta/\sigma}^{*} \sigma(Q)$.
- If $P \to_{\beta} P_1$ (a $\beta$-step), then the Simulation Lemma (thesis Theorem 7, `docs/enve-beta-normal-form-simulation.md`) gives $\sigma(P) \to_{\beta/\sigma}^{*} \sigma(P_1)$. The induction hypothesis, applied to $P_1 \to_{\beta\sigma}^{*} Q$, gives $\sigma(P_1) \to_{\beta/\sigma}^{*} \sigma(Q)$. Concatenating, $\sigma(P) \to_{\beta/\sigma}^{*} \sigma(Q)$.

This proves the Fact. $\blacksquare$

Now suppose $M \to_{\beta\sigma}^{*} N_1$ and $M \to_{\beta\sigma}^{*} N_2$. By the Fact, $\sigma(M) \to_{\beta/\sigma}^{*} \sigma(N_1)$ and $\sigma(M) \to_{\beta/\sigma}^{*} \sigma(N_2)$. By confluence of $\to_{\beta/\sigma}$ (thesis Theorem 12, `docs/enve-beta-over-sigma-confluence.md`, applied to the common source $\sigma(M)$), there exists a $\sigma$-normal form $L$ such that $\sigma(N_1) \to_{\beta/\sigma}^{*} L$ and $\sigma(N_2) \to_{\beta/\sigma}^{*} L$.

Since $\to_{\beta/\sigma}$ is, by construction (Definition 13, `docs/enve-beta-over-sigma-reduction.md`), a sequence of $\to_{\beta}$-steps and $\to_{\sigma}$-steps interleaved, every $\to_{\beta/\sigma}^{*}$-reduction is in particular a $\to_{\beta\sigma}^{*}$-reduction: so $\sigma(N_1) \to_{\beta\sigma}^{*} L$ and $\sigma(N_2) \to_{\beta\sigma}^{*} L$. Combined with $N_1 \to_{\sigma}^{*} \sigma(N_1)$ and $N_2 \to_{\sigma}^{*} \sigma(N_2)$ (both instances of $\to_{\beta\sigma}^{*}$, since $\to_{\sigma} \subseteq \to_{\beta\sigma}$), we get
$$
N_1 \to_{\beta\sigma}^{*} \sigma(N_1) \to_{\beta\sigma}^{*} L,
\qquad
N_2 \to_{\beta\sigma}^{*} \sigma(N_2) \to_{\beta\sigma}^{*} L.
$$
Taking this $L$ completes the proof.

#### End of Proof.

---

## Remarks and Adjustments Made to the Source Material

- **"Theorem 1" replaced by a self-contained argument.** As explained above, the thesis's citation of a general early "Theorem 1" (§1.3.2, itself citing external literature) could not be reliably transcribed from the scanned source. Rather than assert an unverifiable paraphrase of it, this document proves Theorem 13 directly: the Fact (lifting an arbitrary $\to_{\beta\sigma}^{*}$-reduction to a $\to_{\beta/\sigma}^{*}$-reduction between $\sigma$-normal forms) does the work that "Theorem 1" was presumably invoked for, using only Theorem 7, Theorem 12, and the basic normal-form facts of Definition 12 -- all already recorded, precisely, elsewhere in this repository.
- **No constants involved.** As with every other reduction document in this repository, this theorem does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{Env}\varepsilon}$ has none (`docs/enve-syntax.md`).
