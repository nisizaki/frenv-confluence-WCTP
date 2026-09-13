# Confluence of $\beta/\sigma$-Reduction

This document states and proves thesis Theorem 12 (§2.4.5): $\to_{\beta/\sigma}$ (`docs/enve-beta-over-sigma-reduction.md`, thesis Definition 13) is confluent. This is the payoff of the whole parallel-reduction development (`docs/enve-parallel-reduction.md` through `docs/enve-parallel-reduction-confluence.md`): confluence of $\Rightarrow_{\mathrm{par}}$ transfers back to $\to_{\beta/\sigma}$ because the two relations reach exactly the same pairs of $\sigma$-normal forms (thesis Theorems 8 and 9).

> **Note for AI-assisted formalization.**
> The proof needs the *multi-step* versions of Theorem 8 (Simulation) and
> Theorem 9 (Soundness) -- i.e. with $\to_{\beta/\sigma}^{*}$ and
> $\Rightarrow_{\mathrm{par}}^{*}$ in place of single steps. Both multi-step versions
> follow from their single-step originals by a routine induction on the
> number of steps in the chain (spelled out below as Facts, since neither
> is stated separately elsewhere in this repository).

---

## Theorem (Confluence of $\beta/\sigma$-Reduction)

For all $\sigma$-normal forms $U, U_1, U_2$ of $\lambda_{\mathrm{Env}\varepsilon}$, if $U \to_{\beta/\sigma}^{*} U_1$ and $U \to_{\beta/\sigma}^{*} U_2$, then there exists a $\sigma$-normal form $U_3$ such that $U_1 \to_{\beta/\sigma}^{*} U_3$ and $U_2 \to_{\beta/\sigma}^{*} U_3$.

#### Proof.

**Fact 1 (multi-step Simulation).** If $P \to_{\beta/\sigma}^{*} Q$, then $P \Rightarrow_{\mathrm{par}}^{*} Q$. Proof by induction on the number of steps in $P \to_{\beta/\sigma}^{*} Q$: zero steps give $P = Q$, so $P \Rightarrow_{\mathrm{par}}^{*} Q$ holds trivially (zero steps); for $P \to_{\beta/\sigma} P_1 \to_{\beta/\sigma}^{*} Q$, the Simulation Lemma (thesis Theorem 8) gives $P \Rightarrow_{\mathrm{par}} P_1$, and the induction hypothesis gives $P_1 \Rightarrow_{\mathrm{par}}^{*} Q$, so $P \Rightarrow_{\mathrm{par}}^{*} Q$ by concatenating.

**Fact 2 (multi-step Soundness).** If $P \Rightarrow_{\mathrm{par}}^{*} Q$, then $P \to_{\beta/\sigma}^{*} Q$. Proof by induction on the number of steps in $P \Rightarrow_{\mathrm{par}}^{*} Q$: zero steps give $P = Q$, so $P \to_{\beta/\sigma}^{*} Q$ holds trivially; for $P \Rightarrow_{\mathrm{par}} P_1 \Rightarrow_{\mathrm{par}}^{*} Q$, the Soundness Lemma (thesis Theorem 9, `docs/enve-parallel-reduction-soundness.md`) gives $P \to_{\beta/\sigma}^{*} P_1$, and the induction hypothesis gives $P_1 \to_{\beta/\sigma}^{*} Q$, so $P \to_{\beta/\sigma}^{*} Q$ by concatenating.

Now suppose $U \to_{\beta/\sigma}^{*} U_1$ and $U \to_{\beta/\sigma}^{*} U_2$. By Fact 1, $U \Rightarrow_{\mathrm{par}}^{*} U_1$ and $U \Rightarrow_{\mathrm{par}}^{*} U_2$. By confluence of $\Rightarrow_{\mathrm{par}}$ (`docs/enve-parallel-reduction-confluence.md`, thesis Theorem 11), there exists a $\sigma$-normal form $U_3$ with $U_1 \Rightarrow_{\mathrm{par}}^{*} U_3$ and $U_2 \Rightarrow_{\mathrm{par}}^{*} U_3$. By Fact 2, $U_1 \to_{\beta/\sigma}^{*} U_3$ and $U_2 \to_{\beta/\sigma}^{*} U_3$.

#### End of Proof.

---

## Remarks and Adjustments Made to the Source Material

- **Multi-step lifting of Theorems 8 and 9 made explicit.** The scanned source applies Theorem 8 directly to $U \to_{\beta/\sigma}^{*} U_1$ (giving $U \Rightarrow_{\mathrm{par}}^{*} U_1$) and Theorem 9 directly to $U_1 \Rightarrow_{\mathrm{par}}^{*} U_3$ (giving $U_1 \to_{\beta/\sigma}^{*} U_3$), even though those two theorems are stated only for a single step (`docs/enve-parallel-reduction-simulation.md`, thesis Theorem 8; `docs/enve-parallel-reduction-soundness.md`, thesis Theorem 9). This document adds Facts 1 and 2, each a one-paragraph induction on chain length, to justify that direct use of the multi-step versions.
- **No other changes.** The core argument -- lift both chains to $\Rightarrow_{\mathrm{par}}^{*}$, join them via confluence of $\Rightarrow_{\mathrm{par}}$, then lift the join back down to $\to_{\beta/\sigma}^{*}$ -- matches the source exactly.
- **No constants involved.** As with every other reduction document in this repository, this theorem does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{Env}\varepsilon}$ has none (`docs/enve-syntax.md`).
