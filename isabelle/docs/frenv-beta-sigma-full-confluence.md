# Confluence of $\lambda_{\mathrm{FREnv}}$

This document states and proves thesis Theorem 14 (§2.4.5): $\lambda_{\mathrm{FREnv}}$'s full reduction relation $\to_{\beta\sigma}$ (`docs/frenv-reduction-beta-sigma.md`) is confluent -- on *all* terms, not just $\sigma$-normal forms, and not merely the *local* confluence already established in `docs/frenv-beta-sigma-local-confluence.md`. This is the payoff of transferring confluence from $\lambda_{\mathrm{Env}\varepsilon}$ (`docs/enve-beta-sigma-full-confluence.md`, thesis Theorem 13) back across the translation $⟦-⟧$ (`docs/enve-frenv-translation.md`, thesis Definition 10).

> **Note on the cited proof.** The thesis states this theorem's proof as
> "follows from Theorem 2 and Theorem 13." Theorem 13 is already
> established in this repository. "Theorem 2" is, by its position in the
> thesis (§2.3.1, immediately after the Multi-Step Lifting Lemma, thesis
> Lemma 4), almost certainly the conditional statement "if
> $\lambda_{\mathrm{Env}\varepsilon}$'s $\to_{\beta\sigma}$ is confluent, then
> $\lambda_{\mathrm{FREnv}}$'s $\to_{\beta\sigma}$ is confluent" -- exactly
> the shape needed to make Theorem 14 a one-line consequence of Theorem 13
> discharging that hypothesis. Its precise original wording could not be
> reliably recovered from the scanned source. Rather than guess at it,
> this document proves that conditional statement directly, from the
> Surjectivity Lemma, the Simulation Lemma, and the Multi-Step Lifting
> Lemma (thesis Lemmas 1, 2, and 4, all already established precisely in
> this repository), and then discharges its hypothesis with Theorem 13 --
> reaching the same conclusion the thesis's citation of "Theorem 2" was
> presumably used to package.

---

## Theorem (Confluence of $\lambda_{\mathrm{FREnv}}$)

For all $P, Q_1, Q_2 \in \mathbf{Term}(\lambda_{\mathrm{FREnv}})$, if $P \to_{\beta\sigma}^{*} Q_1$ and $P \to_{\beta\sigma}^{*} Q_2$, then there exists $L \in \mathbf{Term}(\lambda_{\mathrm{FREnv}})$ such that $Q_1 \to_{\beta\sigma}^{*} L$ and $Q_2 \to_{\beta\sigma}^{*} L$.

#### Proof.

By confluence of $\lambda_{\mathrm{Env}\varepsilon}$ (thesis Theorem 13, `docs/enve-beta-sigma-full-confluence.md`), the hypothesis of the Multi-Step Lifting Lemma (thesis Lemma 4, `docs/enve-frenv-translation-multi-step-lifting.md`) is satisfied, so that lemma applies unconditionally from here on.

Suppose $P \to_{\beta\sigma}^{*} Q_1$ and $P \to_{\beta\sigma}^{*} Q_2$. By the Surjectivity Lemma (thesis Lemma 1, `docs/enve-frenv-translation-surjective.md`), there exists $M \in \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$ with $⟦M⟧ = P$.

Applying the Multi-Step Lifting Lemma to $⟦M⟧ = P \to_{\beta\sigma}^{*} Q_1$ gives $\lambda_{\mathrm{Env}\varepsilon}$ terms $N_1, L_1$ with $⟦N_1⟧ = Q_1$, $N_1 \to_{\beta\sigma}^{*} L_1$, $M \to_{\beta\sigma}^{*} L_1$. Applying it again to $⟦M⟧ = P \to_{\beta\sigma}^{*} Q_2$ gives $N_2, L_2$ with $⟦N_2⟧ = Q_2$, $N_2 \to_{\beta\sigma}^{*} L_2$, $M \to_{\beta\sigma}^{*} L_2$.

Now $M \to_{\beta\sigma}^{*} L_1$ and $M \to_{\beta\sigma}^{*} L_2$ are two $\lambda_{\mathrm{Env}\varepsilon}$-side reductions from the common source $M$. By confluence of $\lambda_{\mathrm{Env}\varepsilon}$ (Theorem 13) again, there exists $W \in \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$ with $L_1 \to_{\beta\sigma}^{*} W$ and $L_2 \to_{\beta\sigma}^{*} W$.

Chaining, $N_1 \to_{\beta\sigma}^{*} L_1 \to_{\beta\sigma}^{*} W$ and $N_2 \to_{\beta\sigma}^{*} L_2 \to_{\beta\sigma}^{*} W$. By the Simulation Lemma (thesis Lemma 2, `docs/enve-frenv-translation-simulation.md`, applied to each of these two $\lambda_{\mathrm{Env}\varepsilon}$-side reductions in turn), $⟦N_1⟧ \to_{\beta\sigma}^{*} ⟦W⟧$ and $⟦N_2⟧ \to_{\beta\sigma}^{*} ⟦W⟧$, i.e. $Q_1 \to_{\beta\sigma}^{*} ⟦W⟧$ and $Q_2 \to_{\beta\sigma}^{*} ⟦W⟧$.

Taking $L := ⟦W⟧$ completes the proof.

#### End of Proof.

---

## Remarks and Adjustments Made to the Source Material

- **"Theorem 2" replaced by a self-contained argument.** As explained above, the thesis's citation of "Theorem 2" (§2.3.1) could not be reliably transcribed from the scanned source. This document proves the same conditional confluence-transfer fact directly, using only the Surjectivity Lemma, the Simulation Lemma, and the Multi-Step Lifting Lemma (thesis Lemmas 1, 2, 4) -- all already recorded precisely elsewhere in this repository -- and then discharges the lifting lemma's confluence hypothesis using Theorem 13, exactly as the thesis's one-line proof does.
- **Redundant phrasing dropped from the statement.** Per the request, the theorem statement omits "with the `Eps-eps` rule added," since `docs/frenv-reduction-sigma.md` and `docs/frenv-reduction-beta-sigma.md` already include `Eps-eps` as a standing part of $\lambda_{\mathrm{FREnv}}$'s reduction relation -- there is no separate "before/after adding `Eps-eps`" version of the calculus to distinguish.
- **No constants involved.** As with every other reduction document in this repository, this theorem does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{FREnv}}$ has none (`docs/frenv-syntax.md`).
