# Confluence of Parallel Reduction

This document states and proves thesis Theorem 11 (§2.4.5): parallel reduction (`docs/enve-parallel-reduction.md`) is confluent -- if a $\sigma$-normal form $U$ reaches $V_1$ and $V_2$ by any number of $\Rightarrow_{\mathrm{par}}$-steps, $V_1$ and $V_2$ can always be brought back together at a common term. The thesis proof is one line -- "follows from the diamond property of $\Rightarrow_{\mathrm{par}}$ (Theorem 10)" -- combining the Triangle Property Lemma with the standard, calculus-independent fact that the diamond property of a single-step relation always upgrades to confluence of its reflexive-transitive closure; this document spells that combination out.

> **Note for AI-assisted formalization.**
> Write $\Rightarrow_{\mathrm{par}}^{*}$ for the reflexive-transitive closure of
> $\Rightarrow_{\mathrm{par}}$. The proof below has two layers: a general fact about
> any relation with the diamond property (not specific to
> $\lambda_{\mathrm{Env}\varepsilon}$ at all, so stated and proved as a
> standalone Fact), and its one-line application to $\Rightarrow_{\mathrm{par}}$ using
> the Triangle Property Lemma (`docs/enve-parallel-reduction-triangle-property.md`,
> thesis Theorem 10) as the one-step diamond property that fact needs.

---

## Theorem (Confluence of Parallel Reduction)

For all $\sigma$-normal forms $U, V_1, V_2$ of $\lambda_{\mathrm{Env}\varepsilon}$, if $U \Rightarrow_{\mathrm{par}}^{*} V_1$ and $U \Rightarrow_{\mathrm{par}}^{*} V_2$, then there exists a $\sigma$-normal form $W$ such that $V_1 \Rightarrow_{\mathrm{par}}^{*} W$ and $V_2 \Rightarrow_{\mathrm{par}}^{*} W$.

#### Proof.

**Fact (the diamond property implies confluence).** Let $R$ be any relation with the diamond property: for all $x, y, z$, if $x \mathrel{R} y$ and $x \mathrel{R} z$, then there exists $w$ with $y \mathrel{R} w$ and $z \mathrel{R} w$. Then $R^{*}$ (the reflexive-transitive closure of $R$) is confluent: for all $x, y, z$, if $x \mathrel{R^{*}} y$ and $x \mathrel{R^{*}} z$, then there exists $w$ with $y \mathrel{R^{*}} w$ and $z \mathrel{R^{*}} w$.

This Fact is proved in two steps, both by ordinary induction on the number of $R$-steps in a chain (no termination assumption on $R$ is needed anywhere, unlike Newman's Lemma -- the diamond property is strong enough on its own).

*Step 1.* If $x \mathrel{R} y$ and $x \mathrel{R^{*}} z$, then there exists $w$ with $y \mathrel{R^{*}} w$ and $z \mathrel{R^{*}} w$. Proof by induction on the number of steps in $x \mathrel{R^{*}} z$:
- Zero steps: $z = x$. Take $w := y$: $y \mathrel{R^{*}} y$ holds trivially (zero steps), and $z = x \mathrel{R} y = w$ gives $z \mathrel{R^{*}} w$ (one step).
- $n+1$ steps: $x \mathrel{R} z_1 \mathrel{R^{*}} z$ (one step to $z_1$, then $n$ more steps to $z$). By the diamond property applied to $x \mathrel{R} y$ and $x \mathrel{R} z_1$ (both single steps from $x$), there is $x'$ with $y \mathrel{R} x'$ and $z_1 \mathrel{R} x'$. By the induction hypothesis (Step 1 itself, applied to $z_1 \mathrel{R} x'$ and the shorter chain $z_1 \mathrel{R^{*}} z$), there is $w$ with $x' \mathrel{R^{*}} w$ and $z \mathrel{R^{*}} w$. Then $y \mathrel{R} x' \mathrel{R^{*}} w$ gives $y \mathrel{R^{*}} w$, and $z \mathrel{R^{*}} w$ already holds.

*Step 2.* If $x \mathrel{R^{*}} y$ and $x \mathrel{R^{*}} z$, then there exists $w$ with $y \mathrel{R^{*}} w$ and $z \mathrel{R^{*}} w$. Proof by induction on the number of steps in $x \mathrel{R^{*}} y$:
- Zero steps: $y = x$. Take $w := z$: $y = x \mathrel{R^{*}} z = w$, and $z \mathrel{R^{*}} z$ trivially (zero steps).
- $n+1$ steps: $x \mathrel{R} y_1 \mathrel{R^{*}} y$ (one step to $y_1$, then $n$ more steps to $y$). By Step 1 applied to $x \mathrel{R} y_1$ and $x \mathrel{R^{*}} z$, there is $w_1$ with $y_1 \mathrel{R^{*}} w_1$ and $z \mathrel{R^{*}} w_1$. By the induction hypothesis (Step 2 itself, applied to the shorter chain $y_1 \mathrel{R^{*}} y$ and $y_1 \mathrel{R^{*}} w_1$), there is $w$ with $y \mathrel{R^{*}} w$ and $w_1 \mathrel{R^{*}} w$. Then $z \mathrel{R^{*}} w_1 \mathrel{R^{*}} w$ gives $z \mathrel{R^{*}} w$, and $y \mathrel{R^{*}} w$ already holds.

This proves the Fact.

**Applying the Fact to $\Rightarrow_{\mathrm{par}}$.** By the Triangle Property Lemma (`docs/enve-parallel-reduction-triangle-property.md`, thesis Theorem 10), $\Rightarrow_{\mathrm{par}}$ has the diamond property: if $U \Rightarrow_{\mathrm{par}} V_1$ and $U \Rightarrow_{\mathrm{par}} V_2$, then, setting $W := \mathrm{cd}(U)$ (`docs/enve-complete-development.md`), Theorem 10 applied to each of the two steps gives $V_1 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U) = W$ and $V_2 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U) = W$ directly. Applying the Fact with $R := \Rightarrow_{\mathrm{par}}$ then gives exactly the statement of this theorem: for $\sigma$-normal forms $U, V_1, V_2$ with $U \Rightarrow_{\mathrm{par}}^{*} V_1$ and $U \Rightarrow_{\mathrm{par}}^{*} V_2$, there exists $W$ with $V_1 \Rightarrow_{\mathrm{par}}^{*} W$ and $V_2 \Rightarrow_{\mathrm{par}}^{*} W$.

#### End of Proof.

---

## Remarks and Adjustments Made to the Source Material

- **Expanded from the source's one-line proof.** The thesis states this theorem's proof as "follows from the diamond property of $\Rightarrow_{\mathrm{par}}$ (Theorem 10)" without spelling out how a *one-step* diamond property upgrades to confluence of the *closure* $\Rightarrow_{\mathrm{par}}^{*}$. This document supplies that missing link as the Fact, with its own two-step proof by ordinary induction -- noting explicitly that, unlike Newman's Lemma (`docs/enve-sigma-reduction-confluence.md`), no termination assumption is needed here: the diamond property is exactly strong enough (single step joins to single step, not just "eventually joinable") for the induction to go through directly.
- **No constants involved.** As with every other reduction document in this repository, this theorem does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{Env}\varepsilon}$ has none (`docs/enve-syntax.md`).
