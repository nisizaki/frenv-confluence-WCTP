# Simulation of $\beta/\sigma$-Reduction by Parallel Reduction

This document states and proves thesis Theorem 8 (§2.4.5), presented here as a **Lemma** as requested: every $\to_{\beta/\sigma}$-step (`docs/enve-beta-over-sigma-reduction.md`, thesis Definition 13) between $\sigma$-normal forms is also a parallel-reduction step (`docs/enve-parallel-reduction.md`, thesis Definition 14). Together with the Reflexivity Lemma (`docs/enve-parallel-reduction-reflexivity.md`, thesis Lemma 6), this is what lets $\Rightarrow_{\mathrm{par}}^{*}$ stand in for $\to_{\beta/\sigma}^{*}$ when proving confluence via the diamond property.

> **Note for AI-assisted formalization.**
> The proof is a structural induction on $U$, case-split on the rule used
> last in the derivation of $U \to_{\beta} M$ (the same case split as
> `docs/enve-beta-normal-form-simulation.md`, thesis Theorem 7, but here
> the induction is directly on the structure of $U$, since every recursive
> call is to a literal subterm of $U$ -- there is no need for the length
> measure this time). Every case either applies the Reflexivity Lemma to
> an unchanged subterm, or applies the induction hypothesis (via
> `docs/enve-beta-over-sigma-reduction.md`'s own definition, $P \to_{\beta} Q$
> and $Q \to_{\sigma}^{*} \sigma(Q)$ together mean exactly $P \to_{\beta/\sigma} \sigma(Q)$)
> to a changed subterm, then combines the results with a single rule of
> $\Rightarrow_{\mathrm{par}}$.

---

## Lemma (Simulation of $\to_{\beta/\sigma}$ by Parallel Reduction)

Let $U$ be a $\sigma$-normal form of $\lambda_{\mathrm{Env}\varepsilon}$. If $U \to_{\beta/\sigma} U'$, then $U \Rightarrow_{\mathrm{par}} U'$.

#### Proof.

Since $U \to_{\beta/\sigma} U'$, by Definition 13 (`docs/enve-beta-over-sigma-reduction.md`) there is $M$ with $U \to_{\beta} M$ and $U' = \sigma(M)$. The proof is by induction on the structure of $U$, case-split on the rule used last in the derivation of $U \to_{\beta} M$.

**`Beta`.** There are $\sigma$-normal forms $U_1, U_2$ with $U = (\lambda x.\,U_1)U_2$ and $M = U_1 \circ ((U_2/x)\cdot \mathsf{id})$. By the Reflexivity Lemma, $U_1 \Rightarrow_{\mathrm{par}} U_1$ and $U_2 \Rightarrow_{\mathrm{par}} U_2$. So, by rule `ParBeta`, $U \Rightarrow_{\mathrm{par}} \sigma(U_1 \circ ((U_2/x)\cdot \mathsf{id})) = \sigma(M) = U'$.

**`BetaClos`.** There are $\sigma$-normal forms $U_1, U_2, U_3$ with $U = ((\lambda x.\,U_1) \circ U_3)U_2$ and $M = U_1 \circ ((U_2/x)\cdot U_3)$. By the Reflexivity Lemma, $U_1 \Rightarrow_{\mathrm{par}} U_1$, $U_2 \Rightarrow_{\mathrm{par}} U_2$, $U_3 \Rightarrow_{\mathrm{par}} U_3$. So, by rule `ParBetaClos`, $U \Rightarrow_{\mathrm{par}} \sigma(U_1 \circ ((U_2/x)\cdot U_3)) = \sigma(M) = U'$.

**`Comp` ($\mathrm{Comp}_{\varepsilon}$).** There are $\sigma$-normal forms $U_1, U_2$ with $U = \varepsilon(U_1)U_2$ and $M = U_1 \circ U_2$. By the Reflexivity Lemma, $U_1 \Rightarrow_{\mathrm{par}} U_1$, $U_2 \Rightarrow_{\mathrm{par}} U_2$. So, by rule `ParComp$_\varepsilon$`, $U \Rightarrow_{\mathrm{par}} \sigma(U_1 \circ U_2) = \sigma(M) = U'$.

**`Lam`.** There are $\lambda_{\mathrm{Env}\varepsilon}$ terms $U_1, M_1$ with $U = \lambda x.\,U_1$, $U_1 \to_{\beta} M_1$, and $M = \lambda x.\,M_1$. Since $U_1 \to_{\beta} M_1$, we have $U_1 \to_{\beta/\sigma} \sigma(M_1)$ (Definition 13, taking the intermediate term to be $M_1$), so the induction hypothesis (applied to the subterm $U_1$) gives $U_1 \Rightarrow_{\mathrm{par}} \sigma(M_1)$. So, by rule `ParLam`, $U \Rightarrow_{\mathrm{par}} \lambda x.\,\sigma(M_1) = \sigma(M) = U'$ (the last equality since $\sigma(\lambda x.\,M_1) = \lambda x.\,\sigma(M_1)$, as `Lam` is never itself a $\sigma$-redex).

**`Eop`.** There are $\lambda_{\mathrm{Env}\varepsilon}$ terms $U_1, M_1$ with $U = \varepsilon(U_1)$, $U_1 \to_{\beta} M_1$, and $M = \varepsilon(M_1)$. As in the `Lam` case, $U_1 \to_{\beta/\sigma} \sigma(M_1)$, so the induction hypothesis gives $U_1 \Rightarrow_{\mathrm{par}} \sigma(M_1)$. So, by rule `ParEps`, $U \Rightarrow_{\mathrm{par}} \varepsilon(\sigma(M_1)) = \sigma(M) = U'$.

**`AppL`.** There are $\sigma$-normal forms $U_1, U_2$ and a $\lambda_{\mathrm{Env}\varepsilon}$ term $M_1$ with $U = U_1 U_2$, $U_1 \to_{\beta} M_1$, and $M = M_1 U_2$. Since $U_1 \to_{\beta/\sigma} \sigma(M_1)$, the induction hypothesis gives $U_1 \Rightarrow_{\mathrm{par}} \sigma(M_1)$; by the Reflexivity Lemma, $U_2 \Rightarrow_{\mathrm{par}} U_2$. So, by rule `ParApp`, $U \Rightarrow_{\mathrm{par}} \sigma(M_1)\,U_2 = \sigma(M)$ (since $U_2$ is already $\sigma$-normal, $\sigma(M_1 U_2) = \sigma(M_1)\,U_2$) $= U'$.

**`AppR`.** Symmetric to `AppL`: there are $\sigma$-normal forms $U_1, U_2$ and $M_2$ with $U = U_1 U_2$, $U_2 \to_{\beta} M_2$, $M = U_1 M_2$. The induction hypothesis gives $U_2 \Rightarrow_{\mathrm{par}} \sigma(M_2)$; by the Reflexivity Lemma, $U_1 \Rightarrow_{\mathrm{par}} U_1$. By rule `ParApp`, $U \Rightarrow_{\mathrm{par}} U_1\,\sigma(M_2) = \sigma(M) = U'$.

**`ExtnL`.** There are $\sigma$-normal forms $U_1, U_2$ and $M_1$ with $U = (U_1/x)\cdot U_2$, $U_1 \to_{\beta} M_1$, $M = (M_1/x)\cdot U_2$. The induction hypothesis gives $U_1 \Rightarrow_{\mathrm{par}} \sigma(M_1)$; by the Reflexivity Lemma, $U_2 \Rightarrow_{\mathrm{par}} U_2$. By rule `ParExtn`, $U \Rightarrow_{\mathrm{par}} (\sigma(M_1)/x)\cdot U_2 = \sigma(M) = U'$.

**`ExtnR`.** Symmetric to `ExtnL`: there are $\sigma$-normal forms $U_1, U_2$ and $M_2$ with $U = (U_1/x)\cdot U_2$, $U_2 \to_{\beta} M_2$, $M = (U_1/x)\cdot M_2$. The induction hypothesis gives $U_2 \Rightarrow_{\mathrm{par}} \sigma(M_2)$; by the Reflexivity Lemma, $U_1 \Rightarrow_{\mathrm{par}} U_1$. By rule `ParExtn`, $U \Rightarrow_{\mathrm{par}} (U_1/x)\cdot \sigma(M_2) = \sigma(M) = U'$.

**`CompL`.** There are $\sigma$-normal forms $U_1, U_2$ and $M_1$ with $U = U_1 \circ U_2$, $U_1 \to_{\beta} M_1$, $M = M_1 \circ U_2$. The induction hypothesis gives $U_1 \Rightarrow_{\mathrm{par}} \sigma(M_1)$. Since $U = U_1 \circ U_2$ is itself a $\sigma$-normal form, $U_1$ is `Lam`-headed or `Var`-headed, and the $\to_{\beta}$-step $U_1 \to_{\beta} M_1$ never changes that (neither `Beta`, `BetaClos`, `Comp$_\varepsilon$`, nor any congruence rule turns a `Lam`- or `Var`-headed term into a term of a different head shape at the root), so $\sigma(M_1)$ is `Lam`- or `Var`-headed exactly as $U_1$ was; likewise $U_2$'s remaining unchanged means the side condition on the right ($U_2 \neq \mathsf{id}$, respectively $U_2$ not an environment extension) still holds. So, applying `ParLamComp` or `ParVarComp` as appropriate, $U \Rightarrow_{\mathrm{par}} \sigma(\sigma(M_1) \circ U_2) = \sigma(M_1) \circ U_2$ (the outer $\sigma(-)$ is a no-op, since $\sigma(M_1) \circ U_2$ is already $\sigma$-normal by the shape argument just given) $= \sigma(M) = U'$.

**`CompR`.** Symmetric to `CompL`: there are $\sigma$-normal forms $U_1, U_2$ and $M_2$ with $U = U_1 \circ U_2$, $U_2 \to_{\beta} M_2$, $M = U_1 \circ M_2$. The induction hypothesis gives $U_2 \Rightarrow_{\mathrm{par}} \sigma(M_2)$; and, since none of `Beta`/`BetaClos`/`Comp$_\varepsilon$`/congruence ever produces $\mathsf{id}$ or an environment extension out of a term that was not already one, $\sigma(M_2)$ still satisfies whichever side condition $U_2$ did. Applying `ParLamComp` or `ParVarComp` as appropriate, $U \Rightarrow_{\mathrm{par}} \sigma(U_1 \circ \sigma(M_2)) = U_1 \circ \sigma(M_2) = \sigma(M) = U'$.

This exhausts every rule by which $U \to_{\beta} M$ could have been derived, so $U \Rightarrow_{\mathrm{par}} U'$ holds whenever $U \to_{\beta/\sigma} U'$.

#### End of Proof.

---

## Remarks and Adjustments Made to the Source Material

- **Typo corrected.** The `Lam` case of the scanned source renders $U$ as "$\lambda U_1.$", omitting the bound variable; this document reads it as $U = \lambda x.\,U_1$, consistent with every other occurrence of the `Lam` constructor in this repository (`docs/enve-syntax.md`).
- **Shape-preservation argument for `CompL`/`CompR` made explicit.** The scanned source writes the `CompL`/`CompR` conclusions directly as $\sigma(M_1) \circ U_2$ and $U_1 \circ \sigma(M_2)$ (with no further $\sigma(-)$ needed around the whole term), without commenting on why that outer $\sigma(-)$ is safe to omit. This document adds the justification: a $\to_{\beta}$-step never changes whether a term is `Lam`-headed, `Var`-headed, equal to $\mathsf{id}$, or an environment extension at the root (these are exactly the shape facts the $\sigma$-normal-form grammar's side conditions depend on), so $U_1 \circ U_2$ being $\sigma$-normal (given) guarantees $\sigma(M_1) \circ U_2$ and $U_1 \circ \sigma(M_2)$ are too, making the outer $\sigma(-)$ that `ParLamComp`/`ParVarComp` would otherwise add a no-op.
- **No other changes.** Every other case matches the corresponding rule of `docs/enve-parallel-reduction.md` and the corresponding case of `docs/enve-beta-over-sigma-reduction.md` exactly; no further corrections were needed.
- **No constants involved.** As with every other reduction document in this repository, this lemma does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{Env}\varepsilon}$ has none (`docs/enve-syntax.md`).
