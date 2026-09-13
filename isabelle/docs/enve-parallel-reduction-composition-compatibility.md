# Composition Compatibility of Parallel Reduction

This document states and proves thesis Lemma 7 (§2.4.5): parallel reduction (`docs/enve-parallel-reduction.md`) is compatible with $\sigma$-normalized composition -- reducing $U$ and $V$ in parallel lets you reduce $\sigma(U \circ V)$ in parallel too, to the corresponding $\sigma(U' \circ V')$. This is the key technical lemma used to establish the diamond property of $\Rightarrow_{\mathrm{par}}$ via complete development (`docs/enve-complete-development.md`), since $\Rightarrow_{\mathrm{par}}$'s own `ParLamComp`, `ParVarComp`, `ParBeta`, `ParBetaClos`, and `ParComp$_\varepsilon$` rules all build their conclusion by forming a composition and then $\sigma$-normalizing it.

> **Note for AI-assisted formalization.**
> Throughout, $\sigma(M)$ denotes the $\sigma$-normal form of $M$
> (`docs/enve-sigma-normal-form.md`, thesis Definition 12). Two background
> facts are used repeatedly without being restated at each step: (1)
> normalizing a subterm first never changes the final $\sigma$-normal form
> of a larger term built around it (e.g. $\sigma(P \circ \sigma(Q)) = \sigma(P \circ Q)$),
> since $\sigma$-reduction is confluent and terminating
> (`docs/enve-sigma-reduction-confluence.md`, `docs/enve-sigma-reduction-termination.md`);
> and (2) $\sigma((M_1 \circ M_2) \circ M_3) = \sigma(M_1 \circ (M_2 \circ M_3))$
> and its variants (`Assoc`-equivalence), since the two sides of each
> $\sigma$-rule of `docs/enve-reduction-sigma.md` always have the same
> $\sigma$-normal form.

---

## Lemma (Composition Compatibility of Parallel Reduction)

Let $U, V$ be $\sigma$-normal forms of $\lambda_{\mathrm{Env}\varepsilon}$. If $U \Rightarrow_{\mathrm{par}} U'$ and $V \Rightarrow_{\mathrm{par}} V'$, then $\sigma(U \circ V) \Rightarrow_{\mathrm{par}} \sigma(U' \circ V')$.

#### Proof.

By induction on $\mathrm{length}(U \circ V)$ (`docs/enve-term-length-measure.md`).

### When $U \circ V$ is already $\sigma$-normal

This happens exactly when $U = \lambda x.\,U_1$ for some $\sigma$-normal form $U_1$ and $V \neq \mathsf{id}$, or when $U = x$ and $V$ is neither $\mathsf{id}$ nor an environment extension (these are exactly the two `Comp`-shaped productions of grammar (2.32), `docs/enve-sigma-normal-form-grammar.md`).

**$U = \lambda x.\,U_1$ ($V \neq \mathsf{id}$).** There is $U_1'$ with $U_1 \Rightarrow_{\mathrm{par}} U_1'$ and $U' = \lambda x.\,U_1'$. So $\sigma(U \circ V) = (\lambda x.\,U_1) \circ V \Rightarrow_{\mathrm{par}} \sigma((\lambda x.\,U_1') \circ V') = \sigma(U' \circ V')$, by rule `ParLamComp` (whose side condition $V \neq \mathsf{id}$ holds by assumption).

**$U = x$ ($V$ not an environment extension, $V \neq \mathsf{id}$).** $\sigma(U \circ V) = \sigma(x \circ V) \Rightarrow_{\mathrm{par}} \sigma(x \circ V') = \sigma(U' \circ V')$, by rule `ParVarComp` (whose side condition holds by assumption).

### When $U \circ V$ is not already $\sigma$-normal

Then one or more of the following hold, for $\sigma$-normal forms $U_1, U_2, V_1, V_2, W$:

1. $U = (\lambda x.\,U_1) \circ U_2$ ($U_2 \neq \mathsf{id}$)
2. $U = x \circ W$ ($W$ neither an environment extension nor $\mathsf{id}$)
3. $U = \mathsf{id}$
4. $V = \mathsf{id}$
5. $U = (U_1/x)\cdot U_2$
6. $U = x$, $V = (V_1/x)\cdot V_2$
7. $U = x$, $V = (V_1/y)\cdot V_2$ ($x \neq y$)
8. $U = U_1 U_2$
9. $U = \varepsilon(U_1)$

**Case 1: $U = (\lambda x.\,U_1) \circ U_2$ ($U_2 \neq \mathsf{id}$).** There are $U_1', U_2'$ with $U_1 \Rightarrow_{\mathrm{par}} U_1'$, $U_2 \Rightarrow_{\mathrm{par}} U_2'$, $U' = (\lambda x.\,U_1') \circ U_2'$. Since $\mathrm{length}(U_2 \circ V) < \mathrm{length}(U \circ V)$ (`docs/enve-sigma-reduction-length-decrease.md`'s `Assoc` case, applied to $U \circ V = ((\lambda x.\,U_1) \circ U_2) \circ V \to_{\sigma} (\lambda x.\,U_1) \circ (U_2 \circ V)$), the induction hypothesis applies to $U_2, V$: $\sigma(U_2 \circ V) \Rightarrow_{\mathrm{par}} \sigma(U_2' \circ V')$. Since $\lambda x.\,U_1 \Rightarrow_{\mathrm{par}} \lambda x.\,U_1'$ (rule `ParLam`) and $\mathrm{length}((\lambda x.\,U_1) \circ (U_2 \circ V)) < \mathrm{length}(U \circ V)$ likewise, the induction hypothesis applies again, to $\lambda x.\,U_1, U_2 \circ V$ (via its normal form $\sigma(U_2 \circ V)$): $\sigma((\lambda x.\,U_1) \circ \sigma(U_2 \circ V)) \Rightarrow_{\mathrm{par}} \sigma((\lambda x.\,U_1') \circ \sigma(U_2' \circ V'))$, i.e. $\sigma((\lambda x.\,U_1) \circ (U_2 \circ V)) \Rightarrow_{\mathrm{par}} \sigma((\lambda x.\,U_1') \circ (U_2' \circ V'))$. By `Assoc`-equivalence on both sides, $\sigma(U \circ V) = \sigma((\lambda x.\,U_1) \circ (U_2 \circ V))$ and $\sigma(U' \circ V') = \sigma((\lambda x.\,U_1') \circ (U_2' \circ V'))$, so $\sigma(U \circ V) \Rightarrow_{\mathrm{par}} \sigma(U' \circ V')$.

**Case 2: $U = x \circ W$ ($W$ neither an environment extension nor $\mathsf{id}$).** There is $W'$ with $W \Rightarrow_{\mathrm{par}} W'$ and $U' = x \circ W'$. Since $\mathrm{length}(W \circ V) < \mathrm{length}(U \circ V)$ (the `Assoc` length decrease, applied to $U \circ V \to_{\sigma} x \circ (W \circ V)$), the induction hypothesis gives $\sigma(W \circ V) \Rightarrow_{\mathrm{par}} \sigma(W' \circ V')$. So, by rule `ParVarComp`, $x \circ \sigma(W \circ V) \Rightarrow_{\mathrm{par}} \sigma(x \circ \sigma(W' \circ V')) = \sigma(x \circ (W' \circ V'))$, i.e. $\sigma(x \circ (W \circ V)) \Rightarrow_{\mathrm{par}} \sigma(x \circ (W' \circ V'))$. By `Assoc`-equivalence, $\sigma(U \circ V) = \sigma(x \circ (W \circ V))$ and $\sigma(U' \circ V') = \sigma(x \circ (W' \circ V'))$, so $\sigma(U \circ V) \Rightarrow_{\mathrm{par}} \sigma(U' \circ V')$.

**Case 3: $U = \mathsf{id}$.** Then $U' = \mathsf{id}$ (the only rule matching $\mathsf{id}$ is `ParId`). So $\sigma(U \circ V) = \sigma(V) \Rightarrow_{\mathrm{par}} \sigma(V') = \sigma(U' \circ V')$.

**Case 4: $V = \mathsf{id}$.** Then $V' = \mathsf{id}$. So $\sigma(U \circ V) = \sigma(U) \Rightarrow_{\mathrm{par}} \sigma(U') = \sigma(U' \circ V')$.

**Case 5: $U = (U_1/x)\cdot U_2$.** There are $U_1', U_2'$ with $U_1 \Rightarrow_{\mathrm{par}} U_1'$, $U_2 \Rightarrow_{\mathrm{par}} U_2'$, $U' = (U_1'/x)\cdot U_2'$. Since $\mathrm{length}(U_1 \circ V), \mathrm{length}(U_2 \circ V) < \mathrm{length}(U \circ V)$ (`docs/enve-sigma-reduction-length-decrease.md`'s `DExtn` case), the induction hypothesis gives $\sigma(U_1 \circ V) \Rightarrow_{\mathrm{par}} \sigma(U_1' \circ V')$ and $\sigma(U_2 \circ V) \Rightarrow_{\mathrm{par}} \sigma(U_2' \circ V')$. By rule `ParExtn`, $\sigma(U \circ V) = (\sigma(U_1 \circ V)/x)\cdot \sigma(U_2 \circ V) \Rightarrow_{\mathrm{par}} (\sigma(U_1' \circ V')/x)\cdot \sigma(U_2' \circ V') = \sigma(U' \circ V')$.

**Case 6: $U = x$, $V = (V_1/x)\cdot V_2$.** There are $V_1', V_2'$ with $V_1 \Rightarrow_{\mathrm{par}} V_1'$, $V_2 \Rightarrow_{\mathrm{par}} V_2'$, $V' = (V_1'/x)\cdot V_2'$. So $\sigma(U \circ V) = V_1 \Rightarrow_{\mathrm{par}} V_1' = \sigma(U' \circ V')$ (since $U' = x$, and both sides reduce, via `VarRef`, to $V_1$ and $V_1'$ respectively).

**Case 7: $U = x$, $V = (V_1/y)\cdot V_2$ ($x \neq y$).** There are $V_1', V_2'$ with $V_1 \Rightarrow_{\mathrm{par}} V_1'$, $V_2 \Rightarrow_{\mathrm{par}} V_2'$, $V' = (V_1'/y)\cdot V_2'$. So $\sigma(U \circ V) = x \circ V_2 \Rightarrow_{\mathrm{par}} x \circ V_2' = \sigma(U' \circ V')$ (since $U' = x$, and both sides reduce, via `VarSkip`, to $x \circ V_2$ and $x \circ V_2'$ respectively; note $V_1, V_1'$ play no role in either normal form).

**Case 8: $U = U_1 U_2$.** Sub-case on the rule used to derive $U \Rightarrow_{\mathrm{par}} U'$.

- *Via `ParApp`.* There are $U_1', U_2'$ with $U_1 \Rightarrow_{\mathrm{par}} U_1'$, $U_2 \Rightarrow_{\mathrm{par}} U_2'$, $U' = U_1' U_2'$. Since $\mathrm{length}(U_1 \circ V), \mathrm{length}(U_2 \circ V) < \mathrm{length}(U \circ V)$ (`docs/enve-sigma-reduction-length-decrease.md`'s `DApp` case), the induction hypothesis gives $\sigma(U_1 \circ V) \Rightarrow_{\mathrm{par}} \sigma(U_1' \circ V')$ and $\sigma(U_2 \circ V) \Rightarrow_{\mathrm{par}} \sigma(U_2' \circ V')$. By rule `ParApp`, $\sigma(U \circ V) = \sigma(U_1 \circ V)\,\sigma(U_2 \circ V) \Rightarrow_{\mathrm{par}} \sigma(U_1' \circ V')\,\sigma(U_2' \circ V') = \sigma(U' \circ V')$.

- *Via `ParBeta`.* $U_1 = \lambda x.\,U_3$, and there are $U_3', U_2'$ with $U_3 \Rightarrow_{\mathrm{par}} U_3'$, $U_2 \Rightarrow_{\mathrm{par}} U_2'$, $U' = \sigma(U_3' \circ ((U_2'/x)\cdot \mathsf{id}))$. Since $\lambda x.\,U_3 \Rightarrow_{\mathrm{par}} \lambda x.\,U_3'$ (rule `ParLam`) and $\mathrm{length}(\lambda x.\,U_3 \circ V), \mathrm{length}(U_2 \circ V) < \mathrm{length}(U \circ V)$, the induction hypothesis gives $\sigma((\lambda x.\,U_3) \circ V) \Rightarrow_{\mathrm{par}} \sigma((\lambda x.\,U_3') \circ V')$ and $\sigma(U_2 \circ V) \Rightarrow_{\mathrm{par}} \sigma(U_2' \circ V')$. By rule `ParApp`, $\sigma(U \circ V) = \sigma((\lambda x.\,U_3) \circ V)\,\sigma(U_2 \circ V) \Rightarrow_{\mathrm{par}} \sigma((\lambda x.\,U_3') \circ V')\,\sigma(U_2' \circ V')$. This last term equals $\sigma(U' \circ V')$: since $U' = \sigma((\lambda x.\,U_3')U_2')$ (this is exactly `Beta` applied to $(\lambda x.\,U_3')U_2'$ followed by $\sigma$-normalization), $\sigma(U' \circ V') = \sigma((\lambda x.\,U_3')U_2' \circ V') = \sigma((\lambda x.\,U_3') \circ V')\,\sigma(U_2' \circ V')$ by the `DApp`-equivalence used above. So $\sigma(U \circ V) \Rightarrow_{\mathrm{par}} \sigma(U' \circ V')$.

- *Via `ParBetaClos`.* $U_1 = (\lambda x.\,U_3) \circ U_4$, and there are $U_3', U_4', U_2'$ with $U_3 \Rightarrow_{\mathrm{par}} U_3'$, $U_4 \Rightarrow_{\mathrm{par}} U_4'$, $U_2 \Rightarrow_{\mathrm{par}} U_2'$, $U' = \sigma(U_3' \circ ((U_2'/x)\cdot U_4'))$. By the induction hypothesis (applied to $U_4, V$ and to $U_2, V$, both of strictly smaller length): $\sigma(U_4 \circ V) \Rightarrow_{\mathrm{par}} \sigma(U_4' \circ V')$ and $\sigma(U_2 \circ V) \Rightarrow_{\mathrm{par}} \sigma(U_2' \circ V')$. Since $\lambda x.\,U_3 \Rightarrow_{\mathrm{par}} \lambda x.\,U_3'$, the induction hypothesis applies once more (to $\lambda x.\,U_3$ and $\sigma(U_4 \circ V)$, again of strictly smaller length), giving $\sigma((\lambda x.\,U_3) \circ \sigma(U_4 \circ V)) \Rightarrow_{\mathrm{par}} \sigma((\lambda x.\,U_3') \circ \sigma(U_4' \circ V'))$, i.e. $\sigma((\lambda x.\,U_3) \circ (U_4 \circ V)) \Rightarrow_{\mathrm{par}} \sigma((\lambda x.\,U_3') \circ (U_4' \circ V'))$. By `Assoc`-equivalence, this is $\sigma(((\lambda x.\,U_3) \circ U_4) \circ V) \Rightarrow_{\mathrm{par}} \sigma(((\lambda x.\,U_3') \circ U_4') \circ V')$. By rule `ParApp` (combined with $\sigma(U_2 \circ V) \Rightarrow_{\mathrm{par}} \sigma(U_2' \circ V')$): $\sigma(U \circ V) = \sigma(U_1 \circ V)\,\sigma(U_2 \circ V) \Rightarrow_{\mathrm{par}} \sigma(U_1' \circ V')\,\sigma(U_2' \circ V')$, where $U_1' = (\lambda x.\,U_3') \circ U_4'$. As in the `ParBeta` sub-case, this last term equals $\sigma(U' \circ V')$, since $U' = \sigma(U_1'U_2')$ (exactly `BetaClos` applied to $U_1'U_2' = ((\lambda x.\,U_3') \circ U_4')U_2'$ followed by $\sigma$-normalization) and the same `DApp`-equivalence applies. So $\sigma(U \circ V) \Rightarrow_{\mathrm{par}} \sigma(U' \circ V')$.

- *Via `ParComp$_\varepsilon$`.* $U_1 = \varepsilon(U_3)$, and there are $U_3', U_2'$ with $U_3 \Rightarrow_{\mathrm{par}} U_3'$, $U_2 \Rightarrow_{\mathrm{par}} U_2'$, $U' = U_3' \circ U_2'$. By the induction hypothesis (applied to $U_2, V$), $\sigma(U_2 \circ V) \Rightarrow_{\mathrm{par}} \sigma(U_2' \circ V')$. Since $U_3 \Rightarrow_{\mathrm{par}} U_3'$, rule `ParComp$_\varepsilon$` (taking its two premises to be $U_3 \Rightarrow_{\mathrm{par}} U_3'$ and $\sigma(U_2 \circ V) \Rightarrow_{\mathrm{par}} \sigma(U_2' \circ V')$) gives $\varepsilon(U_3)\,\sigma(U_2 \circ V) \Rightarrow_{\mathrm{par}} \sigma(U_3' \circ \sigma(U_2' \circ V')) = \sigma(U_3' \circ (U_2' \circ V'))$. Since $U = \varepsilon(U_3)U_2$ is `DApp`-shaped once composed with $V$, and $\varepsilon(U_3) \circ V$ reduces (via `Eps-eps`) directly to $\varepsilon(U_3)$, $\sigma(U \circ V) = \varepsilon(U_3)\,\sigma(U_2 \circ V)$. And $\sigma(U' \circ V') = \sigma((U_3' \circ U_2') \circ V') = \sigma(U_3' \circ (U_2' \circ V'))$ by `Assoc`-equivalence. So $\sigma(U \circ V) \Rightarrow_{\mathrm{par}} \sigma(U' \circ V')$.

**Case 9: $U = \varepsilon(U_1)$.** There is $U_1'$ with $U_1 \Rightarrow_{\mathrm{par}} U_1'$ and $U' = \varepsilon(U_1')$. Since $\varepsilon(U_1) \circ V$ reduces (via `Eps-eps`) directly to $\varepsilon(U_1)$, and likewise for $U' \circ V'$: $\sigma(U \circ V) = \varepsilon(U_1) \Rightarrow_{\mathrm{par}} \varepsilon(U_1') = \sigma(U' \circ V')$, by rule `ParEps`.

This exhausts every case (the "already $\sigma$-normal" cases and the nine listed shapes together cover every possible pair $(U, V)$ of $\sigma$-normal forms), so $\sigma(U \circ V) \Rightarrow_{\mathrm{par}} \sigma(U' \circ V')$ holds whenever $U \Rightarrow_{\mathrm{par}} U'$ and $V \Rightarrow_{\mathrm{par}} V'$.

#### End of Proof.

---

## Remarks and Adjustments Made to the Source Material

- **Missing side condition in the "already normal" cases restored.** The scanned source's description of when $\sigma(U \circ V) = U \circ V$ states only "$U = \lambda x.\,U_1$" or "$U = x$ and $V$ is not an environment extension", without mentioning $V \neq \mathsf{id}$. Since $V = \mathsf{id}$ is listed as its own, separate case (Case 4, where $U \circ V$ is *not* already normal, e.g. $(\lambda x.\,U_1) \circ \mathsf{id} \to_{\sigma} U_1$), this document adds $V \neq \mathsf{id}$ as an explicit conjunct to both "already normal" sub-cases, so that the two branches of the case split (already normal vs. not) are mutually exclusive and jointly exhaustive.
- **Normalization step made explicit for `ParBetaClos`'s inner application of the lemma.** The scanned source applies the (inductive) lemma to the pair $(\lambda x.\,U_3,\, U_4 \circ V)$ directly, but the lemma's own hypotheses require its second argument to already be a $\sigma$-normal form, which $U_4 \circ V$ is not in general. This document routes through $\sigma(U_4 \circ V)$ explicitly (using the previously-established $\sigma(U_4 \circ V) \Rightarrow_{\mathrm{par}} \sigma(U_4' \circ V')$ as the actual second hypothesis of that inner application), and notes that $\sigma(P \circ \sigma(Q)) = \sigma(P \circ Q)$ makes this equivalent to the source's more compressed presentation.
- **Beta/BetaClos target rewritten via `DApp`-equivalence, stated explicitly.** In the `ParBeta` and `ParBetaClos` sub-cases of Case 8, the scanned source asserts the final equality (that the `ParApp`-combined term equals $\sigma(U' \circ V')$) without spelling out why. This document adds the one-line justification: $U'$ is, by construction, the $\sigma$-normal form of a `Beta`/`BetaClos` redex, so $\sigma(U' \circ V')$ can be unfolded back through that same redex and then through `DApp`, landing on exactly the term already reached.
- **Typo corrected in the `x, (V₁/y)·V₂` case.** The scanned source's stated $V'$ in this case renders as "$(V_1'/x)\cdot V_2'$", reusing the bound variable $x$ where the extension's own key is $y$ (per the case's own heading, $V = (V_1/y)\cdot V_2$). This document reads it as $V' = (V_1'/y)\cdot V_2'$; the conclusion is unaffected either way, since it only depends on $V_2'$.
- **No constants involved.** As with every other reduction document in this repository, this lemma does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{Env}\varepsilon}$ has none (`docs/enve-syntax.md`).
