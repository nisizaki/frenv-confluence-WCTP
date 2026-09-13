# Reflexivity of Parallel Reduction on $\sigma$-Normal Forms

This document states and proves thesis Lemma 6 (§2.4.5): every $\sigma$-normal form of $\lambda_{\mathrm{Env}\varepsilon}$ (`docs/enve-sigma-normal-form-grammar.md`) parallel-reduces to itself under $\Rightarrow_{\mathrm{par}}$ (`docs/enve-parallel-reduction.md`). This is the fact that lets $\Rightarrow_{\mathrm{par}}$ play the role of an (extended) identity step alongside its $\beta$-contracting rules, and it is exactly what is needed, together with the diamond property, to relate $\Rightarrow_{\mathrm{par}}^{*}$ to $\to_{\beta/\sigma}^{*}$.

> **Note for AI-assisted formalization.**
> The proof is a single structural induction with one case per production
> of grammar (2.32) (`docs/enve-sigma-normal-form-grammar.md`), each case
> applying exactly the correspondingly-named rule of $\Rightarrow_{\mathrm{par}}$
> (`docs/enve-parallel-reduction.md`) to the induction hypothesis. No case
> needs anything beyond that -- in particular, the side conditions of
> `ParLamComp` and `ParVarComp` are automatically satisfied because $U$ is
> already assumed to be a $\sigma$-normal form of the matching grammar
> production, which carries exactly those side conditions built in.

---

## Lemma (Reflexivity of Parallel Reduction)

For every $\sigma$-normal form $U$ of $\lambda_{\mathrm{Env}\varepsilon}$, $U \Rightarrow_{\mathrm{par}} U$.

#### Proof.

By induction on the structure of $U$, case-split according to grammar (2.32) (`docs/enve-sigma-normal-form-grammar.md`).

**$U = \mathsf{id}$.** By rule `ParId`, $U \Rightarrow_{\mathrm{par}} U$.

**$U = x$.** By rule `ParVar`, $U \Rightarrow_{\mathrm{par}} U$.

**$U = (U_1/x)\cdot U_2$.** By the induction hypothesis, $U_1 \Rightarrow_{\mathrm{par}} U_1$ and $U_2 \Rightarrow_{\mathrm{par}} U_2$. So, by rule `ParExtn`, $U \Rightarrow_{\mathrm{par}} U$.

**$U = \lambda x.\,U_1$.** By the induction hypothesis, $U_1 \Rightarrow_{\mathrm{par}} U_1$. So, by rule `ParLam`, $U \Rightarrow_{\mathrm{par}} U$.

**$U = U_1 U_2$.** By the induction hypothesis, $U_1 \Rightarrow_{\mathrm{par}} U_1$ and $U_2 \Rightarrow_{\mathrm{par}} U_2$. So, by rule `ParApp`, $U \Rightarrow_{\mathrm{par}} U$.

**$U = (\lambda x.\,U_1) \circ U_2$.** By the induction hypothesis, $U_1 \Rightarrow_{\mathrm{par}} U_1$ and $U_2 \Rightarrow_{\mathrm{par}} U_2$. Since $U$ is (by assumption) a $\sigma$-normal form of this grammar production, $U_2 \neq \mathsf{id}$ holds automatically, so rule `ParLamComp` applies, giving $U \Rightarrow_{\mathrm{par}} \sigma((\lambda x.\,U_1) \circ U_2) = \sigma(U) = U$ (the last equality because $U$ is already $\sigma$-normal). So $U \Rightarrow_{\mathrm{par}} U$.

**$U = x \circ U_1$.** By the induction hypothesis, $U_1 \Rightarrow_{\mathrm{par}} U_1$. Since $U$ is (by assumption) a $\sigma$-normal form of this grammar production, $U_1$ is automatically not an environment extension, so rule `ParVarComp` applies, giving $U \Rightarrow_{\mathrm{par}} \sigma(x \circ U_1) = \sigma(U) = U$. So $U \Rightarrow_{\mathrm{par}} U$.

**$U = \varepsilon(U_1)$.** By the induction hypothesis, $U_1 \Rightarrow_{\mathrm{par}} U_1$. So, by rule `ParEps`, $U \Rightarrow_{\mathrm{par}} U$.

This covers every production of grammar (2.32), so $U \Rightarrow_{\mathrm{par}} U$ holds for every $\sigma$-normal form $U$.

#### End of Proof.

---

## Remarks and Adjustments Made to the Source Material

- **Side conditions made explicit.** The scanned source applies `ParLamComp` and `ParVarComp` directly without commenting on their side conditions ($V \neq \mathsf{id}$ and "$W$ is not an environment extension", respectively, per `docs/enve-parallel-reduction.md`). This document adds a one-sentence justification in each of those two cases: since $U$ is assumed to be a $\sigma$-normal form matching that exact grammar production, and grammar (2.32) already bakes in those same side conditions on that production, they hold for free and need no separate argument.
- **No other changes.** Every other case matches its corresponding rule and grammar production exactly; no corrections were needed.
- **No constants involved.** As with every other reduction document in this repository, this lemma does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{Env}\varepsilon}$ has none (`docs/enve-syntax.md`).
