# Parallel Reduction on $\sigma$-Normal Forms of $\lambda_{\mathrm{Env}\varepsilon}$

This document records thesis Definition 14 (§2.4.5): a relation $\Rightarrow_{\mathrm{par}}$, called **parallel reduction**, defined only between $\sigma$-normal forms of $\lambda_{\mathrm{Env}\varepsilon}$ (`docs/enve-sigma-normal-form-grammar.md`, thesis equation (2.32)).

> **Note.** This relation is written $\Rightarrow_{\mathrm{par}}$ (a double
> arrow), to distinguish it from all of the single-arrow reduction
> relations defined elsewhere in this repository ($\to_{\sigma}$,
> $\to_{\beta\sigma}$, $\to_{\beta}$, $\to_{\beta/\sigma}$). Throughout this
> document, $x$ ranges over $\mathbf{Var}$, and $U, V, W, U', V', W'$ range
> over $\sigma$-normal forms of $\lambda_{\mathrm{Env}\varepsilon}$.

> **Note for AI-assisted formalization.**
> $\Rightarrow_{\mathrm{par}}$ has exactly one rule per production of the
> $\sigma$-normal-form grammar (2.32) -- `ParVar`, `ParId`, `ParLam`,
> `ParEps`, `ParApp`, `ParExtn`, `ParLamComp`, `ParVarComp` -- plus three
> further rules, `ParBeta`, `ParBetaClos`, `ParComp$_\varepsilon$`, that
> perform one parallel $\beta$-contraction. Every rule whose conclusion
> could produce a term outside the grammar (2.32) -- because a
> subterm changed shape during the recursive $\Rightarrow_{\mathrm{par}}$ steps in its
> premises -- explicitly re-normalizes with $\sigma(-)$ (`docs/enve-sigma-normal-form.md`)
> before being stated, so every conclusion is guaranteed to itself be a
> $\sigma$-normal form.

---

#### Definition (Parallel Reduction)

For $\sigma$-normal forms of $\lambda_{\mathrm{Env}\varepsilon}$, the relation $\Rightarrow_{\mathrm{par}}$ is defined by the following rules.

### Reflexivity rules

$$
\begin{prooftree}
\AxiomC{}
\RightLabel{ParVar}
\UnaryInfC{$x \Rightarrow_{\mathrm{par}} x$}
\end{prooftree}
\qquad\qquad
\begin{prooftree}
\AxiomC{}
\RightLabel{ParId}
\UnaryInfC{$\mathsf{id} \Rightarrow_{\mathrm{par}} \mathsf{id}$}
\end{prooftree}
$$

### Structural (congruence) rules

$$
\begin{prooftree}
\AxiomC{$U \Rightarrow_{\mathrm{par}} U'$}
\RightLabel{ParLam}
\UnaryInfC{$\lambda x.\,U \Rightarrow_{\mathrm{par}} \lambda x.\,U'$}
\end{prooftree}
\qquad\qquad
\begin{prooftree}
\AxiomC{$U \Rightarrow_{\mathrm{par}} U'$}
\RightLabel{ParEps}
\UnaryInfC{$\varepsilon(U) \Rightarrow_{\mathrm{par}} \varepsilon(U')$}
\end{prooftree}
$$

$$
\begin{prooftree}
\AxiomC{$U \Rightarrow_{\mathrm{par}} U'$}
\AxiomC{$V \Rightarrow_{\mathrm{par}} V'$}
\RightLabel{ParApp}
\BinaryInfC{$U\,V \Rightarrow_{\mathrm{par}} U'\,V'$}
\end{prooftree}
\qquad\qquad
\begin{prooftree}
\AxiomC{$U \Rightarrow_{\mathrm{par}} U'$}
\AxiomC{$V \Rightarrow_{\mathrm{par}} V'$}
\RightLabel{ParExtn}
\BinaryInfC{$(U/x)\cdot V \Rightarrow_{\mathrm{par}} (U'/x)\cdot V'$}
\end{prooftree}
$$

$$
\begin{prooftree}
\AxiomC{$U \Rightarrow_{\mathrm{par}} U'$}
\AxiomC{$V \Rightarrow_{\mathrm{par}} V'$}
\AxiomC{$V \neq \mathsf{id}$}
\RightLabel{ParLamComp}
\TrinaryInfC{$(\lambda x.\,U) \circ V \Rightarrow_{\mathrm{par}} \sigma((\lambda x.\,U') \circ V')$}
\end{prooftree}
$$

$$
\begin{prooftree}
\AxiomC{$W \Rightarrow_{\mathrm{par}} W'$}
\AxiomC{$W$ is not an environment extension}
\RightLabel{ParVarComp}
\BinaryInfC{$x \circ W \Rightarrow_{\mathrm{par}} \sigma(x \circ W')$}
\end{prooftree}
$$

### Parallel $\beta$-contraction rules

$$
\begin{prooftree}
\AxiomC{$U \Rightarrow_{\mathrm{par}} U'$}
\AxiomC{$V \Rightarrow_{\mathrm{par}} V'$}
\RightLabel{ParBeta}
\BinaryInfC{$(\lambda x.\,U)\,V \Rightarrow_{\mathrm{par}} \sigma(U' \circ ((V'/x)\cdot \mathsf{id}))$}
\end{prooftree}
$$

$$
\begin{prooftree}
\AxiomC{$U \Rightarrow_{\mathrm{par}} U'$}
\AxiomC{$V \Rightarrow_{\mathrm{par}} V'$}
\AxiomC{$W \Rightarrow_{\mathrm{par}} W'$}
\RightLabel{ParBetaClos}
\TrinaryInfC{$((\lambda x.\,U) \circ W)\,V \Rightarrow_{\mathrm{par}} \sigma(U' \circ ((V'/x)\cdot W'))$}
\end{prooftree}
$$

$$
\begin{prooftree}
\AxiomC{$U \Rightarrow_{\mathrm{par}} U'$}
\AxiomC{$V \Rightarrow_{\mathrm{par}} V'$}
\RightLabel{ParComp$_{\varepsilon}$}
\BinaryInfC{$\varepsilon(U)\,V \Rightarrow_{\mathrm{par}} \sigma(U' \circ V')$}
\end{prooftree}
$$

---

## Why Every Rule Preserves $\sigma$-Normality

Each of the eight non-$\beta$ rules (`ParVar`, `ParId`, `ParLam`, `ParEps`, `ParApp`, `ParExtn`, `ParLamComp`, `ParVarComp`) corresponds to exactly one of the eight productions of grammar (2.32) (`docs/enve-sigma-normal-form-grammar.md`). For the four purely structural rules (`ParLam`, `ParEps`, `ParApp`, `ParExtn`), the conclusion is automatically a $\sigma$-normal form of the matching shape whenever the premises' outputs $U', V'$ are, since none of `Lam`, `Eps`, `App`, `Ext` can themselves be reduced by a $\sigma$-rule (`docs/enve-reduction-sigma.md`; see also the "safe context" observation in `docs/enve-beta-normal-form-simulation.md`). The two `Comp`-producing rules (`ParLamComp`, `ParVarComp`) and the three $\beta$-contraction rules, by contrast, *can* produce a term that is momentarily not $\sigma$-normal (e.g. if `ParLamComp`'s $V'$ turned out to equal $\mathsf{id}$, or `ParBeta`'s substitution happened to create a further $\sigma$-redex) -- which is exactly why each of those five rules' conclusions is wrapped in $\sigma(-)$, forcing the result back to the (unique) $\sigma$-normal form before the rule's conclusion is stated.

---

## Remarks and Adjustments Made to the Source Material

- **No content issues found.** Each rule was checked against the corresponding production of grammar (2.32) (`docs/enve-sigma-normal-form-grammar.md`) and, for the three $\beta$-contraction rules, against the `Beta`/`BetaClos`/`Comp$_\varepsilon$` rules of `docs/enve-reduction-beta-sigma.md`; all side conditions (`ParLamComp`'s $V \neq \mathsf{id}$, `ParVarComp`'s "$W$ is not an environment extension") match the grammar's own side conditions on its two `Comp`-shaped productions exactly. No corrections were necessary.
- **Notation.** Per the request, this relation is written $\Rightarrow_{\mathrm{par}}$ throughout (a double arrow, as in the thesis), kept visually and notationally distinct from the single-arrow relations $\to_{\sigma}$, $\to_{\beta\sigma}$, $\to_{\beta}$, and $\to_{\beta/\sigma}$ defined elsewhere in this repository.
- **No constants involved.** As with every other reduction document in this repository, this definition does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{Env}\varepsilon}$ has none (`docs/enve-syntax.md`).
