# Complete Development on $\sigma$-Normal Forms of $\lambda_{\mathrm{Env}\varepsilon}$

This document records thesis Definition 15 (§2.4.5, equations (2.52), (2.53)): a function that, given a $\sigma$-normal form (`docs/enve-sigma-normal-form-grammar.md`), contracts *every* $\beta$-redex present in it simultaneously, in one shot. This is the standard "complete development" construction used to prove that parallel reduction (`docs/enve-parallel-reduction.md`) has the diamond property.

> **Note on notation.** The thesis writes this function as a postfix star,
> $M^{*}$. As requested, this document instead writes it as a named
> prefix function, $\mathrm{cd}(M)$ ("complete development of $M$"), which
> renders unambiguously in plain Markdown/MathJax and is easier for an AI
> reader (or an Isabelle/HOL `fun` definition) to parse than an overloaded
> postfix operator. $\mathrm{cd}(M) = M^{*}$ throughout; the two notations
> name exactly the same function.

> **Note for AI-assisted formalization.**
> $\mathrm{cd}$ is defined by structural recursion on $\sigma$-normal forms
> (`docs/enve-sigma-normal-form-grammar.md`, grammar (2.32)), with one
> equation per production, exactly as `docs/enve-parallel-reduction.md`
> has one rule per production. In fact $\mathrm{cd}(M)$ is intended to be
> *the* result reached by developing every redex of $M$ at once via
> $\Rightarrow_{\mathrm{par}}$: informally, $M \Rightarrow_{\mathrm{par}} \mathrm{cd}(M)$, and
> $\mathrm{cd}(M)$ is the "most reduced" $\Rightarrow_{\mathrm{par}}$-successor of $M$ (used
> to prove the diamond property of $\Rightarrow_{\mathrm{par}}$: whenever $M \Rightarrow_{\mathrm{par}} P$,
> also $P \Rightarrow_{\mathrm{par}} \mathrm{cd}(M)$).

---

#### Definition (Complete Development, $\mathrm{cd}$)

For $\sigma$-normal forms $M, N$ of $\lambda_{\mathrm{Env}\varepsilon}$, the function $\mathrm{cd}$ is defined by structural recursion, one case per production of grammar (2.32):

$$
\begin{aligned}
\mathrm{cd}(x) &= x \\
\mathrm{cd}(\mathsf{id}) &= \mathsf{id} \\
\mathrm{cd}(\lambda x.\,M) &= \lambda x.\,\mathrm{cd}(M) \\
\mathrm{cd}(\varepsilon(M)) &= \varepsilon(\mathrm{cd}(M)) \\
\mathrm{cd}((M/x)\cdot N) &= (\mathrm{cd}(M)/x)\cdot \mathrm{cd}(N) \\
\mathrm{cd}(x \circ M) &= \sigma(x \circ \mathrm{cd}(M)) \\
\mathrm{cd}((\lambda x.\,M) \circ N) &= \sigma((\lambda x.\,\mathrm{cd}(M)) \circ \mathrm{cd}(N))
\end{aligned}
\tag{2.52}
$$

and, for the one remaining production, $M\,N$ (an application), $\mathrm{cd}(M\,N)$ is defined by a further case split on the shape of $M$:

$$
\mathrm{cd}(M\,N) =
\begin{cases}
\sigma\big(\mathrm{cd}(M_1) \circ ((\mathrm{cd}(N)/x)\cdot \mathsf{id})\big) & \text{if } M = \lambda x.\,M_1 \\[4pt]
\sigma\big(\mathrm{cd}(M_1) \circ ((\mathrm{cd}(N)/x)\cdot \mathrm{cd}(M_2))\big) & \text{if } M = (\lambda x.\,M_1) \circ M_2 \\[4pt]
\sigma\big(\mathrm{cd}(M_1) \circ \mathrm{cd}(N)\big) & \text{if } M = \varepsilon(M_1) \\[4pt]
\mathrm{cd}(M)\,\mathrm{cd}(N) & \text{otherwise}
\end{cases}
\tag{2.53}
$$

### Reading the definition

Equation (2.52) handles the six productions of grammar (2.32) that are never, by themselves, the site of a $\beta$-redex: `Var`, `Id`, `Lam`, `Eps`, `Ext`, and the two `Comp`-shaped productions `x ∘ M` and `(λx.M) ∘ N` (recall from `docs/enve-sigma-normal-form-grammar.md` that these are the *only* two shapes a `Comp`-headed $\sigma$-normal form can take). For `Lam`, `Eps`, and `Ext`, $\mathrm{cd}$ simply recurses into the subterms, since none of these three constructors is ever itself reducible. For the two `Comp`-shaped productions, $\mathrm{cd}$ recurses into the subterms and then re-normalizes with $\sigma(-)$, because developing the subterms can produce a term that is momentarily not $\sigma$-normal (exactly as in `docs/enve-parallel-reduction.md`'s `ParVarComp` and `ParLamComp` rules).

Equation (2.53) handles the eighth production, $M\,N$ (an application). Here $M$, being itself a $\sigma$-normal form, must have one of the shapes admitted by grammar (2.32); of those, only three enable an *immediate* $\beta$-redex once applied to $N$ -- $M = \lambda x.\,M_1$ (a `Beta` redex), $M = (\lambda x.\,M_1) \circ M_2$ (a `BetaClos` redex), and $M = \varepsilon(M_1)$ (a $\mathrm{Comp}_{\varepsilon}$ redex) -- and in each of those three cases, $\mathrm{cd}(M\,N)$ both contracts that redex *and* develops the subterms $M_1$ (and $M_2$, $N$) first, then re-normalizes with $\sigma(-)$. In every other case (`M` a variable, `M` an application, `M` an environment extension, or `M` a `Var`-headed `Comp`), $M\,N$ has no redex at its root, so $\mathrm{cd}(M\,N)$ is simply $\mathrm{cd}(M)\,\mathrm{cd}(N)$, with no further $\sigma$-normalization needed (an application of two already-$\sigma$-normal, non-redex-forming terms is itself $\sigma$-normal).

---

## Remarks and Adjustments Made to the Source Material

- **Notation changed from postfix $M^{*}$ to prefix $\mathrm{cd}(M)$.** As requested, this document does not use the thesis's postfix-star notation; it names the function $\mathrm{cd}$ ("complete development") and writes it prefix, $\mathrm{cd}(M)$, throughout.
- **Missing `Ext` case added.** The scanned source's equation (2.52) gives six defining equations, covering `Var`, `Id`, `Lam`, `Eps`, and the two `Comp`-shaped productions of grammar (2.32) -- but omits the seventh production, $(M/x)\cdot N$ (`Ext`). Since $\mathrm{cd}$ must be a *total* function on all $\sigma$-normal forms (all eight productions of the grammar) to serve its purpose (proving the diamond property of $\Rightarrow_{\mathrm{par}}$, `docs/enve-parallel-reduction.md`), this document adds the missing equation $\mathrm{cd}((M/x)\cdot N) = (\mathrm{cd}(M)/x)\cdot \mathrm{cd}(N)$, following exactly the same pattern as the `Lam` and `Eps` cases (`Ext` is never itself the left-hand side of a $\sigma$-rule, so no $\sigma$-normalization is needed after recursing).
- **No constants involved.** As with every other reduction document in this repository, this definition does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{Env}\varepsilon}$ has none (`docs/enve-syntax.md`).
