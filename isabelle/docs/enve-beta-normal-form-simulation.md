# Simulation of $\beta$-Reduction on $\sigma$-Normal Forms

This document states and proves thesis Theorem 7 (§2.4.4), presented here as a **Lemma** as requested: taking $\sigma$-normal forms (`docs/enve-sigma-normal-form.md`) turns every $\to_{\beta}$-step (`docs/enve-beta-over-sigma-reduction.md`) into a $\to_{\beta/\sigma}^{*}$-reduction. This is what makes $\sigma(-)$ a sound way to represent $\lambda_{\mathrm{Env}\varepsilon}$-computation purely in terms of $\sigma$-normal forms and $\to_{\beta/\sigma}$.

> **Note for AI-assisted formalization.**
> The induction is on $\mathrm{length}(M)$ (`docs/enve-term-length-measure.md`),
> case-split on the structure of $M$. Two auxiliary facts, both already
> available in this repository, are used repeatedly: the Length Decrease
> Lemma (`docs/enve-sigma-reduction-length-decrease.md`, thesis Theorem 3),
> to justify applying the induction hypothesis to a term produced by a
> $\sigma$-step rather than to a literal subterm; and a "safe context"
> observation (`Fact` below) that lets a $\to_{\beta/\sigma}^{*}$-reduction
> be lifted through `Lam`, `Eps`, `App`, or `Ext`, since none of those four
> constructors is ever itself the left-hand side of a $\sigma$-rule.

---

## Lemma (Simulation of $\beta$-Reduction on $\sigma$-Normal Forms)

For all $M, N \in \mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$, if $M \to_{\beta} N$, then $\sigma(M) \to_{\beta/\sigma}^{*} \sigma(N)$.

#### Proof.

By induction on $\mathrm{length}(M)$ (`docs/enve-term-length-measure.md`, thesis Definition 11), case-split on the structure of $M$.

**Fact (safe contexts).** None of `Lam`, `Eps`, `App`, `Ext` is ever the left-hand side of a base $\sigma$-rule (`docs/enve-reduction-sigma.md`: all eight base rules decompose a `Comp`-headed term). Consequently, $\sigma$-normalizing commutes with these four constructors -- e.g. $\sigma(\lambda x.\,P) = \lambda x.\,\sigma(P)$, $\sigma(PQ) = \sigma(P)\,\sigma(Q)$, and likewise for `Eps` and `Ext` -- and if $P \to_{\beta/\sigma}^{*} P'$ (for $\sigma$-normal forms $P, P'$), then $\lambda x.\,P \to_{\beta/\sigma}^{*} \lambda x.\,P'$, $\varepsilon(P) \to_{\beta/\sigma}^{*} \varepsilon(P')$, $P\,Q \to_{\beta/\sigma}^{*} P'\,Q$, $Q\,P \to_{\beta/\sigma}^{*} Q\,P'$, and $(P/x)\cdot Q \to_{\beta/\sigma}^{*} (P'/x)\cdot Q$, $(Q/x)\cdot P \to_{\beta/\sigma}^{*} (Q/x)\cdot P'$, for any fixed $\sigma$-normal form $Q$. (`Comp` is deliberately excluded from this Fact, since it *can* be a $\sigma$-redex depending on its left argument's shape -- this is exactly why the `Comp`-headed cases below need individual treatment rather than a blanket lift.)

### $M = \mathsf{id}$ or $M$ a variable

There is no $N$ with $M \to_{\beta} N$ (neither has a $\beta$-redex or a subterm to contain one), so this case is vacuous.

### $M = \lambda x.\,M_1$

Then $N = \lambda x.\,N_1$ for some $N_1$ with $M_1 \to_{\beta} N_1$. By the induction hypothesis, $\sigma(M_1) \to_{\beta/\sigma}^{*} \sigma(N_1)$. By the Fact, $\sigma(M) = \lambda x.\,\sigma(M_1) \to_{\beta/\sigma}^{*} \lambda x.\,\sigma(N_1) = \sigma(N)$.

### $M = \varepsilon(M_1)$

Then $N = \varepsilon(N_1)$ for some $N_1$ with $M_1 \to_{\beta} N_1$. By the induction hypothesis and the Fact: $\sigma(M) = \varepsilon(\sigma(M_1)) \to_{\beta/\sigma}^{*} \varepsilon(\sigma(N_1)) = \sigma(N)$.

### $M$ is `Comp`-headed ($M = M_1 \circ M_2$ for some $M_1, M_2$)

Case-split further on the shape of $M_1$ (and, where relevant, $M_2$), matching the eight base $\sigma$-rules plus one residual case.

**`Assoc`-shaped: $M = (M_1 \circ M_2) \circ M_3$.** By the Length Decrease Lemma's `Assoc` case, $\mathrm{length}(M) > \mathrm{length}(M_1 \circ (M_2 \circ M_3))$, so the induction hypothesis applies to $M_1 \circ (M_2 \circ M_3)$ once we exhibit a $\to_{\beta}$-step out of it. There are $N_1, N_2, N_3$ with $N = (N_1 \circ N_2) \circ N_3$ and one of
$$
M_1 \to_{\beta} N_1,\ M_2 = N_2,\ M_3 = N_3
\quad\text{or}\quad
M_1 = N_1,\ M_2 \to_{\beta} N_2,\ M_3 = N_3
\quad\text{or}\quad
M_1 = N_1,\ M_2 = N_2,\ M_3 \to_{\beta} N_3.
$$
In every case, lifting the single changed part through the corresponding congruence position gives $M_1 \circ (M_2 \circ M_3) \to_{\beta} N_1 \circ (N_2 \circ N_3)$, so the induction hypothesis yields $\sigma(M_1 \circ (M_2 \circ M_3)) \to_{\beta/\sigma}^{*} \sigma(N_1 \circ (N_2 \circ N_3))$. Since $\sigma(M) = \sigma(M_1 \circ (M_2 \circ M_3))$ (as $M \to_{\sigma} M_1 \circ (M_2 \circ M_3)$ via `Assoc`) and likewise $\sigma(N) = \sigma(N_1 \circ (N_2 \circ N_3))$, this gives $\sigma(M) \to_{\beta/\sigma}^{*} \sigma(N)$.

**`IdL`-shaped: $M = \mathsf{id} \circ M_1$.** $\sigma(M) = \sigma(M_1)$. $N = \mathsf{id} \circ N_1$ for some $N_1$ with $M_1 \to_{\beta} N_1$; $\sigma(N) = \sigma(N_1)$. By the induction hypothesis (applied to the subterm $M_1$), $\sigma(M) = \sigma(M_1) \to_{\beta/\sigma}^{*} \sigma(N_1) = \sigma(N)$.

**`IdR`-shaped: $M = M_1 \circ \mathsf{id}$.** Symmetric to `IdL`: $\sigma(M) = \sigma(M_1) \to_{\beta/\sigma}^{*} \sigma(N_1) = \sigma(N)$, using the induction hypothesis on the subterm $M_1$.

**`DExtn`-shaped: $M = ((M_1/x)\cdot M_2) \circ M_3$.** $\sigma(M) = ((\sigma(M_1 \circ M_3))/x)\cdot(\sigma(M_2 \circ M_3))$ (since $M \to_{\sigma} ((M_1 \circ M_3)/x)\cdot(M_2 \circ M_3)$ via `DExtn`, and $\sigma$ of an `Ext`-headed term is `Ext` of the normalized parts, by the Fact). By the `DExtn` case of the Length Decrease Lemma, $\mathrm{length}(M_1 \circ M_3) < \mathrm{length}(M)$ and $\mathrm{length}(M_2 \circ M_3) < \mathrm{length}(M)$ (each is smaller than their sum, which is already smaller than $\mathrm{length}(M)$), so the induction hypothesis applies to both. There are $N_1, N_2, N_3$ with $N = ((N_1/x)\cdot N_2) \circ N_3$ and one of
$$
M_1 \to_{\beta} N_1,\ M_2 = N_2,\ M_3 = N_3
\quad\text{or}\quad
M_1 = N_1,\ M_2 \to_{\beta} N_2,\ M_3 = N_3
\quad\text{or}\quad
M_1 = N_1,\ M_2 = N_2,\ M_3 \to_{\beta} N_3.
$$
In each case, lifting through `CompL`/`CompR` gives $M_1 \circ M_3 \to_{\beta} N_1 \circ N_3$ and/or $M_2 \circ M_3 \to_{\beta} N_2 \circ N_3$ as appropriate (the unchanged side being literally equal), so the induction hypothesis gives $\sigma(M_1 \circ M_3) \to_{\beta/\sigma}^{*} \sigma(N_1 \circ N_3)$ and $\sigma(M_2 \circ M_3) \to_{\beta/\sigma}^{*} \sigma(N_2 \circ N_3)$ (the latter trivially, by equality, whenever that side did not change). Lifting both through the Fact (for `Ext`) gives $\sigma(M) \to_{\beta/\sigma}^{*} \sigma(N)$.

**`VarRef`-shaped: $M = x \circ ((M_1/x)\cdot M_2)$.** $\sigma(M) = \sigma(M_1)$. There are $N_1, N_2$ with $N = x \circ ((N_1/x)\cdot N_2)$ and either $M_1 \to_{\beta} N_1, M_2 = N_2$, or $M_1 = N_1, M_2 \to_{\beta} N_2$. In the first case, $\sigma(N) = \sigma(N_1)$, and the induction hypothesis (on the subterm $M_1$) gives $\sigma(M) = \sigma(M_1) \to_{\beta/\sigma}^{*} \sigma(N_1) = \sigma(N)$. In the second case, $M_1 = N_1$ gives $\sigma(M) = \sigma(M_1) = \sigma(N_1) = \sigma(N)$ directly (zero steps), since $M_2$ plays no role in the normal form of a `VarRef`-shaped term. Either way, $\sigma(M) \to_{\beta/\sigma}^{*} \sigma(N)$.

**`VarSkip`-shaped: $M = x \circ ((M_1/y)\cdot M_2)$, $x \neq y$.** $\sigma(M) = x \circ \sigma(M_2)$. There are $N_1, N_2$ with $N = x \circ ((N_1/y)\cdot N_2)$ and either $M_1 \to_{\beta} N_1, M_2 = N_2$, or $M_1 = N_1, M_2 \to_{\beta} N_2$. In the first case, $M_2 = N_2$ gives $\sigma(M) = x \circ \sigma(M_2) = x \circ \sigma(N_2) = \sigma(N)$ directly, since $M_1$ plays no role in the normal form of a `VarSkip`-shaped term. In the second case, the induction hypothesis (on the subterm $M_2$) gives $\sigma(M_2) \to_{\beta/\sigma}^{*} \sigma(N_2)$, so $\sigma(M) = x \circ \sigma(M_2) \to_{\beta/\sigma}^{*} x \circ \sigma(N_2) = \sigma(N)$ (lifting through `App` via the Fact, treating $x$ as a fixed left argument). Either way, $\sigma(M) \to_{\beta/\sigma}^{*} \sigma(N)$.

**`DApp`-shaped: $M = (M_1 M_2) \circ M_3$.** $\sigma(M) = \sigma(M_1 \circ M_3)\,\sigma(M_2 \circ M_3)$ (since $M \to_{\sigma} (M_1 \circ M_3)(M_2 \circ M_3)$ via `DApp`, and $\sigma$ of an `App`-headed term is `App` of the normalized parts). By the `DApp` case of the Length Decrease Lemma, $\mathrm{length}(M_1 \circ M_3) < \mathrm{length}(M)$ and $\mathrm{length}(M_2 \circ M_3) < \mathrm{length}(M)$, so the induction hypothesis applies to both. There are $N_1, N_2, N_3$ with $N = (N_1 N_2) \circ N_3$ and one of
$$
M_1 \to_{\beta} N_1,\ M_2 = N_2,\ M_3 = N_3
\quad\text{or}\quad
M_1 = N_1,\ M_2 \to_{\beta} N_2,\ M_3 = N_3
\quad\text{or}\quad
M_1 = N_1,\ M_2 = N_2,\ M_3 \to_{\beta} N_3.
$$
As in the `DExtn` case, this lifts to $M_1 \circ M_3 \to_{\beta} N_1 \circ N_3$ and/or $M_2 \circ M_3 \to_{\beta} N_2 \circ N_3$, so the induction hypothesis and the Fact (for `App`) give $\sigma(M) = \sigma(M_1 \circ M_3)\,\sigma(M_2 \circ M_3) \to_{\beta/\sigma}^{*} \sigma(N_1 \circ N_3)\,\sigma(N_2 \circ N_3) = \sigma(N)$.

**`Eps-eps`-shaped: $M = \varepsilon(M_1) \circ M_2$.** $\sigma(M) = \varepsilon(\sigma(M_1))$. There are $N_1, N_2$ with $N = \varepsilon(N_1) \circ N_2$ and either $M_1 \to_{\beta} N_1, M_2 = N_2$, or $M_1 = N_1, M_2 \to_{\beta} N_2$. In the first case, $\sigma(N) = \varepsilon(\sigma(N_1))$, and the induction hypothesis (on the subterm $M_1$) plus the Fact (for `Eps`) give $\sigma(M) = \varepsilon(\sigma(M_1)) \to_{\beta/\sigma}^{*} \varepsilon(\sigma(N_1)) = \sigma(N)$. In the second case, $M_1 = N_1$ gives $\sigma(M) = \varepsilon(\sigma(M_1)) = \varepsilon(\sigma(N_1)) = \sigma(N)$ directly, since $M_2$ plays no role in the normal form of an `Eps-eps`-shaped term. Either way, $\sigma(M) \to_{\beta/\sigma}^{*} \sigma(N)$.

**Other (none of the eight patterns above apply): $M = M_1 \circ M_2$.** Then $M_1 \circ M_2$ is already $\sigma$-irreducible at the root (it matches neither `Assoc`, `IdL`, `DExtn`, `VarRef`/`VarSkip`, `DApp`, nor `Eps-eps` -- meaning $M_1$ is either `Lam`-headed, or `Var`-headed with $M_2$ not an environment extension -- and $M_2 \neq \mathsf{id}$ rules out `IdR`), so $\sigma(M) = \sigma(M_1) \circ \sigma(M_2)$. There are $N_1, N_2$ with $N = N_1 \circ N_2$ and either $M_1 \to_{\beta} N_1, M_2 = N_2$, or $M_1 = N_1, M_2 \to_{\beta} N_2$. By the induction hypothesis on whichever side changed (and equality on the other), $\sigma(M) = \sigma(M_1) \circ \sigma(M_2) \to_{\beta/\sigma}^{*} \sigma(N_1) \circ \sigma(N_2) = \sigma(N)$ (lifting the change through `Comp` with the other, fixed, side -- justified directly here since $M_1$'s safe shape, `Lam`- or `Var`-headed, is exactly what makes composing with a normal form on the right safe, per the case analysis of `docs/enve-sigma-normal-form-grammar.md`).

### $M$ is `App`-headed ($M = M_1 M_2$ for some $M_1, M_2$)

Case-split on the rule used to derive $M \to_{\beta} N$.

**`Beta`.** $M = (\lambda x.\,M_1)M_2$, $N = M_1 \circ ((M_2/x)\cdot \mathsf{id})$. Since `App` is never itself a $\sigma$-redex, $\sigma(M) = (\lambda x.\,\sigma(M_1))\,\sigma(M_2)$. This is exactly a `Beta` redex, so $\sigma(M) \to_{\beta} \sigma(M_1) \circ ((\sigma(M_2)/x)\cdot \mathsf{id})$; normalizing (the $\sigma$-step of $\to_{\beta/\sigma}$) gives $\sigma(M) \to_{\beta/\sigma} \sigma\big(\sigma(M_1) \circ ((\sigma(M_2)/x)\cdot \mathsf{id})\big) = \sigma\big(M_1 \circ ((M_2/x)\cdot \mathsf{id})\big) = \sigma(N)$ (normalizing subterms first does not change the final $\sigma$-normal form of the whole).

**`BetaClos`.** $M = ((\lambda x.\,M_1) \circ M_3)M_2$, $N = M_1 \circ ((M_2/x)\cdot M_3)$. As above, $\sigma(M) = ((\lambda x.\,\sigma(M_1)) \circ \sigma(M_3))\,\sigma(M_2)$, a `BetaClos` redex: $\sigma(M) \to_{\beta} \sigma(M_1) \circ ((\sigma(M_2)/x)\cdot \sigma(M_3))$, and normalizing gives $\sigma(M) \to_{\beta/\sigma} \sigma\big(M_1 \circ ((M_2/x)\cdot M_3)\big) = \sigma(N)$.

**`Comp` ($\mathrm{Comp}_{\varepsilon}$).** $M = \varepsilon(M_1)M_2$, $N = M_1 \circ M_2$. $\sigma(M) = \varepsilon(\sigma(M_1))\,\sigma(M_2)$, a $\mathrm{Comp}_{\varepsilon}$ redex: $\sigma(M) \to_{\beta} \sigma(M_1) \circ \sigma(M_2)$, and normalizing gives $\sigma(M) \to_{\beta/\sigma} \sigma(M_1 \circ M_2) = \sigma(N)$.

**`AppL`.** $M = M_1 M_2$, $N = N_1 M_2$, from $M_1 \to_{\beta} N_1$. By the induction hypothesis, $\sigma(M_1) \to_{\beta/\sigma}^{*} \sigma(N_1)$. By the Fact, $\sigma(M) = \sigma(M_1)\,\sigma(M_2) \to_{\beta/\sigma}^{*} \sigma(N_1)\,\sigma(M_2) = \sigma(N)$.

**`AppR`.** $M = M_1 M_2$, $N = M_1 N_2$, from $M_2 \to_{\beta} N_2$. Symmetric to `AppL`: $\sigma(M) = \sigma(M_1)\,\sigma(M_2) \to_{\beta/\sigma}^{*} \sigma(M_1)\,\sigma(N_2) = \sigma(N)$.

### $M$ is `Ext`-headed ($M = (M_1/x)\cdot M_2$ for some $M_1, M_2$)

There are $N_1, N_2$ with $N = (N_1/x)\cdot N_2$ and either $M_1 \to_{\beta} N_1, M_2 = N_2$, or $M_1 = N_1, M_2 \to_{\beta} N_2$. In the first case, the induction hypothesis gives $\sigma(M_1) \to_{\beta/\sigma}^{*} \sigma(N_1)$; in the second, $\sigma(M_2) \to_{\beta/\sigma}^{*} \sigma(N_2)$. Either way, by the Fact (for `Ext`), $\sigma(M) = (\sigma(M_1)/x)\cdot \sigma(M_2) \to_{\beta/\sigma}^{*} (\sigma(N_1)/x)\cdot \sigma(N_2) = \sigma(N)$.

This exhausts every constructor of $\mathbf{Term}(\lambda_{\mathrm{Env}\varepsilon})$, so $\sigma(M) \to_{\beta/\sigma}^{*} \sigma(N)$ holds whenever $M \to_{\beta} N$.

#### End of Proof.

---

## Remarks and Adjustments Made to the Source Material

- **`DApp` case's target shape corrected.** In the `DApp`-shaped case of the `Comp`-headed branch, the scanned source renders the derived term $N$ as "$(N_1 \circ N_2) \circ N_3$", using `Comp` where the whole case is about $M = (M_1 M_2) \circ M_3$, i.e. `App`-inside-`Comp`. Since none of the rules involved (`AppL`, `AppR`, `CompR`) turn an `App` node into a `Comp` node, and the rest of that case's argument explicitly reasons about $M_1 \circ M_3$ and $M_2 \circ M_3$ (pairing $M_1$, $M_2$ individually with $M_3$, exactly as `DApp`'s own right-hand side does), this document reads $N$ as $(N_1 N_2) \circ N_3$ (keeping the inner node `App`-headed, matching $M$'s shape) instead.
- **$\sigma(M_1)\circ\sigma(M_3)$ notation clarified as $\sigma(M_1 \circ M_3)$.** In the same `DApp` case, the source's formula for $\sigma(M)$ is read as $\sigma(M_1 \circ M_3)\,\sigma(M_2 \circ M_3)$ (normalizing each full composition), matching how the rest of that case's argument consistently writes $\sigma(M_1 \circ M_3)$ and $\sigma(N_1 \circ N_3)$, rather than as literally "$\sigma(M_1) \circ \sigma(M_3)$" (composing two already-normalized terms without a further normalization step), since the latter is not guaranteed to already be $\sigma$-irreducible.
- **Auxiliary "safe context" Fact made explicit.** The source repeatedly lifts a $\to_{\beta/\sigma}^{*}$ (or $\to_{\beta}$) step through `Lam`, `Eps`, `App`, or `Ext` without restating why this is valid. This document states it once, up front, as the Fact, and is careful to note that `Comp` is *not* such a safe context in general (which is exactly why the `Comp`-headed cases are handled one $\sigma$-rule-shape at a time instead).
- **No constants involved.** As with every other reduction document in this repository, this lemma does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{Env}\varepsilon}$ has none (`docs/enve-syntax.md`).
- **`Other` case's classification-by-syntax replaced with a general argument in the formalization.** The `Other` case above classifies $\sigma(M) = \sigma(M_1) \circ \sigma(M_2)$ by the *syntactic* shape of $M_1$ (`Lam`-/`Var`-headed) and $M_2$ ($\neq \mathsf{id}$ syntactically) -- but since $M$ here is arbitrary (not assumed already $\sigma$-normal), $M_2$ can itself $\sigma$-normalize down to $\mathsf{id}$ or to an environment extension even though it is not syntactically one, in which case a further $\sigma$-step (`IdR` or `DExtn`/`VarRef`/`VarSkip`) still applies once $M_2$ is normalized, making the syntactic classification unsound as stated. Rather than re-deriving this case split in terms of $\sigma(M_2)$'s own shape, the Isabelle formalization (`EnvEps_Beta_Normal_Form_Simulation.thy`) instead proves both `Comp` congruence cases (`CompL`/`CompR`) at once via a general chain lemma that round-trips each side through $\Rightarrow_{\mathrm{par}}$'s already-proven, fully general composition-compatibility fact (roadmap item 22), which handles every $\sigma(M_2)$-shape case exhaustively already. No rule-by-rule case split on $M$'s own `Comp`-shape (`Assoc`/`IdL`/`IdR`/`DExtn`/`VarRef`/`VarSkip`/`DApp`/`Eps-eps`/`Other` above) is needed at that level.
