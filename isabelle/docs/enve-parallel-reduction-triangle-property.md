# Triangle Property of Parallel Reduction

This document states and proves thesis Theorem 10 (§2.4.5), presented here as a **Lemma** as requested: every parallel reduct of a $\sigma$-normal form $U$ (`docs/enve-parallel-reduction.md`) itself parallel-reduces to $U$'s complete development $\mathrm{cd}(U)$ (`docs/enve-complete-development.md`). This is the classical "triangle" (or "complete development") lemma that makes the diamond property of $\Rightarrow_{\mathrm{par}}$ immediate: whenever $U \Rightarrow_{\mathrm{par}} V_1$ and $U \Rightarrow_{\mathrm{par}} V_2$, both $V_1$ and $V_2$ reduce further, in parallel, to the *same* term $\mathrm{cd}(U)$.

> **Note.** As in `docs/enve-complete-development.md`, this document writes
> the complete development of $U$ as $\mathrm{cd}(U)$ rather than the
> thesis's postfix $U^{*}$; the two notations name the same function.

> **Note for AI-assisted formalization.**
> The proof is a structural induction on $U$, case-split on the rule used
> last in the derivation of $U \Rightarrow_{\mathrm{par}} V$ -- exactly mirroring the case
> split of `docs/enve-complete-development.md`'s own definition of
> $\mathrm{cd}$. Every case where $U$ is `Comp`-headed or where a $\beta$-rule
> fires needs the Composition Compatibility Lemma
> (`docs/enve-parallel-reduction-composition-compatibility.md`, thesis
> Lemma 7) to combine the pieces back together through $\sigma(-)$; every
> other case is a direct application of the matching rule of
> $\Rightarrow_{\mathrm{par}}$ to the induction hypothesis.

---

## Lemma (Triangle Property of Parallel Reduction)

Let $U, V$ be $\sigma$-normal forms of $\lambda_{\mathrm{Env}\varepsilon}$. If $U \Rightarrow_{\mathrm{par}} V$, then $V \Rightarrow_{\mathrm{par}} \mathrm{cd}(U)$.

#### Proof.

By induction on the structure of $U$, case-split on the rule used last in the derivation of $U \Rightarrow_{\mathrm{par}} V$.

**`ParId`.** $U = V = \mathsf{id}$. Since $\mathrm{cd}(\mathsf{id}) = \mathsf{id} = V$, rule `ParId` gives $V \Rightarrow_{\mathrm{par}} \mathrm{cd}(U)$.

**`ParVar`.** $U = x$. Since $\mathrm{cd}(x) = x = V$, rule `ParVar` gives $V \Rightarrow_{\mathrm{par}} \mathrm{cd}(U)$.

**`ParLam`.** $U = \lambda x.\,U_1$, $V = \lambda x.\,V_1$, from $U_1 \Rightarrow_{\mathrm{par}} V_1$. By the induction hypothesis, $V_1 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_1)$. So, by rule `ParLam`, $V = \lambda x.\,V_1 \Rightarrow_{\mathrm{par}} \lambda x.\,\mathrm{cd}(U_1) = \mathrm{cd}(U)$.

**`ParEps`.** $U = \varepsilon(U_1)$, $V = \varepsilon(V_1)$, from $U_1 \Rightarrow_{\mathrm{par}} V_1$. By the induction hypothesis, $V_1 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_1)$. So, by rule `ParEps`, $V = \varepsilon(V_1) \Rightarrow_{\mathrm{par}} \varepsilon(\mathrm{cd}(U_1)) = \mathrm{cd}(U)$.

**`ParApp`.** $U = U_1 U_2$, $V = V_1 V_2$, from $U_1 \Rightarrow_{\mathrm{par}} V_1$, $U_2 \Rightarrow_{\mathrm{par}} V_2$. By the induction hypothesis, $V_2 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_2)$. Sub-case on the shape of $U_1$ (matching `docs/enve-complete-development.md`'s own case split for $\mathrm{cd}(U_1U_2)$):

- *$U_1 = \lambda x.\,U_3$.* Since $U_1$ is `Lam`-headed, the only rule that could derive $U_1 \Rightarrow_{\mathrm{par}} V_1$ is `ParLam`, so $V_1 = \lambda x.\,V_3$ for some $V_3$ with $U_3 \Rightarrow_{\mathrm{par}} V_3$. By the induction hypothesis, $V_3 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_3)$. So, by rule `ParBeta` (with premises $V_3 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_3)$ and $V_2 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_2)$): $V = (\lambda x.\,V_3)V_2 \Rightarrow_{\mathrm{par}} \sigma(\mathrm{cd}(U_3) \circ ((\mathrm{cd}(U_2)/x)\cdot \mathsf{id})) = \mathrm{cd}(U)$.

- *$U_1 = (\lambda x.\,U_3) \circ U_4$.* Since $U_1$ is `Comp`-headed with `Lam`-headed left argument, the only rule deriving $U_1 \Rightarrow_{\mathrm{par}} V_1$ is `ParLamComp`, so $V_1 = \sigma((\lambda x.\,V_3) \circ V_4)$ for some $V_3, V_4$ with $U_3 \Rightarrow_{\mathrm{par}} V_3$, $U_4 \Rightarrow_{\mathrm{par}} V_4$. By the induction hypothesis, $V_3 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_3)$ and $V_4 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_4)$. By the Composition Compatibility Lemma (thesis Lemma 7, applied with $\lambda x.\,V_3 \Rightarrow_{\mathrm{par}} \lambda x.\,\mathrm{cd}(U_3)$ via `ParLam`, and $V_4 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_4)$): $V_1 = \sigma((\lambda x.\,V_3) \circ V_4) \Rightarrow_{\mathrm{par}} \sigma((\lambda x.\,\mathrm{cd}(U_3)) \circ \mathrm{cd}(U_4))$. By rule `ParBetaClos` (with this and $V_2 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_2)$ as premises -- taking the intermediate reduct of $V_1$ as its "$V_1$"): $V = ((\lambda x.\,V_3) \circ U_4)V_2 \Rightarrow_{\mathrm{par}} \sigma(\mathrm{cd}(U_3) \circ ((\mathrm{cd}(U_2)/x)\cdot \mathrm{cd}(U_4))) = \mathrm{cd}(U)$.

- *$U_1 = \varepsilon(U_3)$.* Since $U_1$ is `Eps`-headed, the only rule deriving $U_1 \Rightarrow_{\mathrm{par}} V_1$ is `ParEps`, so $V_1 = \varepsilon(V_3)$ for some $V_3$ with $U_3 \Rightarrow_{\mathrm{par}} V_3$. By the induction hypothesis, $V_3 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_3)$. So, by rule `ParComp$_\varepsilon$`: $V = \varepsilon(V_3)V_2 \Rightarrow_{\mathrm{par}} \sigma(\mathrm{cd}(U_3) \circ \mathrm{cd}(U_2)) = \mathrm{cd}(U)$.

- *Otherwise* ($U_1$ is neither `Lam`-headed, a `Lam`-headed `Comp`, nor `Eps`-headed). Then $\mathrm{cd}(U) = \mathrm{cd}(U_1)\,\mathrm{cd}(U_2)$. By the induction hypothesis, $V_1 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_1)$. So, by rule `ParApp`: $V = V_1 V_2 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_1)\,\mathrm{cd}(U_2) = \mathrm{cd}(U)$.

**`ParExtn`.** $U = (U_1/x)\cdot U_2$, $V = (V_1/x)\cdot V_2$, from $U_1 \Rightarrow_{\mathrm{par}} V_1$, $U_2 \Rightarrow_{\mathrm{par}} V_2$. By the induction hypothesis, $V_1 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_1)$ and $V_2 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_2)$. So, by rule `ParExtn`: $V = (V_1/x)\cdot V_2 \Rightarrow_{\mathrm{par}} (\mathrm{cd}(U_1)/x)\cdot \mathrm{cd}(U_2) = \mathrm{cd}(U)$.

**`ParVarComp`.** $U = x \circ U_1$, $V = \sigma(x \circ V_1)$, from $U_1 \Rightarrow_{\mathrm{par}} V_1$. By the induction hypothesis, $V_1 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_1)$. By the Composition Compatibility Lemma (applied with $x \Rightarrow_{\mathrm{par}} x$ via `ParVar`, and $V_1 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_1)$): $V = \sigma(x \circ V_1) \Rightarrow_{\mathrm{par}} \sigma(x \circ \mathrm{cd}(U_1)) = \mathrm{cd}(U)$.

**`ParLamComp`.** $U = (\lambda x.\,U_1) \circ U_2$, $V = \sigma((\lambda x.\,V_1) \circ V_2)$, from $U_1 \Rightarrow_{\mathrm{par}} V_1$, $U_2 \Rightarrow_{\mathrm{par}} V_2$. By the induction hypothesis, $V_1 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_1)$ and $V_2 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_2)$. By the Composition Compatibility Lemma (applied with $\lambda x.\,V_1 \Rightarrow_{\mathrm{par}} \lambda x.\,\mathrm{cd}(U_1)$ via `ParLam`, and $V_2 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_2)$): $V = \sigma((\lambda x.\,V_1) \circ V_2) \Rightarrow_{\mathrm{par}} \sigma((\lambda x.\,\mathrm{cd}(U_1)) \circ \mathrm{cd}(U_2)) = \mathrm{cd}(U)$.

**`ParBeta`.** $U = (\lambda x.\,U_1)U_2$, $V = \sigma(V_1 \circ ((V_2/x)\cdot \mathsf{id}))$, from $U_1 \Rightarrow_{\mathrm{par}} V_1$, $U_2 \Rightarrow_{\mathrm{par}} V_2$. By the induction hypothesis, $V_1 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_1)$ and $V_2 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_2)$, so also $(V_2/x)\cdot \mathsf{id} \Rightarrow_{\mathrm{par}} (\mathrm{cd}(U_2)/x)\cdot \mathsf{id}$ (rule `ParExtn`, with $\mathsf{id} \Rightarrow_{\mathrm{par}} \mathsf{id}$ via `ParId`). By the Composition Compatibility Lemma: $V = \sigma(V_1 \circ ((V_2/x)\cdot \mathsf{id})) \Rightarrow_{\mathrm{par}} \sigma(\mathrm{cd}(U_1) \circ ((\mathrm{cd}(U_2)/x)\cdot \mathsf{id})) = \mathrm{cd}(U)$.

**`ParBetaClos`.** $U = ((\lambda x.\,U_1) \circ U_3)U_2$, $V = \sigma(V_1 \circ ((V_2/x)\cdot V_3))$, from $U_1 \Rightarrow_{\mathrm{par}} V_1$, $U_2 \Rightarrow_{\mathrm{par}} V_2$, $U_3 \Rightarrow_{\mathrm{par}} V_3$. By the induction hypothesis, $V_1 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_1)$, $V_2 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_2)$, $V_3 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_3)$, so also $(V_2/x)\cdot V_3 \Rightarrow_{\mathrm{par}} (\mathrm{cd}(U_2)/x)\cdot \mathrm{cd}(U_3)$ (rule `ParExtn`). By the Composition Compatibility Lemma: $V = \sigma(V_1 \circ ((V_2/x)\cdot V_3)) \Rightarrow_{\mathrm{par}} \sigma(\mathrm{cd}(U_1) \circ ((\mathrm{cd}(U_2)/x)\cdot \mathrm{cd}(U_3))) = \mathrm{cd}(U)$.

**`ParComp$_\varepsilon$`.** $U = \varepsilon(U_1)U_2$, $V = \sigma(V_1 \circ V_2)$, from $U_1 \Rightarrow_{\mathrm{par}} V_1$, $U_2 \Rightarrow_{\mathrm{par}} V_2$. By the induction hypothesis, $V_1 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_1)$ and $V_2 \Rightarrow_{\mathrm{par}} \mathrm{cd}(U_2)$. By the Composition Compatibility Lemma: $V = \sigma(V_1 \circ V_2) \Rightarrow_{\mathrm{par}} \sigma(\mathrm{cd}(U_1) \circ \mathrm{cd}(U_2)) = \mathrm{cd}(U)$.

This exhausts every rule by which $U \Rightarrow_{\mathrm{par}} V$ could have been derived, so $V \Rightarrow_{\mathrm{par}} \mathrm{cd}(U)$ holds whenever $U \Rightarrow_{\mathrm{par}} V$.

#### End of Proof.

---

## Remarks and Adjustments Made to the Source Material

- **Notation changed from $U^{*}$ to $\mathrm{cd}(U)$.** Consistent with `docs/enve-complete-development.md`, this document writes the complete development function as $\mathrm{cd}$ rather than the thesis's postfix star.
- **`ParApp`'s three "shape-forcing" observations made explicit.** In the sub-cases of `ParApp` where $U_1$ is `Lam`-headed, a `Lam`-headed `Comp`, or `Eps`-headed, the scanned source asserts that $V_1$ has the correspondingly-shaped form (e.g. $V_1 = \lambda x.\,V_3$) without stating why. This document adds, in each of the first three sub-cases, the one-sentence reason: since $U_1$'s head constructor admits only one rule of $\Rightarrow_{\mathrm{par}}$ that could derive $U_1 \Rightarrow_{\mathrm{par}} V_1$ (`ParLam`, `ParLamComp`, or `ParEps` respectively -- each rule's conclusion pattern being tied to a specific head constructor), $V_1$ is forced into the matching shape.
- **No other changes.** Every other case matches the corresponding rule of `docs/enve-parallel-reduction.md`, the corresponding case of `docs/enve-complete-development.md`, and (where used) the Composition Compatibility Lemma (`docs/enve-parallel-reduction-composition-compatibility.md`) exactly; no further corrections were needed.
- **No constants involved.** As with every other reduction document in this repository, this lemma does not involve `Const` or any constant symbols, since $\lambda_{\mathrm{Env}\varepsilon}$ has none (`docs/enve-syntax.md`).
